# atomic_ptr_cell
Safe no_std repr(transparent) wrapper for AtomicPtr and &AtomicPtr with an api similar to a cell.

The crate requires an allocator using `extern crate alloc;` if used without std.
This crate supports all targets that satisfy `#[cfg(target_has_atomic = "ptr")]`. 
On other targets this crate is a noop and does nothing.
## Comparison to other similar crates
|                 | Borrow  | Borrow Mut | Exclusive Borrow (*1) | Sound (*2)   | repr(transparent) | Borrowing solves ABA Problem | Supports &AtomicPtr<T> |
|-----------------|---------|------------|-----------------------|--------------|-------------------|------------------------------|------------------------|
| atomic_ptr_cell | &check; | &check;    | &cross;               | &check;      | &check;           | &cross;                      | &check;                |
| atomiccell      | &check; | &check;    | &check;               | &check;      | &cross;           | &check;                      | &cross;                |
| ptr_cell        | &cross; | &cross;    | _                     | &cross; (*3) | &check;           | _                            | &cross;                |

(*1) While a value is borrowed from the cell other threads cannot interact with the cell in a way that would violate borrowing rules if this were a normal RefCell:
<br>&check; other threads are prevented from modifying/accessing the cell
<br>&cross; other threads can overwrite the value in the cell while it is borrowed.

(*2) Can you cause UB using only safe functions from the crate?
<br>&check; UB is not possible using only safe functions of the crate.
<br>&cross; UB is possible with only using unsafe functions.

(*3) ptr_cell v2.1.1 replace_ptr fn should be unsafe as it allows the user to place an arbitrary pointer 
into its cell which is directly fed into Box::from_raw from various other safe fn's. 
This can cause UB if the user calls it with a non-null ptr not created by Box::into_raw making the entire fn unsound.
I refrain from creating an issue in that crate as comments in the source code indicate 
that the author of that crate is aware of it.

## How does this crate do borrowing?
A thread that borrows a value atomically moves it out of the cell and transfers ownership of it to the guard.
When the guard is dropped the value is atomically written back into the cell if the cell happens to be empty at that time.

Because the value is always temporarily owned by the guard it is both Deref and DerefMut of the cells type.

As should be obvious this does absolutely nothing to prevent [ABA](https://en.wikipedia.org/wiki/ABA_problem)
from occurring with the cell while the value is borrowed.
If you require this then consider using the `atomiccell` crate.

## Convenience features of atomic_ptr_cell
Aside from the really obvious new/set/take/borrow functions this crate provides the following fn's for its cell types.
1. `from(&[&AtomicPtr]) -> &[&Cell]` constructor (essentially mem transmute thanks to repr(transparent))
2. const `new() -> Cell` constructor
3. `swap(T) -> Option<T>`
4. `set_if_absent(T) -> Option<T>`
   - returns Some(input) if the cell was not empty. None if input is now in the cell.
5. `set_if_present(T) -> enum WasPresent(T) or WasAbsent(T)`
6. `borrow_swap(T) -> enum WasPresent(Guard(T)) or WasAbsent(T)`
   - Borrow the value into a guard and atomically replace it with the given value instead of leaving the cell empty.
   - Only swaps the value if the cell was not empty initially.
7. `borrow_or_else(FnOnce() -> T) -> Guard(T)`
   - Move the value from the cell into the guard or use the value provided from the function if the cell was empty to fill the guard.
8. Into/From implementations where they make sense. (ex: `From<T> for Cell<T>`)
9. Discard a Guard(T) so that its value is not written back into the cell.
10. Force the value of a Guard(T) to be written back into the cell even if the cell contains another value in the meantime.


## Is this crate lock/wait free?
This crate is lock free. 

It is not entirely wait free. The `set_if_present` fn is not wait free and contains the usual CAS loop.

## Examples

### Owned AtomicPtr

```rust
use std::thread;
use atomic_ptr_cell::*;

static CELL: AtomicPointerCell<String> = AtomicPointerCell::new();

fn test() {
 CELL.set("Hello".to_string());
 let guard = CELL.borrow().unwrap();
 assert_eq!("Hello", guard.as_str());
 let jh = thread::spawn(|| {
    CELL.set("World".to_string());
    let guard = CELL.borrow().unwrap();
    assert!("Hello" == guard.as_str() || "World" == guard.as_str());
    drop(guard);

 });
 drop(guard);

 //This small example already has a surprising amount of possible outcomes :D

 let Some(value) = CELL.take() else {
    _= jh.join();
    let value = CELL.take().unwrap();
    assert!("Hello" == value.as_str() || "World" == value.as_str());
    return;
 };

 assert!("Hello" == value.as_str() || "World" == value.as_str());
 _= jh.join();
 if let Some(value2) = CELL.take() {
    //Depending on the order of execution CELL.take() may return None here.
    assert_ne!(value, value2);
 }
}
```

### &AtomicPtr reference:

```rust
use atomic_ptr_cell::*;
use std::ptr::null_mut;
use std::sync::atomic::AtomicPtr;
use std::thread;

static CELL: AtomicPtr<String> = AtomicPtr::new(null_mut());

#[test]
fn test() {
   // Safety: Caller must guarantee that the AtomicPtr never contains a non-null pointer that is not from Box::into_raw
   let cell: AtomicPtrCell<String> = unsafe { AtomicPtrCell::new(&CELL) };
   cell.set("Hello".to_string());
   let guard = cell.borrow().unwrap();
   assert_eq!("Hello", guard.as_str());
   let jh = thread::spawn(move || {
      //The AtomicPtrCell is copy as its layout is equivalent to &AtomicPtr
      // making it easy to use in closures and threads.
      // You just need to ensure the lifetime of &AtomicPtr outlives the scope.
      // In this example the lifetime is static.

      cell.set("World".to_string());
      let guard = cell.borrow().unwrap();
      assert!("Hello" == guard.as_str() || "World" == guard.as_str());
      drop(guard);
   });
   drop(guard);

   //This small example already has a surprising amount of possible outcomes :D

   let Some(value) = cell.take() else {
      _ = jh.join();
      let value = cell.take().unwrap();
      assert!("Hello" == value.as_str() || "World" == value.as_str());
      return;
   };

   assert!("Hello" == value.as_str() || "World" == value.as_str());
   _ = jh.join();
   if let Some(value2) = cell.take() {
      //Depending on the order of execution CELL.take() may return None here.
      assert_ne!(value, value2);
   }
}
```