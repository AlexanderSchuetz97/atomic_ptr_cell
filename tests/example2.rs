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
