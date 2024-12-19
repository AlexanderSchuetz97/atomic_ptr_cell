//! # `atomic_ptr_cell`
//! Safe `no_std` repr(transparent) wrapper for `AtomicPtr` and &`AtomicPtr` with an api similar to a cell.
//!
//! The crate requires an allocator using `extern crate alloc;` if used without std.
//! # Example using owned `AtomicPtr`:
//! ```rust
//! use std::thread;
//! use atomic_ptr_cell::*;
//!
//! static CELL: AtomicPointerCell<String> = AtomicPointerCell::new();
//!
//! fn test() {
//!  CELL.set("Hello".to_string());
//!  let guard = CELL.borrow().unwrap();
//!  assert_eq!("Hello", guard.as_str());
//!  let jh = thread::spawn(|| {
//!     CELL.set("World".to_string());
//!     let guard = CELL.borrow().unwrap();
//!     assert!("Hello" == guard.as_str() || "World" == guard.as_str());
//!     drop(guard);
//!
//!  });
//!  drop(guard);
//!
//!  //This small example already has a surprising amount of possible outcomes :D
//!
//!  let Some(value) = CELL.take() else {
//!     _= jh.join();
//!     let value = CELL.take().unwrap();
//!     assert!("Hello" == value.as_str() || "World" == value.as_str());
//!     return;
//!  };
//!
//!  assert!("Hello" == value.as_str() || "World" == value.as_str());
//!  _= jh.join();
//!  if let Some(value2) = CELL.take() {
//!     //Depending on the order of execution CELL.take() may return None here.
//!     assert_ne!(value, value2);
//!  }
//! }
//! ```
//!
//! # Example using `&AtomicPtr` reference
//! ```rust
//! use atomic_ptr_cell::*;
//! use std::ptr::null_mut;
//! use std::sync::atomic::AtomicPtr;
//! use std::thread;
//!
//! static CELL: AtomicPtr<String> = AtomicPtr::new(null_mut());
//!
//! fn test() {
//!     // Safety: Caller must guarantee that the AtomicPtr never contains a non-null pointer that is not from Box::into_raw
//!     let cell: AtomicPtrCell<String> = unsafe { AtomicPtrCell::new(&CELL) };
//!     cell.set("Hello".to_string());
//!     let guard = cell.borrow().unwrap();
//!     assert_eq!("Hello", guard.as_str());
//!     let jh = thread::spawn(move || {
//!         //The AtomicPtrCell is copy as its layout is equivalent to &AtomicPtr
//!         // making it easy to use in closures and threads.
//!         // You just need to ensure the lifetime of &AtomicPtr outlives the scope.
//!         // In this example the lifetime is static.
//!         cell.set("World".to_string());
//!         let guard = cell.borrow().unwrap();
//!         assert!("Hello" == guard.as_str() || "World" == guard.as_str());
//!         drop(guard);
//!     });
//!     drop(guard);
//!
//!     //This small example already has a surprising amount of possible outcomes :D
//!
//!     let Some(value) = cell.take() else {
//!         _ = jh.join();
//!         let value = cell.take().unwrap();
//!         assert!("Hello" == value.as_str() || "World" == value.as_str());
//!         return;
//!     };
//!
//!     assert!("Hello" == value.as_str() || "World" == value.as_str());
//!     _ = jh.join();
//!     if let Some(value2) = cell.take() {
//!         //Depending on the order of execution CELL.take() may return None here.
//!         assert_ne!(value, value2);
//!     }
//! }
//! ```
#![no_std]
#![deny(clippy::correctness)]
#![deny(
    clippy::perf,
    clippy::complexity,
    clippy::style,
    clippy::nursery,
    clippy::pedantic,
    clippy::clone_on_ref_ptr,
    clippy::decimal_literal_representation,
    clippy::float_cmp_const,
    clippy::missing_docs_in_private_items,
    clippy::multiple_inherent_impl,
    clippy::unwrap_used,
    clippy::cargo_common_metadata,
    clippy::used_underscore_binding
)]

#[cfg(target_has_atomic = "ptr")]
pub use inner::*;

/// inner module that contains the actual implementation.
#[cfg(target_has_atomic = "ptr")]
mod inner {
    extern crate alloc;
    use alloc::boxed::Box;
    use core::fmt::{Debug, Formatter};
    use core::ops::{Deref, DerefMut};
    use core::ptr::null_mut;
    use core::sync::atomic::Ordering::SeqCst;
    use core::sync::atomic::{AtomicPtr, Ordering};

    /// Result enum to indicate the outcomes of a `borrow_swap` operation.
    pub enum BorrowSwapResult<'a, T: Sync + Send + 'static, E: Sync + Send + 'static> {
        /// Borrow swap succeeded and the returned guard should be used.
        BorrowSwapped(BorrowGuard<'a, T>),
        /// Cell was empty when the borrow swap operation was performed
        CellWasEmpty(E),
    }

    impl<T: Sync + Send + Debug + 'static, E: Sync + Send + Debug + 'static> Debug
        for BorrowSwapResult<'_, T, E>
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            match self {
                BorrowSwapResult::BorrowSwapped(inner) => {
                    f.write_fmt(format_args!("BorrowSwapped({inner:?})"))
                }
                BorrowSwapResult::CellWasEmpty(inner) => {
                    f.write_fmt(format_args!("CellWasEmpty({inner:?})"))
                }
            }
        }
    }

    impl<'a, T: Sync + Send + 'static, E: Sync + Send + 'static> BorrowSwapResult<'a, T, E> {
        /// Unwraps the borrow guard
        /// # Panics
        /// if `CellWasEmpty`
        pub fn unwrap(self) -> BorrowGuard<'a, T> {
            match self {
                BorrowSwapResult::BorrowSwapped(inner) => inner,
                BorrowSwapResult::CellWasEmpty(_) => {
                    panic!("unwrap called on BorrowSwapResult::CellWasEmpty()")
                }
            }
        }

        pub const fn is_ok(&self) -> bool {
            matches!(self, BorrowSwapResult::BorrowSwapped(_))
        }

        pub const fn is_err(&self) -> bool {
            matches!(self, BorrowSwapResult::CellWasEmpty(_))
        }

        /// Unwraps the value intended as replacement as result of a failed operation.
        /// # Panics
        /// if `BorrowSwapped`
        pub fn unwrap_err(self) -> E {
            match self {
                BorrowSwapResult::BorrowSwapped(_) => {
                    panic!("unwrap_err called on BorrowSwapResult::BorrowSwapped()")
                }
                BorrowSwapResult::CellWasEmpty(inner) => inner,
            }
        }

        /// Maps the type in the `CellWasEmpty` case. Does nothing for `BorrowSwapped`.
        pub fn map_err<X: Sync + Send + 'static>(
            self,
            f: impl FnOnce(E) -> X,
        ) -> BorrowSwapResult<'a, T, X> {
            match self {
                BorrowSwapResult::BorrowSwapped(inner) => {
                    BorrowSwapResult::BorrowSwapped::<T, X>(inner)
                }
                BorrowSwapResult::CellWasEmpty(inner) => BorrowSwapResult::CellWasEmpty(f(inner)),
            }
        }

        /// Transforms this into a `core::Result` type.
        /// # Errors
        /// In case of `CellWasEmpty`
        pub fn into_result(self) -> Result<BorrowGuard<'a, T>, E> {
            match self {
                BorrowSwapResult::BorrowSwapped(inner) => Ok(inner),
                BorrowSwapResult::CellWasEmpty(inner) => Err(inner),
            }
        }
    }

    impl<'a, T: Sync + Send + 'static, E: Sync + Send + 'static> From<BorrowSwapResult<'a, T, E>>
        for Result<BorrowGuard<'a, T>, E>
    {
        fn from(value: BorrowSwapResult<'a, T, E>) -> Self {
            value.into_result()
        }
    }

    pub enum PresentResult<T: Sync + Send + 'static> {
        /// The cell had a value when the operation was performed
        CellHadValue(T),
        /// The cell did not have a value when the operation was performed.
        CellWasEmpty(T),
    }

    impl<T: Sync + Send + Debug + 'static> Debug for PresentResult<T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            match self {
                Self::CellHadValue(inner) => f.write_fmt(format_args!("CellHadValue({inner:?})")),
                Self::CellWasEmpty(inner) => f.write_fmt(format_args!("CellWasEmpty({inner:?})")),
            }
        }
    }

    impl<T: Sync + Send + 'static> PresentResult<T> {
        /// Unwraps the `PresentResult`, this call never fails but the information what type of value is referred to is lost.
        pub fn unwrap(self) -> T {
            match self {
                Self::CellHadValue(inner) | Self::CellWasEmpty(inner) => inner,
            }
        }

        /// Unwraps the `PresentResult::CellWasEmpty` result.
        /// # Panics
        /// if called on `PresentResult::CellHadValue`
        pub fn unwrap_empty(self) -> T {
            match self {
                Self::CellHadValue(_) => {
                    panic!("unwrap_empty() on PresentResult::CellHadValue")
                }
                Self::CellWasEmpty(inner) => inner,
            }
        }

        /// Unwraps the `PresentResult::CellHadValue` result.
        /// # Panics
        /// if called on `PresentResult::CellWasEmpty`
        pub fn unwrap_value(self) -> T {
            match self {
                Self::CellHadValue(inner) => inner,
                Self::CellWasEmpty(_) => {
                    panic!("unwrap_value() on PresentResult::CellWasEmpty")
                }
            }
        }

        /// Returns true if the result is a result from a Cell value.
        pub const fn is_value(&self) -> bool {
            matches!(self, Self::CellHadValue(_))
        }

        /// Returns true if the result contains data not from the cell because the cell was empty.
        pub const fn is_empty(&self) -> bool {
            matches!(self, Self::CellWasEmpty(_))
        }

        /// Maps the value in the `PresentResult`
        pub fn map<X: Sync + Send + 'static>(self, f: impl FnOnce(T) -> X) -> PresentResult<X> {
            match self {
                Self::CellHadValue(inner) => PresentResult::CellHadValue(f(inner)),
                Self::CellWasEmpty(inner) => PresentResult::CellWasEmpty(f(inner)),
            }
        }
    }

    ///
    /// This is a helper struct that is guaranteed to have the exact same layout as `AtomicPtr<T>`.
    ///
    /// It offers high level safe manipulation functions to move data in and out of the pointer.
    /// It offers boxed and non-boxed variants for operation.
    /// In general all boxed operations are marginally faster because the "Box" is already on the heap
    /// and the data must not be moved from the stack to the heap and vice versa.
    ///
    #[repr(transparent)]
    #[derive(Debug)]
    pub struct AtomicPointerCell<T: Sync + Send + 'static>(AtomicPtr<T>);

    impl<T: Sync + Send + 'static> AtomicPointerCell<T> {
        /// Constructs a new `AtomicPointerCell` without a value.
        #[must_use]
        pub const fn new() -> Self {
            Self(AtomicPtr::new(null_mut()))
        }

        ///
        /// # Safety
        /// The ptr must contain 0 or a pointer created by `Box::into_raw`
        /// Any external write to the pointer may also not violate this constraint
        /// during the lifetime of the returned `AtomicPointerCell`.
        #[must_use]
        pub const unsafe fn from_ptr(ptr: AtomicPtr<T>) -> Self {
            Self(ptr)
        }

        ///
        /// # Safety
        /// Every pointer in the slice must either be null or crated by `Box::into_raw` and be of type T.
        /// Any external writes to the pointers may also not violate this constraint during the lifetime of the returned slice.
        #[must_use]
        pub const unsafe fn from_ptr_slice(value: &mut [*mut T]) -> &mut [Self] {
            core::slice::from_raw_parts_mut(value.as_mut_ptr().cast::<Self>(), value.len())
        }

        ///
        /// # Safety
        /// Every `AtomicPtr` in the slice must either contain null or a pointer crated by `Box::into_raw` and be of type T.
        /// Any external writes to the pointers may also not violate this constraint during the lifetime of the returned slice.
        #[must_use]
        pub const unsafe fn from_slice(value: &[AtomicPtr<T>]) -> &[Self] {
            core::slice::from_raw_parts(value.as_ptr().cast::<Self>(), value.len())
        }

        /// Constructs a new `AtomicPointerCell` with a value.
        #[must_use]
        pub fn from_value(value: T) -> Self {
            Self(AtomicPtr::new(Box::into_raw(Box::new(value))))
        }

        /// Constructs a new `AtomicPointerCell` with a boxed value.
        #[must_use]
        pub fn from_box(value: Box<T>) -> Self {
            Self(AtomicPtr::new(Box::into_raw(value)))
        }

        /// Deconstructs this `AtomicPointerCell` into its raw `AtomicPtr`.
        #[must_use]
        pub const fn into_inner(self) -> AtomicPtr<T> {
            self.0
        }

        /// Gets an unowned `AtomicPtrCell`.
        /// It is subject to the lifetime of this `AtomicPointerCell`,
        /// but otherwise refers to the same underlying `AtomicPtr`
        ///
        /// The layout of the `AtomicPtrCell` is guaranteed to be equivalent to that of a `&AtomicPtr`.
        #[must_use]
        pub const fn as_ptr_cell(&self) -> AtomicPtrCell<'_, T> {
            AtomicPtrCell::from_internal(&self.0)
        }

        /// returns true if the cell is currently observed to be empty according to the given ordering.
        pub fn is_empty(&self) -> bool {
            self.as_ptr_cell().is_empty()
        }

        /// Atomically swap the current value with the given value.
        /// returns None if the pointer was null
        pub fn swap(&self, value: T) -> Option<T> {
            self.as_ptr_cell().swap(value)
        }

        /// Atomically swap the current value with the given value.
        /// returns None if the pointer was null
        pub fn swap_boxed(&self, value: Box<T>) -> Option<Box<T>> {
            self.as_ptr_cell().swap_boxed(value)
        }

        /// Atomically Take T out of the pointer or return None if the pointer was null.
        pub fn take(&self) -> Option<T> {
            self.take_boxed().map(|v| *v)
        }

        /// Atomically Take T out of the pointer or return None if the pointer was null.
        pub fn take_boxed(&self) -> Option<Box<T>> {
            self.as_ptr_cell().take_boxed()
        }

        /// Atomically sets the value of the pointer to T.
        /// This fn is also guaranteed to invoke the Drop
        /// of a previous value if one was present before returning.
        pub fn set(&self, value: T) {
            self.as_ptr_cell().set(value);
        }

        /// Atomically sets the value of the pointer to T.
        /// This fn is also guaranteed to invoke the Drop
        /// of a previous value if one was present before returning.
        pub fn set_boxed(&self, value: Box<T>) {
            self.as_ptr_cell().set_boxed(value);
        }

        /// Atomically sets the value in the cell if the cell was empty.
        /// If the Cell was not empty then Some is returned containing
        /// the value that was intended to be written into the cell.
        pub fn set_if_absent(&self, value: T) -> Option<T> {
            self.as_ptr_cell().set_if_absent(value)
        }

        /// Atomically sets the value in the cell if the cell was empty.
        /// If the Cell was not empty then Some is returned containing
        /// the value that was intended to be written into the cell.
        pub fn set_if_absent_boxed(&self, value: Box<T>) -> Option<Box<T>> {
            self.as_ptr_cell().set_if_absent_boxed(value)
        }

        /// Atomically replaces the value in a Cell if the Cell is not empty.
        /// If the cell is empty then this fn does not modify the cell and instead returns `PresetResult::CellWasEmpty` with the value that would have been stored in the cell otherwise.
        /// If the cell was not empty then `PresetResult::WasPresent` is returned containing the value that was atomically replaced.
        pub fn set_if_present(&self, value: T) -> PresentResult<T> {
            self.as_ptr_cell().set_if_present(value)
        }

        /// Atomically replaces the value in a Cell if the Cell is not empty.
        /// If the cell is empty then this fn does not modify the cell and instead returns `PresetResult::CellWasEmpty` with the value that would have been stored in the cell otherwise.
        /// If the cell was not empty then `PresetResult::WasPresent` is returned containing the value that was atomically replaced.
        pub fn set_if_present_boxed(&self, value: Box<T>) -> PresentResult<Box<T>> {
            self.as_ptr_cell().set_if_present_boxed(value)
        }

        /// Moves the value out of the cell and put it in a `BorrowGuard`.
        /// The returned guard Deref's the value.
        /// Once the guard is dropped the value is moved back
        /// into the cell if it is empty at that time.
        /// Otherwise, dropping the guard drops the value.
        pub fn borrow(&self) -> Option<BorrowGuard<'_, T>> {
            self.as_ptr_cell().borrow()
        }

        /// Moves the value out of the cell and put it in a `BorrowGuard`.
        /// The returned guard Deref's the value.
        /// Once the guard is dropped the value is moved back
        /// into the cell if it is empty at that time.
        /// Otherwise, dropping the guard drops the value.
        ///
        /// If the cell is empty this fn calls the `FnOnce` to create a value to put into the `BorrowGuard`.
        /// The value will be moved into the Cell once the
        ///
        pub fn borrow_or_else(&self, f: impl FnOnce() -> T) -> BorrowGuard<'_, T> {
            self.as_ptr_cell().borrow_or_else(f)
        }

        /// Moves the value out of the cell and put it in a `BorrowGuard`.
        /// The returned guard Deref's the value.
        /// Once the guard is dropped the value is moved back
        /// into the cell if it is empty at that time.
        /// Otherwise, dropping the guard drops the value.
        ///
        /// If the cell is empty this fn calls the `FnOnce` to create a value to put into the `BorrowGuard`.
        /// The value will be moved into the Cell once the
        ///
        pub fn borrow_or_else_boxed(&self, f: impl FnOnce() -> Box<T>) -> BorrowGuard<'_, T> {
            self.as_ptr_cell().borrow_or_else_boxed(f)
        }

        /// Borrows the current value in the cell and in doing so atomically replaces the value with the given value.
        /// If the cell was empty then this fn returns `CellWasEmpty` with value that should
        /// have been stored in the cell and the cell is left empty.
        pub fn borrow_swap(&self, value: T) -> BorrowSwapResult<T, T> {
            self.as_ptr_cell().borrow_swap(value)
        }

        /// Borrows the current value in the cell and in doing so atomically replaces the value with the given value.
        /// If the cell was empty then this fn returns `CellWasEmpty` with value that should
        /// have been stored in the cell and the cell is left empty.
        pub fn borrow_swap_boxed(&self, value: Box<T>) -> BorrowSwapResult<T, Box<T>> {
            self.as_ptr_cell().borrow_swap_boxed(value)
        }

        ///
        /// Get the inner ptr.
        /// # Safety
        /// The caller must guarantee that no values other than pointers created by `Box::into_raw` or null can be read from the underlying pointer.
        /// The easiest way to guarantee this is to never write those "garbage" values into the pointer.
        ///
        /// In addition, the caller can assume that any invocation of any fn of this crate in any thread may move the value behind the pointer or drop it making the pointer dangling.
        /// If the caller wants to get a "ref" to the underlying value of the pointer then it must therefore ensure that no such calls occur
        ///
        pub const unsafe fn inner(&self) -> &AtomicPtr<T> {
            &self.0
        }

        ///
        /// Get the inner ptr as a mut.
        ///
        /// # Safety
        /// The caller must guarantee that no values other than pointers created by `Box::into_raw` or null can be read from the underlying pointer.
        /// The easiest way to guarantee this is to never write those "garbage" values into the pointer.
        ///
        /// In addition, the caller can assume that any invocation of any fn of this crate may move the value behind the pointer or drop it making the pointer dangling.
        /// If the caller wants to get a "ref" to the underlying value of the pointer then it must therefore ensure that no such calls occur
        ///
        pub const unsafe fn inner_mut(&mut self) -> &mut AtomicPtr<T> {
            &mut self.0
        }
    }

    ///
    /// This is a helper struct that is guaranteed to have the exact same layout as `&AtomicPtr<T>`.
    ///
    /// It offers high level safe manipulation functions to move data in and out of the pointer.
    /// It offers boxed and non-boxed variants for operation.
    /// In general all boxed operations are marginally faster because the "Box" is already on the heap
    /// and the data must not be moved from the stack to the heap and vice versa.
    ///
    #[repr(transparent)]
    #[derive(Debug)]
    pub struct AtomicPtrCell<'a, T: Sync + Send + 'static>(&'a AtomicPtr<T>);

    impl<'a, T: Sync + Send + 'static> AtomicPtrCell<'a, T> {
        ///
        /// Construct a new non-owned `AtomicPtrCell` from a given `AtomicPtr`.
        /// # Safety
        /// `AtomicPtr` must contain null or a pointer made by `Box<T>::into_raw`
        ///
        pub const unsafe fn new(value: &'a AtomicPtr<T>) -> Self {
            Self(value)
        }

        ///
        /// # Safety
        /// The pointer must contain null or a pointer made by `Box<T>::into_raw`
        /// Pointer must be valid for the lifetime `'a`.
        ///
        pub const unsafe fn from_ptr(value: *mut *mut T) -> Self {
            Self(AtomicPtr::from_ptr(value))
        }

        ///
        /// # Safety
        /// Each `AtomicPtr` in the slice must either contain null or a pointer made by `Box<T>::into_raw`
        ///
        pub const unsafe fn from_slice<'b>(value: &'b [&'a AtomicPtr<T>]) -> &'b [Self] {
            core::slice::from_raw_parts(value.as_ptr().cast::<AtomicPtrCell<T>>(), value.len())
        }

        ///
        /// # Safety
        /// The slice must not contain null elements.
        /// Each Pointer in the slice must point to a pointer which is either null or was made by `Box<T>::into_raw`
        /// The pointers must be valid for the lifetime 'a.
        ///
        pub const unsafe fn from_ptr_slice(value: &[*mut *mut T]) -> &[Self] {
            core::slice::from_raw_parts(value.as_ptr().cast::<AtomicPtrCell<T>>(), value.len())
        }

        /// Internal constructor where safety guarantees can be made.
        pub(crate) const fn from_internal(value: &'a AtomicPtr<T>) -> Self {
            Self(value)
        }

        /// Helper fn to turn the moved raw ptr into a Box if it was not null.
        fn inner_from_raw(value: *mut T) -> Option<Box<T>> {
            if value.is_null() {
                return None;
            }

            Some(unsafe { Box::from_raw(value) })
        }

        /// returns true if the cell is currently observed to be empty according to the given ordering.
        #[must_use]
        pub fn is_empty(&self) -> bool {
            self.0.load(SeqCst).is_null()
        }

        /// Atomically swaps the value out of the cell returning the previous value if there was one.
        #[must_use]
        pub fn swap(&self, value: T) -> Option<T> {
            self.swap_boxed(Box::new(value)).map(|v| *v)
        }

        /// Atomically swaps the value out of the cell returning the previous value if there was one.
        #[must_use]
        pub fn swap_boxed(&self, value: Box<T>) -> Option<Box<T>> {
            Self::inner_from_raw(self.0.swap(Box::into_raw(value), SeqCst))
        }

        /// Atomically moves the value out of the cell leaving it empty.
        /// returns none if the cell was already empty.
        #[must_use = "use take_boxed() instead if you want to just discard the value as it is just slightly faster."]
        pub fn take(&self) -> Option<T> {
            self.take_boxed().map(|v| *v)
        }

        /// Atomically moves the value out of the cell leaving it empty.
        /// returns none if the cell was already empty.
        #[allow(clippy::must_use_candidate)]
        pub fn take_boxed(&self) -> Option<Box<T>> {
            Self::inner_from_raw(self.0.swap(null_mut(), SeqCst))
        }

        /// Atomically sets the value in the cell.
        /// If the cell was not empty then the previous value is dropped in the current thread before this fn returns.
        pub fn set(&self, value: T) {
            self.set_boxed(Box::new(value));
        }

        /// Atomically sets the value in the cell.
        /// If the cell was not empty then the previous value is dropped in the current thread before this fn returns.
        pub fn set_boxed(&self, value: Box<T>) {
            _ = self.swap_boxed(value);
        }

        /// Atomically sets the value in the cell if the cell was empty.
        /// If the Cell was not empty then Some is returned containing
        /// the value that was intended to be written into the cell.
        #[allow(clippy::must_use_candidate)]
        pub fn set_if_absent(&self, value: T) -> Option<T> {
            self.set_if_absent_boxed(Box::new(value)).map(|v| *v)
        }

        /// Atomically sets the value in the cell if the cell was empty.
        /// If the Cell was not empty then Some is returned containing
        /// the value that was intended to be written into the cell.
        #[allow(clippy::must_use_candidate)]
        pub fn set_if_absent_boxed(&self, value: Box<T>) -> Option<Box<T>> {
            let raw = Box::into_raw(value);
            if self
                .0
                .compare_exchange(null_mut(), raw, SeqCst, Ordering::Acquire)
                .is_err()
            {
                return Some(unsafe { Box::from_raw(raw) });
            };

            None
        }

        /// Atomically replaces the value in a Cell if the Cell is not empty.
        /// If the cell is empty then this fn does not modify the cell and instead returns `PresetResult::CellWasEmpty` with the value that would have been stored in the cell otherwise.
        /// If the cell was not empty then `PresetResult::WasPresent` is returned containing the value that was atomically replaced.
        #[allow(clippy::must_use_candidate)]
        pub fn set_if_present(&self, value: T) -> PresentResult<T> {
            self.set_if_present_boxed(Box::new(value)).map(|v| *v)
        }

        /// Atomically replaces the value in a Cell if the Cell is not empty.
        /// If the cell is empty then this fn does not modify the cell and instead returns `PresetResult::CellWasEmpty` with the value that would have been stored in the cell otherwise.
        /// If the cell was not empty then `PresetResult::WasPresent` is returned containing the value that was atomically replaced.
        #[allow(clippy::must_use_candidate)]
        pub fn set_if_present_boxed(&self, value: Box<T>) -> PresentResult<Box<T>> {
            let raw = Box::into_raw(value);

            let mut cur = self.0.load(SeqCst);
            loop {
                if cur.is_null() {
                    return PresentResult::CellWasEmpty(unsafe { Box::from_raw(raw) });
                }

                cur = match self.0.compare_exchange(cur, raw, SeqCst, SeqCst) {
                    Ok(actual) => {
                        return PresentResult::CellHadValue(unsafe { Box::from_raw(actual) })
                    }
                    Err(actual) => actual,
                };
            }
        }

        /// Moves the value out of the cell and put it in a `BorrowGuard`.
        /// The returned guard Deref's the value.
        /// Once the guard is dropped the value is moved back
        /// into the cell if it is empty at that time.
        /// Otherwise, dropping the guard drops the value.
        ///
        /// This fn returns none if the cell is empty.
        #[must_use]
        pub fn borrow(&self) -> Option<BorrowGuard<'a, T>> {
            self.take_boxed().map(|b| BorrowGuard(Some(b), self.0))
        }

        /// Moves the value out of the cell and put it in a `BorrowGuard`.
        /// The returned guard Deref's the value.
        /// Once the guard is dropped the value is moved back
        /// into the cell if it is empty at that time.
        /// Otherwise, dropping the guard drops the value.
        ///
        /// If the cell is empty this fn calls the `FnOnce` to create a value to put into the `BorrowGuard`.
        /// The value will be moved into the Cell once the
        ///
        pub fn borrow_or_else(&self, f: impl FnOnce() -> T) -> BorrowGuard<'a, T> {
            self.borrow_or_else_boxed(|| Box::new(f()))
        }

        /// Moves the value out of the cell and put it in a `BorrowGuard`.
        /// The returned guard Deref's the value.
        /// Once the guard is dropped the value is moved back
        /// into the cell if it is empty at that time.
        /// Otherwise, dropping the guard drops the value.
        ///
        /// If the cell is empty this fn calls the `FnOnce` to create a value to put into the `BorrowGuard`.
        /// The value will be moved into the Cell once the
        ///
        pub fn borrow_or_else_boxed(&self, f: impl FnOnce() -> Box<T>) -> BorrowGuard<'a, T> {
            self.borrow()
                .unwrap_or_else(|| BorrowGuard(Some(f()), self.0))
        }

        /// Borrows the current value in the cell and in doing so atomically replaces the value with the given value.
        /// If the cell was empty then this fn returns `CellWasEmpty` with value that should
        /// have been stored in the cell and the cell is left empty.
        pub fn borrow_swap(&self, value: T) -> BorrowSwapResult<'a, T, T> {
            self.borrow_swap_boxed(Box::new(value)).map_err(|v| *v)
        }

        /// Borrows the current value in the cell and in doing so atomically replaces the value with the given value.
        /// If the cell was empty then this fn returns `CellWasEmpty` with value that should
        /// have been stored in the cell and the cell is left empty.
        #[must_use]
        pub fn borrow_swap_boxed(&self, value: Box<T>) -> BorrowSwapResult<'a, T, Box<T>> {
            match self.set_if_present_boxed(value) {
                PresentResult::CellHadValue(value) => {
                    BorrowSwapResult::BorrowSwapped(BorrowGuard(Some(value), self.0))
                }
                PresentResult::CellWasEmpty(np) => BorrowSwapResult::CellWasEmpty(np),
            }
        }

        ///
        /// Get the inner ptr.
        /// # Safety
        /// The caller must guarantee that no values other than pointers created by `Box::into_raw` or null can be read from the underlying pointer.
        /// The easiest way to guarantee this is to never write those "garbage" values into the pointer.
        ///
        /// In addition, the caller can assume that any invocation of any fn of this crate in any thread may move the value behind the pointer or drop it making the pointer dangling.
        /// If the caller wants to get a "ref" to the underlying value of the pointer then it must therefore ensure that no such calls occur
        #[must_use]
        pub const unsafe fn inner(&self) -> &'a AtomicPtr<T> {
            self.0
        }
    }

    /// Borrow guard of a `AtomicCell`. Once this cell is dropped the value is moved back into the cell
    /// if the cell is empty at that time.
    ///
    /// This guard has no knowledge of what is happening to the cell in the meantime.
    /// It is entirely possible that during the lifetime of the guard the cell is filled and emptied multiple times.
    /// This has no effect on the behavior of the guard.
    /// The guard and its fn's only care about the state it can atomically observe when an action occurs, not what happened in the meantime.
    /// Essentially it does not solve the ABA problem and cannot be used for use cases where solving the ABA Problem is required.
    ///
    pub struct BorrowGuard<'a, T: Sync + Send + 'static>(Option<Box<T>>, &'a AtomicPtr<T>);
    impl<T: Sync + Send + 'static> BorrowGuard<'_, T> {
        /// Drop the borrow guard while discarding the value
        pub fn discard(mut self) {
            self.0 = None;
            //DROP IT
        }

        /// Drop the borrow guard and discard the value if the cell is empty.
        pub fn discard_if_absent(mut self) {
            _ = AtomicPtrCell::from_internal(self.1)
                .set_if_present_boxed(unsafe { self.0.take().unwrap_unchecked() });
            self.0 = None;
            //DROP IT
        }

        /// Try to swap the borrowed value with the value in the cell.
        /// Returns true if the value was swapped. false if the cell was empty.
        pub fn try_swap(&mut self) -> bool {
            let boxed = unsafe { self.0.take().unwrap_unchecked() };
            match AtomicPtrCell::from_internal(self.1).set_if_present_boxed(boxed) {
                PresentResult::CellHadValue(bx) => {
                    self.0 = Some(bx);
                    true
                }
                PresentResult::CellWasEmpty(bx) => {
                    self.0 = Some(bx);
                    false
                }
            }
        }

        /// Drop the borrow guard and write the value back into the cell.
        /// This may also drop the value in the cell that is replaced.
        pub fn force(mut self) {
            AtomicPtrCell::from_internal(self.1)
                .set_boxed(unsafe { self.0.take().unwrap_unchecked() });
            self.0 = None;
            //DROP IT
        }

        /// Drops the borrow guard if the value can be written back into the cell (i.e. the cell was empty)
        /// Returns Some(self) if the cell was not empty.
        #[allow(clippy::must_use_candidate)]
        pub fn try_drop(mut self) -> Option<Self> {
            if let Some(me) = AtomicPtrCell::from_internal(self.1)
                .set_if_absent_boxed(unsafe { self.0.take().unwrap_unchecked() })
            {
                self.0 = Some(me);
                return Some(self);
            }

            None
        }

        /// Drops the Borrow guard while yielding the inner value to the caller. The Cell is left untouched by this call.
        #[must_use]
        pub fn into_inner(mut self) -> T {
            unsafe { *self.0.take().unwrap_unchecked() }
        }

        /// Drops the Borrow guard while yielding the inner value to the caller. The Cell is left untouched by this call.
        #[must_use]
        pub fn into_inner_box(mut self) -> Box<T> {
            unsafe { self.0.take().unwrap_unchecked() }
        }
    }

    impl<T: Sync + Send + 'static> Drop for BorrowGuard<'_, T> {
        fn drop(&mut self) {
            if let Some(boxed) = self.0.take() {
                _ = AtomicPtrCell::from_internal(self.1).set_if_absent_boxed(boxed);
            }
        }
    }

    impl<T: Sync + Send + 'static> Deref for BorrowGuard<'_, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            unsafe { self.0.as_ref().unwrap_unchecked() }
        }
    }

    impl<T: Sync + Send + 'static> DerefMut for BorrowGuard<'_, T> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { self.0.as_mut().unwrap_unchecked() }
        }
    }

    impl<T: Sync + Send + Debug + 'static> Debug for BorrowGuard<'_, T> {
        fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
            f.write_fmt(format_args!("BorrowGuard({:?}, {:?})", self.0, self.1))
        }
    }

    impl<T: Sync + Send + 'static> From<T> for AtomicPointerCell<T> {
        fn from(value: T) -> Self {
            Self::from_value(value)
        }
    }

    impl<T: Sync + Send + 'static> Default for AtomicPointerCell<T> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T: Sync + Send + 'static> From<AtomicPointerCell<T>> for AtomicPtr<T> {
        fn from(value: AtomicPointerCell<T>) -> Self {
            value.into_inner()
        }
    }

    impl<'a, T: Sync + Send + 'static> From<&'a AtomicPointerCell<T>> for AtomicPtrCell<'a, T> {
        fn from(value: &'a AtomicPointerCell<T>) -> Self {
            value.as_ptr_cell()
        }
    }

    impl<T: Sync + Send + 'static> Clone for AtomicPtrCell<'_, T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T: Sync + Send + 'static> Copy for AtomicPtrCell<'_, T> {}
}
