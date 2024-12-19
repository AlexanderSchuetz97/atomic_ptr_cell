use atomic_ptr_cell::{AtomicPointerCell, AtomicPtrCell, BorrowGuard, BorrowSwapResult};
use std::ptr::null_mut;
use std::sync::atomic::Ordering::SeqCst;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

#[test]
pub fn tc1() {
    let mut a = [Box::into_raw(Box::new(1u32)), Box::into_raw(Box::new(2))];
    let n = unsafe { AtomicPointerCell::from_ptr_slice(a.as_mut()) };
    assert_eq!(1, n[0].take().unwrap());
    assert_eq!(2, n[1].take().unwrap());
    assert!(n[0].take().is_none());
    assert!(n[1].take().is_none());

    let brw = n[0].as_ptr_cell();
    brw.set(54);
    assert_eq!(54, n[0].take().unwrap());
    assert!(brw.take().is_none());
}

#[test]
pub fn tc2() {
    let a = [
        AtomicPtr::new(Box::into_raw(Box::new(1u32))),
        AtomicPtr::new(Box::into_raw(Box::new(2))),
    ];
    let n = unsafe { AtomicPointerCell::from_slice(a.as_slice()) };
    assert_eq!(1, n[0].take().unwrap());
    assert_eq!(2, n[1].take().unwrap());
    assert!(n[0].take().is_none());
    assert!(n[1].take().is_none());

    let brw = n[0].as_ptr_cell();
    brw.set(54);
    assert_eq!(54, n[0].take().unwrap());
    assert!(brw.take().is_none());
}

#[test]
pub fn tc3() {
    let n = unsafe { AtomicPointerCell::from_ptr(AtomicPtr::new(Box::into_raw(Box::new(1u32)))) };
    assert_eq!(1, n.take().unwrap());
    assert!(n.take().is_none());
}

#[test]
pub fn tc4() {
    let n = AtomicPointerCell::from_value(1u32);
    assert_eq!(1, n.take().unwrap());
    assert!(n.take().is_none());
}

#[test]
pub fn tc5() {
    let n = AtomicPointerCell::from_box(Box::new(1u32));
    assert_eq!(1, n.take().unwrap());
    assert!(n.take().is_none());
}

#[test]
pub fn tc6() {
    let cell = AtomicPointerCell::new();
    assert!(cell.is_empty());
    cell.set(1);
    assert_eq!(1, cell.take().unwrap());
    assert!(cell.take().is_none());
    assert!(cell.is_empty());
    assert!(cell.swap(2).is_none());
    assert_eq!(2, cell.swap(3).unwrap());
    assert!(!cell.is_empty());
    assert_eq!(3, cell.take().unwrap());
    assert!(cell.is_empty());
    assert!(cell.take().is_none());
    cell.set(4);
    assert!(!cell.is_empty());
    cell.set(5);
    assert_eq!(5, cell.swap(6).unwrap());
    assert_eq!(7, cell.set_if_absent(7).unwrap());
    assert_eq!(6, cell.take().unwrap());
    assert!(cell.set_if_absent(8).is_none());
    assert_eq!(8, cell.take().unwrap());
    assert_eq!(9, cell.set_if_present(9).unwrap());
    assert!(cell.is_empty());
    assert_eq!(9, cell.set_if_present(9).unwrap_empty());
    cell.set(10);
    assert_eq!(10, cell.set_if_present(11).unwrap());
    assert_eq!(11, cell.take().unwrap());
    cell.set(12);
    assert_eq!(12, cell.set_if_present(13).unwrap_value());
    assert_eq!(13, cell.take().unwrap());
}

#[test]
pub fn tc7() {
    let cell = AtomicPointerCell::new();
    assert!(cell.is_empty());
    assert!(cell.borrow().is_none());
    cell.set(1);
    let guard = cell.borrow().unwrap();
    assert!(cell.is_empty());
    assert_eq!(1, *guard);
    assert!(cell.is_empty());
    cell.set(2);
    assert!(!cell.is_empty());
    assert_eq!(2, cell.take().unwrap());
    assert!(cell.is_empty());
    drop(guard);
    assert!(!cell.is_empty());
    assert_eq!(1, cell.take().unwrap());
    assert!(cell.is_empty());
}

#[test]
pub fn tc8() {
    let cell = AtomicPointerCell::new();
    assert!(cell.is_empty());
    let guard = cell.borrow_or_else(|| 1);
    assert!(cell.is_empty());
    assert_eq!(1, *guard);
    assert!(cell.is_empty());
    drop(guard);
    let guard = cell.borrow_or_else(|| unreachable!());
    assert!(cell.is_empty());
    assert_eq!(1, *guard);
    assert!(cell.is_empty());
    drop(guard);
    assert!(!cell.is_empty());
    assert_eq!(1, cell.take().unwrap());
    assert!(cell.is_empty());
}

#[test]
pub fn tc9() {
    let cell = AtomicPointerCell::new();
    assert!(cell.is_empty());
    cell.set(1);
    let guard = cell.borrow_swap(2).unwrap();
    assert!(!cell.is_empty());
    assert_eq!(1, *guard);
    assert!(!cell.is_empty());
    assert_eq!(2, cell.take().unwrap());
    drop(guard);
    assert_eq!(1, cell.take().unwrap());
}

static CELL10: AtomicPointerCell<u32> = AtomicPointerCell::new();
#[test]
pub fn tc10() {
    CELL10.set(0);
    let toggle = Arc::new(AtomicBool::new(true));
    let mut threads = Vec::new();
    for n in 0..100 {
        let toggle = toggle.clone();
        threads.push(thread::spawn(move || {
            while toggle.load(SeqCst) {
                let uw = CELL10.set_if_present(n).unwrap_value();
                assert!(uw < 100);

                #[cfg(not(miri))] // we don't want to be nice to miri!
                thread::yield_now();
            }
        }));
    }

    thread::sleep(Duration::from_secs(10));
    toggle.store(false, SeqCst);
    for thread in threads {
        thread.join().unwrap();
    }
}

static CELL11: AtomicPointerCell<u32> = AtomicPointerCell::new();
#[test]
pub fn tc11() {
    let insert_count = Arc::new(AtomicU64::new(0));
    let take_count = Arc::new(AtomicU64::new(0));

    let toggle = Arc::new(AtomicBool::new(true));
    let mut threads = Vec::new();
    for n in 0..50 {
        {
            let toggle = toggle.clone();
            let insert_count = insert_count.clone();
            threads.push(thread::spawn(move || {
                while toggle.load(SeqCst) {
                    if CELL11.set_if_absent(n).is_none() {
                        insert_count.fetch_add(1, SeqCst);
                    }

                    #[cfg(not(miri))] // we don't want to be nice to miri!
                    thread::yield_now();
                }
            }));
        }
        {
            let toggle = toggle.clone();
            let take_count = take_count.clone();
            threads.push(thread::spawn(move || {
                while toggle.load(SeqCst) {
                    if CELL11.take().is_some() {
                        take_count.fetch_add(1, SeqCst);
                    }

                    #[cfg(not(miri))] // we don't want to be nice to miri!
                    thread::yield_now();
                }
            }));
        }
    }

    thread::sleep(Duration::from_secs(10));
    toggle.store(false, SeqCst);
    for thread in threads {
        thread.join().unwrap();
    }

    if CELL11.take().is_some() {
        take_count.fetch_add(1, SeqCst);
    }

    assert_eq!(insert_count.load(SeqCst), take_count.load(SeqCst));
}

#[test]
pub fn tc12() {
    let cell = AtomicPointerCell::new();
    assert!(cell.is_empty());
    match cell.borrow_swap(2) {
        BorrowSwapResult::BorrowSwapped(x) => panic!("{:?}", x),
        BorrowSwapResult::CellWasEmpty(y) => assert_eq!(y, 2),
    }
    drop(cell);
}

#[test]
pub fn tc13() {
    fn test_cell(cell: AtomicPtrCell<i32>, load: i32) {
        cell.set(1);
        assert_eq!(1, cell.take().unwrap());
        assert!(cell.take().is_none());
        assert!(cell.is_empty());
        assert!(cell.swap(2).is_none());
        assert_eq!(2, cell.swap(3).unwrap());
        assert!(!cell.is_empty());
        assert_eq!(3, cell.take().unwrap());
        assert!(cell.is_empty());
        assert!(cell.take().is_none());
        cell.set(4);
        assert!(!cell.is_empty());
        cell.set(5);
        assert_eq!(5, cell.swap(6).unwrap());
        assert_eq!(7, cell.set_if_absent(7).unwrap());
        assert_eq!(6, cell.take().unwrap());
        assert!(cell.set_if_absent(8).is_none());
        assert_eq!(8, cell.take().unwrap());
        assert_eq!(9, cell.set_if_present(9).unwrap());
        assert!(cell.is_empty());
        assert_eq!(9, cell.set_if_present(9).unwrap_empty());
        cell.set(10);
        assert_eq!(10, cell.set_if_present(11).unwrap());
        assert_eq!(11, cell.take().unwrap());
        cell.set(12);
        assert_eq!(12, cell.set_if_present(13).unwrap_value());
        assert_eq!(13, cell.take().unwrap());
        cell.set(load);
    }
    unsafe {
        let ptr = AtomicPtr::new(null_mut());
        test_cell(AtomicPtrCell::new(&ptr), 14);
        assert_eq!(*Box::from_raw(ptr.load(SeqCst)), 14);

        let mut ptr: *mut i32 = null_mut();
        test_cell(AtomicPtrCell::from_ptr(&mut ptr), 15);
        assert_eq!(*Box::from_raw(ptr), 15);

        let ptr1 = AtomicPtr::new(null_mut());
        let ptr2 = AtomicPtr::new(null_mut());
        let slice1 = &[&ptr1, &ptr2];
        let slice2 = AtomicPtrCell::from_slice(slice1.as_slice());
        test_cell(slice2[0], 16);
        test_cell(slice2[1], 17);
        assert_eq!(*Box::from_raw(ptr1.load(SeqCst)), 16);
        assert_eq!(*Box::from_raw(ptr2.load(SeqCst)), 17);

        let mut ptr1: *mut i32 = null_mut();
        let mut ptr2: *mut i32 = null_mut();
        let slice1: &[*mut *mut i32; 2] = &[&mut ptr1, &mut ptr2];
        let slice2 = AtomicPtrCell::from_ptr_slice(slice1.as_slice());
        test_cell(slice2[0], 18);
        test_cell(slice2[1], 19);
        assert_eq!(*Box::from_raw(ptr1), 18);
        assert_eq!(*Box::from_raw(ptr2), 19);
    }
}

#[test]
pub fn tc14() {
    unsafe {
        let ato = AtomicPtr::new(null_mut::<i32>());
        let x = AtomicPtrCell::new(&ato);
        let a = x.inner().as_ptr();
        let b = ato.as_ptr();
        assert_eq!(a, b);
    }
}

#[test]
pub fn tc15() {
    let ptr = AtomicPointerCell::new();
    let r = ptr.borrow_swap(1);
    assert!(!r.is_ok());
    assert!(r.is_err());
    assert_eq!(r.unwrap_err(), 1);
    let r = ptr.borrow_swap(2);
    assert!(!r.is_ok());
    assert!(r.is_err());
    assert!(format!("{:?}", &r).contains("CellWasEmpty("));
    let x = std::panic::catch_unwind(|| {
        r.unwrap();
    });

    assert!(x.is_err());
    ptr.set(3);
    let r = ptr.borrow_swap(4);
    assert!(r.is_ok());
    assert!(!r.is_err());
    assert!(format!("{:?}", &r).contains("BorrowSwapped("));
    let x = std::panic::catch_unwind(|| {
        r.unwrap_err();
    });

    assert!(x.is_err());
    let r = ptr.borrow_swap(5);
    let x: Result<BorrowGuard<i32>, i32> = r.into();
    assert!(x.is_ok());
    assert_eq!(4, *x.unwrap());
    ptr.take();
    let r = ptr.borrow_swap(6);
    let x: Result<BorrowGuard<i32>, i32> = r.into();
    assert!(x.is_err());
    assert_eq!(6, x.unwrap_err());
}

#[test]
pub fn tc16() {
    let mut ptr = AtomicPointerCell::new();
    ptr.set(4);
    let g = unsafe { *ptr.inner().load(SeqCst) };
    assert_eq!(4, g);
    let gg = unsafe { ptr.inner_mut().get_mut().as_mut().unwrap() };
    *gg = 5;

    let x = ptr.into_inner();
    unsafe {
        assert_eq!(5, *Box::from_raw(x.load(SeqCst)));
    }
}

#[test]
pub fn tc17() {
    let ptr = AtomicPointerCell::new();
    ptr.set(1);
    let r = ptr.set_if_present(2);
    assert!(!r.is_empty());
    assert!(r.is_value());
    assert!(
        format!("{:?}", &r).contains("CellHadValue("),
        "{}",
        format!("{:?}", &r)
    );
    let x = std::panic::catch_unwind(|| {
        r.unwrap_empty();
    });

    assert!(x.is_err());

    assert_eq!(ptr.take().unwrap(), 2);
    let r = ptr.set_if_present(3);
    assert!(r.is_empty());
    assert!(!r.is_value());
    assert!(
        format!("{:?}", &r).contains("CellWasEmpty("),
        "{}",
        format!("{:?}", &r)
    );
    let x = std::panic::catch_unwind(|| {
        r.unwrap_value();
    });

    assert!(x.is_err());
}

#[test]
pub fn tc18() {
    let ptr = AtomicPointerCell::new();
    assert!(ptr.swap_boxed(Box::new(1)).is_none());
    assert_eq!(ptr.swap_boxed(Box::new(2)).unwrap(), Box::new(1));
    ptr.set_boxed(Box::new(3));
    assert_eq!(ptr.take_boxed().unwrap(), Box::new(3));
    assert_eq!(ptr.set_if_present_boxed(Box::new(4)).unwrap(), Box::new(4));
    assert!(ptr.set_if_absent_boxed(Box::new(5)).is_none());
    assert_eq!(ptr.set_if_present_boxed(Box::new(6)).unwrap(), Box::new(5));

    let guard = ptr.borrow_or_else_boxed(|| unreachable!());
    assert!(ptr.take_boxed().is_none());
    assert_eq!(*guard, 6);
    guard.discard();

    let guard = ptr.borrow_or_else_boxed(|| Box::new(7));
    assert!(ptr.take_boxed().is_none());
    assert_eq!(*guard, 7);
    drop(guard);

    let mut guard = ptr.borrow_swap_boxed(Box::new(8)).unwrap();
    assert_eq!(ptr.take().unwrap(), 8);
    assert_eq!(*guard, 7);
    assert!(!guard.try_swap());
    ptr.set(9);
    assert!(guard.try_swap());
    assert_eq!(*guard, 9);
    guard = guard.try_drop().unwrap();
    assert_eq!(ptr.take().unwrap(), 7);
    assert!(guard.try_drop().is_none());

    assert_eq!(ptr.take().unwrap(), 9);
}

#[test]
pub fn tc19() {
    let ptr = AtomicPointerCell::new();
    ptr.set(1);
    let guard = ptr.borrow().unwrap();
    guard.discard_if_absent();
    assert!(ptr.take().is_none());

    ptr.set(1);
    let guard = ptr.borrow().unwrap();
    ptr.set(2);
    guard.discard_if_absent();
    assert_eq!(1, ptr.take().unwrap());
}

#[test]
pub fn tc20() {
    let ptr = AtomicPointerCell::new();
    ptr.set(1);
    let mut guard = ptr.borrow().unwrap();
    assert_eq!(*guard, 1);
    *guard = 2;
    assert_eq!(*guard, 2);
    guard.force();

    let guard = ptr.borrow().unwrap();
    assert_eq!(*guard, 2);
    ptr.set(3);
    guard.force();

    assert_eq!(ptr.take().unwrap(), 2);
}

#[test]
pub fn tc21() {
    let ptr = AtomicPointerCell::new();
    ptr.set(1);
    let guard = ptr.borrow().unwrap();
    assert_eq!(Box::new(1), guard.into_inner_box());

    ptr.set(2);
    let guard = ptr.borrow().unwrap();
    assert_eq!(2, guard.into_inner());
}

#[test]
pub fn tc22() {
    let ptr = AtomicPointerCell::from("beep".to_string());
    assert_eq!("beep", ptr.take().unwrap());

    let g: AtomicPtr<String> = ptr.into();
    assert!(g.load(SeqCst).is_null());

    let ptr = AtomicPointerCell::from("beep".to_string());
    let cell1 = ptr.as_ptr_cell();
    let cell2 = cell1;

    assert_eq!("beep", cell1.take().unwrap());
    cell2.set("beep2".to_string());
    assert_eq!("beep2", cell1.take().unwrap());

    let cell: AtomicPtrCell<String> = (&ptr).into();
    assert!(cell.take().is_none());
}
