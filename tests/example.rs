use atomic_ptr_cell::*;
use std::thread;

static CELL: AtomicPointerCell<String> = AtomicPointerCell::new();

#[test]
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
        _ = jh.join();
        let value = CELL.take().unwrap();
        assert!("Hello" == value.as_str() || "World" == value.as_str());
        return;
    };

    assert!("Hello" == value.as_str() || "World" == value.as_str());
    _ = jh.join();
    if let Some(value2) = CELL.take() {
        //Depending on the order of execution CELL.take() may return None here.
        assert_ne!(value, value2);
    }
}
