fn ref_mut_test() {
    unsafe {
        let mut x = 0;
        let p = &mut x as *mut i32;
        *p = 10;
        //@ end_ref_mut(p);
        let q = &mut x as *mut i32;
        *q = 20;
        //@ end_ref_mut(q);
        // *p = 30; // This should fail
    }
}

fn print(_x: i32) {}

fn ref_test() {
    unsafe {
        let mut x = 0;
        //@ let p_ = precreate_ref(&x);
        //@ init_ref(p_, 1/3);
        let p = &x as *const i32 as *mut i32;
        print(*p);
        //@ let q_ = precreate_ref(&x);
        //@ init_ref(q_, 1/3);
        let q = &x as *const i32 as *mut i32;
        print(*q);
        // x = 3; // This should fail
        print(*p);
        print(*q);
        //@ end_ref(p);
        //@ end_ref(q);
        x = 3;
    }
}