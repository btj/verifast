unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
    if !b { //~allow_dead_code
        let p = std::ptr::null_mut(); //~allow_dead_code
        *p = 42; //~allow_dead_code
    }
}

fn main() {
    unsafe {
        //@ assert thread_token(?t);
        let mut v = std::vec::Vec::<u8>::new();
        v.push(10);
        //@ end_ref_mut_();
        v.push(20);
        //@ end_ref_mut_();
        //@ std::vec::init_ref_Vec(precreate_ref(&v), 1/2);
        assert(v.len() == 2);
        //@ { assert ref_end_token(?r, &v, 1/2); std::vec::end_ref_Vec(r); }
        //@ std::vec::Vec_separate_buffer(v);
        //@ open array(?buffer, 2, _);
        //@ std::vec::init_ref_Vec(precreate_ref(&v), 1/2);
        let v1 = *v.as_ptr();
        //@ { assert ref_end_token(?r, &v, 1/2); std::vec::end_ref_Vec(r); }
        //@ open array(_, _, _);
        //@ std::vec::init_ref_Vec(precreate_ref(&v), 1/2);
        let v2 = *v.as_ptr().add(1);
        //@ { assert ref_end_token(?r, &v, 1/2); std::vec::end_ref_Vec(r); }
        assert(v1 == 10);
        assert(v2 == 20);
        //@ close array(buffer + 1, 1, [20]);
        //@ close array(buffer, 2, [10, 20]);
        //@ std::vec::Vec_unseparate_buffer(v);
        //@ close u8_own(t, 10);
        //@ close own::<u8>(t)(10);
        //@ close u8_own(t, 20);
        //@ close own::<u8>(t)(20);
        //@ close foreach::<u8>([], own::<u8>(t));
        //@ close foreach::<u8>([20], own::<u8>(t));
        //@ close foreach::<u8>([10, 20], own::<u8>(t));
        //@ std::vec::Vec_to_own(v);
        std::mem::drop(v);
    }
}
