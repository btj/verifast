/*@
pred<T> <ptr::NonNull<T>>.own(t, nonNull;) = nonNull.pointer as usize != 0;
pred_ctor ptr::NonNull_frac_bc<T>(t: thread_id_t, l: *ptr::NonNull<T>)(;) = (*l).pointer |-> ?p &*& struct_ptr::NonNull_padding(l) &*& ptr::NonNull_own(t, ptr::NonNull::<T> { pointer: p });
pred<T> <ptr::NonNull<T>>.share(k, t, l) =
    frac_borrow(k, ptr::NonNull_frac_bc(t, l));

lem ptr::NonNull_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *ptr::NonNull<T>)
    req lifetime_inclusion(k1, k) == true &*& [_]ptr::NonNull_share(k, t, l);
    ens [_]ptr::NonNull_share(k1, t, l);
{
    open ptr::NonNull_share::<T>()(k, t, l);
    frac_borrow_mono(k, k1, ptr::NonNull_frac_bc(t, l));
    assert [?q]frac_borrow(k1, _);
    close [q]ptr::NonNull_share::<T>()(k1, t, l);
}

lem ptr::NonNull_share_full<T>(k: lifetime_t, t: thread_id_t, l: *ptr::NonNull<T>)
    req atomic_mask(Nlft) &*& full_borrow(k, ptr::NonNull_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [_]ptr::NonNull_share(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(ptr::NonNull_frac_bc(t, l), ptr::NonNull_full_borrow_content(t, l))(){
        open ptr::NonNull_frac_bc::<T>(t, l)();
        close ptr::NonNull_full_borrow_content::<T>(t, l)();
    }{
        produce_lem_ptr_chunk implies(ptr::NonNull_full_borrow_content(t, l), ptr::NonNull_frac_bc(t, l))(){
            open ptr::NonNull_full_borrow_content::<T>(t, l)();
            close ptr::NonNull_frac_bc::<T>(t, l)();
        }{
            full_borrow_implies(k, ptr::NonNull_full_borrow_content(t, l), ptr::NonNull_frac_bc(t, l));
            full_borrow_into_frac_m(k, ptr::NonNull_frac_bc(t, l));
        }
    }
    assert [?qf]frac_borrow(k, ptr::NonNull_frac_bc(t, l));
    close [qf]ptr::NonNull_share::<T>(k, t, l);
}
@*/

pub mod ptr {
    pub struct NonNull<T> {
        pointer: *const T,
    }

    impl<T> NonNull<T> {
        pub fn from<'a>(reference: &'a mut T) -> Self {
            let r = NonNull {
                pointer: reference as *mut T,
            };
            //@ open_full_borrow(_q_a, 'a, <T>.full_borrow_content(_t, reference));
            //@ open_full_borrow_content::<T>(_t, reference);
            //@ points_to_limits(reference);
            //@ close_full_borrow_content::<T>(_t, reference);
            //@ close_full_borrow(<T>.full_borrow_content(_t, reference));
            //@ close ptr::NonNull_own::<T>(_t, r);
            //@ leak full_borrow(_, _);
            r
        }

        pub unsafe fn new_unchecked(ptr: *mut T) -> Self
            //@ req true;
            //@ ens result.pointer == ptr;
        {
            NonNull { pointer: ptr }
        }

        pub unsafe fn as_ref<'a>(&'a self) -> &'a T
            //@ req [?q](*self).pointer |-> ?p &*& ref_precreated_token(p, ?r) &*& ref_initialized(r);
            //@ ens [q](*self).pointer |-> p &*& ref_initialized(r) &*& result == r;
        {
            &*self.pointer
        }

        pub fn as_ptr(self) -> *mut T {
            //@ open ptr::NonNull_own::<T>(_t, _);
            self.pointer as *mut T
        }
    }

    impl<T> Copy for NonNull<T> {}
    impl<T> Clone for NonNull<T> {
        fn clone<'a>(&'a self) -> Self {
            //@ open ptr::NonNull_share::<T>()('a, _t, self);
            //@ open_frac_borrow('a, ptr::NonNull_frac_bc(_t, self), _q_a);
            //@ open ptr::NonNull_frac_bc::<T>(_t, self)();
            let r = *self;
            //@ open ptr::NonNull_own::<T>(_t, ?nnp);
            //@ assert [?qp](*self).pointer |-> _;
            //@ close [qp]ptr::NonNull_own::<T>()(_t, nnp);
            //@ close [qp]ptr::NonNull_frac_bc::<T>(_t, self)();
            //@ close_frac_borrow(qp, ptr::NonNull_frac_bc(_t, self));
            //@ close ptr::NonNull_own::<T>(_t, r);
            r
        }
    }
}
