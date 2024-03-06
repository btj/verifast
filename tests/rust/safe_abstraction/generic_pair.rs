pub struct Pair<A, B> {
    fst: A,
    snd: B
}

/*@

pred Pair_own<A, B>(t: thread_id_t, fst: A, snd: B) = <A>.own(t, fst) &*& <B>.own(t, snd);

pred Pair_share<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>) =
    [_](<A>.share)(k, t, &(*l).fst) &*&
    pointer_within_limits(&(*l).snd) == true &*&
    [_](<B>.share)(k, t, &(*l).snd);

lem Pair_share_mono<A, B>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req type_interp::<A>() &*& type_interp::<B>() &*& lifetime_inclusion(k1, k) == true &*& [_]Pair_share::<A, B>(k, t, l);
    ens type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k1, t, l);
{
    open Pair_share(k, t, l);
    share_mono::<A>(k, k1, t, &(*l).fst);
    share_mono::<B>(k, k1, t, &(*l).snd);
    close Pair_share(k1, t, l);
    leak Pair_share(k1, t, l);
}

lem Pair_share_full<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req type_interp::<A>() &*& type_interp::<B>() &*& full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k, t, l) &*& [q]lifetime_token(k);
{
    assume(false); // TODO; requires splitting the full borrow.
}

@*/

impl<A, B> Pair<A, B> {

    pub fn new(fst: A, snd: B) -> Self {
        //@ close Pair_own::<A, B>(_t, fst, snd);
        Pair { fst, snd }
    }

    pub fn get_fst_leak_snd(self) -> A {
        //@ open Pair_own::<A, B>(_t, self.fst, self.snd);
        let _snd = std::mem::ManuallyDrop::new(self.snd);
        //@ leak <B>.own(_t, self.snd);
        self.fst
    }

    pub fn get_snd_leak_fst(self) -> B {
        //@ open Pair_own::<A, B>(_t, self.fst, self.snd);
        let _fst = std::mem::ManuallyDrop::new(self.fst);
        //@ leak <A>.own(_t, self.fst);
        self.snd
    }
    
    pub fn deref_fst<'a>(&'a self) -> &'a A {
        //@ open Pair_share::<A, B>(a, _t, self);
        &self.fst
    }
    
    pub fn deref_snd<'a>(&'a self) -> &'a B {
        //@ open Pair_share::<A, B>(a, _t, self);
        &self.snd
    }

}
