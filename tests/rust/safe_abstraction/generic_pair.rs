pub struct Pair<A, B> {
    fst: A,
    snd: B
}

/*@

pred<A, B> <Pair<A, B>>.own(t, pair) = <A>.own(t, pair.fst) &*& <B>.own(t, pair.snd);

lem Pair_drop<A, B>()
    req Pair_own::<A, B>(?t, ?pair);
    ens <A>.own(t, pair.fst) &*& <B>.own(t, pair.snd);
{
    open Pair_own::<A, B>(t, pair);
}

lem Pair_send<A, B>(t1: thread_id_t)
    req type_interp::<A>() &*& type_interp::<B>() &*& Pair_own::<A, B>(?t, ?pair) &*& is_Send(typeid(A)) && is_Send(typeid(B));
    ens type_interp::<A>() &*& type_interp::<B>() &*& Pair_own::<A, B>(t1, pair);
{
    open Pair_own::<A, B>(t, pair);
    Send::send::<A>(t, t1, pair.fst);
    Send::send::<B>(t, t1, pair.snd);
    close Pair_own::<A, B>(t1, pair);
}

pred<A, B> <Pair<A, B>>.share(k, t, l) =
    [_](<A>.share)(k, t, &(*l).fst) &*&
    pointer_within_limits(&(*l).snd) == true &*&
    [_](<B>.share)(k, t, &(*l).snd);

lem Pair_share_mono<A, B>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req type_interp::<A>() &*& type_interp::<B>() &*& lifetime_inclusion(k1, k) == true &*& [_]Pair_share::<A, B>(k, t, l);
    ens type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k1, t, l);
{
    open Pair_share::<A, B>()(k, t, l);
    share_mono::<A>(k, k1, t, &(*l).fst);
    share_mono::<B>(k, k1, t, &(*l).snd);
    close Pair_share::<A, B>()(k1, t, l);
    leak Pair_share(k1, t, l);
}

pred_ctor struct_Pair_padding_<A, B>(l: *Pair<A, B>)() = struct_Pair_padding(l);

pred True(;) = true;

lem Pair_split_full_borrow_m<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req
        atomic_mask(?mask) &*& mask_le(Nlft, mask) == true &*&
        type_interp::<A>() &*& type_interp::<B>() &*&
        full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k);
    ens
        atomic_mask(mask) &*& type_interp::<A>() &*& type_interp::<B>() &*&
        full_borrow(k, <A>.full_borrow_content(t, &(*l).fst)) &*&
        full_borrow(k, <B>.full_borrow_content(t, &(*l).snd)) &*&
        [q]lifetime_token(k) &*&
        pointer_within_limits(&(*l).snd) == true;
{
    let klong = open_full_borrow_strong_m(k, Pair_full_borrow_content::<A, B>(t, l), q);
    {
        open Pair_full_borrow_content::<A, B>(t, l)();
        open Pair_fst(l, _);
        open Pair_snd(l, _);
        open Pair_own::<A, B>(_, _);
        close struct_Pair_padding_::<A, B>(l)();
        close_full_borrow_content::<A>(t, &(*l).fst);
        close_full_borrow_content::<B>(t, &(*l).snd);
        close sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        close sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
    }
    produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))), klong, Pair_full_borrow_content::<A, B>(t, l))() {
        open sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
        open struct_Pair_padding_::<A, B>(l)();
        open sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        open_full_borrow_content(t, &(*l).fst);
        open_full_borrow_content(t, &(*l).snd);
        close Pair_fst(l, ?fst);
        close Pair_snd(l, ?snd);
        close Pair_own::<A, B>(t, Pair::<A, B> { fst, snd });
        close Pair_full_borrow_content::<A, B>(t, l)();
    } {
        close_full_borrow_strong_m(klong, Pair_full_borrow_content::<A, B>(t, l), sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    }
    full_borrow_mono(klong, k, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    full_borrow_split_m(k, struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)));
    full_borrow_split_m(k, <A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd));
    leak full_borrow(k, struct_Pair_padding_::<A, B>(l));
}

lem Pair_split_full_borrow<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>) // TODO: Eliminate this duplication.
    nonghost_callers_only
    req
        full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k);
    ens
        full_borrow(k, <A>.full_borrow_content(t, &(*l).fst)) &*&
        full_borrow(k, <B>.full_borrow_content(t, &(*l).snd)) &*&
        [q]lifetime_token(k) &*&
        pointer_within_limits(&(*l).snd) == true;
{
    produce_type_interp::<A>();
    produce_type_interp::<B>();
    let klong = open_full_borrow_strong(k, Pair_full_borrow_content::<A, B>(t, l), q);
    {
        open Pair_full_borrow_content::<A, B>(t, l)();
        open Pair_fst(l, _);
        open Pair_snd(l, _);
        open Pair_own::<A, B>(_, _);
        close struct_Pair_padding_::<A, B>(l)();
        close_full_borrow_content::<A>(t, &(*l).fst);
        close_full_borrow_content::<B>(t, &(*l).snd);
        close sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        close sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
    }
    produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))), klong, Pair_full_borrow_content::<A, B>(t, l))() {
        open sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
        open struct_Pair_padding_::<A, B>(l)();
        open sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        open_full_borrow_content(t, &(*l).fst);
        open_full_borrow_content(t, &(*l).snd);
        close Pair_fst(l, ?fst);
        close Pair_snd(l, ?snd);
        close Pair_own::<A, B>(t, Pair::<A, B> { fst, snd });
        close Pair_full_borrow_content::<A, B>(t, l)();
    } {
        close_full_borrow_strong(klong, Pair_full_borrow_content::<A, B>(t, l), sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    }
    full_borrow_mono(klong, k, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    full_borrow_split(k, struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)));
    full_borrow_split(k, <A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd));
    leak full_borrow(k, struct_Pair_padding_::<A, B>(l));
    leak type_interp() &*& type_interp();
}

lem Pair_share_full<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req atomic_mask(Nlft) &*& type_interp::<A>() &*& type_interp::<B>() &*& full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens atomic_mask(Nlft) &*& type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k, t, l) &*& [q]lifetime_token(k);
{
    Pair_split_full_borrow_m(k, t, l);
    share_full_borrow_m::<A>(k, t, &(*l).fst);
    share_full_borrow_m::<B>(k, t, &(*l).snd);
    close Pair_share::<A, B>(k, t, l);
    leak Pair_share(k, t, l);
}

lem init_ref_Pair<A, B>(p: *Pair<A, B>)
    req type_interp::<A>() &*& type_interp::<B>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Pair_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<A>() &*& type_interp::<B>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Pair_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open Pair_share::<A, B>(k, t, x);
    open_ref_init_perm(p);
    init_ref_share(k, t, &(*p).fst);
    init_ref_share(k, t, &(*p).snd);
    note(pointer_within_limits(ref_origin(&(*p).snd)));
    close Pair_share::<A, B>(k, t, p);
    leak Pair_share(k, t, p);
    frac_borrow_sep(k, ref_initialized_(&(*p).fst), ref_initialized_(&(*p).snd));
    produce_lem_ptr_chunk implies_frac(sep_(ref_initialized_(&(*p).fst), ref_initialized_(&(*p).snd)), ref_initialized_(p))() {
        open [?f]sep_(ref_initialized_(&(*p).fst), ref_initialized_(&(*p).snd))();
        open ref_initialized_::<A>(&(*p).fst)();
        open ref_initialized_::<B>(&(*p).snd)();
        close_ref_initialized(p);
        close [f]ref_initialized_::<Pair<A, B>>(p)();
    } {
        produce_lem_ptr_chunk implies_frac(ref_initialized_(p), sep_(ref_initialized_(&(*p).fst), ref_initialized_(&(*p).snd)))() {
            open [?f]ref_initialized_::<Pair<A, B>>(p)();
            open_ref_initialized(p);
            close [f]ref_initialized_::<A>(&(*p).fst)();
            close [f]ref_initialized_::<B>(&(*p).snd)();
            close [f]sep_(ref_initialized_(&(*p).fst), ref_initialized_(&(*p).snd))();
        } {
            frac_borrow_implies(k, sep_(ref_initialized_(&(*p).fst), ref_initialized_(&(*p).snd)), ref_initialized_(p));
        }
    }
}

lem Pair_sync<A, B>(t1: thread_id_t)
    req type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(?k, ?t, ?l) &*& is_Sync(typeid(A)) && is_Sync(typeid(B));
    ens type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k, t1, l);
{
    open Pair_share::<A, B>(k, t, l);
    Sync::sync::<A>(k, t, t1, &(*l).fst);
    Sync::sync::<B>(k, t, t1, &(*l).snd);
    close Pair_share::<A, B>(k, t1, l);
    leak Pair_share::<A, B>(k, t1, l);
}

@*/

impl<A, B> Pair<A, B> {

    pub fn new(fst: A, snd: B) -> Self {
        //@ close Pair_own::<A, B>(_t, Pair::<A, B> { fst, snd });
        Pair { fst, snd }
    }

    pub fn get_fst_leak_snd(self) -> A {
        //@ open Pair_own::<A, B>(_t, _);
        let _snd = std::mem::ManuallyDrop::new(self.snd);
        //@ leak <B>.own(_t, self.snd);
        self.fst
    }

    pub fn get_fst_drop_snd(self) -> A {
        //@ open Pair_own::<A, B>(_t, _);
        std::mem::drop(self.snd);
        self.fst
    }

    pub fn get_snd_leak_fst(self) -> B {
        //@ open Pair_own::<A, B>(_t, _);
        let _fst = std::mem::ManuallyDrop::new(self.fst);
        //@ leak <A>.own(_t, self.fst);
        self.snd
    }
    
    pub fn get_snd_drop_fst(self) -> B {
        //@ open Pair_own::<A, B>(_t, self);
        std::mem::drop(self.fst);
        self.snd
    }
    
    pub fn deref_fst<'a>(&'a self) -> &'a A {
        //@ open Pair_share::<A, B>('a, _t, self);
        &self.fst
    }
    
    pub fn deref_snd<'a>(&'a self) -> &'a B {
        //@ open Pair_share::<A, B>('a, _t, self);
        &self.snd
    }
    
    pub fn replace_fst<'a>(&'a mut self, new_fst: A) -> A {
        unsafe {
            //@ open_full_borrow(_q_a, 'a, Pair_full_borrow_content::<A, B>(_t, self));
            //@ open Pair_full_borrow_content::<A, B>(_t, self)();
            //@ open Pair_own::<A, B>(_t, ?pair0);
            //@ open Pair_fst(self, pair0.fst);
            let result = std::ptr::read(&self.fst);
            std::ptr::write(&mut self.fst, new_fst);
            //@ close Pair_fst(self, new_fst);
            //@ close Pair_own::<A, B>(_t, Pair::<A, B> { fst: new_fst, snd: pair0.snd });
            //@ close Pair_full_borrow_content::<A, B>(_t, self)();
            //@ close_full_borrow(Pair_full_borrow_content::<A, B>(_t, self));
            //@ leak full_borrow(_, _);
            result
        }
    }

    pub fn replace_snd<'a>(&'a mut self, new_snd: B) -> B {
        unsafe {
            //@ open_full_borrow(_q_a, 'a, Pair_full_borrow_content::<A, B>(_t, self));
            //@ open Pair_full_borrow_content::<A, B>(_t, self)();
            //@ open Pair_own::<A, B>(_t, ?pair0);
            //@ open Pair_snd(self, pair0.snd);
            let result = std::ptr::read(&self.snd);
            std::ptr::write(&mut self.snd, new_snd);
            //@ close Pair_snd(self, new_snd);
            //@ close Pair_own::<A, B>(_t, Pair::<A, B> { fst: pair0.fst, snd: new_snd });
            //@ close Pair_full_borrow_content::<A, B>(_t, self)();
            //@ close_full_borrow(Pair_full_borrow_content::<A, B>(_t, self));
            //@ leak full_borrow(_, _);
            result
        }
    }
    
    pub fn deref_fst_mut<'a>(&'a mut self) -> &'a mut A {
        //@ Pair_split_full_borrow('a, _t, self);
        //@ leak full_borrow('a, <B>.full_borrow_content(_t, &(*self).snd));
        &mut self.fst
    }

    pub fn deref_snd_mut<'a>(&'a mut self) -> &'a mut B {
        //@ Pair_split_full_borrow('a, _t, self);
        //@ leak full_borrow('a, <A>.full_borrow_content(_t, &(*self).fst));
        &mut self.snd
    }
    
}
