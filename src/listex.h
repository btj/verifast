#ifndef LISTEX_H
#define LISTEX_H

/*

Contents:
- lemmas about the definitions in list.h (in the same order)
- fixpoints update, max

*/

/*@

lemma void take_plus_one<t>(int i, list<t> xs);
    requires 0 <= i &*& i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));

lemma void distinct_mem_nth_take<t>(list<t> xs, int i);
    requires distinct(xs) == true &*& 0 <= i &*& i < length(xs);
    ensures !mem(nth(i, xs), take(i, xs));

lemma void nth_drop<t>(int n, int k, list<t> xs);
    requires 0 <= n &*& 0 <= k &*& n + k < length(xs);
    ensures nth(n, drop(k, xs)) == nth(n + k, xs);

lemma void length_remove(int x, list<int> xs);
    requires mem(x, xs) == true;
    ensures length(remove(x, xs)) == length(xs) - 1;

lemma void neq_mem_remove<t>(t x, t y, list<t> xs);
    requires x != y;
    ensures mem(x, remove(y, xs)) == mem(x, xs);

lemma void mem_remove_mem<t>(t x, t y, list<t> xs);
    requires mem(x, remove(y, xs)) == true;
    ensures mem(x, xs) == true;

lemma void distinct_mem_remove<t>(t x, list<t> xs);
    requires distinct(xs) == true;
    ensures !mem(x, remove(x, xs));

lemma void distinct_remove<t>(t x, list<t> xs);
    requires distinct(xs) == true;
    ensures distinct(remove(x, xs)) == true;

lemma void mem_nth_index_of<t>(t x, list<t> xs);
    requires mem(x, xs) == true;
    ensures nth(index_of(x, xs), xs) == x;
lemma void map_append<a, b>(fixpoint(a, b) f, list<a> xs, list<a> ys);    requires true;    ensures map(f, append(xs, ys)) == append(map(f, xs), map(f, ys));lemma void mem_map<a, b>(a x, list<a> xs, fixpoint(a, b) f);    requires mem(x, xs) == true;    ensures mem(f(x), map(f, xs)) == true;
lemma void forall_append<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p);
    requires true;
    ensures forall(append(xs, ys), p) == (forall(xs, p) && forall(ys, p));

lemma void forall_mem<t>(t x, list<t> xs, fixpoint(t, bool) p);
    requires forall(xs, p) == true && mem(x, xs) == true;
    ensures p(x) == true;

lemma void forall_drop<t>(list<t> xs, fixpoint(t, bool) p, int i);
    requires forall(xs, p) == true;
    ensures forall(drop(i, xs), p) == true;

fixpoint int max(int x, list<int> xs) {
    switch (xs) {
        case nil: return x;
        case cons(x0, xs0): return x < x0 ? max(x0, xs0) : max(x, xs0);
    }
}

lemma void mem_max(int x, list<int> xs);
    requires true;
    ensures mem(max(x, xs), cons(x, xs)) == true;


fixpoint a fold_left<a, b>(a x0, fixpoint(a, b, a) f, list<b> xs) {
    switch (xs) {
        case nil: return x0;
        case cons(x, xs0): return fold_left(f(x0, x), f, xs0);
    }
}

lemma void fold_left_append<a, b>(a x0, fixpoint(a, b, a) f, list<b> xs1, list<b> xs2);
    requires true;
    ensures fold_left(x0, f, append(xs1, xs2)) == fold_left(fold_left(x0, f, xs1), f, xs2);

lemma_auto void append_drop_take<t>(list<t> vs, int i);
  requires 0 <= i && i <= length(vs);
  ensures append(take(i, vs), drop(i, vs)) == vs;

@*/

#endif