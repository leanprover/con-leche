--#export Iter.elim Iter.elim_step Reach.elim Reach.elim_step Reach.elim_refl

/- End-to-end test (task #202): REFLEXIVE constructors — a recursive
   field that is a FUNCTION into the family (`∀ k, Nat.le k n → Iter f k`)
   — through the direct fixed-point install, `Prop`-valued with two
   constructors so the official kernel gives the SMALL eliminator only.

   * `Iter f n` — `step`'s field `h : ∀ k, Nat.le k n → Iter f k` is a
     function-space slot into the fibres at the index expression `k`
     (the bound variable); the inductive hypothesis is POINTWISE,
     `ih : ∀ k, Nat.le k n → motive k (h k a)`;
   * `Reach r x y` — a two-index family whose reflexive field's index
     expressions read the bound variables (`∀ z, r x z → Reach r z y`),
     beside a finitary one; the consumers fire iota on both. -/

inductive Iter (f : Nat → Nat) : Nat → Prop where
  | base : Iter f Nat.zero
  | step (n : Nat) (h : ∀ k, Nat.le k n → Iter f k) : Iter f (f n)

theorem Iter.elim {f : Nat → Nat} {n : Nat} (t : Iter f n) (p : Nat → Prop)
    (hb : p Nat.zero) (hs : ∀ n, (∀ k, Nat.le k n → p k) → p (f n)) : p n :=
  Iter.rec (motive := fun n _ => p n) hb (fun n _ ih => hs n ih) t

theorem Iter.elim_step {f : Nat → Nat} (n : Nat) (h : ∀ k, Nat.le k n → Iter f k)
    (p : Nat → Prop) (hb : p Nat.zero) (hs : ∀ n, (∀ k, Nat.le k n → p k) → p (f n)) :
    Eq (Iter.elim (Iter.step n h) p hb hs) (hs n (fun k hk => Iter.elim (h k hk) p hb hs)) := rfl

inductive Reach (r : Nat → Nat → Prop) : Nat → Nat → Prop where
  | refl (x : Nat) : Reach r x x
  | step (x y : Nat) (h : ∀ z, r x z → Reach r z y) (t : Reach r x y) : Reach r x y

theorem Reach.elim {r : Nat → Nat → Prop} {x y : Nat} (t : Reach r x y) (p : Nat → Nat → Prop)
    (hr : ∀ x, p x x) (hs : ∀ x y, (∀ z, r x z → p z y) → p x y → p x y) : p x y :=
  Reach.rec (motive := fun x y _ => p x y) hr (fun x y _ _ ih iht => hs x y ih iht) t

theorem Reach.elim_refl {r : Nat → Nat → Prop} (x : Nat) (p : Nat → Nat → Prop)
    (hr : ∀ x, p x x) (hs : ∀ x y, (∀ z, r x z → p z y) → p x y → p x y) :
    Eq (Reach.elim (Reach.refl x) p hr hs) (hr x) := rfl

theorem Reach.elim_step {r : Nat → Nat → Prop} (x y : Nat) (h : ∀ z, r x z → Reach r z y)
    (t : Reach r x y) (p : Nat → Nat → Prop)
    (hr : ∀ x, p x x) (hs : ∀ x y, (∀ z, r x z → p z y) → p x y → p x y) :
    Eq (Reach.elim (Reach.step x y h t) p hr hs)
      (hs x y (fun z hz => Reach.elim (h z hz) p hr hs) (Reach.elim t p hr hs)) := rfl
