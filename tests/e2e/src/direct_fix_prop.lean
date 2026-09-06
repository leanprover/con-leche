--#export Ev.elim Ev.two Ev.elim_step Chain'.elim Chain'.elim_cons

/- End-to-end test (task #188): recursive `Prop`s through the direct
   fixed-point install — the two-constructor `Ev` and the parametrised
   `Chain' P` with a data field and a proof field before the recursive
   one.  With two constructors the official kernel gives the SMALL
   eliminator only (`elim_only_at_universe_zero`), so every consumer
   eliminates into `Prop`; the iota equations hold by proof
   irrelevance.  (A ONE-constructor recursive `Prop` with a large
   eliminator is positively declined by this route — see
   `direct_fix_prop_large.lean`.) -/

inductive Ev : Prop where
  | base : Ev
  | step (h : Ev) : Ev

theorem Ev.elim (h : Ev) (p : Prop) (hp : p) (hs : p → p) : p :=
  Ev.rec (motive := fun _ => p) hp (fun _ ih => hs ih) h

theorem Ev.two : Ev := Ev.step (Ev.step Ev.base)

theorem Ev.elim_step (h : Ev) (p : Prop) (hp : p) (hs : p → p) :
    Eq (Ev.elim (Ev.step h) p hp hs) (hs (Ev.elim h p hp hs)) := rfl

inductive Chain' (P : Nat → Prop) : Prop where
  | nil : Chain' P
  | cons (n : Nat) (h : P n) (rest : Chain' P) : Chain' P

theorem Chain'.elim {P : Nat → Prop} (c : Chain' P) (q : Prop) (hn : q)
    (hc : ∀ n, P n → q → q) : q :=
  Chain'.rec (motive := fun _ => q) hn (fun n h _ ih => hc n h ih) c

theorem Chain'.elim_cons {P : Nat → Prop} (n : Nat) (h : P n) (c : Chain' P) (q : Prop) (hn : q)
    (hc : ∀ n, P n → q → q) :
    Eq (Chain'.elim (Chain'.cons n h c) q hn hc) (hc n h (Chain'.elim c q hn hc)) := rfl
