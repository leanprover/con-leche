--#export Le'.trans Le'.succ_right Le'.zero_le Even'.four Even'.elim_ss Even'.elim_zero
import Lean

/- End-to-end test (task #188 indexed): `Prop`-valued INDEXED recursive
   families through the direct fixed-point install — `Le' a b` (two
   indices, the recursive `step` at index `Nat.succ m`) and `Even' n`
   (one index, the recursive `ss` two steps up).  Both have two
   constructors, so the official kernel gives the SMALL eliminator
   only (`elim_only_at_universe_zero`); every consumer eliminates into
   `Prop` and the iota equations hold by proof irrelevance.  (A
   ONE-constructor indexed recursive `Prop` with the large eliminator
   is positively declined — `direct_fix_acc_large.lean`.)

   `Le'` is added through `Lean.addDecl` directly: the `inductive`
   command would promote its fixed first index to a parameter
   (`Le' (n : Nat) : Nat → Prop`), which is not the shape under test
   (as at `direct_idx_prop.lean`). -/

open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let nat := mkConst ``Nat
  addDecl <| .inductDecl [] 0
    [{ name := `Le',
       type := mkForall `a .default nat (mkForall `b .default nat (mkSort levelZero)),
       ctors := [{ name := `Le'.refl,
                   type := mkForall `n .default nat
                     (mkApp2 (mkConst `Le') (mkBVar 0) (mkBVar 0)) },
                 { name := `Le'.step,
                   type := mkForall `n .default nat (mkForall `m .default nat
                     (mkForall `h .default (mkApp2 (mkConst `Le') (mkBVar 1) (mkBVar 0))
                       (mkApp2 (mkConst `Le') (mkBVar 2)
                         (mkApp (mkConst ``Nat.succ) (mkBVar 1))))) }] }]
    false

theorem Le'.succ_right {a b : Nat} (h : Le' a b) : Le' a (Nat.succ b) := Le'.step a b h

theorem Le'.trans {a b c : Nat} (hab : Le' a b) (hbc : Le' b c) : Le' a c :=
  Le'.rec (motive := fun b c _ => Le' a b → Le' a c) (fun _ h => h)
    (fun _ m _ ih h => Le'.step a m (ih h)) hbc hab

theorem Le'.zero_le (n : Nat) : Le' Nat.zero n :=
  Nat.rec (motive := fun n => Le' Nat.zero n) (Le'.refl Nat.zero)
    (fun n ih => Le'.step Nat.zero n ih) n

inductive Even' : Nat → Prop where
  | zero : Even' Nat.zero
  | ss (n : Nat) (h : Even' n) : Even' (Nat.succ (Nat.succ n))

theorem Even'.four : Even' (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) :=
  Even'.ss (Nat.succ (Nat.succ Nat.zero)) (Even'.ss Nat.zero Even'.zero)

theorem Even'.elim {n : Nat} (h : Even' n) (p : Nat → Prop) (hz : p Nat.zero)
    (hs : ∀ n, p n → p (Nat.succ (Nat.succ n))) : p n :=
  Even'.rec (motive := fun n _ => p n) hz (fun n _ ih => hs n ih) h

theorem Even'.elim_zero (p : Nat → Prop) (hz : p Nat.zero)
    (hs : ∀ n, p n → p (Nat.succ (Nat.succ n))) :
    Eq (Even'.elim Even'.zero p hz hs) hz := rfl

theorem Even'.elim_ss (n : Nat) (h : Even' n) (p : Nat → Prop) (hz : p Nat.zero)
    (hs : ∀ n, p n → p (Nat.succ (Nat.succ n))) :
    Eq (Even'.elim (Even'.ss n h) p hz hs) (hs n (Even'.elim h p hz hs)) := rfl
