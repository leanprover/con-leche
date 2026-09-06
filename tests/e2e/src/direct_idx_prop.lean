--#export IsSucc.pred_mk IsSucc.inv Both.get_mk Rel.elim Rel.symm Hidden.small Hidden.elim
import Lean

/- End-to-end test (task #175 indexed): `Prop`-valued INDEXED families
   through the direct install, at every elimination shape official
   admits.

   * `IsSucc n (n+1)` — one constructor with a DATA field that occurs
     in the indices: the LARGE eliminator (official's
     `elim_only_at_universe_zero` at one constructor: a field that is
     not a proposition must be an index expression), `IsSucc.pred`
     reads the field back off the index and `pred_mk` fires the rule;
   * `Both n` — a data index field and a proof field: large as well;
   * `Rel` — two constructors: the SMALL eliminator only (`Rel.elim`
     into `Prop`, `Rel.symm` with a motive reading the indices);
   * `Hidden (n+1)` — a data field NOT (literally) in the indices: the
     SMALL eliminator (the bad twin `direct_idx_prop_large_bad.ndjson`
     patches its recursor's motive to `Sort u` and must be rejected).

   `IsSucc` and `Both` are added through `Lean.addDecl` directly: the
   `inductive` command would promote their fixed index to a parameter
   (`IsSucc (n : Nat) : Nat → Prop`), which is not the shape under
   test; the kernel generates their recursors from the unpromoted
   declarations exactly as the export carries them. -/

open Lean in
run_cmd Lean.Elab.Command.liftCoreM do
  let nat := mkConst ``Nat
  addDecl <| .inductDecl [] 0
    [{ name := `IsSucc,
       type := mkForall `a .default nat (mkForall `b .default nat (mkSort levelZero)),
       ctors := [{ name := `IsSucc.mk,
                   type := mkForall `n .default nat
                     (mkApp2 (mkConst `IsSucc) (mkBVar 0)
                       (mkApp (mkConst ``Nat.succ) (mkBVar 0))) }] }]
    false
  addDecl <| .inductDecl [] 0
    [{ name := `Both,
       type := mkForall `a .default nat (mkSort levelZero),
       ctors := [{ name := `Both.mk,
                   type := mkForall `n .default nat
                     (mkForall `h .default
                       (mkApp2 (mkConst `IsSucc) (mkBVar 0)
                         (mkApp (mkConst ``Nat.succ) (mkBVar 0)))
                       (mkApp (mkConst `Both) (mkBVar 1))) }] }]
    false

noncomputable def IsSucc.pred {a b : Nat} (h : IsSucc a b) : Nat :=
  IsSucc.rec (motive := fun _ _ _ => Nat) (fun n => n) h

theorem IsSucc.pred_mk (n : Nat) : Eq (IsSucc.pred (IsSucc.mk n)) n := rfl

theorem IsSucc.inv {a b : Nat} (h : IsSucc a b) : Eq b (Nat.succ a) :=
  IsSucc.rec (motive := fun a b _ => Eq b (Nat.succ a)) (fun _ => rfl) h

noncomputable def Both.get {n : Nat} (h : Both n) : Nat :=
  Both.rec (motive := fun _ _ => Nat) (fun n _ => n) h

theorem Both.get_mk (n : Nat) : Eq (Both.get (Both.mk n (IsSucc.mk n))) n := rfl

inductive Rel : Nat → Nat → Prop where
  | l (n : Nat) : Rel n Nat.zero
  | r (n : Nat) : Rel Nat.zero n

theorem Rel.elim {a b : Nat} {c : Prop} (h : Rel a b) (hl : ∀ (_ : Nat), Eq b Nat.zero → c)
    (hr : ∀ (_ : Nat), Eq a Nat.zero → c) : c :=
  Rel.rec (motive := fun a b _ => (Eq b Nat.zero → c) → (Eq a Nat.zero → c) → c)
    (fun _ f _ => f rfl) (fun _ _ g => g rfl) h (hl a) (hr b)

theorem Rel.symm {a b : Nat} (h : Rel a b) : Rel b a :=
  Rel.rec (motive := fun a b _ => Rel b a) (fun n => Rel.r n) (fun n => Rel.l n) h

inductive Hidden : Nat → Prop where
  | mk (n m : Nat) : Hidden (Nat.succ n)

theorem Hidden.small {n : Nat} (h : Hidden n) (p : Prop) (hp : Nat → p) : p :=
  Hidden.rec (motive := fun _ _ => p) (fun _ m => hp m) h

theorem Hidden.elim {n : Nat} (h : Hidden n) : Hidden n :=
  Hidden.rec (motive := fun k _ => Hidden k) (fun n m => Hidden.mk n m) h
