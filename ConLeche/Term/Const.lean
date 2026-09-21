module

public import ConLeche.Term.Subst

@[expose] public section

/-!
# Types of the built-in constants

`BConst.type c us` is the (closed) type of the constant `c` at the
level instantiation `us`.  Level lists shorter than `c.numLevels` read
`0` for the missing entries, so `BConst.type` is total and the `const`
typing rule needs no arity side condition.

The smart constructors below (`natT`, `psigmaT`, …) are what the
denotation function emits (`ConLeche/Verify/Denote.lean`) and what
`ConLeche/Semantics/BasisType.lean`, `ConLeche/SetModel/Value.lean` and
`ConLeche/Model/Capstone.lean` read.
-/

namespace ConLeche.Term

open Term

/-- Level lookup with a `0` default. -/
def lv (us : List Nat) (i : Nat) : Nat := us.getD i 0

/-! ## Smart constructors -/

/-- `Nat` -/
def natT : Term := .const .nat []
/-- `Nat.zero` -/
def natZeroT : Term := .const .natZero []
/-- `Nat.succ e` -/
def natSuccT (e : Term) : Term := .app (.const .natSucc []) e

/-- `PUnit.{u}` -/
def punitT (u : Nat) : Term := .const .punit [u]
/-- `PUnit.unit.{u}` -/
def punitUnitT (u : Nat) : Term := .const .punitUnit [u]

/-- `@PSigma'.{u,v} A B` -/
def psigmaT (u v : Nat) (A B : Term) : Term :=
  mkAppN (.const .psigma [u, v]) [A, B]
/-- `@PSigma'.mk.{u,v} A B a b` -/
def psigmaMkT (u v : Nat) (A B a b : Term) : Term :=
  mkAppN (.const .psigmaMk [u, v]) [A, B, a, b]

/-- `Empty.{u}` (level-polymorphic: `Empty.{0}` is `False`) -/
def emptyT (u : Nat) : Term := .const .empty [u]
/-- `¬ A`, i.e. `A → False` -/
def negT (A : Term) : Term := arrow A (emptyT 0)

/-- `@Quot.{u} A r` -/
def quotT (u : Nat) (A r : Term) : Term :=
  mkAppN (.const .quot [u]) [A, r]
/-- `@Quot.mk.{u} A r a` -/
def quotMkT (u : Nat) (A r a : Term) : Term :=
  mkAppN (.const .quotMk [u]) [A, r, a]

/-- The type of a relation on `A`, where `A` is the term `a` in the
ambient context: `A → A → Prop`.  (Written out rather than built from
`arrow`, because the second domain sits under one extra binder.) -/
def relT (A : Term) : Term := .pi A (.pi A.lift (.sort 0))

/-! ## The block carrier's tuple spelling (task #315, the uniform route)

`lfpTuple k` binds ONE tuple of index sets and ONE operator on the
tuple of families, so its type mentions two right-nested pair towers —
`⟨Sort u_0, …, Sort u_{k-1}⟩` and `⟨I_0 → Sort w, …, I_{k-1} → Sort w⟩`
— and the members' index sets are read off the first by the uniform
projection family.  Both towers are NON-dependent: component `m` may
mention the ambient tuple variable but never an earlier component, so
the former takes the components **already lifted to their own depth**
(component `m` sits under `m` of the tower's fibre binders). -/

/-- `.fst ∘ .snd^i` — the `Term` mirror of `projAV`, the uniform
projection spelling. -/
def projPairT : Nat → Term → Term
  | 0, e => .fst e
  | i + 1, e => projPairT i (.snd e)

/-- The non-dependent pair tower at level `r`, `PUnit`-terminated:
`⟨G s, …, G (s + n - 1)⟩`, each component given at its own depth. -/
def ndTowerT (r : Nat) (G : Nat → Term) : Nat → Nat → Term
  | _, 0 => .const .punit [r]
  | s, n + 1 =>
    .app (.app (.const .psigma [r, r]) (G s)) (.lam (G s) (ndTowerT r G (s + 1) n))

/-- An upper bound for every level a list mentions (`0` past its
end, so the bound is global in the index — which is what a tower's
formation premise wants). -/
def levMax (us : List Nat) : Nat := us.foldr Nat.max 0

theorem lv_le_levMax : ∀ (us : List Nat) (m : Nat), lv us m ≤ levMax us
  | [], m => by simp [lv, levMax]
  | u :: us, 0 => by
    show u ≤ Nat.max u (levMax us)
    exact Nat.le_max_left _ _
  | u :: us, m + 1 => by
    show lv us m ≤ Nat.max u (levMax us)
    exact Nat.le_trans (lv_le_levMax us m) (Nat.le_max_right _ _)

/-- The sort of `lfpTuple k`'s index-set tuple `⟨Sort u_0, …⟩`. -/
def tupleIdxSort (us : List Nat) : Nat := levMax us + 1

/-- The sort of `lfpTuple k`'s family tuple `⟨I_0 → Sort w, …⟩`. -/
def tupleFamSort (k : Nat) (us : List Nat) : Nat :=
  Nat.max (levMax us) (lv us k + 1)

/-- `⟨Sort u_0, …, Sort u_{k-1}⟩`, the index-set tuple's type. -/
def tupleSortsT (k : Nat) (us : List Nat) : Term :=
  ndTowerT (tupleIdxSort us) (fun m => .sort (lv us m)) 0 k

/-- `⟨proj_0 Is → Sort w, …, proj_{k-1} Is → Sort w⟩`, the family
tuple's type, with `Is` at de Bruijn index `j` (each component lifted
to its own depth in the tower). -/
def tupleFamsT (k : Nat) (us : List Nat) (j : Nat) : Term :=
  ndTowerT (tupleFamSort k us)
    (fun m => arrow (projPairT m (.bvar (j + m))) (.sort (lv us k))) 0 k

/-! ## The type assignment -/

/-- The type of each built-in constant. -/
def BConst.type : BConst → List Nat → Term
  | .nat, _ => .sort 1
  | .natZero, _ => natT
  | .natSucc, _ => arrow natT natT
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (arrow natT (.sort u)) <|
    .pi (.app (.bvar 0) natZeroT) <|
    .pi (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccT (.bvar 1))))) <|
    .pi natT <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitT (lv us 0)
  | .punitRec, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ (M : PUnit.{u} → Sort v), M unit → ∀ t, M t`
    .pi (arrow (punitT u) (.sort v)) <|
    .pi (.app (.bvar 0) (punitUnitT u)) <|
    .pi (punitT u) <|
    .app (.bvar 2) (.bvar 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <| .pi (arrow (.bvar 0) (.sort v)) <| .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <|
    .pi (arrow (.bvar 0) (.sort v)) <|
    .pi (.bvar 1) <|
    .pi (.app (.bvar 1) (.bvar 0)) <|
    psigmaT u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (arrow (emptyT u) (.sort v)) <| .pi (emptyT u) <| .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (.sort u) <| .pi (relT (.bvar 0)) <| .sort u
  | .quotMk, us =>
    let u := lv us 0
    .pi (.sort u) <| .pi (relT (.bvar 0)) <| .pi (.bvar 1) <|
      quotT u (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (.sort u) <|
    .pi (relT (.bvar 0)) <|
    .pi (.sort v) <|
    .pi (.pi (.bvar 2) (.bvar 1)) <|
    .pi (.pi (.bvar 3) (.pi (.bvar 4)
          (.pi (mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi (quotT u (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relT (.bvar 0)) <|
    .pi (.pi (quotT u (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi (.pi (.bvar 2) (.app (.bvar 1) (quotMkT u (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi (quotT u (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relT (.bvar 0)) <|
    .pi (.bvar 1) <|
    .pi (.bvar 2) <|
    .pi (mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotMkT u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkT u (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi (.sort 0) <| .pi (.sort 0) <|
    .pi (.pi (.bvar 1) (.bvar 1)) <|
    .pi (.pi (.bvar 1) (.bvar 3)) <|
    .eqE (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (.sort u) <| .pi (negT (negT (.bvar 0))) <| .bvar 1
  | .lfpFam, us =>
    let u := lv us 0; let w := lv us 1
    -- `Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w` (task #188, indexed)
    .pi (.sort u) <|
    .pi (arrow (arrow (.bvar 0) (.sort w)) (arrow (.bvar 0) (.sort w))) <|
    .pi (.bvar 1) (.sort w)
  | .lfpTuple k, us =>
    -- `Π (Is : ⟨Sort u_0, …, Sort u_{k-1}⟩) (F : Fams Is → Fams Is), Fams Is`
    .pi (tupleSortsT k us) <|
    .pi (.pi (tupleFamsT k us 0) (tupleFamsT k us 1)) <|
    tupleFamsT k us 1

end ConLeche.Term
