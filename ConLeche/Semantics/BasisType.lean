module

public import ConLeche.Semantics.Syntax
public import ConLeche.Term.Const

@[expose] public section

/-!
# `BConst.typeAV` — the annotated basis-constant types (#151)

The first of the two suppliers the skeleton's `const` row waits on
(`Semantics/Skeleton.lean`): the annotated mirror of
`ConLeche/Term/Const.lean`'s `BConst.type`, so that a built-in constant's
type can be *written* as an `AnnotTerm` at all (`BConst.type` yields a
`Term`, not an `AnnotTerm`).

## The annotation convention, inherited not invented

`SetModel/Value.lean` fixed it for the value side, and this file mirrors
it exactly, because the two must agree for the capstone
(`bval_mem_type`) to typecheck at all:

* **every binder's codomain slot carries the tower's result sort `r`**,
  not the exact `imax` fold.  Sound because `piR`/`lamR` read the
  numeral only through `v = 0`, and `imax x y = 0 ↔ y = 0`
  (`imax_eq_zero_iff`);
* **every binder's domain slot carries the domain's exact sort**,
  because those are what the consumers' membership hypotheses are
  stated with — `WellDenoted`'s binder clauses and `Skeleton.sound_pi`
  both read the domain numeral.

So `.pi u' r A B` throughout, with `u'` exact.  The `v'`-for-a-`Sort`
trap is worth naming once: a codomain slot holds the sort of `B` **as
a type**, so a codomain `.sort k` gets `k + 1`, never `k`.  That is why
`A → Prop` annotates as `.pi u 1 A (.sort 0)` and is a *type*
(`Sort (max u 1)`), not a proposition.

## The result sorts, read off the towers

| constant | `r` | tower |
|---|---|---|
| the five atomic types | — | no binder |
| `natSucc` | `1` | `lamR 1 omega natsucc` |
| `natRec` | `u` | `natRecV` |
| `punitRec` | `v` | `punitRecV` |
| `psigma` | `max u v + 1` | `psigmaV` (a type former) |
| `psigmaMk` | `max u v` | `psigmaMkV` |
| `emptyRec` | `v` | `emptyRecV` |
| `quot` | `u + 1` | `quotV` (a type former) |
| `quotMk` | `u` | `quotMkV` |
| `quotLift` | `v` | `quotLiftV` |
| `quotInd`/`quotSound`/`propext` | `0` | `pt`: the types are `Prop` |
| `choice` | `u` | `choiceV` |
| `lfpFam` | `max (u + 1) (w + 1)` | `lfpFamV` (a type former) |
-/

namespace ConLeche.Semantics

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term (BConst lv tupleIdxSort tupleFamSort)

/-! ## Annotated smart constructors

Mirrors of `ConLeche/Term/Const.lean`'s, one per former the basis types
mention.  Each carries the numerals its own shape fixes. -/

/-- `Nat` -/
def natTyAV : AnnotTerm := .const .nat []
/-- `Nat.zero` -/
def natZeroAV : AnnotTerm := .const .natZero []
/-- `Nat.succ e` -/
def natSuccAV (e : AnnotTerm) : AnnotTerm := .app (.const .natSucc []) e
/-- `PUnit.{u}` -/
def punitAV (u : Nat) : AnnotTerm := .const .punit [u]
/-- `PUnit.unit.{u}` -/
def punitUnitAV (u : Nat) : AnnotTerm := .const .punitUnit [u]
/-- `Empty.{u}` -/
def emptyAV (u : Nat) : AnnotTerm := .const .empty [u]
/-- `@BConst.psigma.{u,v} A B`, the dependent pair -/
def psigmaAV (u v : Nat) (A B : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [u, v]) [A, B]
/-- `@Quot.{u} A r` -/
def quotAV (u : Nat) (A r : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .quot [u]) [A, r]
/-- `@Quot.mk.{u} A r a` -/
def quotMkAV (u : Nat) (A r a : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .quotMk [u]) [A, r, a]

/-- `A → B`, at the domain's sort `u` and the codomain's sort `v`. -/
def arrowA (u v : Nat) (A B : AnnotTerm) : AnnotTerm := .pi u v A B.lift

/-- `A → A → Prop`, the relation type at `A : Sort u`.  Its own sort is
`max u 1` — a *type*, because `Prop` lives in `Sort 1`.  Matches
`relSpace`. -/
def relAV (u : Nat) (A : AnnotTerm) : AnnotTerm :=
  .pi u (Nat.max u 1) A (.pi u 1 A.lift (.sort 0))

/-- `¬ A`, i.e. `A → False`: a proposition, so the codomain slot is
`0`. -/
def negTyAV (u : Nat) (A : AnnotTerm) : AnnotTerm := arrowA u 0 A (emptyAV 0)

/-! ## The block carrier's tuple spelling (#315)

`lfpTuple k` binds ONE tuple of index sets and ONE operator on the
tuple of families, so its type mentions two right-nested pair towers —
`⟨Sort u_0, …, Sort u_{k-1}⟩` and `⟨proj_0 Is → Sort w, …⟩`.  Both are
NON-dependent: component `m` may mention the ambient tuple variable but
never an earlier component, so the former takes its components
**already lifted to their own depth** (component `m` sits under `m` of
the tower's fibre binders).

`projAV` lives here rather than with the tower kit
(`Semantics/Tower/TowerKit.lean`, which imports this module) because a
basis constant's type needs it: it is ONE definition for every
structure and every index.  `ndTowerAV r` is `towerBodyAVPos r`'s
non-dependent twin — the same `.psigma [r, r]` tower with the same
`r + 1` fibre annotation (the codomain type's sort, never `0`, so the
fibre computes by `app_lamR_pos` in both regimes), differing only in
the terminator's level, which no value reads (`bval .punit = unitSet`
at every level). -/

/-- The uniform projection spelling: `.fst ∘ .snd^i` — the `AnnotTerm`
form of the tier's `projS i = sfst ∘ ssnd^i`.  Depends only on the
index. -/
def projAV : Nat → AnnotTerm → AnnotTerm
  | 0, e => .fst e
  | i + 1, e => projAV i (.snd e)

/-- The non-dependent pair tower at level `r`, `PUnit`-terminated:
`⟨G s, …, G (s + n - 1)⟩`.  The components are given at the BASE frame
and lifted to their own depth `d` by the former (component `s + i` sits
under `i` of the tower's fibre binders). -/
def ndTowerAV (r : Nat) (G : Nat → AnnotTerm) : Nat → Nat → Nat → AnnotTerm
  | _, _, 0 => .const .punit [r]
  | s, d, n + 1 =>
    .app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
      (.lam (r + 1) ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n))

/-- `⟨Sort u_0, …, Sort u_{k-1}⟩`, the index-set tuple's type. -/
def tupleSortsAV (k : Nat) (us : List Nat) : AnnotTerm :=
  ndTowerAV (tupleIdxSort us) (fun m => .sort (lv us m)) 0 0 k

/-- `⟨proj_0 Is → Sort w, …, proj_{k-1} Is → Sort w⟩`, the family
tuple's type, with `Is` at de Bruijn index `j` of the base frame. -/
def tupleFamsAV (k : Nat) (us : List Nat) (j : Nat) : AnnotTerm :=
  ndTowerAV (tupleFamSort k us)
    (fun m => .pi (lv us m) (lv us k + 1) (projAV m (.bvar j)) (.sort (lv us k))) 0 0 k

/-! ## The annotated type assignment -/

/-- The annotated type of each built-in constant — `BConst.type` with
every binder's two numerals supplied (see the module docstring). -/
def BConst.typeAV : BConst → List Nat → AnnotTerm
  | .nat, _ => .sort 1
  | .natZero, _ => natTyAV
  | .natSucc, _ => arrowA 1 1 natTyAV natTyAV
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (u + 1) u (arrowA 1 (u + 1) natTyAV (.sort u)) <|
    .pi u u (.app (.bvar 0) natZeroAV) <|
    .pi u u (.pi 1 u natTyAV (.pi u u (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccAV (.bvar 1))))) <|
    .pi 1 u natTyAV <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitAV (lv us 0)
  | .punitRec, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ (M : PUnit.{u} → Sort v), M unit → ∀ t, M t`
    .pi (Nat.max u (v + 1)) v
      (arrowA u (v + 1) (punitAV u) (.sort v)) <|
    .pi v v (.app (.bvar 0) (punitUnitAV u)) <|
    .pi u v (punitAV u) <|
    .app (.bvar 2) (.bvar 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    let r := Nat.max u v + 1
    .pi (u + 1) r (.sort u) <|
    .pi (Nat.max u (v + 1)) r
      (arrowA u (v + 1) (.bvar 0) (.sort v)) <|
    .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    let r := Nat.max u v
    .pi (u + 1) r (.sort u) <|
    .pi (Nat.max u (v + 1)) r
      (arrowA u (v + 1) (.bvar 0) (.sort v)) <|
    .pi u r (.bvar 1) <|
    .pi v r (.app (.bvar 1) (.bvar 0)) <|
    psigmaAV u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (Nat.max u (v + 1)) v
      (arrowA u (v + 1) (emptyAV u) (.sort v)) <|
    .pi u v (emptyAV u) <|
    .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (u + 1) (u + 1) (.sort u) <|
    .pi (Nat.max u 1) (u + 1) (relAV u (.bvar 0)) <|
    .sort u
  | .quotMk, us =>
    let u := lv us 0
    .pi (u + 1) u (.sort u) <|
    .pi (Nat.max u 1) u (relAV u (.bvar 0)) <|
    .pi u u (.bvar 1) <|
    quotAV u (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (u + 1) v (.sort u) <|
    .pi (Nat.max u 1) v (relAV u (.bvar 0)) <|
    .pi (v + 1) v (.sort v) <|
    .pi (ConLeche.Term.imax u v) v (.pi u v (.bvar 2) (.bvar 1)) <|
    .pi 0 v (.pi u 0 (.bvar 3) (.pi u 0 (.bvar 4)
          (.pi 0 0 (AnnotTerm.mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi u v (quotAV u (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0
    .pi (u + 1) 0 (.sort u) <|
    .pi (Nat.max u 1) 0 (relAV u (.bvar 0)) <|
    .pi (Nat.max u 1) 0
      (.pi u 1 (quotAV u (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi 0 0 (.pi u 0 (.bvar 2)
      (.app (.bvar 1) (quotMkAV u (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi u 0 (quotAV u (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0
    .pi (u + 1) 0 (.sort u) <|
    .pi (Nat.max u 1) 0 (relAV u (.bvar 0)) <|
    .pi u 0 (.bvar 1) <|
    .pi u 0 (.bvar 2) <|
    .pi 0 0 (AnnotTerm.mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotMkAV u (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkAV u (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi 1 0 (.sort 0) <| .pi 1 0 (.sort 0) <|
    .pi 0 0 (.pi 0 0 (.bvar 1) (.bvar 1)) <|
    .pi 0 0 (.pi 0 0 (.bvar 1) (.bvar 3)) <|
    .eqE (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (u + 1) u (.sort u) <|
    .pi 0 u (negTyAV 0 (negTyAV u (.bvar 0))) <|
    .bvar 1
  | .lfpFam, us =>
    let u := lv us 0; let w := lv us 1
    let m := Nat.max u (w + 1)
    -- `Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w` (task
    -- #188, indexed): `I → Sort w` has sort `max u (w + 1)`, and so do the
    -- functor space and the tail
    .pi (u + 1) m (.sort u) <|
    .pi m m (arrowA m m (arrowA u (w + 1) (.bvar 0) (.sort w)) (arrowA u (w + 1) (.bvar 0) (.sort w))) <|
    .pi u (w + 1) (.bvar 1) (.sort w)
  | .lfpTuple k, us =>
    let R := tupleFamSort k us
    -- `Π (Is : ⟨Sort u_0, …, Sort u_{k-1}⟩) (F : Fams Is → Fams Is), Fams Is`,
    -- every binder's result slot the family tuple's own sort `R`
    .pi (tupleIdxSort us) R (tupleSortsAV k us) <|
    .pi R R (.pi R R (tupleFamsAV k us 0) (tupleFamsAV k us 1)) <|
    tupleFamsAV k us 1

end ConLeche.Semantics
