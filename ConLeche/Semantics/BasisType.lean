module

public import ConLeche.Verify.Denote

@[expose] public section

/-!
# `BConst.typeAV` — the spelled basis-constant types (#151)

The first of the two suppliers the skeleton's `const` row waits on
(`Semantics/Skeleton.lean`): each built-in constant's type, *written*
as a `Term`.

The spelling carries no regime: `interp` reads each binder's regime off
the values (`piV`/`lamV`).  A codomain `Sort k` makes a function space
into a universe a *type*, never a proposition: `A → Prop` reads as
`piV ⟦A⟧ (fun _ => univ 0)`, whose fibre `univ 0` is not a truth value.

## The result sorts, read off the towers

| constant | `r` | tower |
|---|---|---|
| the five atomic types | — | no binder |
| `natSucc` | `1` | `lamR 1 omega natsucc` |
| `natRec` | `u` | `natRecV` |
| `psigma` | `max u v + 1` | `psigmaV` (a type former) |
| `psigmaMk` | `max u v` | `psigmaMkV` |
| `emptyRec` | `v` | `emptyRecV` |
| `quot` | `c + 1` | `quotV` (a type former; `c` the construction level, `quotCl`) |
| `quotMk` | `c` | `quotMkV` |
| `quotLift` | `v` | `quotLiftV` |
| `quotInd`/`quotSound`/`propext` | `0` | `pt`: the types are `Prop` |
| `choice` | `u` | `choiceV` |
| `lfpFam` | `max (u + 1) (w + 1)` | `lfpFamV` (a type former) |
-/

namespace ConLeche.Semantics
open ConLeche.Verify (projNV)


open ConLeche.Term (Term BConst lv quotCl tupleIdxSort tupleFamSort emptyT)

/-! ## `Term` smart constructors

One per former the basis types mention, beside
`ConLeche/Term/Const.lean`'s `emptyT`.  Each carries the level numerals
its own shape fixes. -/

/-- `Nat` -/
def natTyAV : Term := .const .nat []
/-- `Nat.zero` -/
def natZeroAV : Term := .const .natZero []
/-- `Nat.succ e` -/
def natSuccAV (e : Term) : Term := .app (.const .natSucc []) e
/-- `PUnit.{u}` -/
def punitAV (u : Nat) : Term := .const .punit [u]
/-- `@BConst.psigma.{u,v} A B`, the dependent pair -/
def psigmaAV (u v : Nat) (A B : Term) : Term :=
  Term.mkAppN (.const .psigma [u, v]) [A, B]
/-- `@Quot.{us} A r`, at a quotient level list `[u, ℓ]` (`quotCl`) -/
def quotAV (us : List Nat) (A r : Term) : Term :=
  Term.mkAppN (.const .quot us) [A, r]
/-- `@Quot.mk.{us} A r a`, at a quotient level list `[u, ℓ]` (`quotCl`) -/
def quotMkAV (us : List Nat) (A r a : Term) : Term :=
  Term.mkAppN (.const .quotMk us) [A, r, a]

/-- `A → B`. -/
def arrowA (A B : Term) : Term := .pi A B.lift

/-- `A → A → Prop`, the relation type at `A : Sort u`.  Its own sort is
`max u 1` — a *type*, because `Prop` lives in `Sort 1`.  Matches
`relSpace`. -/
def relAV (A : Term) : Term :=
  .pi A (.pi A.lift (.sort 0))

/-- `¬ A`, i.e. `A → False`. -/
def negTyAV (A : Term) : Term := arrowA A (emptyT 0)

/-! ## The block carrier's tuple spelling (#315)

`lfpTuple k` binds ONE tuple of index sets and ONE operator on the
tuple of families, so its type mentions two right-nested pair towers —
`⟨Sort u_0, …, Sort u_{k-1}⟩` and `⟨proj_0 Is → Sort w, …⟩`.  Both are
NON-dependent: component `m` may mention the ambient tuple variable but
never an earlier component, so the former takes its components
**already lifted to their own depth** (component `m` sits under `m` of
the tower's fibre binders).

`projNV` lives here rather than with the tower kit
(`Semantics/Tower/TowerKit.lean`, which imports this module) because a
basis constant's type needs it: it is ONE definition for every
structure and every index.  `ndTowerAV r` is `towerBodyAVPos r`'s
non-dependent twin — the same `.psigma [r, r]` tower, differing only in
the terminator's level, which no value reads (`bval .punit` is the
same `{∅}` at every positive level, task #342 B). -/

/-- The non-dependent pair tower at level `r`, `PUnit`-terminated:
`⟨G s, …, G (s + n - 1)⟩`.  The components are given at the BASE frame
and lifted to their own depth `d` by the former (component `s + i` sits
under `i` of the tower's fibre binders). -/
def ndTowerAV (r : Nat) (G : Nat → Term) : Nat → Nat → Nat → Term
  | _, _, 0 => .const .punit [r]
  | s, d, n + 1 =>
    .app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
      (.lam ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n))

/-- `⟨Sort u_0, …, Sort u_{k-1}⟩`, the index-set tuple's type. -/
def tupleSortsAV (k : Nat) (us : List Nat) : Term :=
  ndTowerAV (tupleIdxSort us) (fun m => .sort (lv us m)) 0 0 k

/-- `⟨proj_0 Is → Sort w, …, proj_{k-1} Is → Sort w⟩`, the family
tuple's type, with `Is` at de Bruijn index `j` of the base frame. -/
def tupleFamsAV (k : Nat) (us : List Nat) (j : Nat) : Term :=
  ndTowerAV (tupleFamSort k us)
    (fun m => .pi (projNV m (.bvar j)) (.sort (lv us k))) 0 0 k

/-! ## The spelled type assignment -/

/-- The spelled type of each built-in constant — `BConst.type` as an
`Term` (see the module docstring). -/
def BConst.typeAV : BConst → List Nat → Term
  | .nat, _ => .sort 1
  | .natZero, _ => natTyAV
  | .natSucc, _ => arrowA natTyAV natTyAV
  | .natRec, us =>
    let u := lv us 0
    -- `∀ (M : Nat → Sort u), M 0 → (∀ n, M n → M (n+1)) → ∀ t, M t`
    .pi (arrowA natTyAV (.sort u)) <|
    .pi (.app (.bvar 0) natZeroAV) <|
    .pi (.pi natTyAV (.pi (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (natSuccAV (.bvar 1))))) <|
    .pi natTyAV <|
    .app (.bvar 3) (.bvar 0)
  | .punit, us => .sort (lv us 0)
  | .punitUnit, us => punitAV (lv us 0)
  | .psigma, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <|
    .pi (arrowA (.bvar 0) (.sort v)) <|
    .sort (Nat.max u v)
  | .psigmaMk, us =>
    let u := lv us 0; let v := lv us 1
    .pi (.sort u) <|
    .pi (arrowA (.bvar 0) (.sort v)) <|
    .pi (.bvar 1) <|
    .pi (.app (.bvar 1) (.bvar 0)) <|
    psigmaAV u v (.bvar 3) (.bvar 2)
  | .empty, us => .sort (lv us 0)
  | .emptyRec, us =>
    let u := lv us 0; let v := lv us 1
    .pi (arrowA (emptyT u) (.sort v)) <|
    .pi (emptyT u) <|
    .app (.bvar 1) (.bvar 0)
  | .quot, us =>
    let u := lv us 0
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .sort (quotCl us 1)
  | .quotMk, us =>
    let u := lv us 0; let qs := [u, lv us 1]
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.bvar 1) <|
    quotAV qs (.bvar 2) (.bvar 1)
  | .quotLift, us =>
    let u := lv us 0; let v := lv us 1; let qs := [u, lv us 2]
    -- `∀ A r B (f : A → B), (∀ a b, r a b → f a = f b) → Quot A r → B`
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.sort v) <|
    .pi (.pi (.bvar 2) (.bvar 1)) <|
    .pi (.pi (.bvar 3) (.pi (.bvar 4)
          (.pi (Term.mkAppN (.bvar 4) [.bvar 1, .bvar 0])
            (.eqE (.app (.bvar 3) (.bvar 2))
              (.app (.bvar 3) (.bvar 1)))))) <|
    .pi (quotAV qs (.bvar 4) (.bvar 3)) <|
    .bvar 3
  | .quotInd, us =>
    let u := lv us 0; let qs := [u, lv us 1]
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.pi (quotAV qs (.bvar 1) (.bvar 0)) (.sort 0)) <|
    .pi (.pi (.bvar 2)
      (.app (.bvar 1) (quotMkAV qs (.bvar 3) (.bvar 2) (.bvar 0)))) <|
    .pi (quotAV qs (.bvar 3) (.bvar 2)) <|
    .app (.bvar 2) (.bvar 0)
  | .quotSound, us =>
    let u := lv us 0; let qs := [u, lv us 1]
    .pi (.sort u) <|
    .pi (relAV (.bvar 0)) <|
    .pi (.bvar 1) <|
    .pi (.bvar 2) <|
    .pi (Term.mkAppN (.bvar 2) [.bvar 1, .bvar 0]) <|
    .eqE (quotMkAV qs (.bvar 4) (.bvar 3) (.bvar 2))
      (quotMkAV qs (.bvar 4) (.bvar 3) (.bvar 1))
  | .propext, _ =>
    -- `∀ (A B : Prop), (A → B) → (B → A) → A = B`
    .pi (.sort 0) <| .pi (.sort 0) <|
    .pi (.pi (.bvar 1) (.bvar 1)) <|
    .pi (.pi (.bvar 1) (.bvar 3)) <|
    .eqE (.bvar 3) (.bvar 2)
  | .choice, us =>
    let u := lv us 0
    -- `∀ (A : Sort u), ¬¬A → A`
    .pi (.sort u) <|
    .pi (negTyAV (negTyAV (.bvar 0))) <|
    .bvar 1
  | .lfpFam, us =>
    let u := lv us 0; let w := lv us 1
    -- `Π (I : Sort u), ((I → Sort w) → (I → Sort w)) → I → Sort w` (task
    -- #188, indexed)
    .pi (.sort u) <|
    .pi (arrowA (arrowA (.bvar 0) (.sort w)) (arrowA (.bvar 0) (.sort w))) <|
    .pi (.bvar 1) (.sort w)
  | .lfpTuple k, us =>
    -- `Π (Is : ⟨Sort u_0, …, Sort u_{k-1}⟩) (F : Fams Is → Fams Is), Fams Is`
    .pi (tupleSortsAV k us) <|
    .pi (.pi (tupleFamsAV k us 0) (tupleFamsAV k us 1)) <|
    tupleFamsAV k us 1

end ConLeche.Semantics
