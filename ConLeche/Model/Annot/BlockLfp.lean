module

public import ConLeche.Semantics.Sat
public import ConLeche.Semantics.Tower.FixTower
public import ConLeche.Semantics.Inductives.HoleApp
public section

/-!
# The LFP CLAUSE of an inductive block (lane ENVLFP)

The fact the maintainer wanted in the environment invariant from the
start: **a member's denotation `⟦I⟧ p⃗` is the least fixed point of its
block's right-hand-side operator, with holes for the recursive
fields.**  The recursor model's graph route (DESIGN, ruling of
2026-09-23) asks nothing else of an inductive: the recursor's
uniqueness is ONE induction over the majors, and that induction is a
corollary of this clause (`LfpClause.ind`, which the graph producer's
`blockGraphInd_run`, `Model/Inductives/BlockRecGraph.lean`, reads).

**Why a separate datum.**  The clause is recorded in `EnvModelM`
(`Model/Annot/EnvModelM.lean`), which sits BELOW the block
representation (`BlockData`/`BlockModelAt`,
`Model/Inductives/BlockRep.lean`) in the import order.  So the clause
is stated over `LfpDatum`, the part of a block's representation the
clause reads — its member names, widths, parameter and index
telescopes, the operator `Φ`, and the constructors' fit relation and
injections — and a uniform block's datum is `BlockData.toLfp d`
(`BlockRep.lean`), its fields literally `d`'s.  The OPERATOR is
therefore exactly the one `BlockModelAt` uses: `d.Φ`, which at the
fixpoint route's data is `blockPhi` by `rfl` (`BlockDatum.lean`); the
clause's `fibre` says what that operator IS, fibre by fibre
(injections of the spines fitting a constructor, a recursive field
read at the tuple's component) — the NARROW clause: a container's
instance is read ordinarily, it is not a component.

**The clause** (`LfpClause`), at every level assignment `ψ` and every
parameter frame `ρp` satisfying the parameter telescope (exactly the
quantification `BlockModelAt` has, which is what the install proves):

* `functor` — `Φ` is monotone, maps the tuple space into itself, and
  has a closed tuple: the three facts `lfpTuple`'s laws need
  (`lfpTuple_induction` takes the first and the third);
* `fibre` — component `c`'s fibre at `(X, t)` is the set of injections
  of the spines fitting one of `c`'s constructors at `(X, t)`;
* `leaf` — a member's former, at fitting parameters and its own
  indices, is the least pre-fixed tuple's component at the index
  tuple.

**Universe instantiation.**  `leaf` holds at EVERY level assignment
`ψ`.  A use `.const I us` under `φ` reads the leaf at
`Level.substFn φ lps us` (`EnvModelM.constType`'s crossing), which is
one such `ψ` — `LfpClause.leaf_inst` states that case explicitly.
The installer establishes the clause at every `ψ` because it checks
the block's parameters once, polymorphically, and the model reads the
member's leaf as a function of the assignment.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetTheory
open ConLeche.SetModel (lamR app_lamR_pos)
open ConLeche.SetTheory.Tower (projS)

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

section HoleFam

variable {V : Type w} [SetTheory V]

/-- **The λ-tower over a telescope** `Fs`, read progressively from `ρ`,
of `g` at the bound values — in the graph regime (a type-valued
function; lane HOLE2's hole values). -/
@[expose] noncomputable def holeFam (ρ : Nat → V) : List AnnotTerm → (List V → V) → V
  | [], g => g []
  | F :: Fs, g => lamR 1 (interp V ρ F) fun a => holeFam (cons a ρ) Fs fun as => g (a :: as)

omit [SetTheory V] in
theorem shiftE_one_succ (n : Nat) (ρ : Nat → V) :
    shiftE n 0 (fun j => ρ (j + 1)) = shiftE (n + 1) 0 ρ := by
  funext i; simp only [shiftE, Nat.not_lt_zero, if_false]; rw [Nat.add_assoc]

omit [SetTheory V] in
theorem frameIdx_concat (n : Nat) (ρ : Nat → V) :
    frameIdx (n + 1) ρ = frameIdx n (fun j => ρ (j + 1)) ++ [ρ 0] := by
  unfold frameIdx
  rw [List.range_succ, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro l hl
    have := List.mem_range.mp hl
    show ρ (n + 1 - 1 - l) = ρ (n - 1 - l + 1)
    congr 1; omega
  · simp

/-- `spineFit_frameIdx_of_sat`, by induction on the length. -/
theorem spineFit_frameIdx_of_sat_len :
    ∀ (n : Nat) {Ds : List AnnotTerm} {ρ : Nat → V}, Ds.length = n → Sat V Ds.reverse ρ →
      SpineFit (shiftE Ds.length 0 ρ) Ds (frameIdx Ds.length ρ)
  | 0, Ds, _, hn, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn; trivial
  | n + 1, Ds, ρ, hn, h => by
    rcases List.eq_nil_or_concat Ds with rfl | ⟨Ds', D, rfl⟩
    · exact absurd hn (by simp)
    rw [List.concat_eq_append] at hn h ⊢
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at h
    have h0 : ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) D := by
      have := h 0 D rfl; simpa using this
    have htl : Sat V Ds'.reverse (fun j => ρ (j + 1)) := Sat_tail h
    have hlen : Ds'.length = n := by simpa using hn
    have hih := spineFit_frameIdx_of_sat_len n hlen htl
    rw [List.length_append, List.length_singleton, frameIdx_concat, ← shiftE_one_succ]
    refine hih.append ⟨?_, trivial⟩
    rw [consList_frameIdx]
    exact h0

/-- **A satisfied reversed context is a fitting spine of its own frame
index over its shift.** -/
theorem spineFit_frameIdx_of_sat {Ds : List AnnotTerm} {σ : Nat → V}
    (h : Sat V Ds.reverse σ) :
    SpineFit (shiftE Ds.length 0 σ) Ds (frameIdx Ds.length σ) :=
  spineFit_frameIdx_of_sat_len _ rfl h

end HoleFam

/-- **The part of a block's representation the lfp clause reads** (see
the module docstring).  A uniform block's is `BlockData.toLfp`. -/
structure LfpDatum (V : Type w) where
  /-- the members' names, by position -/
  names : List Name
  /-- the number of MEMBERS -/
  k : Nat
  /-- the operator's WIDTH (members, then instance components) -/
  N : Nat
  /-- the result sort's value, per level assignment -/
  w : (Name → Nat) → Nat
  /-- the parameter telescope -/
  params : (Name → Nat) → List AnnotTerm
  /-- member `m`'s OWN parameter telescope (its former's binders): a
  hole's λ-tower is over it, as the member's former value is.  At a
  checked block it is `Sat`-equivalent to `params`. -/
  pars : Nat → (Name → Nat) → List AnnotTerm
  /-- per component: its own index telescope -/
  ids : Nat → (Name → Nat) → List AnnotTerm
  /-- per component: its index-tuple sort -/
  u : Nat → (Name → Nat) → Nat
  /-- **the tuple operator**, at a level assignment and a parameter frame -/
  Φ : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- the constructor injections -/
  inj : (Name → Nat) → Nat → Nat → List V → V
  /-- **the hole reading** (charter item 2, lane HOLE2): component `c`'s
  constructor count -/
  nctors : Nat → Nat
  /-- component `c`'s constructor `j`'s name -/
  ctorName : Nat → Nat → Name
  /-- component `c`'s constructor `j`'s FIELD READINGS WITH HOLES: the
  member-abstracted constructor domains, read at the parameters, then
  one hole per member (member `m` at the variable `nP + m`), then the
  earlier fields -/
  fields : (Name → Nat) → Nat → Nat → List AnnotTerm
  /-- component `c`'s constructor `j`'s result index readings, below the
  fields -/
  resIdx : (Name → Nat) → Nat → Nat → List AnnotTerm

namespace LfpDatum

variable {V : Type w} [SetTheory V] (D : LfpDatum V)

/-- Member `mm`'s name. -/
@[expose] def member (mm : Nat) : Name := D.names.getD mm .anonymous

/-- The tuple of index-tuple sets at a parameter frame. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  fun c => idxSet (D.u c ψ) ρp (D.ids c ψ)

/-- **The carrier**: the least pre-fixed tuple of the operator. -/
@[expose] noncomputable def carrier (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  lfpTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp)

/-- **Member `m`'s hole value** at the tuple `X` (lane HOLE2): the
λ-tower over the parameters and `m`'s indices (the member former's
binders, read from below the parameter frame) of `X m` at the index
tuple — the family of `X`, curried, blind in its parameters (a hole is
only ever applied to the block's own parameters). -/
@[expose] noncomputable def holeVal (ψ : Name → Nat) (ρp X : Nat → V) (m : Nat) : V :=
  holeFam (shiftE (D.pars m ψ).length 0 ρp) (D.pars m ψ ++ D.ids m ψ)
    fun vs => app (X m) (tupW (D.u m ψ) (vs.drop (D.pars m ψ).length))

/-- **The hole frame** at `(ρp, X)`: the parameter frame with member
`m`'s hole value at the variable `nP + m` (so the last member is
innermost). -/
@[expose] noncomputable def frame (ψ : Name → Nat) (ρp X : Nat → V) : Nat → V :=
  consList ((List.range D.k).map (D.holeVal ψ ρp X)) ρp

/-- **The hole fit**: `fs` fits component `c`'s constructor `j` at the
hole frame of `(ρp, X)` — each field in its reading with holes at the
earlier ones — and its result index readings are the components of the
index tuple `t`. -/
@[expose] def HFits (ψ : Name → Nat) (ρp X : Nat → V) (t : V) (c j : Nat) (fs : List V) :
    Prop :=
  j < D.nctors c ∧ SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs ∧
    ∀ l, l < (D.ids c ψ).length → ∃ e, (D.resIdx ψ c j)[l]? = some e ∧
      interp V (consList fs (D.frame ψ ρp X)) e = projS l t

/-- **The holes occur only applied to the parameters** (lane CONTSEM,
R23's M3) in component `c`'s constructor `j`'s field readings (field `l`
below the `l` earlier fields) and result index readings (below all of
them): the fact that lets a container's instantiation read the fields
at a frame whose member slots hold group-mates' formers or frame holes
(`interp_congr_holeApp`). -/
@[expose] def HolesApplied (ψ : Name → Nat) (c j : Nat) : Prop :=
  (∀ l F, (D.fields ψ c j)[l]? = some F → HoleApp D.k (D.params ψ).length l F) ∧
  ∀ e ∈ D.resIdx ψ c j, HoleApp D.k (D.params ψ).length (D.fields ψ c j).length e

end LfpDatum

/-! ## The hole values -/

section HoleVals

variable {V : Type w} [SetTheory V]

/-- A λ-tower applied to a spine fitting its telescope computes. -/
theorem holeFam_app :
    ∀ {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V} (g : List V → V),
      SpineFit ρ Fs as → as.foldl app (holeFam ρ Fs g) = g as
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim
  | ρ, F :: Fs, a :: as, g, h => by
    show as.foldl app (app (lamR 1 (interp V ρ F) _) a) = g (a :: as)
    rw [app_lamR_pos (by decide) h.1]
    exact holeFam_app (fun bs => g (a :: bs)) h.2

namespace LfpDatum

variable {D : LfpDatum V}

/-- **A hole applied to the block's own parameters and fitting indices
is the tuple's component** at the index tuple. -/
theorem holeVal_app {ψ : Name → Nat} {ρp X : Nat → V} {m : Nat}
    (hs : Sat V (D.pars m ψ).reverse ρp) {is : List V} (his : SpineFit ρp (D.ids m ψ) is) :
    (frameIdx (D.pars m ψ).length ρp ++ is).foldl app (D.holeVal ψ ρp X m)
      = app (X m) (tupW (D.u m ψ) is) := by
  have hsp : SpineFit (shiftE (D.pars m ψ).length 0 ρp) (D.pars m ψ)
      (frameIdx (D.pars m ψ).length ρp) := spineFit_frameIdx_of_sat hs
  have hlen : (frameIdx (D.pars m ψ).length ρp).length = (D.pars m ψ).length := by
    simp [frameIdx]
  have hfr : consList (frameIdx (D.pars m ψ).length ρp) (shiftE (D.pars m ψ).length 0 ρp) = ρp :=
    consList_frameIdx _ ρp
  unfold holeVal
  rw [holeFam_app _ (hsp.append (by rw [hfr]; exact his)), List.drop_left' hlen]

end LfpDatum

end HoleVals

variable {V : Type w} [SetTheory V]

/-- **The constructors' result indices fit the index telescope** at
the carrier (lane NESTIND, finding F5 — `BlockModelAt.resIdxFit`'s
clause form): a spine hole-fitting constructor `(c, j)` at the carrier
of a satisfying parameter frame has result index readings fitting
component `c`'s index telescope there.  The recursor's rule data at an
OUTSIDE class need it (the fired major's index tuple lies in the index
set: `instCtor_decode`); recorded as `LfpClause.resIdxFit`. -/
@[expose] def LfpResIdxFit (D : LfpDatum V) : Prop :=
  ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ fs : List V,
      SpineFit (D.frame ψ ρp (D.carrier ψ ρp)) (D.fields ψ c j) fs →
      SpineFit ρp (D.ids c ψ)
        ((D.resIdx ψ c j).map (interp V (consList fs (D.frame ψ ρp (D.carrier ψ ρp)))))

/-- **The lfp clause** of the block `D`, over the leaf valuation
`acval` (see the module docstring). -/
structure LfpClause (acval : Name → (Name → Nat) → AnnotTerm) (D : LfpDatum V) : Prop where
  /-- the members come first among the components -/
  kN : D.k ≤ D.N
  /-- **every component's index telescope is graded** at every
  satisfying parameter frame (lane NESTIND, finding F1): what inverting
  an index tuple back to its spine (`isOfW_tupW`) needs at a container -/
  idxOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ c, c < D.N → IdxOk (D.u c ψ) ρp (D.ids c ψ)
  /-- **`Φ` is a monotone tuple functor** with a closed tuple -/
  functor : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) ∧
    MapsTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) ∧
    ∃ L, IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) L
  /-- **what `Φ` is**: component `c`'s fibre at `(X, t)` is the set of
  injections of the spines fitting one of `c`'s constructors -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
    ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
      x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs
  /-- **the hole fit grows with the tuple** (positivity's, at the fit):
  a spine fitting a constructor at the hole frame of a tuple fits it at
  the hole frame of every larger tuple -/
  fitsMono : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp →
    ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y →
    TupleLe D.N (D.idx ψ ρp) X Y → ∀ c, c < D.N → ∀ (t : V) (j : Nat) (fs : List V),
      D.HFits ψ ρp X t c j fs → D.HFits ψ ρp Y t c j fs
  /-- **the leaf**: a member's former at fitting parameters and its own
  indices is the carrier's component at the index tuple -/
  leaf : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (D.params ψ) as → SpineFit (consList as ρ) (D.ids mm ψ) is →
    (as ++ is).foldl app (interp V ρ (acval (D.member mm) ψ))
      = app (D.carrier ψ (consList as ρ) mm) (tupW (D.u mm ψ) is)
  /-- at a `Prop`-valued block every injection is the point -/
  mkZero : ∀ ψ : Name → Nat, D.w ψ = 0 → ∀ c j fs, D.inj ψ c j fs = pt
  /-- at a `Type`-valued block a component's injections are injective
  across its constructors, at spines of the constructors' lengths -/
  mkInj : ∀ ψ : Name → Nat, D.w ψ ≠ 0 → ∀ c, c < D.N → ∀ j fs j' fs',
    j < D.nctors c → j' < D.nctors c →
    fs.length = (D.fields ψ c j).length → fs'.length = (D.fields ψ c j').length →
    D.inj ψ c j fs = D.inj ψ c j' fs' → j = j' ∧ fs = fs'
  /-- **the constructors**: component `c`'s constructor `j`, at fitting
  parameters and fields fitting its hole reading at the carrier, is its
  injection -/
  ctor : ∀ c, c < D.N → ∀ j (ψ : Name → Nat) (ρ : Nat → V) (as fs : List V) (t : V),
    SpineFit ρ (D.params ψ) as → t ∈ˢ D.idx ψ (consList as ρ) c →
    D.HFits ψ (consList as ρ) (D.carrier ψ (consList as ρ)) t c j fs →
    (as ++ fs).foldl app (interp V ρ (acval (D.ctorName c j) ψ)) = D.inj ψ c j fs
  /-- **each member's own parameter telescope is the block's** (R23's M1):
  as long, and satisfied where the block's is — what `holeVal_app` needs
  to read a hole applied to the block's parameters -/
  parsLen : ∀ mm, mm < D.k → ∀ ψ : Name → Nat, (D.pars mm ψ).length = (D.params ψ).length
  parsSat : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (D.params ψ).reverse ρ → Sat V (D.pars mm ψ).reverse ρ
  /-- **… and satisfied only where the block's is** (lane CONTSEM, M1′):
  a container instance's parameters are typed by the container's own
  former telescope, the leaf reads them at the block's -/
  parsSatInv : ∀ mm, mm < D.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (D.pars mm ψ).reverse ρ → Sat V (D.params ψ).reverse ρ
  /-- **the holes occur only applied to the parameters** (R23's M3) -/
  holeApp : ∀ (ψ : Name → Nat) c, c < D.N → ∀ j, j < D.nctors c → D.HolesApplied ψ c j
  /-- **the constructors' result indices fit the index telescope** at the
  carrier (lane NESTIND, finding F5) -/
  resIdxFit : LfpResIdxFit D
  /-- **at a `Type`-valued parameterised block no injection is the point**
  (lane ACCMODEL, session 3: the container case of the accessibility
  route — the TYPE REGIME of a container instance, whose truth-valued
  fibre is then empty).  The parameter guard is necessary: the pinned
  `PUnit.{u+1}`'s constructor denotes `pt`; every parameterised recorded
  block is a uniform one (tagged injections) or `Prop`-valued (`Eq`). -/
  injNePt : ∀ ψ : Name → Nat, D.w ψ ≠ 0 → (D.params ψ).length ≠ 0 →
    ∀ c j fs, D.inj ψ c j fs ≠ pt
  /-- **the constructors' fields are small** at a `Type`-valued block, at
  every hole frame of the tuple space (lane ACCMODEL, session 3: the
  frame walk of a container reads its constructors' fields along the
  accessibility relation, which supports small elements only — the
  install's own `FieldsOkB`, recorded) -/
  fieldsOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (D.params ψ).reverse ρp → D.w ψ ≠ 0 →
    ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N → ∀ j, j < D.nctors c →
      FieldsOkB (D.w ψ) (D.frame ψ ρp X) (D.fields ψ c j)

namespace LfpClause

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}

/-- **Transport**: the clause reads the leaf valuation only at the
members' and the constructors' names. -/
theorem congr (h : LfpClause acval D) {acval' : Name → (Name → Nat) → AnnotTerm}
    (hag : ∀ mm, mm < D.k → acval' (D.member mm) = acval (D.member mm))
    (hagC : ∀ c, c < D.N → ∀ j, j < D.nctors c → acval' (D.ctorName c j) = acval (D.ctorName c j)) :
    LfpClause acval' D where
  kN := h.kN
  idxOk := h.idxOk
  functor := h.functor
  fibre := h.fibre
  fitsMono := h.fitsMono
  leaf := fun mm hmm ψ ρ as is hsa hsi => by
    rw [hag mm hmm]; exact h.leaf mm hmm ψ ρ as is hsa hsi
  mkZero := h.mkZero
  mkInj := h.mkInj
  ctor := fun c hc j ψ ρ as fs t hsa ht hf => by
    rw [hagC c hc j hf.1]; exact h.ctor c hc j ψ ρ as fs t hsa ht hf
  parsLen := h.parsLen
  parsSat := h.parsSat
  parsSatInv := h.parsSatInv
  holeApp := h.holeApp
  resIdxFit := h.resIdxFit
  injNePt := h.injNePt
  fieldsOk := h.fieldsOk


/-- **The carrier is a fixed point**, componentwise. -/
theorem carrier_eq (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {c : Nat} (hc : c < D.N) :
    D.Φ ψ ρp (D.carrier ψ ρp) c = D.carrier ψ ρp c := by
  obtain ⟨hmono, hmaps, hcl⟩ := h.functor ψ ρp hsat
  exact lfpTuple_eq hcl hmono hmaps hc

/-- **The carrier's case analysis**: an element of component `c`'s
carrier is the injection of a spine fitting one of `c`'s constructors
at the carrier. -/
theorem carrier_case (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {c : Nat} (hc : c < D.N) {t : V}
    (ht : t ∈ˢ D.idx ψ ρp c) {x : V} (hx : x ∈ˢ app (D.carrier ψ ρp c) t) :
    ∃ j fs, D.HFits ψ ρp (D.carrier ψ ρp) t c j fs ∧ x = D.inj ψ c j fs := by
  rw [← h.carrier_eq hsat hc] at hx
  exact (h.fibre ψ ρp hsat _ (lfpTuple_mem _ _ _ _) c hc t ht x).mp hx


/-- **The fibre in hole form**: component `c`'s fibre at `(X, t)` is the
set of injections of the spines fitting one of `c`'s constructors'
readings with holes at the hole frame of `X`. -/
theorem fibre_holes (h : LfpClause acval D) {ψ : Name → Nat} {ρp : Nat → V}
    (hsat : Sat V (D.params ψ).reverse ρp) {X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {c : Nat} (hc : c < D.N) {t : V}
    (ht : t ∈ˢ D.idx ψ ρp c) (x : V) :
    x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs :=
  h.fibre ψ ρp hsat X hX c hc t ht x

end LfpClause

end ConLeche.Model
