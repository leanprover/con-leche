module

public import ConLeche.Model.Inductives.FixStageRec
public import ConLeche.SetTheory.Derive.LfpCompose
public section

/-!
# `IsBlockModel` — THE ONE DATUM of an inductive block (task #315, M2; the nested arm M6)

Every stored inductive type is a MEMBER of a block of `k` families,
and the block is represented as the simultaneous least pre-fixed point
of ONE operator on a TUPLE of families (`lfpTuple`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`), one component per member,
each over the member's own plain index-tuple set.  No member tag enters
an index, no constructor position is flattened across members, no copy
of anything is minted: the block model of a mutual block is the block model of a
single family with the family replaced by a tuple, and a single family
is the block with `k = 1` (`lfpTuple_one`).

**The block model** (`BlockModel`) is the fixpoint route's spelling of a
block, keyed by MEMBER and by the member's OWN constructor position:
per member its telescope reading, index-tuple sort and constructors,
per constructor the readings of its stored type (`FixCtorDataI`'s
data: field data `dsF`, index readings `esF`, kinds `ksF`, the
recursive fields' index expressions `eissF` and reflexive telescopes
`tssF`) and, per field, the MEMBER it targets (`tgts`); the tuple
operator `Φ` (per level assignment and parameter frame, a meta-level
function on tuples) and the member-local constructor injections `inj`
— both abstract, so a pinned block whose elements are not tagged
towers (`Nat` as ω) is represented on the nose.

**The clause** (`IsBlockModel`), for the stored inductive `T` = member `mm`
with recursor `T.rec = .recInfo cvR mI rP rules`:

* the stored types read as the spelling says (`former`, `ctors` — the
  latter with the field kinds' TARGET MEMBERS: `BlockCtorFacts`, the
  target-aware twin of `FixCtorFactsAt`), and the recursor's arithmetic
  and rules are the block's (`mI`, `rP`, `rules`);
* at every parameter frame each member's index telescope is graded
  (`idxOk`) and `Φ` is a monotone, space-preserving tuple functor with
  a closed tuple (`functor` — its third conjunct is (W) at tuples,
  `SetModel/TupleContainer.lean`), whose component `mm'`'s fibre at
  `(X, t)` consists exactly of the injections `inj mm' j fs` of the
  spines fitting member `mm'`'s constructor `j` at `(X, t)` (`fibre`),
  a recursive field read at the component of the member it targets
  (`ChainFit`, stated SEMANTICALLY: an entry is a set, the slot the
  target member's family at the tuple of the index expressions under
  the field's telescope — `slotSet`);
* **the leaf**: the member's former at fitting parameters and its own
  indices is the fibre of the least pre-fixed TUPLE's component `mm`
  at the index tuple (`leaf`);
* **the constructors**: constructor `j` of member `mm'` at fitting
  parameters and fields is `inj mm' j fs` (`ctor`); the injections are
  the point at a `Prop`-valued block (`mkZero`) and injective WITHIN a
  member at a `Type`-valued one (`mkInj` — cross-member disjointness is
  never needed: the recursor's union tags the members, DESIGN §U.1 (f)).

**The section view** (`IsBlockModel.ofMember`, Bekić): member `mm`'s
component is the least pre-fixed FAMILY of `Φ`'s section at `mm`, the
other members held at their carriers — a single-family block model whose
operator reads the other members as CONSTANTS, the way parameters
enter (`lfpTuple_eq_section`).  It is a DERIVED law, not a clause:
the section laws alone do not determine the tuple (DESIGN §M.58).

What is NOT here, against `inductives`' `IndRep`: the doubled index
readings (`essC`/`eissC`) and every container-level `IdsC`/`u`/`tup`
(there is no tagged container), the flat constructor positions (the
injection is member-local by type), the syntactic X-chain grading
`chains` (its semantic content is `functor`'s `MapsTuple` and `idxOk`;
no uniform consumer reads syntax through the fibre), and the
`ModeledLeaf` disjunct (the modeled route's, deleted with it at M8).
**The nested-slot arm** (task #315 M6, DESIGN §U.13): a TARGET is a
member (`tgt < k`) or a PIN (`tgt = k + q`) — a stored container
applied to components that mention the members (`List (Tree α)`).  A
pin is a syntactic record (`PinSyn`: the container, its level
assignment at the pin, the components at the block's parameter
openers and their readings, the container's own telescope) and ONE
abstract semantic field, `pinCar ψ ρp X q` — the pin's carrier as a
FAMILY at the tuple `X` — so a nested field's slot is literally the
recursive slot's `slotSet` at the target's family (`famAt`): no
parallel kind, no change to `RecFieldKind`.  The clauses tie the
abstract field down: `pinMem` (a family over the pin's index set),
`pinMono` (monotone in the tuple — the container's map action, D-2b's
(P)), `pinLeaf` (at the carrier the pin's stored reading IS `pinCar`
at the least tuple — the reading law (X.1) and the level fit K.27 are
consumed by the ASSEMBLY that supplies this clause, never by a
consumer).  A mutual or single block has `pins = []` and every target
a member.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## A pin -/

/-- **A pin's syntactic record**: a stored container `J` applied at
the block's parameter openers to components `Ds` that mention the
members (`nestedPinsOk`'s subject, K.3 `pinsClosed`: `DsE` are
fvar-free below the openers).  `ψJ` is the container's level
assignment at the pin's levels `lvls`; `Ds` the components' BAKED
readings at depth `nP` (the members' leaves inside); `pps` the
container's OWN telescope reading (closed, at its level assignment),
`nPJ` its parameter count, `nIdx` its index count and `u` its
index-tuple sort. -/
structure PinSyn where
  /-- the container -/
  J : Name
  /-- the pin's level arguments (over the block's level parameters) -/
  lvls : List Level
  /-- the container's level assignment at the pin -/
  ψJ : (Name → Nat) → (Name → Nat)
  /-- the container's parameter count -/
  nPJ : Nat
  /-- the pin's components at the block's parameter openers -/
  DsE : List Expr
  /-- the components' readings at depth `nP` -/
  Ds : (Name → Nat) → List AnnotTerm
  /-- the container's index count -/
  nIdx : Nat
  /-- the container's index-tuple sort, at the pin's level assignment -/
  u : (Name → Nat) → Nat
  /-- the container's parameter-and-index telescope reading, at ITS level assignment -/
  pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)

instance : Inhabited PinSyn :=
  ⟨⟨.anonymous, [], id, 0, [], fun _ => [], 0, fun _ => 0, fun _ => []⟩⟩

/-- The container's index telescope at the pin (over ITS parameters). -/
@[expose] def PinSyn.Ids (q : PinSyn) (ψ : Name → Nat) : List AnnotTerm :=
  ((q.pps (q.ψJ ψ)).drop q.nPJ).map (·.2.2)

/-! ## The constructor's reading with target members -/

/-- **`nativeOpenedOk`, read positionally, with a TARGET MEMBER per
field**: `FixOpened`'s twin in which a recursive or reflexive field's
head is the former of the member it targets (`Tof i`) with that
member's index count (`nIdxOf i`).  At a single family `Tof = fun _ =>
T`, `nIdxOf = fun _ => nIdx` and this IS `FixOpened`
(`BlockOpened.ofFix`). -/
structure BlockOpened (env₀ : Env) (Tof : Nat → Name) (nIdxOf : Nat → Nat)
    (nest : Nat → Option Nat) (pins : Nat → PinSyn) (lps : List Name)
    (nP nF : Nat) (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr) : Prop where
  residRes : ∀ e ∈ xrest.getAppArgs.drop nP, e.constsResolve env₀ = true
  ord : ∀ i x, xFvs[i]? = some x → ks.getD i .ordinary = .ordinary →
    x.fvarTypeD.constsResolve env₀ = true
  recF : ∀ i x, xFvs[i]? = some x → nest i = none → ks.getD i .ordinary = .recursive →
    x.fvarTypeD.getAppFn = Expr.const (Tof i) (lps.map .param) ∧
    x.fvarTypeD.getAppArgs.take nP = fvsP ∧
    x.fvarTypeD.getAppArgs.length = nP + nIdxOf i ∧
    (∀ e ∈ x.fvarTypeD.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
    (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
    xrest.mentionsFvar (nP + i) = false
  reflF : ∀ i x, xFvs[i]? = some x → nest i = none → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      afvs.length ≠ 0 ∧
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env₀ = true) ∧
      body.getAppFn = Expr.const (Tof i) (lps.map .param) ∧
      body.getAppArgs.take nP = fvsP ∧
      body.getAppArgs.length = nP + nIdxOf i ∧
      (∀ e ∈ body.getAppArgs.drop nP, e.constsResolve env₀ = true) ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false
  /-- a NESTED finitary field: the pin's container (the components'
  identity is SEMANTIC — `BlockCtorData.nestEntry` — since the opened
  form re-annotates the parameter variables), then index arguments free
  of the block -/
  nestF : ∀ i x q, xFvs[i]? = some x → nest i = some q → ks.getD i .ordinary = .recursive →
    x.fvarTypeD.getAppFn = Expr.const (pins q).J (pins q).lvls ∧
    x.fvarTypeD.getAppArgs.length = (pins q).nPJ + (pins q).nIdx ∧
    (∀ e ∈ x.fvarTypeD.getAppArgs.drop (pins q).nPJ, e.constsResolve env₀ = true) ∧
    (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
    xrest.mentionsFvar (nP + i) = false
  /-- a NESTED reflexive field -/
  nestReflF : ∀ i x q, xFvs[i]? = some x → nest i = some q → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      afvs.length ≠ 0 ∧
      (∀ a ∈ afvs, a.fvarTypeD.constsResolve env₀ = true) ∧
      body.getAppFn = Expr.const (pins q).J (pins q).lvls ∧
      body.getAppArgs.length = (pins q).nPJ + (pins q).nIdx ∧
      (∀ e ∈ body.getAppArgs.drop (pins q).nPJ, e.constsResolve env₀ = true) ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false
  kinds : ∀ i, i < nF → ks.getD i .ordinary = .ordinary ∨ ks.getD i .ordinary = .recursive ∨
    ks.getD i .ordinary = .reflexive

/-- A single family's opened form is the block form with every field
targeting the family. -/
theorem BlockOpened.ofFix {env₀ : Env} {T : Name} {lps : List Name} {nP nIdx nF : Nat}
    {ks : List RecFieldKind} {fvsP xFvs : List Expr} {xrest : Expr}
    (nest : Nat → Option Nat) (pins : Nat → PinSyn)
    (hn : ∀ i x, xFvs[i]? = some x → nest i = none)
    (h : FixOpened env₀ T lps nP nIdx nF ks fvsP xFvs xrest) :
    BlockOpened env₀ (fun _ => T) (fun _ => nIdx) nest pins lps nP nF ks fvsP xFvs xrest :=
  ⟨h.residRes, h.ord, fun i x hx _ hk => h.recF i x hx hk, fun i x hx _ hk => h.reflF i x hx hk,
    (fun i x q hx hq _ => by rw [hn i x hx] at hq; exact nomatch hq),
    (fun i x q hx hq _ => by rw [hn i x hx] at hq; exact nomatch hq),
    h.kinds⟩

/-- **A constructor's data with target members** — `FixCtorDataI`'s
twin: the sum's reading at the constructor's OWN member `T`, the opened
form with a target per field, and the readings a recursive or
reflexive field yields at ITS target's former (`recEntry`,
`reflEntry`) with that target's index count (`eisLen`,
`eisLenRefl`). -/
structure BlockCtorData {env : Env} (m : EnvModel V env) (env₀ : Env) (T : Name)
    (Tof : Nat → Name) (nIdxOf : Nat → Nat) (nest : Nat → Option Nat) (pins : Nat → PinSyn)
    (lps : List Name) (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) (ks : List RecFieldKind) (fvsP xFvs : List Expr) (xrest : Expr)
    (Eiss : (Name → Nat) → List (List AnnotTerm))
    (tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : Prop
    extends CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs where
  opened : BlockOpened env₀ Tof nIdxOf nest pins lps nP nF ks fvsP xFvs xrest
  opens : ∃ crest, openPisAtFvars nP cvC.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nF crest nP = some (xFvs, xrest)
  ksLen : ks.length = nF
  xLen : xFvs.length = nF
  pLen : fvsP.length = nP
  xIdx : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty
  idxEq : idxArgs = xrest.getAppArgs.drop nP
  domRead : ∀ ψ i x, xFvs[i]? = some x →
    denoteMeta m.acval env ψ (nP + i) x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2
  eissLen : ∀ ψ, (Eiss ψ).length = nF
  eisRead : ∀ ψ i x, xFvs[i]? = some x → nest i = none → ks.getD i .ordinary = .recursive →
    DenoteMetaSpine m.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLen : ∀ ψ i, nest i = none → ks.getD i .ordinary = .recursive → i < nF →
    ((Eiss ψ).getD i []).length = nIdxOf i
  recEntry : ∀ ψ i, nest i = none → ks.getD i .ordinary = .recursive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = AnnotTerm.mkAppN (m.acval (Tof i) ψ) (paramBvarsAt nP (nP + i) ++ (Eiss ψ).getD i [])
  /-- a NESTED finitary field's index arguments read -/
  nestEisRead : ∀ ψ i x q, xFvs[i]? = some x → nest i = some q → ks.getD i .ordinary = .recursive →
    DenoteMetaSpine m.acval env ψ (nP + i) (x.fvarTypeD.getAppArgs.drop (pins q).nPJ)
      ((Eiss ψ).getD i [])
  nestEisLen : ∀ ψ i q, nest i = some q → ks.getD i .ordinary = .recursive → i < nF →
    ((Eiss ψ).getD i []).length = (pins q).nIdx
  /-- **a NESTED finitary field's entry**: the container's leaf at the
  pin's components (lifted past the earlier fields) and the field's
  index readings -/
  nestEntry : ∀ ψ i q, nest i = some q → ks.getD i .ordinary = .recursive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = AnnotTerm.mkAppN (m.acval (pins q).J ((pins q).ψJ ψ))
          (((pins q).Ds ψ).map (·.liftN i 0) ++ (Eiss ψ).getD i [])
  eissParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → Eiss ψ₁ = Eiss ψ₂
  eissBelow : ∀ ψ i, ∀ E ∈ (Eiss ψ).getD i [],
    Term.bvarsBelow (nP + i + ((tss ψ).getD i []).length) E.erase
  ordNone : ∀ ψ i, ks.getD i .ordinary ≠ .recursive → ks.getD i .ordinary ≠ .reflexive →
    (Eiss ψ).getD i [] = []
  tssLen : ∀ ψ, (tss ψ).length = nF
  tssNone : ∀ ψ i, ks.getD i .ordinary ≠ .reflexive → (tss ψ).getD i [] = []
  tssBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], (d.2.1 = 0 ↔ resSort.eval ψ = 0)
  tssPiBits : ∀ ψ i, ∀ d ∈ (tss ψ).getD i [], d.1 = 0 ∧ d.2.1 ≤ 1
  tssBelow : ∀ ψ i, DomsBelow (nP + i) ((tss ψ).getD i [])
  tssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cvC.levelParams, ψ₁ q = ψ₂ q) → tss ψ₁ = tss ψ₂
  reflOpen : ∀ ψ i x, xFvs[i]? = some x → nest i = none → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      ((tss ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
      (∀ k a, afvs[k]? = some a →
        denoteMeta m.acval env ψ (nP + i + k) a.fvarTypeD
          = some (((tss ψ).getD i []).getD k default).2.2) ∧
      DenoteMetaSpine m.acval env ψ (nP + i + ((tss ψ).getD i []).length)
        (body.getAppArgs.drop nP) ((Eiss ψ).getD i [])
  eisLenRefl : ∀ ψ i, nest i = none → ks.getD i .ordinary = .reflexive → i < nF →
    ((Eiss ψ).getD i []).length = nIdxOf i
  reflEntry : ∀ ψ i, nest i = none → ks.getD i .ordinary = .reflexive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = mkPisAV ((tss ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval (Tof i) ψ)
            (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i []))
  /-- a NESTED reflexive field opens under its telescope -/
  nestReflOpen : ∀ ψ i x q, xFvs[i]? = some x → nest i = some q → ks.getD i .ordinary = .reflexive →
    ∃ afvs body,
      openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
      ((tss ψ).getD i []).length = (x.fvarTypeD.piBinders).1.length ∧
      (∀ k a, afvs[k]? = some a →
        denoteMeta m.acval env ψ (nP + i + k) a.fvarTypeD
          = some (((tss ψ).getD i []).getD k default).2.2) ∧
      DenoteMetaSpine m.acval env ψ (nP + i + ((tss ψ).getD i []).length)
        (body.getAppArgs.drop (pins q).nPJ) ((Eiss ψ).getD i [])
  nestEisLenRefl : ∀ ψ i q, nest i = some q → ks.getD i .ordinary = .reflexive → i < nF →
    ((Eiss ψ).getD i []).length = (pins q).nIdx
  /-- **a NESTED reflexive field's entry** -/
  nestReflEntry : ∀ ψ i q, nest i = some q → ks.getD i .ordinary = .reflexive → i < nF →
    ((ds ψ).getD (nP + i) default).2.2
      = mkPisAV ((tss ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval (pins q).J ((pins q).ψJ ψ))
            (((pins q).Ds ψ).map (·.liftN (i + ((tss ψ).getD i []).length) 0) ++ (Eiss ψ).getD i []))

/-- A single family's constructor data is the block form with every
field targeting the family. -/
theorem BlockCtorData.ofFix {m : EnvModel V env} {env₀ : Env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (nest : Nat → Option Nat) (pins : Nat → PinSyn) (hn : ∀ i, i < nF → nest i = none)
    (h : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks
      fvsP xFvs xrest Eiss tss) :
    BlockCtorData m env₀ T (fun _ => T) (fun _ => nIdx) nest pins lps cvC nP nF nIdx resSort isProp
      large idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss :=
  have hnx : ∀ i x, xFvs[i]? = some x → nest i = none := fun i x hx =>
    hn i (h.xLen ▸ (List.getElem?_eq_some_iff.mp hx).1)
  { h.toCtorDataI with
    opened := BlockOpened.ofFix nest pins hnx h.opened, opens := h.opens, ksLen := h.ksLen
    xLen := h.xLen, pLen := h.pLen
    xIdx := h.xIdx, pIdx := h.pIdx, idxEq := h.idxEq, domRead := h.domRead, eissLen := h.eissLen
    eisRead := fun ψ i x hx _ hk => h.eisRead ψ i x hx hk
    eisLen := fun ψ i _ hk hi => h.eisLen ψ i hk hi
    recEntry := fun ψ i _ hk hi => h.recEntry ψ i hk hi
    nestEisRead := fun _ i x q hx hq _ => by rw [hnx i x hx] at hq; exact nomatch hq
    nestEisLen := fun _ i q hq _ hi => by rw [hn i hi] at hq; exact nomatch hq
    nestEntry := fun _ i q hq _ hi => by rw [hn i hi] at hq; exact nomatch hq
    eissParams := h.eissParams
    eissBelow := h.eissBelow, ordNone := h.ordNone, tssLen := h.tssLen, tssNone := h.tssNone
    tssBits := h.tssBits, tssPiBits := h.tssPiBits, tssBelow := h.tssBelow
    tssParams := h.tssParams
    reflOpen := fun ψ i x hx _ hk => h.reflOpen ψ i x hx hk
    eisLenRefl := fun ψ i _ hk hi => h.eisLenRefl ψ i hk hi
    reflEntry := fun ψ i _ hk hi => h.reflEntry ψ i hk hi
    nestReflOpen := fun _ i x q hx hq _ => by rw [hnx i x hx] at hq; exact nomatch hq
    nestEisLenRefl := fun _ i q hq _ hi => by rw [hn i hi] at hq; exact nomatch hq
    nestReflEntry := fun _ i q hq _ hi => by rw [hn i hi] at hq; exact nomatch hq }

/-! ## The pins' constructors at the pin -/

/-- **A pin's constructors at the pin** (see the module docstring):
the container's constructors instantiated at the pin's components —
per constructor its field domains at the block's parameter frame
(depth `nP`; a recursive entry is its target's family applied), its
recursive flags, its fields' targets in `members ++ pins`, its
reflexive telescopes and index expressions, its result's index
readings — and the pin's injection (the container's, abstract). -/
structure PinCtors (V : Type w) where
  /-- the container's constructors, with their field counts -/
  ctors : List (ConstantVal × Nat)
  /-- per constructor: the field domains at the block's parameter frame -/
  Fss : (Name → Nat) → List (List AnnotTerm)
  /-- per constructor: the recursive flags -/
  rss : List (List Bool)
  /-- per constructor and field: the target class -/
  tgts : Nat → Nat → Nat
  /-- per constructor: the reflexive fields' telescopes -/
  tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))
  /-- per constructor: the recursive fields' index expressions -/
  Eiss : (Name → Nat) → List (List (List AnnotTerm))
  /-- per constructor: the result's index readings -/
  Ess : (Name → Nat) → List (List AnnotTerm)
  /-- the injection at a field spine -/
  inj : (Name → Nat) → Nat → List V → V

noncomputable instance : Inhabited (PinCtors V) :=
  ⟨⟨[], fun _ => [], [], fun _ _ => 0, fun _ => [], fun _ => [], fun _ => [], fun _ _ _ => pt⟩⟩

/-! ## The block model -/

/-- **The representation block model of a block** (see the module
docstring): the fixpoint route's spelling of the block, keyed by
member and by the member's own constructor position, the tuple
operator `Φ` and the member-local constructor injections `inj`. -/
structure BlockModel (V : Type w) where
  /-- the parameter count (shared by the members) -/
  nP : Nat
  /-- the number of members -/
  k : Nat
  /-- the result sort (every member's stored type ends in it) -/
  resSort : Level
  /-- `resSort` is provably zero -/
  isProp : Bool
  /-- the eliminator is large -/
  large : Bool
  /-- the pre-block environment (a ghost witness: the ordinary field
  domains resolve in it) -/
  env₀ : Env
  /-- the members' names, by position -/
  memberNames : List Name
  /-- per member: its index count -/
  nIdxs : List Nat
  /-- per member: its parameter-and-index telescope reading -/
  ppsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- per member: its index-tuple sort -/
  uM : Nat → (Name → Nat) → Nat
  /-- per member: its constructors, in order, with their field counts -/
  ctorsM : Nat → List (ConstantVal × Nat)
  /-- per member and constructor: the residual's index arguments -/
  idxF : Nat → Nat → List Expr
  /-- per member and constructor: the type reading's binder data -/
  dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)
  /-- per member and constructor: the result's index readings -/
  esF : Nat → Nat → (Name → Nat) → List AnnotTerm
  /-- per member and constructor: the field sources -/
  srcsF : Nat → Nat → List (Option Nat)
  /-- per member and constructor: the field kinds -/
  ksF : Nat → Nat → List RecFieldKind
  /-- per member, constructor and field: the member the field targets -/
  tgts : Nat → Nat → Nat → Nat
  /-- per member and constructor: the opened parameter variables -/
  fvsPF : Nat → Nat → List Expr
  /-- per member and constructor: the opened field variables -/
  xFvsF : Nat → Nat → List Expr
  /-- per member and constructor: the opened residual -/
  xrestF : Nat → Nat → Expr
  /-- per member and constructor: the recursive fields' index expressions -/
  eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm)
  /-- per member and constructor: the reflexive fields' telescopes -/
  tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))
  /-- **the pins**, in order: a nested field's target `k + q` is pin `q`
  (empty at a mutual or single block) -/
  pins : List PinSyn
  /-- **the tuple operator**, at a level assignment and a parameter
  frame: a meta-level function on tuples of families, component `mm`
  a set-level family over member `mm`'s index-tuple set -/
  Φ : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- **the pins' carriers**: at a level assignment, a parameter frame
  and a tuple `X`, pin `q`'s carrier as a family over the container's
  index-tuple set at the pin — the container at the pin's components
  with the members read as `X` (abstract, as `Φ` is) -/
  pinCar : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- **the wide operator**, at a level assignment and a parameter
  frame: the `k + nPins`-tuple operator of the block TOGETHER with one
  component per pin — the object `Φ` and `pinCar` are composed from
  (`composeΦ`, `pinsCar`), and the one a CONTAINER's instance inside a
  later block is identified with.  A block with no pins carries its own
  `Φ` (`composeΦ` at zero pins is the identity). -/
  Ψaux : (Name → Nat) → (Nat → V) → (Nat → V) → Nat → V
  /-- **the pins' constructors**: pin `q`'s copy of the container's
  constructors, at the pin (`PinCtors`) — the auxiliary block's
  per-component constructor data beyond the members, which is what
  makes the wide operator readable FIBREWISE (`auxFibre`).  A block
  with no pins carries the default. -/
  pinCtors : Nat → PinCtors V
  /-- **the constructor injections**: member `mm`'s constructor `j`
  (member-local) at a field spine -/
  inj : (Name → Nat) → Nat → Nat → List V → V

namespace BlockModel

variable (d : BlockModel V)

/-- The result sort's value. -/
@[expose] def w (ψ : Name → Nat) : Nat := d.resSort.eval ψ

/-- Member `mm`'s name. -/
@[expose] def memberName (mm : Nat) : Name := d.memberNames.getD mm .anonymous

/-- Member `mm`'s index count. -/
@[expose] def nIdxAt (mm : Nat) : Nat := d.nIdxs.getD mm 0

/-- The parameter telescope (the block's, read off member `0`: the
members share their parameters). -/
@[expose] def params (ψ : Name → Nat) : List AnnotTerm := ((d.ppsM 0 ψ).take d.nP).map (·.2.2)

/-- Member `mm`'s own index telescope, at the parameter frame. -/
@[expose] def IdsM (mm : Nat) (ψ : Name → Nat) : List AnnotTerm :=
  ((d.ppsM mm ψ).drop d.nP).map (·.2.2)

/-- The block's constructor count (the recursors' minor count). -/
@[expose] def nCtors : Nat := ((List.range d.k).map fun mm => (d.ctorsM mm).length).sum

/-- Member `mm`'s constructor data list (the fixpoint route's). -/
@[expose] def cds (mm : Nat) (ψ : Name → Nat) : List CtorDatumR :=
  fixCtorDataList (d.dsF mm) (d.esF mm) (d.ksF mm) (d.eissF mm) (d.tssF mm) ψ (d.ctorsM mm) 0

/-- Member `mm`'s recursive flags, per constructor. -/
@[expose] def rss (mm : Nat) : List (List Bool) := rssOfK (d.ksF mm) (d.ctorsM mm).length

/-- Member `mm`'s reflexive telescopes, per constructor. -/
@[expose] def tlss (mm : Nat) (ψ : Name → Nat) : List (List (List (Nat × Nat × AnnotTerm))) :=
  tlssOfR (d.cds mm ψ)

/-- Member `mm`'s recursive fields' index expressions, per constructor. -/
@[expose] def Eiss (mm : Nat) (ψ : Name → Nat) : List (List (List AnnotTerm)) := eissOfR (d.cds mm ψ)

/-- Member `mm`'s field domains, per constructor (the real readings: a
recursive entry is its target's former applied). -/
@[expose] def Fss (mm : Nat) (ψ : Name → Nat) : List (List AnnotTerm) := fssOfR d.nP (d.cds mm ψ)

/-- Member `mm`'s results' index readings, per constructor. -/
@[expose] def Ess (mm : Nat) (ψ : Name → Nat) : List (List AnnotTerm) := essOfR (d.cds mm ψ)

/-- **The tuple of index-tuple sets** at a parameter frame: member
`mm`'s is the tower set over its own index telescope. -/
@[expose] noncomputable def idx (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  fun mm => idxSet (d.uM mm ψ) ρp (d.IdsM mm ψ)

/-- Member `mm`'s index spine as its index tuple. -/
@[expose] noncomputable def tup (ψ : Name → Nat) (mm : Nat) (is : List V) : V :=
  tupW (d.uM mm ψ) is

/-- The number of pins. -/
@[expose] def nPins : Nat := d.pins.length

/-- Pin `q`'s record. -/
@[expose] def pinAt (q : Nat) : PinSyn := d.pins.getD q default

/-- **The nested arm's key**: field `i` of member `mm`'s constructor
`j` targets pin `q` when its target is `k + q`, and no pin (a member)
otherwise. -/
@[expose] def nestOf (mm j i : Nat) : Option Nat :=
  if d.tgts mm j i < d.k then none else some (d.tgts mm j i - d.k)

/-- The container's frame at the pin: the components' readings over
the block's parameter frame. -/
@[expose] noncomputable def pinFrame (q : Nat) (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  consList (((d.pinAt q).Ds ψ).map (interp V ρp)) ρp

/-- **Pin `q`'s index-tuple set** at a parameter frame: the container's
tower set over its own index telescope at the pin's frame. -/
@[expose] noncomputable def pinIdx (q : Nat) (ψ : Name → Nat) (ρp : Nat → V) : V :=
  idxSet ((d.pinAt q).u ψ) (d.pinFrame q ψ ρp) ((d.pinAt q).Ids ψ)

/-- A target's index-tuple sort: the member's or the pin's container's. -/
@[expose] def uT (tgt : Nat) (ψ : Name → Nat) : Nat :=
  if tgt < d.k then d.uM tgt ψ else (d.pinAt (tgt - d.k)).u ψ

/-- **A target's family at the tuple `X`**: a member's component of
`X`, a pin's carrier at `X`. -/
@[expose] noncomputable def famAt (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (tgt : Nat) : V :=
  if tgt < d.k then X tgt else d.pinCar ψ ρp X (tgt - d.k)

/-- **A recursive slot**, as a set, at the frame `ρ` (the parameters
and the `i` earlier fields) and the tuple `X`: field `i` of member
`mm`'s constructor `j` reads its TARGET's family at `X` (`famAt`: the
target member's component, or the target pin's carrier — the
nested-slot arm, task #315 M6) at the tuple of its index expressions
under its telescope (`slotSet`).  The parameter frame a pin's carrier
is taken at is the slot's frame below the `i` fields. -/
@[expose] noncomputable def slotAt (ψ : Name → Nat) (X : Nat → V) (mm j i : Nat) (ρ : Nat → V) : V :=
  slotSet (d.w ψ) (d.uT (d.tgts mm j i) ψ) ρ (((d.tlss mm ψ).getD j []).getD i [])
    (((d.Eiss mm ψ).getD j []).getD i [])
    (d.famAt ψ (fun n => ρ (n + i)) X (d.tgts mm j i))

/-- At a member target the slot is the recursive slot of task #315 M2. -/
theorem slotAt_of_mem {ψ : Name → Nat} {X : Nat → V} {mm j i : Nat} {ρ : Nat → V}
    (h : d.tgts mm j i < d.k) :
    d.slotAt ψ X mm j i ρ
      = slotSet (d.w ψ) (d.uM (d.tgts mm j i) ψ) ρ (((d.tlss mm ψ).getD j []).getD i [])
          (((d.Eiss mm ψ).getD j []).getD i []) (X (d.tgts mm j i)) := by
  simp only [slotAt, famAt, uT, if_pos h]

/-- At a pin target the slot is the pin's carrier at the tuple. -/
theorem slotAt_of_pin {ψ : Name → Nat} {X : Nat → V} {mm j i : Nat} {ρ : Nat → V}
    (h : ¬ d.tgts mm j i < d.k) :
    d.slotAt ψ X mm j i ρ
      = slotSet (d.w ψ) ((d.pinAt (d.tgts mm j i - d.k)).u ψ) ρ
          (((d.tlss mm ψ).getD j []).getD i []) (((d.Eiss mm ψ).getD j []).getD i [])
          (d.pinCar ψ (fun n => ρ (n + i)) X (d.tgts mm j i - d.k)) := by
  simp only [slotAt, famAt, uT, if_neg h]

omit [SetTheory V] in
theorem nestOf_none {mm j i : Nat} (h : d.tgts mm j i < d.k) : d.nestOf mm j i = none := by
  simp only [nestOf, if_pos h]

omit [SetTheory V] in
theorem nestOf_some {mm j i : Nat} (h : ¬ d.tgts mm j i < d.k) :
    d.nestOf mm j i = some (d.tgts mm j i - d.k) := by
  simp only [nestOf, if_neg h]

end BlockModel

/-- **The fields fit**, from position `i` on, along the domain list
`Fs` (a suffix of the constructor's), each value in its entry at the
earlier values — a recursive position (`rs`) in its slot, an ordinary
one in its domain's reading: `SpineFit`'s shape, and `chainXIGo`'s
branching. -/
@[expose] def FitsFrom (rs : List Bool) (slot : Nat → (Nat → V) → V) :
    Nat → (Nat → V) → List AnnotTerm → List V → Prop
  | _, _, [], [] => True
  | i, ρ, F :: Fs, a :: as =>
    a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
    FitsFrom rs slot (i + 1) (cons a ρ) Fs as
  | _, _, _, _ => False

theorem FitsFrom.length_eq {rs : List Bool} {slot : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      FitsFrom rs slot i ρ Fs as → as.length = Fs.length
  | _, _, [], [], _ => rfl
  | _, _, [], _ :: _, h => h.elim
  | _, _, _ :: _, [], h => h.elim
  | _, _, _ :: Fs, _ :: as, h =>
    congrArg Nat.succ (FitsFrom.length_eq (Fs := Fs) (as := as) h.2)

/-- A fit reads its slots at the frames it visits only. -/
theorem FitsFrom.congr_slot {rs : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length →
        slot (i + l) (consList (as.take l) ρ) = slot' (i + l) (consList (as.take l) ρ)) →
      (FitsFrom rs slot i ρ Fs as ↔ FitsFrom rs slot' i ρ Fs as)
  | _, _, [], [], _ => Iff.rfl
  | _, _, [], _ :: _, _ => Iff.rfl
  | _, _, _ :: _, [], _ => Iff.rfl
  | i, ρ, F :: Fs, a :: as, hsl => by
    show (a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs as) ↔
      (a ∈ˢ (if rs.getD i false then slot' i ρ else interp V ρ F) ∧
        FitsFrom rs slot' (i + 1) (cons a ρ) Fs as)
    have h0 := hsl 0 (Nat.succ_pos _)
    simp only [List.take_zero, consList_nil, Nat.add_zero] at h0
    rw [h0]
    refine and_congr Iff.rfl (FitsFrom.congr_slot fun l hl => ?_)
    have := hsl (l + 1) (by simpa using hl)
    rw [show i + (l + 1) = i + 1 + l from by omega] at this
    simpa [List.take_succ_cons, consList_cons] using this

/-- A fit is monotone in the slots at its recursive positions. -/
theorem FitsFrom.mono {rs : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length → rs.getD (i + l) false = true → ∀ ρ', slot (i + l) ρ' ⊆ˢ slot' (i + l) ρ') →
      FitsFrom rs slot i ρ Fs as → FitsFrom rs slot' i ρ Fs as
  | _, _, [], [], _, hf => hf
  | _, _, [], _ :: _, _, hf => hf.elim
  | _, _, _ :: _, [], _, hf => hf.elim
  | i, ρ, F :: Fs, a :: as, h, hf => by
    obtain ⟨h1, h2⟩ := hf
    refine ⟨?_, FitsFrom.mono (fun l hl hr ρ' => ?_) h2⟩
    · by_cases hr : rs.getD i false = true
      · rw [if_pos hr] at h1 ⊢
        have := h 0 (Nat.succ_pos _) (by rw [Nat.add_zero]; exact hr) ρ
        rw [Nat.add_zero] at this
        exact this a h1
      · rw [if_neg hr] at h1 ⊢; exact h1
    · have := h (l + 1) (by simpa using hl)
        (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hr) ρ'
      rw [show i + (l + 1) = i + 1 + l from by omega] at this
      exact this

namespace BlockModel

variable (d : BlockModel V) (pc : Nat → PinCtors V)

/-- **A field spine fits member `mm`'s constructor `j` at the functor
frame `(ρp, X, t)`**: it fits the constructor's entries at `X`, and the
constructor's index expressions at it are the components of the tuple
`t` — the elimination shape of the fixpoint route's fibre
(`fixStepI_elim`), with the recursive slots at the target members. -/
@[expose] def ChainFit (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (t : V) (mm j : Nat)
    (fs : List V) : Prop :=
  FitsFrom ((d.rss mm).getD j []) (d.slotAt ψ X mm j) 0 ρp ((d.Fss mm ψ).getD j []) fs ∧
  ∀ l, l < (d.IdsM mm ψ).length →
    interp V (consList fs ρp) (((d.Ess mm ψ).getD j []).getD l default) = projS l t


/-! ### The class readers -/

/-- The number of classes. -/
@[expose] def kT : Nat := d.k + d.nPins

/-- A class's index count. -/
@[expose] def nIdxT (c : Nat) : Nat := if c < d.k then d.nIdxAt c else (d.pinAt (c - d.k)).nIdx

/-- A class's index telescope (the member's at the parameter frame;
the pin's container's, at the pin's frame). -/
@[expose] def IdsT (c : Nat) (ψ : Name → Nat) : List AnnotTerm :=
  if c < d.k then d.IdsM c ψ else (d.pinAt (c - d.k)).Ids ψ

/-- A class's frame at the parameter frame: the parameters for a
member, the pin's frame for a pin. -/
@[expose] noncomputable def frameT (c : Nat) (ψ : Name → Nat) (ρp : Nat → V) : Nat → V :=
  if c < d.k then ρp else d.pinFrame (c - d.k) ψ ρp

/-- **A class's index-tuple set**: the member's `idx`, the pin's `pinIdx`. -/
@[expose] noncomputable def idxT (ψ : Name → Nat) (ρp : Nat → V) (c : Nat) : V :=
  if c < d.k then d.idx ψ ρp c else d.pinIdx (c - d.k) ψ ρp

/-- A class's index spine as its tuple (at the class's sort `uT`). -/
@[expose] noncomputable def tupT (ψ : Name → Nat) (c : Nat) (is : List V) : V := tupW (d.uT c ψ) is

/-- A class's constructors. -/
@[expose] def ctorsT (c : Nat) : List (ConstantVal × Nat) :=
  if c < d.k then d.ctorsM c else (pc (c - d.k)).ctors

/-- A class's field domains, per constructor. -/
@[expose] def FssT (ψ : Name → Nat) (c : Nat) : List (List AnnotTerm) :=
  if c < d.k then d.Fss c ψ else (pc (c - d.k)).Fss ψ

/-- A class's recursive flags, per constructor. -/
@[expose] def rssT (c : Nat) : List (List Bool) := if c < d.k then d.rss c else (pc (c - d.k)).rss

/-- A class's targets, per constructor and field. -/
@[expose] def tgtsT (c : Nat) : Nat → Nat → Nat := if c < d.k then d.tgts c else (pc (c - d.k)).tgts

/-- A class's reflexive telescopes, per constructor. -/
@[expose] def tlssT (ψ : Name → Nat) (c : Nat) : List (List (List (Nat × Nat × AnnotTerm))) :=
  if c < d.k then d.tlss c ψ else (pc (c - d.k)).tlss ψ

/-- A class's recursive fields' index expressions, per constructor. -/
@[expose] def EissT (ψ : Name → Nat) (c : Nat) : List (List (List AnnotTerm)) :=
  if c < d.k then d.Eiss c ψ else (pc (c - d.k)).Eiss ψ

/-- A class's results' index readings, per constructor. -/
@[expose] def EssT (ψ : Name → Nat) (c : Nat) : List (List AnnotTerm) :=
  if c < d.k then d.Ess c ψ else (pc (c - d.k)).Ess ψ

/-- A class's injection. -/
@[expose] def injT (ψ : Name → Nat) (c : Nat) : Nat → List V → V :=
  if c < d.k then d.inj ψ c else (pc (c - d.k)).inj ψ


/-- Field `i'`'s telescope at a class. -/
@[expose] def teleAtT (ψ : Name → Nat) (c j i' : Nat) : List (Nat × Nat × AnnotTerm) :=
  ((d.tlssT pc ψ c).getD j []).getD i' []

/-- Field `i'`'s index expressions at a class. -/
@[expose] def eisAtT (ψ : Name → Nat) (c j i' : Nat) : List AnnotTerm :=
  ((d.EissT pc ψ c).getD j []).getD i' []

/-- **A recursive slot over an EXTENDED tuple** `Y` of `k + nPins`
families: field `i` of class `c`'s constructor `j` reads its target
class's family `Y (tgtsT c j i)` at the tuple of its index expressions
under its telescope. -/
@[expose] noncomputable def slotAtT (ψ : Name → Nat) (Y : Nat → V) (c j i : Nat) (ρ : Nat → V) : V :=
  slotSet (d.w ψ) (d.uT (d.tgtsT pc c j i) ψ) ρ (d.teleAtT pc ψ c j i) (d.eisAtT pc ψ c j i)
    (Y (d.tgtsT pc c j i))

/-- **A field spine fits class `c`'s constructor `j` at the extended
tuple `Y` and index tuple `t`** (`ChainFit`'s twin over the classes). -/
@[expose] def ChainFitT (ψ : Name → Nat) (ρp : Nat → V) (Y : Nat → V) (t : V) (c j : Nat)
    (fs : List V) : Prop :=
  FitsFrom ((d.rssT pc c).getD j []) (d.slotAtT pc ψ Y c j) 0 ρp ((d.FssT pc ψ c).getD j []) fs ∧
  ∀ l, l < (d.IdsT c ψ).length →
    interp V (consList fs ρp) (((d.EssT pc ψ c).getD j []).getD l default) = projS l t


/-! ### The class readers at a member -/

section Members

variable {d pc} {c : Nat} (hc : c < d.k)
include hc

omit [SetTheory V] in
theorem nIdxT_of_mem : d.nIdxT c = d.nIdxAt c := by simp only [nIdxT, if_pos hc]
omit [SetTheory V] in
theorem IdsT_of_mem (ψ : Name → Nat) : d.IdsT c ψ = d.IdsM c ψ := by simp only [IdsT, if_pos hc]
theorem frameT_of_mem (ψ : Name → Nat) (ρp : Nat → V) : d.frameT c ψ ρp = ρp := by
  simp only [frameT, if_pos hc]
theorem idxT_of_mem (ψ : Name → Nat) (ρp : Nat → V) : d.idxT ψ ρp c = d.idx ψ ρp c := by
  simp only [idxT, if_pos hc]
omit [SetTheory V] in
theorem uT_of_mem (ψ : Name → Nat) : d.uT c ψ = d.uM c ψ := by simp only [uT, if_pos hc]
theorem tupT_of_mem (ψ : Name → Nat) (is : List V) : d.tupT ψ c is = d.tup ψ c is := by
  simp only [tupT, tup, uT, if_pos hc]
omit [SetTheory V] in
theorem ctorsT_of_mem : d.ctorsT pc c = d.ctorsM c := by simp only [ctorsT, if_pos hc]
omit [SetTheory V] in
theorem FssT_of_mem (ψ : Name → Nat) : d.FssT pc ψ c = d.Fss c ψ := by simp only [FssT, if_pos hc]
omit [SetTheory V] in
theorem rssT_of_mem : d.rssT pc c = d.rss c := by simp only [rssT, if_pos hc]
omit [SetTheory V] in
theorem tgtsT_of_mem : d.tgtsT pc c = d.tgts c := by simp only [tgtsT, if_pos hc]
omit [SetTheory V] in
theorem tlssT_of_mem (ψ : Name → Nat) : d.tlssT pc ψ c = d.tlss c ψ := by
  simp only [tlssT, if_pos hc]
omit [SetTheory V] in
theorem EissT_of_mem (ψ : Name → Nat) : d.EissT pc ψ c = d.Eiss c ψ := by
  simp only [EissT, if_pos hc]
omit [SetTheory V] in
theorem EssT_of_mem (ψ : Name → Nat) : d.EssT pc ψ c = d.Ess c ψ := by simp only [EssT, if_pos hc]
omit [SetTheory V] in
theorem injT_of_mem (ψ : Name → Nat) : d.injT pc ψ c = d.inj ψ c := by simp only [injT, if_pos hc]

/-- A member's slot over the extended tuple at `X` is its slot at `X`,
at a frame whose parameter part is `ρp` (the pin's carrier is taken at
the slot's frame below the fields). -/
theorem slotAtT_of_mem (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (j i : Nat) {fs' : List V}
    (hlen : fs'.length = i) :
    d.slotAtT pc ψ (d.famAt ψ ρp X) c j i (consList fs' ρp) = d.slotAt ψ X c j i (consList fs' ρp) := by
  have hρ : (fun n => consList fs' ρp (n + i)) = ρp :=
    funext fun n => by rw [← hlen]; exact consList_apply_add fs' ρp n
  simp only [slotAtT, slotAt, teleAtT, eisAtT, tlssT, EissT, tgtsT, if_pos hc, hρ]

end Members

/-! ### The class readers at a pin -/

section Pins

variable {d pc} {c : Nat} (hc : ¬ c < d.k)
include hc

omit [SetTheory V] in
theorem nIdxT_of_pin : d.nIdxT c = (d.pinAt (c - d.k)).nIdx := by simp only [nIdxT, if_neg hc]
omit [SetTheory V] in
theorem IdsT_of_pin (ψ : Name → Nat) : d.IdsT c ψ = (d.pinAt (c - d.k)).Ids ψ := by
  simp only [IdsT, if_neg hc]
theorem frameT_of_pin (ψ : Name → Nat) (ρp : Nat → V) : d.frameT c ψ ρp = d.pinFrame (c - d.k) ψ ρp := by
  simp only [frameT, if_neg hc]
theorem idxT_of_pin (ψ : Name → Nat) (ρp : Nat → V) : d.idxT ψ ρp c = d.pinIdx (c - d.k) ψ ρp := by
  simp only [idxT, if_neg hc]
omit [SetTheory V] in
theorem uT_of_pin (ψ : Name → Nat) : d.uT c ψ = (d.pinAt (c - d.k)).u ψ := by
  simp only [uT, if_neg hc]
omit [SetTheory V] in
theorem ctorsT_of_pin : d.ctorsT pc c = (pc (c - d.k)).ctors := by simp only [ctorsT, if_neg hc]
omit [SetTheory V] in
theorem FssT_of_pin (ψ : Name → Nat) : d.FssT pc ψ c = (pc (c - d.k)).Fss ψ := by
  simp only [FssT, if_neg hc]
omit [SetTheory V] in
theorem rssT_of_pin : d.rssT pc c = (pc (c - d.k)).rss := by simp only [rssT, if_neg hc]
omit [SetTheory V] in
theorem tgtsT_of_pin : d.tgtsT pc c = (pc (c - d.k)).tgts := by simp only [tgtsT, if_neg hc]
omit [SetTheory V] in
theorem tlssT_of_pin (ψ : Name → Nat) : d.tlssT pc ψ c = (pc (c - d.k)).tlss ψ := by
  simp only [tlssT, if_neg hc]
omit [SetTheory V] in
theorem EissT_of_pin (ψ : Name → Nat) : d.EissT pc ψ c = (pc (c - d.k)).Eiss ψ := by
  simp only [EissT, if_neg hc]
omit [SetTheory V] in
theorem EssT_of_pin (ψ : Name → Nat) : d.EssT pc ψ c = (pc (c - d.k)).Ess ψ := by
  simp only [EssT, if_neg hc]
omit [SetTheory V] in
theorem injT_of_pin (ψ : Name → Nat) : d.injT pc ψ c = (pc (c - d.k)).inj ψ := by
  simp only [injT, if_neg hc]

end Pins

omit [SetTheory V] in
/-- The extended tuple at `X`, at a class: the member's component or
the pin's carrier. -/
theorem famAt_of_mem {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {c : Nat} (hc : c < d.k) :
    d.famAt ψ ρp X c = X c := by simp only [famAt, if_pos hc]

omit [SetTheory V] in
theorem famAt_of_pin {ψ : Name → Nat} {ρp : Nat → V} {X : Nat → V} {c : Nat} (hc : ¬ c < d.k) :
    d.famAt ψ ρp X c = d.pinCar ψ ρp X (c - d.k) := by simp only [famAt, if_neg hc]

/-- **`ChainFitT` at a PIN class, read off the pin's constructors**
(task #315 L-E, DESIGN §U.86): every reader is the pin's
(`rssT_of_pin` and friends), so the fit is the one
`copyTransfer_via` takes, at the pin's own lists. -/
theorem chainFitT_of_pin {d : BlockModel V} {pc : Nat → PinCtors V} {ψ : Name → Nat}
    {ρp : Nat → V} {Y : Nat → V} {t : V} {c j : Nat} {fs : List V} (hc : ¬ c < d.k) :
    d.ChainFitT pc ψ ρp Y t c j fs ↔
      (FitsFrom ((pc (c - d.k)).rss.getD j [])
          (fun i' ρ => slotSet (d.w ψ) (d.uT ((pc (c - d.k)).tgts j i') ψ) ρ
            ((((pc (c - d.k)).tlss ψ).getD j []).getD i' [])
            ((((pc (c - d.k)).Eiss ψ).getD j []).getD i' [])
            (Y ((pc (c - d.k)).tgts j i'))) 0 ρp (((pc (c - d.k)).Fss ψ).getD j []) fs ∧
        ∀ l, l < ((d.pinAt (c - d.k)).Ids ψ).length →
          interp V (consList fs ρp) ((((pc (c - d.k)).Ess ψ).getD j []).getD l default)
            = projS l t) := by
  unfold ChainFitT slotAtT teleAtT eisAtT
  simp only [rssT, FssT, tlssT, EissT, EssT, tgtsT, IdsT, if_neg hc]

/-! ### The narrow fit against the class fit -/

/-- A member's fit at `X` is a fit over the extended tuple at `X`. -/
theorem chainFitT_of_chainFit {d : BlockModel V} (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {ρp : Nat → V} {X : Nat → V} {t : V} {c j : Nat} (hc : c < d.k) {fs : List V}
    (hf : d.ChainFit ψ ρp X t c j fs) : d.ChainFitT pc ψ ρp (d.famAt ψ ρp X) t c j fs := by
  obtain ⟨hfit, hidx⟩ := hf
  refine ⟨?_, ?_⟩
  · rw [rssT_of_mem hc, FssT_of_mem hc]
    refine (FitsFrom.congr_slot (Fs := (d.Fss c ψ).getD j []) (fun l hl => ?_)).mpr hfit
    rw [Nat.zero_add]
    exact slotAtT_of_mem hc ψ ρp X j l
      (by rw [List.length_take, hfit.length_eq]; exact Nat.min_eq_left (Nat.le_of_lt hl))
  · rw [IdsT_of_mem hc, EssT_of_mem hc]
    exact hidx

/-- **At a MEMBER class the two fits are the same**: the class fit
over the extended tuple at `X` IS the member's fit at `X` (task #315,
Resolution 1) — what makes `fibre` the restriction of `auxFibre` to
the members, once the extended tuple is the pins' least one. -/
theorem chainFitT_iff_chainFit {d : BlockModel V} (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {ρp : Nat → V} {X : Nat → V} {t : V} {c j : Nat} (hc : c < d.k) {fs : List V} :
    d.ChainFitT pc ψ ρp (d.famAt ψ ρp X) t c j fs ↔ d.ChainFit ψ ρp X t c j fs := by
  refine ⟨fun hf => ⟨?_, ?_⟩, chainFitT_of_chainFit pc hc⟩
  · have hfit := hf.1
    rw [rssT_of_mem hc, FssT_of_mem hc] at hfit
    refine (FitsFrom.congr_slot (Fs := (d.Fss c ψ).getD j []) (fun l hl => ?_)).mp hfit
    rw [Nat.zero_add]
    exact slotAtT_of_mem hc ψ ρp X j l
      (by rw [List.length_take, hfit.length_eq]; exact Nat.min_eq_left (Nat.le_of_lt hl))
  · have hidx := hf.2
    rw [IdsT_of_mem hc, EssT_of_mem hc] at hidx
    exact hidx

/-- **The class fit reads its tuple at the targets only**. -/
theorem chainFitT_congr {d : BlockModel V} (pc : Nat → PinCtors V) {ψ : Name → Nat}
    {ρp : Nat → V} {Y Y' : Nat → V} {t : V} {c j : Nat} {fs : List V}
    (h : ∀ i, i < ((d.FssT pc ψ c).getD j []).length →
      Y (d.tgtsT pc c j i) = Y' (d.tgtsT pc c j i)) :
    d.ChainFitT pc ψ ρp Y t c j fs ↔ d.ChainFitT pc ψ ρp Y' t c j fs := by
  refine and_congr (FitsFrom.congr_slot fun l hl => ?_) Iff.rfl
  rw [Nat.zero_add]
  unfold slotAtT
  rw [h l hl]

end BlockModel

/-! ## The clause -/

/-- **The per-constructor facts of a block member's constructor** —
`FixCtorFactsAt`'s target-aware twin: the constructor is stored with
the block's level parameters and its type reads as the block model says, a
recursive field at the former of the member it targets. -/
@[expose] def BlockCtorFacts {env : Env} (m : EnvModel V env) (d : BlockModel V) (lps : List Name)
    (mm j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧
  cA.1.levelParams = lps ∧
  BlockCtorData m d.env₀ (d.memberName mm) (fun i => d.memberName (d.tgts mm j i))
    (fun i => d.nIdxAt (d.tgts mm j i)) (fun i => d.nestOf mm j i) d.pinAt
    lps cA.1 d.nP cA.2 (d.nIdxAt mm) d.resSort d.isProp d.large
    (d.idxF mm j) (d.dsF mm j) (d.esF mm j) (d.srcsF mm j) (d.ksF mm j) (d.fvsPF mm j)
    (d.xFvsF mm j) (d.xrestF mm j) (d.eissF mm j) (d.tssF mm j)

/-- **The representation of a stored inductive `T`**, member `mm` of
its block, with recursor `T.rec = .recInfo cvR mI rP rules`, at the
block model `d` (see the module docstring).  A single family is the instance
`k = 1`, `mm = 0`. -/
structure IsBlockModel (m : EnvModel V env) (T : Name) (cvT cvR : ConstantVal) (mI rP : Nat)
    (rules : List RecRule) (d : BlockModel V) (mm : Nat) : Prop where
  /-- `T` is a member of the block -/
  memberLt : mm < d.k
  /-- `T` is member `mm` -/
  member : d.memberName mm = T
  /-- the stored type is the telescope over the parameters and the
  member's own indices, ending in a sort EQUIVALENT to the block's
  result sort — the member's own declared sort, which official's
  cross-member check makes `isEquiv`, not equal, to the first
  member's (task #315 U-7, a recorded deviation without a consumer) -/
  strip : ∃ bs s, cvT.type.stripPis (d.nP + d.nIdxAt mm) = some (bs, .sort s) ∧
    ∀ ψ : Name → Nat, s.eval ψ = d.resSort.eval ψ
  /-- the `Prop` bit is the result sort's -/
  isProp : d.isProp = (Level.isEquiv d.resSort .zero == some true)
  /-- the recursor's major position: one motive per member, one minor
  per constructor OF THE BLOCK, the member's own indices -/
  mI : mI = d.nP + d.k + d.nCtors + d.nIdxAt mm
  /-- the recursor's rule prefix -/
  rP : rP = d.nP + d.k + d.nCtors
  /-- the recursor's rules, when it carries any, are the MEMBER's
  constructors in order (a rule-less entry — a block's recursor
  PROVISIONED before its rules are checked, official's order — claims
  the representation with this clause vacuous) -/
  rules : rules ≠ [] → rules.map (·.ctor) = (d.ctorsM mm).map (·.1.name)
  /-- the former's type reads as the member's telescope -/
  former : FormerData m cvT (d.nP + d.nIdxAt mm) d.resSort (d.ppsM mm)
  /-- every constructor OF THE BLOCK is stored and its type reads as
  the block model says, with the per-field target member -/
  ctors : ∀ mm' j cA, mm' < d.k → (d.ctorsM mm')[j]? = some cA →
    BlockCtorFacts m d cvT.levelParams mm' j cA
  /-- every member is a stored inductive — what licenses the
  constructors' readings to cross a fresh cons -/
  memsFound : ∀ mm', mm' < d.k →
    ∃ (cv : ConstantVal) (caps : IndCaps), env.find? (d.memberName mm') = some (.indInfo cv caps)
  /-- every pin's container is a stored inductive -/
  pinsFound : ∀ q, q < d.nPins →
    ∃ (cv : ConstantVal) (caps : IndCaps), env.find? (d.pinAt q).J = some (.indInfo cv caps)
  /-- every field's target is a member or a pin -/
  tgtsLt : ∀ mm' j i, mm' < d.k → j < (d.ctorsM mm').length → i < ((d.ksF mm' j).length) →
    d.tgts mm' j i < d.k + d.nPins
  /-- the residuals' index arguments resolve -/
  idxRes : ∀ mm' j cA, mm' < d.k → (d.ctorsM mm')[j]? = some cA →
    ∀ e ∈ d.idxF mm' j, e.constsResolve env = true
  /-- the index-tuple sorts read only the block's level parameters -/
  uParams : ∀ mm', mm' < d.k → ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ q ∈ cvT.levelParams, ψ₁ q = ψ₂ q) → d.uM mm' ψ₁ = d.uM mm' ψ₂
  /-- a constructor's parameter telescope is the former's, as a frame -/
  paramsIff : ∀ mm' j cA, mm' < d.k → (d.ctorsM mm')[j]? = some cA →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.dsF mm' j ψ).take d.nP).map (·.2.2)).reverse ρ
  /-- at every parameter frame every member's index telescope is graded -/
  idxOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ mm', mm' < d.k → IdxOk (d.uM mm' ψ) ρp (d.IdsM mm' ψ)
  /-- **`Φ` is a monotone tuple functor** on the tuple space over the
  members' index-tuple sets, mapping it into itself, with a closed
  tuple ((W) at tuples) -/
  functor : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    MonoTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) ∧
    MapsTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) ∧
    ∃ L, IsClosedTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) L
  /-- **the container functor**: component `mm'`'s fibre at `(X, t)` is
  the set of injections of the spines fitting one of member `mm'`'s
  constructors at `(X, t)` — a recursive field read at the component of
  the member it targets -/
  fibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → ∀ mm', mm' < d.k →
    ∀ t, t ∈ˢ d.idx ψ ρp mm' → ∀ x,
      x ∈ˢ app (d.Φ ψ ρp X mm') t ↔
        ∃ j fs, j < (d.ctorsM mm').length ∧ d.ChainFit ψ ρp X t mm' j fs ∧ x = d.inj ψ mm' j fs
  /-- the pins' readings are shaped: the container's telescope is in
  the Π regime (its bits nonzero), the components are its parameters,
  the telescope its parameters and indices -/
  pinShape : ∀ q, q < d.nPins → ∀ ψ : Name → Nat,
    (∀ d' ∈ (d.pinAt q).pps ((d.pinAt q).ψJ ψ), d'.2.1 ≠ 0) ∧
    ((d.pinAt q).Ds ψ).length = (d.pinAt q).nPJ ∧
    ((d.pinAt q).pps ((d.pinAt q).ψJ ψ)).length = (d.pinAt q).nPJ + (d.pinAt q).nIdx
  /-- **a pin's carrier is a family** over the pin's index-tuple set,
  at every tuple of the tuple space -/
  pinMem : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → ∀ q, q < d.nPins →
      d.pinCar ψ ρp X q ∈ˢ famSpace (d.w ψ) (d.pinIdx q ψ ρp)
  /-- **a pin's carrier is monotone in the tuple** — the container's
  map action at the pin (DESIGN §DR.1 (P), D-2b) -/
  pinMono : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X Y, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) Y →
      TupleLe d.k (d.idx ψ ρp) X Y → ∀ q, q < d.nPins →
      FamLe (d.pinIdx q ψ ρp) (d.pinCar ψ ρp X q) (d.pinCar ψ ρp Y q)
  /-- **the wide operator is a tuple functor at width `k + nPins`**:
  monotone, space-preserving and with a closed tuple on the tuple
  space over the members' index-tuple sets FOLLOWED BY the pin
  components' (`idx` at `k + q` is the copy's telescope) -/
  auxFunctor : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    MonoTuple (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) (d.Ψaux ψ ρp) ∧
    MapsTuple (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) (d.Ψaux ψ ρp) ∧
    ∃ L, IsClosedTuple (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) (d.Ψaux ψ ρp) L
  /-- **`Φ` is the wide operator composed**: the members' rows of
  `Ψaux` with the pins solved internally at the members' tuple -/
  auxCompose : ∀ (ψ : Name → Nat) (ρp : Nat → V),
    d.Φ ψ ρp = composeΦ (d.w ψ) d.k d.nPins (d.idx ψ ρp) (d.Ψaux ψ ρp)
  /-- **`pinCar` is the wide operator's pins' least tuple** at the
  members' tuple -/
  auxPinsCar : ∀ (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (q : Nat), q < d.nPins →
    d.pinCar ψ ρp X q = pinsCar (d.w ψ) d.k d.nPins (d.idx ψ ρp) (d.Ψaux ψ ρp) X q
  /-- **a pin component's index-tuple set IS the pin's** — the tuple
  space at position `k + q` is the one the pin's carrier lives in.
  Nothing in `pinMem`/`auxPinsCar` forces the two, and the wide
  operator's fibre at a pin class is stated at the pin's (task #315,
  Resolution 1) -/
  auxPinIdx : ∀ q, q < d.nPins → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    d.idx ψ ρp (d.k + q) = d.pinIdx q ψ ρp
  /-- **the wide operator's fibre, at every class**: at a tuple `Z` of
  the WIDE tuple space, component `c`'s fibre at `(Z, t)` is the set
  of injections of the spines fitting one of class `c`'s constructors
  — the members' as `fibre` says, a pin's the copy's (`pinCtors`) —
  with every recursive field read at its target's component of `Z`
  ITSELF (`ChainFitT`: no `famAt` and no `pinCar`, because at this
  width the pins ARE variables).  This is what `fibre` cannot say: it
  pins `Ψaux` down only at the extended tuples `(X, pinCar X)`, and a
  CONTAINER instance's copies are read at tuples that are not of that
  form -/
  auxFibre : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ Z, InTupleSpace (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) Z →
    ∀ c, c < d.k + d.nPins → ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
      x ∈ˢ app (d.Ψaux ψ ρp Z c) t ↔
        ∃ j fs, j < (d.ctorsT d.pinCtors c).length ∧
          d.ChainFitT d.pinCtors ψ ρp Z t c j fs ∧ x = d.injT d.pinCtors ψ c j fs
  /-- **a pin's leaf**: the container at the pin's components (read at
  fitting parameters) and fitting indices is the pin's carrier at the
  least tuple — the pin's stored reading IS `pinCar` at the carrier -/
  pinLeaf : ∀ q, q < d.nPins → ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (d.params ψ) as →
    SpineFit (d.pinFrame q ψ (consList as ρ)) ((d.pinAt q).Ids ψ) is →
    (((d.pinAt q).Ds ψ).map (interp V (consList as ρ)) ++ is).foldl app
        (interp V ρ (m.acval (d.pinAt q).J ((d.pinAt q).ψJ ψ)))
      = app (d.pinCar ψ (consList as ρ)
            (lfpTuple (d.w ψ) d.k (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) q)
          (tupW ((d.pinAt q).u ψ) is)
  /-- **the leaf**: the member's former at fitting parameters and its
  own indices is the least pre-fixed TUPLE's component `mm` at the
  index tuple -/
  leaf : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as is : List V),
    SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) (d.IdsM mm ψ) is →
    (as ++ is).foldl app (interp V ρ (m.acval T ψ))
      = app (lfpTuple (d.w ψ) d.k (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ)) mm)
          (d.tup ψ mm is)
  /-- **the constructors**: member `mm'`'s constructor `j` at fitting
  parameters and fields is its injection -/
  ctor : ∀ mm' j cA, mm' < d.k → (d.ctorsM mm')[j]? = some cA →
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (as fs : List V),
      SpineFit ρ (d.params ψ) as → SpineFit (consList as ρ) ((d.Fss mm' ψ).getD j []) fs →
      (as ++ fs).foldl app (interp V ρ (m.acval cA.1.name ψ)) = d.inj ψ mm' j fs
  /-- at a `Prop`-valued block every injection is the point -/
  mkZero : ∀ ψ : Name → Nat, d.w ψ = 0 → ∀ mm' j fs, d.inj ψ mm' j fs = pt
  /-- at a `Type`-valued block a member's injections are injective
  across its constructors and spines of the constructors' lengths -/
  mkInj : ∀ ψ : Name → Nat, d.w ψ ≠ 0 → ∀ mm', mm' < d.k → ∀ j fs j' fs',
    j < (d.ctorsM mm').length → j' < (d.ctorsM mm').length →
    fs.length = ((d.Fss mm' ψ).getD j []).length → fs'.length = ((d.Fss mm' ψ).getD j' []).length →
    d.inj ψ mm' j fs = d.inj ψ mm' j' fs' → j = j' ∧ fs = fs'

/-! ## Derived laws -/

/-- A fitting parameter spine satisfies the parameter telescope. -/
theorem BlockModel.satOfSpine (d : BlockModel V) {ψ : Name → Nat} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (d.params ψ) as) : Sat V (d.params ψ).reverse (consList as ρ) := by
  have := ConLeche.Model.sat_of_spineFit (Sat_nil V ρ) hsp
  simpa using this

/-- A member's own index spine lands, as a tuple, in its index-tuple
set. -/
theorem BlockModel.tupMem (d : BlockModel V) {ψ : Name → Nat} {ρp : Nat → V} {mm' : Nat}
    {is : List V} (hsp : SpineFit ρp (d.IdsM mm' ψ) is) : d.tup ψ mm' is ∈ˢ d.idx ψ ρp mm' :=
  tupW_mem (u := d.uM mm' ψ) hsp

omit [SetTheory V] in
/-- A member has one domain list per constructor. -/
theorem BlockModel.Fss_length (d : BlockModel V) (mm : Nat) (ψ : Name → Nat) :
    (d.Fss mm ψ).length = (d.ctorsM mm).length := by
  show (fssOfR _ _).length = _
  rw [fssOfR_length]
  show (fixCtorDataList _ _ _ _ _ _ _ _).length = _
  rw [fixCtorDataList_length]

/-- **`fibre` IS `auxFibre` restricted to the members** (task #315,
Resolution 1): at a member and at the EXTENDED tuple `(X, pinCar X)`
the wide fibre is the narrow one, because the class readers are the
members' there (`ctorsT_of_mem`, `injT_of_mem`) and the class fit over
the extended tuple IS the member's fit at `X`
(`chainFitT_iff_chainFit`).  What the narrow clause cannot do is the
converse: it says nothing at a tuple that is not extended, which is
where a CONTAINER instance's copies are read. -/
theorem BlockModel.fibre_of_auxFibre (d : BlockModel V)
    (hcomp : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      d.Φ ψ ρp = composeΦ (d.w ψ) d.k d.nPins (d.idx ψ ρp) (d.Ψaux ψ ρp))
    (hpins : ∀ (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (q : Nat), q < d.nPins →
      d.pinCar ψ ρp X q = pinsCar (d.w ψ) d.k d.nPins (d.idx ψ ρp) (d.Ψaux ψ ρp) X q)
    (htgt : ∀ c j i, c < d.k → j < (d.ctorsM c).length → d.tgts c j i < d.k + d.nPins)
    (haux : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ Z, InTupleSpace (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) Z →
      ∀ c, c < d.k + d.nPins → ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
        x ∈ˢ app (d.Ψaux ψ ρp Z c) t ↔
          ∃ j fs, j < (d.ctorsT d.pinCtors c).length ∧
            d.ChainFitT d.pinCtors ψ ρp Z t c j fs ∧ x = d.injT d.pinCtors ψ c j fs) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → ∀ c, c < d.k →
    ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
      x ∈ˢ app (d.Φ ψ ρp X c) t ↔
        ∃ j fs, j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs ∧ x = d.inj ψ c j fs := by
  intro ψ ρp hρp X hX c hc t ht x
  rw [hcomp, composeΦ_apply,
    haux ψ ρp hρp _ (extT_mem hX) c (by omega) t ht x,
    BlockModel.ctorsT_of_mem hc, BlockModel.injT_of_mem hc]
  refine exists_congr fun j => exists_congr fun fs => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  rw [← BlockModel.chainFitT_iff_chainFit d.pinCtors hc]
  refine BlockModel.chainFitT_congr d.pinCtors fun i hi => ?_
  rw [BlockModel.FssT_of_mem hc] at hi
  have hj : j < (d.ctorsM c).length := by
    rcases Nat.lt_or_ge j (d.ctorsM c).length with h' | h'
    · exact h'
    · exfalso
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [d.Fss_length c ψ]; exact h'), Option.getD_none,
        List.length_nil] at hi
      exact Nat.not_lt_zero i hi
  have hlt := htgt c j i hc hj
  rw [BlockModel.tgtsT_of_mem hc, extT_eq_famAt hlt]
  unfold BlockModel.famAt
  by_cases hk : d.tgts c j i < d.k
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, hpins ψ ρp X _ (by omega)]

/-- **`auxFibre` at a block with NO pins**, from `fibre`: the wide
operator is the narrow one (`hΨ`), every class is a member and every
target is one (`htgt`), so the class readers are the members' and the
class fit over the tuple IS the member's fit at it.  The six pin-less
routes (native, mutual, the four pinned basis blocks) discharge the
wide clause with this. -/
theorem BlockModel.auxFibre_of_noPins (d : BlockModel V) (hn : d.nPins = 0)
    (hΨ : ∀ (ψ : Name → Nat) (ρp : Nat → V), d.Ψaux ψ ρp = d.Φ ψ ρp)
    (htgt : ∀ c j i, c < d.k → j < (d.ctorsM c).length → d.tgts c j i < d.k)
    (hfib : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X, InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) X → ∀ c, c < d.k →
      ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
        x ∈ˢ app (d.Φ ψ ρp X c) t ↔
          ∃ j fs, j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs ∧ x = d.inj ψ c j fs) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ Z, InTupleSpace (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) Z →
    ∀ c, c < d.k + d.nPins → ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
      x ∈ˢ app (d.Ψaux ψ ρp Z c) t ↔
        ∃ j fs, j < (d.ctorsT d.pinCtors c).length ∧
          d.ChainFitT d.pinCtors ψ ρp Z t c j fs ∧ x = d.injT d.pinCtors ψ c j fs := by
  intro ψ ρp hρp Z hZ c hc t ht x
  rw [hn, Nat.add_zero] at hc hZ
  rw [hΨ, hfib ψ ρp hρp Z hZ c hc t ht x, BlockModel.ctorsT_of_mem hc,
    BlockModel.injT_of_mem hc]
  refine exists_congr fun j => exists_congr fun fs => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  rw [← BlockModel.chainFitT_iff_chainFit d.pinCtors hc]
  refine BlockModel.chainFitT_congr d.pinCtors fun i hi => ?_
  rw [BlockModel.FssT_of_mem hc] at hi
  have hj : j < (d.ctorsM c).length := by
    rcases Nat.lt_or_ge j (d.ctorsM c).length with h' | h'
    · exact h'
    · exfalso
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [d.Fss_length c ψ]; exact h'), Option.getD_none,
        List.length_nil] at hi
      exact Nat.not_lt_zero i hi
  rw [BlockModel.tgtsT_of_mem hc, d.famAt_of_mem (htgt c j i hc hj)]

/-- **The WIDE carrier is the EXTENDED narrow one**: the least tuple of
`Ψaux` at a class is the member's component of the block's carrier, or
the pin's carrier there (task #315, Resolution 1).  Bekić's nested form
at the members (`lfpTuple_composeΦ`) and the pins' fixed-point law
(`pinsCar_lfp`) at the pins, both through `auxCompose`/`auxPinsCar`.
This is the tuple the wide identification's BOUND is taken at: "below
the container's own carrier", stated over its classes. -/
theorem BlockModel.auxLfp_eq_famAt (d : BlockModel V) {ψ : Name → Nat} {ρp : Nat → V}
    (hmono : MonoTuple (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) (d.Ψaux ψ ρp))
    (hcl : ∃ L, IsClosedTuple (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) (d.Ψaux ψ ρp) L)
    (hcomp : d.Φ ψ ρp = composeΦ (d.w ψ) d.k d.nPins (d.idx ψ ρp) (d.Ψaux ψ ρp))
    (hpins : ∀ X q, q < d.nPins →
      d.pinCar ψ ρp X q = pinsCar (d.w ψ) d.k d.nPins (d.idx ψ ρp) (d.Ψaux ψ ρp) X q)
    {c : Nat} (hc : c < d.k + d.nPins) :
    lfpTuple (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) (d.Ψaux ψ ρp) c
      = d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c := by
  unfold BlockModel.famAt
  by_cases hk : c < d.k
  · rw [if_pos hk, hcomp, lfpTuple_composeΦ hmono hcl hk]
  · rw [if_neg hk, hpins _ _ (by omega), hcomp, pinsCar_lfp hmono hcl (by omega),
      Nat.add_sub_cancel' (Nat.le_of_not_lt hk)]

namespace IsBlockModel

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockModel V} {mm : Nat}
  (h : IsBlockModel m T cvT cvR mI rP rules d mm)
include h

/-- **TWO CLASSES WITH THE SAME READERS HAVE THE SAME ROW** (task #315,
Resolution 1, WIDE (f1) step 2): if two components of the WIDE operator
are read by the same index-tuple set, the same number of constructors,
the same class fit and the same injection, then the wide operator's rows
there are equal — at every tuple of the wide space.

This is the whole of "the wide operator factors through a collapse".
When the block being installed identifies two of a CONTAINER's classes
— its expansion mints one copy per distinct pin EXPRESSION, so two own
pins instantiated alike arrive at one copy — the identification's
fixpoint theory needs the container's operator to be constant on those
fibres (`FibreConst`), and `auxFibre` is what turns that into a
statement about the two classes' CONSTRUCTOR DATA, which is where the
run can meet it.  Nothing about `σ` or about pins enters here: it is the
fibre law of the stored wide operator, read off its own sealed fibre. -/
theorem row_congr {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp)
    {Z : Nat → V} (hZ : InTupleSpace (d.w ψ) (d.k + d.nPins) (d.idx ψ ρp) Z)
    {c c' : Nat} (hc : c < d.k + d.nPins) (hc' : c' < d.k + d.nPins)
    (hidx : d.idx ψ ρp c = d.idx ψ ρp c')
    (hcnt : (d.ctorsT d.pinCtors c).length = (d.ctorsT d.pinCtors c').length)
    (hfit : ∀ t j fs, d.ChainFitT d.pinCtors ψ ρp Z t c j fs
      ↔ d.ChainFitT d.pinCtors ψ ρp Z t c' j fs)
    (hinj : ∀ j fs, d.injT d.pinCtors ψ c j fs = d.injT d.pinCtors ψ c' j fs) :
    d.Ψaux ψ ρp Z c = d.Ψaux ψ ρp Z c' := by
  have hmaps := (h.auxFunctor ψ ρp hρp).2.1
  refine famSpace_ext (hmaps Z hZ c hc) (by rw [hidx]; exact hmaps Z hZ c' hc') fun t ht => ?_
  have ht' : t ∈ˢ d.idx ψ ρp c' := by rw [← hidx]; exact ht
  refine SetTheory.ext fun x => ?_
  rw [h.auxFibre ψ ρp hρp Z hZ c hc t ht x, h.auxFibre ψ ρp hρp Z hZ c' hc' t ht' x]
  constructor
  · rintro ⟨j, fs, hj, hF, rfl⟩
    exact ⟨j, fs, hcnt ▸ hj, (hfit t j fs).mp hF, hinj j fs⟩
  · rintro ⟨j, fs, hj, hF, rfl⟩
    exact ⟨j, fs, hcnt ▸ hj, (hfit t j fs).mpr hF, (hinj j fs).symm⟩

/-- The carrier's fixed-point equation at a member, fibrewise. -/
theorem carrier_app_eq {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp)
    {mm' : Nat} (hmm : mm' < d.k) {t : V} (ht : t ∈ˢ d.idx ψ ρp mm') :
    app (d.Φ ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) mm') t
      = app (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) mm') t := by
  obtain ⟨hmono, hmaps, hcl⟩ := h.functor ψ ρp hρp
  exact app_lfpTuple_eq hcl hmono hmaps hmm ht

/-- **The section view (Bekić)**: member `mm`'s leaf is the least
pre-fixed FAMILY of `Φ`'s section at `mm`, the other members held at
the block's carriers — the single-family block model shape. -/
theorem leaf_section {ψ : Name → Nat} {ρ : Nat → V} {as is : List V}
    (hsp : SpineFit ρ (d.params ψ) as) (hi : SpineFit (consList as ρ) (d.IdsM mm ψ) is) :
    (as ++ is).foldl app (interp V ρ (m.acval T ψ))
      = app (lfpFamSet (d.w ψ) (d.idx ψ (consList as ρ) mm)
          (secF (d.w ψ) (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
            (lfpTuple (d.w ψ) d.k (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) mm))
          (d.tup ψ mm is) := by
  obtain ⟨hmono, -, hcl⟩ := h.functor ψ (consList as ρ) (d.satOfSpine hsp)
  rw [h.leaf ψ ρ as is hsp hi, lfpTuple_eq_section hcl hmono h.memberLt]

/-- **The member view**: at every parameter frame, `Φ`'s section at
`mm` (the other members at the block's carriers) is a monotone,
space-preserving family functor with a closed family, its fibre at a
family `X` and tuple `t` is member `mm`'s constructor decomposition at
the tuple `L[mm := X]` — the other members read as CONSTANTS, the way
parameters enter — and member `mm`'s carrier is its least pre-fixed
family.  This is `IndRep`'s single-family `functor`/`fibre`/`leaf`
shape, DERIVED from the tuple's. -/
theorem ofMember {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) :
    let L := lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)
    let F := secF (d.w ψ) (d.idx ψ ρp) (d.Φ ψ ρp) L mm
    MonoFam (d.w ψ) (d.idx ψ ρp mm) F ∧
    MapsFam (d.w ψ) (d.idx ψ ρp mm) F ∧
    (∃ L', IsClosedFam (d.w ψ) (d.idx ψ ρp mm) F L') ∧
    (∀ X, X ∈ˢ famSpace (d.w ψ) (d.idx ψ ρp mm) → ∀ t, t ∈ˢ d.idx ψ ρp mm → ∀ x,
      x ∈ˢ app (app F X) t ↔
        ∃ j fs, j < (d.ctorsM mm).length ∧ d.ChainFit ψ ρp (updTuple L mm X) t mm j fs ∧
          x = d.inj ψ mm j fs) ∧
    L mm = lfpFamSet (d.w ψ) (d.idx ψ ρp mm) F := by
  intro L F
  obtain ⟨hmono, hmaps, hcl⟩ := h.functor ψ ρp hρp
  have hLmem := lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)
  refine ⟨secF_mono hmono hLmem h.memberLt, secF_maps hmaps hLmem h.memberLt,
    ⟨_, lfpTuple_closedFam_secF hcl hmono h.memberLt⟩, fun X hX t ht x => ?_,
    lfpTuple_eq_section hcl hmono h.memberLt⟩
  rw [app_secF hX]
  exact h.fibre ψ ρp hρp _ (inTupleSpace_updTuple hLmem hX) mm h.memberLt t ht x

end IsBlockModel

end ConLeche.Model
