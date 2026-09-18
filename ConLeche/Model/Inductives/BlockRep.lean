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

namespace BlockModel

variable (d : BlockModel V)

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

namespace IsBlockModel

variable {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
  {rules : List RecRule} {d : BlockModel V} {mm : Nat}
  (h : IsBlockModel m T cvT cvR mI rP rules d mm)
include h

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
