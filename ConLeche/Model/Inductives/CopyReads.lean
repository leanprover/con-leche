module

public import ConLeche.Model.Inductives.CopyPins
public import ConLeche.Model.Inductives.DeclNested
public import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedLedger
import ConLeche.Verify.Inductives.NestedLeaves
public import ConLeche.Verify.Inductives.NestedMention
import ConLeche.Verify.Inductives.NestedProj
import ConLeche.Verify.Inductives.AuxFormers
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Leaves
import ConLeche.Verify.InstLevels
public section

/-!
# The copies' records, READ off the run (task #279 M-B′ step 3g / §M.24)

`CopyPins.lean` states the three records the copies owe (`PinRead`,
`CopyIdxRead`, `CopyCtorRead`) and discharges `InvSetup`'s copy-side
hypotheses from them; `pinRead_of` reads the first off the pin check,
and `copyIdxRead_of_align` reads the second off the ALIGNMENT of the
copy's stored former with the container's at the annotated pin.

Since K.12 the elimination runs on the ANNOTATED formers and
constructors, so every copy's type is MINTED as the container's stored
(annotated) former at the pin's own components, closed over the
block's first former's annotated binders, and the auxiliary install
stores it as it is (`nestedCopyFormerType_eq`: the grade keeps every
written datum).  The alignment the read consumes — the stored former
opened at the first former's openers IS the container's at the pin's
components — is therefore DERIVED here from the run's ledger
(`elimNested_copy`, `mkCopy_inv`) and the bvar-form round trip
(`openPisAtFvars_closeTelescope_strip`), generically in the container's
datum (any `FormerData` of the member at the scratch environment; the
run-level assembly `PsiRun.lean` supplies its `ContainersRep`); the pins'
free-variable leaves are the first former's openers (`PinsAtOpeners`),
which holds by construction of the elimination (every constructor is
opened at those openers and a pin is one of its sub-terms) and is READ
off the run (`pinsAtOpeners_of_run`, the leaf invariant of
`Verify/Inductives/NestedLeaves.lean`).  The pin check
(`nestedPinsOk`) infers the pin itself, so nothing is annotated on the
way (`pinRead_of` takes the pin's guards and its inference).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember AuxType BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-- The sort transfer of `CopyIdxRead` across the block's re-sorting. -/
theorem CopyIdxRead.congr_sort {d : IndRepData V} {s s' : Level}
    (hs : ∀ φ : Name → Nat, s.eval φ = s'.eval φ)
    {ψ : Name → Nat} {t : Nat} {dJ : IndRepData V} {ψ' : Name → Nat} {mmJ : Nat}
    {DsA : List AnnotTerm}
    (h : ({d with resSort := s} : IndRepData V).CopyIdxRead ψ t dJ ψ' mmJ DsA) :
    ({d with resSort := s'} : IndRepData V).CopyIdxRead ψ t dJ ψ' mmJ DsA :=
  ⟨by
    have h1 : dJ.w ψ' = s.eval ψ := h.sort
    show dJ.w ψ' = s'.eval ψ
    rw [← hs ψ]; exact h1, h.nIdx, h.idxIff⟩

/-- **`PinRead` and `CopyIdxRead` for a copy member, from the run's
facts**: the copy's representation in the scratch block, the block's
opened parameter context, the container's member at the scratch
environment, the pin's guards at the openers and its check, and the
ALIGNMENT (the stored former opened at the openers is the container's
at the pin's components — K.12's construction). -/
theorem copyIdxRead_of_copy {μ : CheckMode} (hμ : μ.verifiedChecks = true) {envAux : Env}
    {mpAux : EnvModelM V μ envAux} {b : MutualBlock} {d : IndRepData V}
    (hreps : MutualBlockReps mpAux.base2 b d) {ψ : Name → Nat}
    -- the copy: member `t` of the scratch block, at the pin `J.{lvls} Ds`
    {t : Nat} (ht : t < b.k) {Jn : Name} {lvls : List Level} {Ds : List Expr}
    {cvT : ConstantVal} {capsT : IndCaps}
    (hfT : envAux.find? (d.memberName t) = some (.indInfo cvT capsT))
    -- the block's parameter context: the first member's former opened at the openers
    {fvsA : List Expr} {cvT₀ : ConstantVal} {oA : Expr} {R : AnnotTerm}
    (hopened : Opened mpAux.base2 ψ d.nP cvT₀.type fvsA oA (d.params ψ).reverse R)
    -- the container's member at the scratch environment
    {cvTJ : ConstantVal} {capsJ : IndCaps} (hfJ : envAux.find? Jn = some (.indInfo cvTJ capsJ))
    (hlvls : lvls.length = cvTJ.levelParams.length)
    {dJ : IndRepData V} {mmJ : Nat}
    (hFDJ : FormerData mpAux.base2 cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ))
    (hDsLen : Ds.length = dJ.nP)
    -- the pin's guards at the openers, and its check at the scratch environment
    (hws : Expr.WScoped d.nP (Expr.mkAppN (.const Jn lvls) Ds))
    (hb : (Expr.mkAppN (.const Jn lvls) Ds).looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ (Expr.mkAppN (.const Jn lvls) Ds).fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsA)
    {ty : Expr} {F₁ : Nat}
    (hpinInf : ConLeche.inferTypeCore μ envAux F₁ d.nP (Expr.mkAppN (.const Jn lvls) Ds) = .ok ty)
    -- THE ALIGNMENT, at the pin's components
    (halign : ∃ rest, ConLeche.openPisAtFvars d.nP cvT.type 0 = some (fvsA, rest) ∧
      Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) Ds = some rest) :
    ∃ (s : Level) (DsA : List AnnotTerm), (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
      DenoteMetaSpine mpAux.base2.acval envAux ψ d.nP Ds DsA ∧
      ({d with resSort := s} : IndRepData V).PinRead ψ
        (mpAux.base2.acval Jn (Level.substFn ψ cvTJ.levelParams lvls)) DsA Ds.length ∧
      ({d with resSort := s} : IndRepData V).CopyIdxRead ψ t dJ
        (Level.substFn ψ cvTJ.levelParams lvls) mmJ DsA := by
  -- the copy's own representation and former
  obtain ⟨-, hkb, hkRb, -, -, -, -, hall⟩ := hreps
  obtain ⟨s, cvT', cvR, caps', mI, rP, rules, hfT', -, -, hsv, hrep⟩ := hall t ht
  obtain ⟨h1, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hfT))
  have h2 := h1.symm
  subst h2
  have hFD : FormerData mpAux.base2 cvT
      (({d with resSort := s} : IndRepData V).nP + ({d with resSort := s} : IndRepData V).nIdxAt t)
      ({d with resSort := s} : IndRepData V).resSort
      (({d with resSort := s} : IndRepData V).ppsM t) (({d with resSort := s} : IndRepData V).lvlsM t) :=
    hrep.formersRead t (by show t < d.kReal; rw [hkRb]; exact ht) cvT capsT hfT
  -- the pin, read
  obtain ⟨DsA, hargs, hsp, hlenD, hpin⟩ :=
    IndRepData.pinRead_of ({d with resSort := s} : IndRepData V) hμ hopened hfJ hlvls hws hb hleaf
      hpinInf
  -- the former, aligned
  obtain ⟨rest, hopen, hrest⟩ := halign
  refine ⟨s, DsA, hsv, hsp, hpin, ?_⟩
  exact IndRepData.copyIdxRead_of_align ({d with resSort := s} : IndRepData V) mpAux hFD hfJ hFDJ
    rfl hDsLen hargs hsp hopen hrest

/-! ## The premise, as the run's consumer states it -/

/-- **The pins carry the block's parameter variables** (K.12: the
elimination opens every constructor at the first former's openers and
the pins are its own sub-terms): every free-variable leaf of a pin is
one of the openers `params`, annotation included.  Proved of the run by
`Verify/Inductives/NestedLeaves.lean` (`elimNested_leaves`, the leaf
invariant beside the ledger) — `pinsAtOpeners_of_run` below. -/
@[expose] def PinsAtOpeners (st : ElimState) (params : List Expr) : Prop :=
  ∀ q ∈ st.pins, ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ params

/-- **The pins mention only pre-block constants and the block's own
REAL members** (task #308, DESIGN §M.48): the block's parameter
openers carry annotations that resolve before the block, and every
pin's components mention only constants the pre-block environment
carries or the block's own members — never a COPY.  Proved of the run
by `Verify/Inductives/NestedMention.lean`
(`elimNested_pinsMentionOnly`, the instance of the elimination's
mention invariant) — `pinsMentionReal_of_run` below. -/
@[expose] def PinsMentionReal (env : Env) (st : ConLeche.ElimState) (params : List Expr)
    (k : Nat) : Prop :=
  (∀ x ∈ params, Expr.MentionsOnly (fun n => (env.find? n).isSome = true) x) ∧
  ∀ q ∈ st.pins, Expr.MentionsOnly
    (fun n => (env.find? n).isSome = true ∨ n ∈ (st.types.map (·.name)).take k) q.pin

/-- **The mention invariant, from the run**: the containers resolve in
`env` (`EnvWF`), the block's own annotated formers and constructors
resolve at their own environments (`checkConstantVal`'s front door),
and `elimNested_mentionInv` carries the invariant to the pins. -/
theorem pinsMentionReal_of_run {μ : CheckMode} {F : Nat} {env : Env} {p : ConLeche.NestedParts}
    {fmsA ctorsA : List ConstantVal} {st : ConLeche.ElimState} {t₀ : AuxType}
    {params : List Expr} {body : Expr} (mp : EnvModelM V μ env)
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (hannC : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (ht₀ : (ConLeche.nestedTypes0 p fmsA ctorsA).head? = some t₀)
    (hop : ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body))
    (hk : fmsA.length = p.k) :
    PinsMentionReal env st params p.k := by
  obtain ⟨hres, hpins⟩ :=
    ConLeche.elimNested_pinsMentionOnly mp.base2.wf hannF hannC helim
  have hres₀ : t₀.type.constsResolve env = true := hres t₀ (by rw [ht₀]; exact rfl)
  refine ⟨(ConLeche.openPisAtFvars_mentionsOnly p.nP hop
    (Expr.mentionsOnly_of_constsResolve hres₀)).1, fun q hq => ?_⟩
  -- the real members' names are the elimination's first `p.k` type names
  have hnames : (st.types.map (·.name)).take p.k = fmsA.map (·.name) := by
    rw [ConLeche.elimNested_names helim, ConLeche.nestedTypes0_names,
      List.take_left' (by rw [List.length_map]; exact hk)]
  rw [hnames]
  exact hpins q hq

/-- **The pins' leaves are the openers, from the run**: the containers'
stored types are closed under the model's `EnvWF`, the block's own
annotated types are closed, and `elimNested_leaves` carries the leaf
invariant through the elimination. -/
theorem pinsAtOpeners_of_run {μ : CheckMode} {F : Nat} {env : Env} {p : ConLeche.NestedParts}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} {t₀ : AuxType} {params : List Expr}
    {body : Expr} (mp : EnvModelM V μ env)
    (hannC : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (ht₀ : (ConLeche.nestedTypes0 p fmsA ctorsA).head? = some t₀)
    (hnf₀ : t₀.type.hasFvar = false)
    (hop : ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body)) :
    PinsAtOpeners st params := by
  have hcc : ConLeche.ContainersClosed env := ConLeche.containersClosed_of_wf mp.base2.wf
  have hty : ∀ t ∈ ConLeche.nestedTypes0 p fmsA ctorsA, ∀ c ∈ t.ctors,
      c.2.1.hasFvar = false := by
    intro t ht c hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
    rw [nestedTypes0_getElem?] at hi
    obtain ⟨cvT, -, rfl⟩ := Option.map_eq_some_iff.mp hi
    simp only at hc
    obtain ⟨⟨c₀, cvCa⟩, hmem, hf⟩ := List.mem_filterMap.mp hc
    simp only at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.of_mem_zip hmem).2
      obtain ⟨c', -, hcheck⟩ := (ConLeche.nestedAnnotCtors_inv hannC).2 j cvCa hj
      exact (ConLeche.checkConstantVal_typeWF hcheck).1
    · exact nomatch hf
  have ht₀' : ∀ t₀' ∈ (ConLeche.nestedTypes0 p fmsA ctorsA).head?, t₀'.type.hasFvar = false := by
    intro t₀' h'
    rw [ht₀] at h'
    obtain rfl := Option.mem_some_iff.mp h'
    exact hnf₀
  obtain ⟨t₀'', params'', body'', ht₀'', hop'', hleaves⟩ :=
    ConLeche.elimNested_leaves hcc helim hty ht₀'
  rw [ht₀] at ht₀''
  obtain rfl := Option.some.inj ht₀''
  rw [hop] at hop''
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hop'')
  exact fun q hq l hl => hleaves q hq l hl

/-! ## The pins carry no projection node at a fresh name's slot (task #309) -/

omit [SetTheory V] in
/-- Consing the ANNOTATED formers changes no projection lookup: a
former's name is not projection-function-shaped, so none of the consed
constants is a projection table. -/
theorem findProj?_nestedFormerEnv {T : Name} {i : Nat} {fmsA : List ConstantVal} {env : Env}
    (h : ∀ cv ∈ fmsA, cv.name.isProjFnShape = false) :
    (ConLeche.nestedFormerEnv fmsA env).findProj? T i = env.findProj? T i := by
  have hfind : (ConLeche.nestedFormerEnv fmsA env).find? (ConLeche.projTableName T)
      = env.find? (ConLeche.projTableName T) := by
    refine ConLeche.Semantics.find?_append_of_new_none (new := (fmsA.map
      fun cv => ConstantInfo.indInfo cv {}).reverse) rfl ?_
    rw [List.find?_eq_none]
    intro c hc hbeq
    rw [List.mem_reverse, List.mem_map] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc
    have hn : cv.name = ConLeche.projTableName T := beq_iff_eq.mp hbeq
    have h1 := h cv hcv
    have h2 : (ConLeche.projTableName T).isProjFnShape = true := rfl
    rw [hn, h2] at h1
    exact Bool.noConfusion h1
  unfold ConLeche.Env.findProj?
  rw [hfind]

/-- **The pins carry no projection node at a slot of a name fresh
before the block** (task #309): the elimination's inputs are the
ANNOTATED formers and constructors (K.12), whose `.proj` nodes are
table-backed at the formers' environment — where a fresh name's slot is
still empty (`annotateCore_noProjAt`) — the first former's type
resolves before the block (`FormerFront.resolve`), and the invariant
travels through the elimination (`elimNested_pins_noProjAt`). -/
theorem pinsNoProj_of_run {μ : CheckMode} {F : Nat} {env : Env} {p : ConLeche.NestedParts}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} (mp : EnvModelM V μ env)
    (hannF : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p.nP
      p.formers = .ok fmsA)
    (hannC : ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st) :
    ∀ q ∈ st.pins, ∀ (T : Name) (i : Nat), env.find? T = none → Expr.NoProjAt T i q.pin := by
  intro q hq T i hT
  have hslot : env.findProj? T i = none := findProj?_none_of_indFresh mp.base2.proj_ok hT i
  have hpshape : ∀ cv ∈ fmsA, cv.name.isProjFnShape = false := by
    intro cv hcv
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcv
    obtain ⟨cv₀, nIdx, -, hff⟩ := (ConLeche.nestedAnnotFormers_inv hannF).2 t cv ht
    rw [hff.name]; exact hff.pshape
  have hslotF : (ConLeche.nestedFormerEnv fmsA env).findProj? T i = none := by
    rw [findProj?_nestedFormerEnv hpshape]; exact hslot
  refine ConLeche.elimNested_pins_noProjAt mp.base2.wf hT hslot helim ?_ ?_ q hq
  · -- the block's ANNOTATED constructors: `.proj` nodes are table-backed
    intro t ht c hc
    obtain ⟨t', ht'⟩ := List.getElem?_of_mem ht
    rw [nestedTypes0_getElem?] at ht'
    obtain ⟨cvT, -, rfl⟩ := Option.map_eq_some_iff.mp ht'
    simp only at hc
    obtain ⟨⟨c₀, cvCa⟩, hmem, hf⟩ := List.mem_filterMap.mp hc
    simp only at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      obtain ⟨j, hj⟩ := List.getElem?_of_mem (List.of_mem_zip hmem).2
      obtain ⟨c', -, hcheck⟩ := (ConLeche.nestedAnnotCtors_inv hannC).2 j cvCa hj
      obtain ⟨-, -, -, -, -, hnfv, ty, -, -, hann, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hcheck
      show Expr.NoProjAt T i cvCa.type
      rw [hty]
      exact ConLeche.annotateCore_noProjAt μ hann hnfv hslotF
    · exact nomatch hf
  · -- the first ANNOTATED former: its type resolves before the block
    intro t₀ h0
    have h0' : (ConLeche.nestedTypes0 p fmsA ctorsA)[0]? = some t₀ := by
      rw [← List.head?_eq_getElem?]; exact Option.mem_def.mp h0
    rw [nestedTypes0_getElem?] at h0'
    obtain ⟨cvT, hcvT, hEq⟩ := Option.map_eq_some_iff.mp h0'
    obtain ⟨cv₀, nIdx, -, hff⟩ := (ConLeche.nestedAnnotFormers_inv hannF).2 0 cvT hcvT
    rw [← hEq]
    exact ConLeche.Expr.noProjAt_of_constsResolve hT _ hff.resolve

/-- A leaf of the head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN_head : ∀ (args : List Expr) (f : Expr) (l : Nat × Expr),
    l ∈ f.fvarLeaves → l ∈ (Expr.mkAppN f args).fvarLeaves
  | [], _, _, hl => hl
  | a :: args, f, l, hl => by
    show l ∈ (Expr.mkAppN (.app f a) args).fvarLeaves
    refine mem_fvarLeaves_mkAppN_head args (.app f a) l ?_
    simp only [Expr.fvarLeaves, List.mem_append]
    exact Or.inl hl

/-- A leaf of a spine argument is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN_arg :
    ∀ (args : List Expr) (f : Expr) {a : Expr}, a ∈ args → ∀ l ∈ a.fvarLeaves,
      l ∈ (Expr.mkAppN f args).fvarLeaves
  | [], _, _, ha, _, _ => nomatch ha
  | a₀ :: args, f, a, ha, l, hl => by
    show l ∈ (Expr.mkAppN (.app f a₀) args).fvarLeaves
    rcases List.mem_cons.mp ha with rfl | ha
    · refine mem_fvarLeaves_mkAppN_head args (.app f a) l ?_
      simp only [Expr.fvarLeaves, List.mem_append]
      exact Or.inr hl
    · exact mem_fvarLeaves_mkAppN_arg args (.app f a₀) ha l hl

/-! ## Every copy of the scratch block, read off the run -/

/-- A member's name in the auxiliary block is its former's. -/
theorem memberNames_getD {b : MutualBlock} {t : Nat} {cv : ConstantVal} {nIdx : Nat}
    (h : b.formers[t]? = some (cv, nIdx)) : b.memberNames.getD t .anonymous = cv.name := by
  unfold MutualBlock.memberNames
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

set_option maxHeartbeats 1600000 in
/-- **`PinRead` and `CopyIdxRead` for EVERY copy of the scratch block,
from the run** (K.12), under the containers' representation at the
scratch environment and the pins' leaves (`PinsAtOpeners`): for pin `j`
the copy member `p.k + j` has its pin `J.{lvls} Ds` read at the block's
parameter frame and its index telescope the container's at the pin's
readings.  The copy's stored former is the minted one
(`nestedCopyFormerType_eq`, `auxFormers_stored`), the minted one is the
container's stored type instantiated at the pin's components closed
over the first former's binders (`mkCopy_inv`), and the bvar-form round
trip (`openPisAtFvars_closeTelescope_strip`) re-opens it at the
openers. -/
theorem copyIdxRead_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ConLeche.ElimState) (b : MutualBlock) (envAux : Env) (params : List Expr)
      (pbs : List (Expr × BinderMeta)) (fmsA ctorsA : List ConstantVal)
      (stored : List ConLeche.AuxStored) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st ∧
      ConLeche.nestedTopoOrder (ConLeche.ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      -- the copies' names are fresh before the block and the pins are
      -- structurally distinct at their containers (K.15) — run facts the
      -- constructor read consumes (task #279 M-B′ step 3p)
      ConLeche.copiesFresh env p.k st = true ∧
      ConLeche.nestedContainersOk env st.pins = true ∧
      -- the auxiliary install, the stored records, K.3's `pinsClosed`,
      -- K.20's formers and K.17's witness — what the walk's facts are
      -- read from (task #279 M-D′ step (1), DESIGN §M.46)
      ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none true
        = .ok envAux ∧
      ConLeche.auxStoredAll envAux b b.k = some stored ∧
      ConLeche.pinsClosed p.nP st.pins = true ∧
      (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true ∧
      -- K.23's record (DESIGN §M.47): the group exclusion, as the kernel decided it
      ConLeche.nestedGroupExclusionOk env envAux p st = true ∧
      ConLeche.nestedCtorsWhnfOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
        (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.nP
        (ConLeche.nestedCtorPairs b stored) = .ok () ∧
      PinsAtOpeners st params ∧
      PinsMentionReal env st params p.k ∧
      (∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
        ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
        t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧
        t₀.type.hasFvar = false) ∧
      -- the block's RECURSOR names (task #309): fresh before the block —
      -- what the formers' model of `env₁` is built from
      -- (`nestedFormersModel`) — and unreserved, which is what says the
      -- scratch install introduces no reserved name
      (∀ t, t < b.k → env.find? (b.recName t) = none ∧
        ConLeche.reservedBasisNames.contains (b.recName t) = false) ∧
      -- the pins carry no projection node at a slot of a name fresh
      -- before the block (task #309, `pinsNoProj_of_run`)
      (∀ q ∈ st.pins, ∀ (T : Name) (i : Nat), env.find? T = none →
        Expr.NoProjAt T i q.pin) ∧
      -- the annotated inputs and the restore stages at these witnesses
      -- (task #279 M-D′, DESIGN §M.52): what D3–D7 read the restored
      -- constructors, recursors and rules from
      DeclNestedRestore μ F env p st b envAux stored fmsA ctorsA envOut ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧ AuxBlockAgree F mp mpAux b true d ∧
        ∀ (j : Nat), j < st.pins.length →
          ∃ (q : ConLeche.NestedPin) (I : Name) (ci : ConLeche.ContainerInfo) (i j₀ : Nat)
            (J : ContainerMember) (lvls : List Level) (Ds : List Expr),
            st.pins[j]? = some q ∧ ConLeche.containerInfo? env I = some ci ∧
            ci.members[i]? = some J ∧ j = j₀ + i ∧
            (∀ i' J', ci.members[i']? = some J' →
              ∃ q', st.pins[j₀ + i']? = some q' ∧ q'.container = J'.name ∧
                q'.pin = Expr.mkAppN (.const J'.name lvls) Ds ∧
                q'.grpBase = j₀ ∧ q'.grpSize = ci.members.length) ∧
            q.container = J.name ∧ q.pin = Expr.mkAppN (.const J.name lvls) Ds ∧
            q.grpBase = j₀ ∧ q.grpSize = ci.members.length ∧
            Ds.length = ci.nP ∧ lvls.length = J.lps.length ∧
            ConLeche.CopyCtorsStored μ F env p st b params pbs j J lvls Ds q ∧
            ∀ (ψ : Name → Nat) (cvTJ : ConstantVal) (capsJ : IndCaps) (dJ : IndRepData V)
              (mmJ : Nat),
              envAux.find? J.name = some (.indInfo cvTJ capsJ) → J.type = cvTJ.type →
              J.lps = cvTJ.levelParams → ci.nP = dJ.nP →
              FormerData mpAux.base2 cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ)
                (dJ.lvlsM mmJ) →
              ∃ (s : Level) (DsA : List AnnotTerm),
                (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
                (∀ a ∈ Ds, Expr.WScoped p.nP a ∧ a.looseBVarsBounded 0 = true) ∧
                DenoteMetaSpine mpAux.base2.acval envAux ψ p.nP Ds DsA ∧
                ({d with resSort := s} : IndRepData V).PinRead ψ
                  (mpAux.base2.acval J.name (Level.substFn ψ cvTJ.levelParams lvls)) DsA Ds.length ∧
                ({d with resSort := s} : IndRepData V).CopyIdxRead ψ (p.k + j) dJ
                  (Level.substFn ψ cvTJ.levelParams lvls) mmJ DsA := by
  obtain ⟨h0, h1, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA, ctorsA, order,
    hannF, hannC, helim, hnum, hfresh, hcont, hord, hb, hcore, hstored, hpc, hpinsAux, hK20, hK23,
    hK17, hctorsR, hrm, hrn, hrulesM, hrulesN, htbl, hpost, hlenR, hrecs⟩ := h
  obtain ⟨mpAux, d, hreps, hchk, hag⟩ :=
    nestedAuxModel hμ mp hE hannF helim hfresh hb hcore hstored hrm
  -- the elimination's opening
  obtain ⟨t₀, params, body, pbs, body₀, ht₀, hop, hstrip, hpbs, htypes⟩ :=
    ConLeche.elimNested_open helim
  have hfmsLen : fmsA.length = p.k := (ConLeche.nestedAnnotFormers_inv hannF).1
  have hlen0 : 0 < (ConLeche.nestedTypes0 p fmsA ctorsA).length := by
    cases hh : ConLeche.nestedTypes0 p fmsA ctorsA with
    | nil => rw [hh] at ht₀; exact nomatch ht₀
    | cons _ _ => simp
  have hkpos : 0 < p.k := by rw [nestedTypes0_length, hfmsLen] at hlen0; exact hlen0
  -- the block's shape
  obtain ⟨hbnP, -, -, -, -, hbformers, -⟩ := ConLeche.auxBlock_inv hb
  have hk : b.k = st.types.length := ConLeche.auxBlock_k hb
  have hlenSt : st.types.length = p.k + st.pins.length := by
    have := ConLeche.elimNested_length helim
    rw [nestedTypes0_length, hfmsLen] at this
    exact this
  have hreps₀ := hreps
  obtain ⟨hctorsC, hkb, hkRb, hnP, -, -, hnames, hall⟩ := hreps
  have hdnP : d.nP = p.nP := by rw [hnP, hbnP]
  have hk0 : 0 < b.k := by rw [hk, hlenSt]; omega
  -- the first entry keeps the first annotated former's type
  obtain ⟨tS0, htS0⟩ : ∃ tS0, st.types[0]? = some tS0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenSt]; omega)⟩
  have htS0ty : tS0.type = t₀.type := by
    have h1 := htypes 0 hlen0
    rw [htS0, ← List.head?_eq_getElem?, ht₀] at h1
    exact Option.some.inj h1
  -- the stored formers are the checked ones
  have hrun : DeclMutualCoreRun μ F env b none true envAux := declMutualCoreRun_of hcore
  have hfacts := nestedRecNameFacts hannF helim hfresh hb hcore hstored hrm
  obtain ⟨fms, hformers, hkF, hposF, hstoredF⟩ :=
    auxFormers_stored hrun (fun t ht => (hfacts t ht).1)
  -- a stored former is the checked one at its entry
  have hstoredTy : ∀ (i : Nat) (tS : AuxType), i < b.k → st.types[i]? = some tS →
      ∀ (cvT : ConstantVal) (capsT : IndCaps),
        envAux.find? (d.memberName i) = some (.indInfo cvT capsT) →
        cvT.type = tS.type ∧ cvT.type.hasFvar = false ∧ cvT.type.looseBVarsBounded 0 = true := by
    intro i tS hi htS cvT capsT hfT
    obtain ⟨nIdx, -, hform⟩ := hbformers i tS htS
    obtain ⟨env₁, fms', f, hformers', -, hf, hfty⟩ :=
      ConLeche.nestedCopyFormerType_eq hb hcore i tS htS
    rw [hformers] at hformers'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hformers')
    obtain ⟨cv', bs, hl, hff, -⟩ := hposF i f hf
    rw [hform] at hl
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl)
    have hname : d.memberName i = tS.name := by rw [hnames _ hi, memberNames_getD hform]
    have hn' : f.cvTa.name = d.memberName i := by rw [hname]; exact hff.name
    have hfindT := hstoredF f (List.mem_of_getElem? hf)
    rw [hn'] at hfindT
    obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT.symm.trans hfindT))
    exact ⟨hfty, hff.noFvar, hff.bounded⟩
  -- the first member: its stored former, opened at the openers
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, hfT₀, -, -, -, hrep₀⟩ := hall 0 hk0
  obtain ⟨hty₀eq, hnf₀, hb₀⟩ := hstoredTy 0 tS0 hk0 htS0 cvT₀ caps₀ hfT₀
  have hnf₀' : t₀.type.hasFvar = false := by rw [← htS0ty, ← hty₀eq]; exact hnf₀
  have hFD₀ : FormerData mpAux.base2 cvT₀
      (({d with resSort := s₀} : IndRepData V).nP + ({d with resSort := s₀} : IndRepData V).nIdxAt 0)
      ({d with resSort := s₀} : IndRepData V).resSort
      (({d with resSort := s₀} : IndRepData V).ppsM 0) (({d with resSort := s₀} : IndRepData V).lvlsM 0) :=
    hrep₀.formersRead 0 (by show 0 < d.kReal; rw [hkRb]; exact hk0) cvT₀ caps₀ hfT₀
  have hfv' : ConLeche.openPisAtFvars ({d with resSort := s₀} : IndRepData V).nP cvT₀.type 0
      = some (params, body) := by
    show ConLeche.openPisAtFvars d.nP cvT₀.type 0 = some (params, body)
    rw [hdnP, hty₀eq, htS0ty]; exact hop
  -- the openers' facts
  obtain ⟨bs₀S, body₀S, -, -, hshape₀, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis p.nP hop
  have hlenP : params.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hop
  have hvar₀ : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    have hi : i < p.nP := by rw [← hlenP]; exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨ty, hty⟩ := hshape₀ i hi
    rw [hx] at hty
    exact ⟨ty, by rw [Nat.zero_add] at hty; exact Option.some.inj hty⟩
  obtain ⟨hwsF₀', -⟩ := ConLeche.openPisAtFvars_WScoped p.nP t₀.type 0 hop
    (Expr.WScoped.of_not_hasFvar hnf₀')
  have hwsF₀ : ∀ x ∈ params, Expr.WScoped p.nP x := by
    intro x hx
    have h := hwsF₀' x hx
    rwa [Nat.zero_add] at h
  obtain ⟨hbsNF, -⟩ := ConLeche.stripPis_not_hasFvar p.nP hstrip hnf₀'
  have hpo : PinsAtOpeners st params := pinsAtOpeners_of_run mp hannC helim ht₀ hnf₀' hop
  have hmo : PinsMentionReal env st params p.k :=
    pinsMentionReal_of_run mp hannF hannC helim ht₀ hop hfmsLen
  refine ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, helim, hord, hlenSt, hfresh,
    hcont, hcore, hstored, hpc, hK20, hK23, hK17, hpo, hmo,
    ⟨tS0, body, body₀, htS0, by rw [htS0ty]; exact hop, by rw [htS0ty]; exact hstrip, hpbs,
      by rw [htS0ty]; exact hnf₀'⟩,
    fun t ht => ⟨(nestedRecNameFacts hannF helim hfresh hb hcore hstored hrm t ht).1,
      (nestedRecNameFacts hannF helim hfresh hb hcore hstored hrm t ht).2.1⟩,
    pinsNoProj_of_run mp hannF hannC helim,
    ⟨h0, h1, hannF, hannC, hnum, hpinsAux, ctorsR, cvRms, cvRns, rulesM, rulesN, hctorsR, hrm, hrn,
      hrulesM, hrulesN, htbl, hpost, hlenR, hrecs⟩,
    mpAux, d, hreps₀, hchk, hag, ?_⟩
  intro j hj
  -- the copy's origin
  obtain ⟨t₀', params', body', pbs', body₀', ht₀', hop', hstrip', I, ci, i, j₀, J, lvls, Ds, q,
    copy, st₁, st₂, cs', hci, hJ, hjE, hgrp, hq, hqc, hqp, hqb, hqs, hmk, hDs, -, -, hDsLen, hty,
    helimC, hst₁, hst₂, hpi, hlt₁, -⟩ := ConLeche.elimNested_copy helim hj
  rw [ht₀] at ht₀'
  obtain rfl := Option.some.inj ht₀'
  rw [hop] at hop'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hop')
  rw [hstrip] at hstrip'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hstrip')
  rw [nestedTypes0_length, hfmsLen] at hty hpi hlt₁
  have ht : p.k + j < b.k := by rw [hk, hlenSt]; omega
  obtain ⟨hlvls, ⟨tyI, htyI, hcopyTy⟩, -, -⟩ := ConLeche.mkCopy_inv hmk
  refine ⟨q, I, ci, i, j₀, J, lvls, Ds, hq, hci, hJ, hjE, hgrp, hqc, hqp, hqb, hqs, hDsLen, hlvls,
    ConLeche.copyCtorsStored_of (mode := μ) hpbs hmk hty helimC hst₁ hst₂ hlt₁ hpi hb hcore, ?_⟩
  intro ψ cvTJ capsJ dJ mmJ hfJ hJtype hJlps hciNP hFDJ
  obtain ⟨R, hopened⟩ := IndRepData.opened_params ({d with resSort := s₀} : IndRepData V) ψ hfT₀
    hFD₀ hfv'
  -- the copy's stored former is the minted one
  obtain ⟨s, cvT, cvR, capsT, mI, rP, rules, hfT, -, -, hsv, hrep⟩ := hall (p.k + j) ht
  obtain ⟨hcvT, -, -⟩ := hstoredTy (p.k + j) _ ht hty cvT capsT hfT
  have hcvT' : cvT.type = copy.type := hcvT
  -- the container at the scratch environment
  have hlvls' : lvls.length = cvTJ.levelParams.length := by rw [← hJlps]; exact hlvls
  have hwfJ := mpAux.base2.wf _ (Env.find?_mem hfJ)
  have hJnf : J.type.hasFvar = false := by rw [hJtype]; exact hwfJ.1
  have hJb : J.type.looseBVarsBounded 0 = true := by rw [hJtype]; exact hwfJ.2.2.2.1
  -- the pin's guards at the openers, and its check
  have hqmem : q ∈ st.pins := List.mem_of_getElem? hq
  have hleafQ : ∀ l ∈ q.pin.fvarLeaves, Expr.fvar l.1 l.2 ∈ params := hpo q hqmem
  rw [hqp] at hleafQ
  have hws : Expr.WScoped p.nP (Expr.mkAppN (.const J.name lvls) Ds) :=
    ConLeche.WScoped_of_leaves hwsF₀ _ hleafQ
  have hbQ : (Expr.mkAppN (.const J.name lvls) Ds).looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_mkAppN rfl hDs
  obtain ⟨ty, hpinInf⟩ := ConLeche.nestedPinsOk_inv hpinsAux q hqmem
  rw [hqp] at hpinInf
  -- the round trip: the minted type re-opens to the openers and `tyI`
  obtain ⟨ds, hAt⟩ := instPisAt_of_instPis Ds htyI
  have hJbL : (J.type.instantiateLevelParams J.lps lvls).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hJb
  have hJnfL : (J.type.instantiateLevelParams J.lps lvls).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hJnf
  obtain ⟨-, htyIb⟩ := ConLeche.Verify.instPisAt_bounded Ds hAt hJbL hDs
  have hcons : ∀ x ∈ params, ∀ (idx : Nat) (ty : Expr), x = .fvar idx ty →
      Expr.fvarConsistent idx ty tyI := by
    intro x hx idx ty hxe
    subst hxe
    refine ConLeche.fvarConsistent_of_leaves tyI fun l hl hidx => ?_
    rcases ConLeche.Verify.instPisAt_leaves Ds hAt l (Or.inr hl) with hl' | ⟨a, ha, hl'⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hJnfL] at hl'; exact nomatch hl'
    · have hmem : Expr.fvar l.1 l.2 ∈ params :=
        hleafQ l (mem_fvarLeaves_mkAppN_arg Ds _ ha l hl')
      rw [hidx] at hmem
      have h1 := ConLeche.openers_mem_eq hvar₀ hmem
      have h2 := ConLeche.openers_mem_eq hvar₀ hx
      rw [h1] at h2
      exact (Expr.fvar.inj (Option.some.inj h2)).2
  have hround := ConLeche.openPisAtFvars_closeTelescope_strip p.nP hstrip hop
    (fun b' hb' => Expr.WScoped.of_not_hasFvar (hbsNF b' hb')) htyIb hcons
  have halign : ∃ rest, ConLeche.openPisAtFvars d.nP cvT.type 0 = some (params, rest) ∧
      Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) Ds = some rest :=
    ⟨tyI, by rw [hdnP, hcvT', hcopyTy]; exact hround, by rw [← hJtype, ← hJlps]; exact htyI⟩
  -- the read
  have hopened' : Opened mpAux.base2 ψ d.nP cvT₀.type params body (d.params ψ).reverse R :=
    hopened
  obtain ⟨s', DsA, hsv', hsp, hpin, hidx⟩ := copyIdxRead_of_copy hμ hreps₀ (ψ := ψ) ht hfT
    hopened' hfJ hlvls' hFDJ (by rw [hDsLen, hciNP]) (by rw [hdnP]; exact hws) hbQ hleafQ
    (by rw [hdnP]; exact hpinInf) halign
  rw [hdnP] at hsp
  -- the components' guards (K.3's `pinsClosed`, per component: what
  -- makes the readings `bvarsBelow p.nP`, `DenoteMetaSpine.bvarsBelow`)
  have hargs : ∀ a ∈ Ds, Expr.WScoped p.nP a ∧ a.looseBVarsBounded 0 = true := fun a ha =>
    ⟨(ConLeche.WScoped_mkAppN_args hws).2 a ha, (ConLeche.looseBVarsBounded_mkAppN_args hbQ).2 a ha⟩
  exact ⟨s', DsA, hsv', hargs, hsp, hpin, hidx⟩

end ConLeche.Model
