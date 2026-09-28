module

public import ConLeche.Model.Inductives.BlockRecData
public import ConLeche.Verify.Inductives.ClassGenRun
import ConLeche.Semantics.DeclRun
import ConLeche.Model.Capstone
import ConLeche.Model.Tiers
import ConLeche.Model.Rules.Recompose

public section

/-!
# The class check's recursors: from the GENERATED family to the STREAM's (G2)

The class check (`Kernel/Inductives/ClassCheck.lean`, check 6) GENERATES
the recursor family from the classes and compares it with the stream's by
`isDefEq`, after inferring both sides (R7):

* per recursor TYPE, `isDefEq fe.env 0 cvRi.type gtyA` at the
  constructors' environment (`classRecTyOk`);
* per RULE, `isDefEq feR.env 0 rhsA genA` at the rule-less recursors'
  environment, the STREAM's annotated rule `rhsA` being what the install
  stores (`classRuleOk`) — so the stored rule is DEFINITIONALLY, not
  syntactically, the generated one (CLASSCHECK/CHECKER's accepted
  superset).

The proof reads structure off the generated terms (G1) and moves it to
the stored ones here.  Three moves:

1. **Readings** (§1, `closedDefEq_read_eq`): two closed terms the
   verified checker inferred and found defeq read to the same value at
   every level valuation — the rules tier's defeq claim at the empty
   context.  Both the types and the rules.
2. **Rules** (§2, `blockRuleRhsOk_of_read_eq`): a stored rule enters the
   model only through its closed reading (`BlockRuleRhsOk`: the applied
   right-hand side's VALUE and its grading), so the generated rule's
   obligation transfers verbatim to any rule reading alike.
3. **Types** (§3, `spineFit_of_teleFit_readEq`): the stored TYPE enters the
   model through its SYNTACTIC telescope — the ι firing's premise is a
   `TeleFitPA` against the stored type's reading — while the family's
   structure is the generated telescope's (`mkPisAV rds concl`).  Equal
   readings of two Π-towers do NOT give equal domains in general (a
   `Prop`-valued Π forgets its domain; an empty Π forgets it too), but
   they do at nonzero binder bits and a NONEMPTY reading: a nonempty
   graph-regime product determines its domain (a member's graph) and its
   fibres (a member modified at one point).  Both hold where the ι law
   is consulted: at `ℓ ≠ 0` every bit of the recursor type is nonzero
   (`OneElimLevel`), and the family's leaf inhabits the type; at `ℓ = 0`
   the rule law's point arm needs no telescope.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. Two closed, inferred, defeq terms read alike -/

/-- **The defeq transfer at the empty context.**  `a` and `b` are
closed (`hasFvar = false`, no loose bound variable), the verified
checker inferred both at depth `0` and found them defeq: at every level
valuation both read, both readings are graded, and they are equal.  The
accepted-reads recipe (`acceptedReads_of`) gives the readings, the
inference claim their grading, and the defeq claim (`checkSoundAt`)
their equality — at the model of the environment the check ran in. -/
theorem closedDefEq_read_eq (hμ : μ.verifiedChecks = true) {env : Env}
    (mp : EnvModelM V μ env) {F : Nat} {a b ta tb : Expr}
    (hfa : a.hasFvar = false) (hba : a.looseBVarsBounded 0 = true)
    (hfb : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (hta : ConLeche.inferTypeCore μ env F 0 a = .ok ta)
    (htb : ConLeche.inferTypeCore μ env F 0 b = .ok tb)
    (hd : ConLeche.isDefEqCore μ env F 0 a b = .ok true) (ψ : Name → Nat) :
    ∃ aa ba : AnnotTerm,
      denoteMeta mp.base2.acval env ψ 0 a = some aa ∧
      denoteMeta mp.base2.acval env ψ 0 b = some ba ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ aa) ∧ (∀ ρ : Nat → V, WellDenotedV V ρ ba) ∧
      ∀ ρ : Nat → V, interp V ρ aa = interp V ρ ba := by
  have hwa : Expr.WScoped 0 a := Expr.WScoped.of_not_hasFvar hfa
  have hwb : Expr.WScoped 0 b := Expr.WScoped.of_not_hasFvar hfb
  have hnla : a.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hfa
  have hnlb : b.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hfb
  have hLa : Expr.LeavesBounded a := fun l hl => by
    rw [hnla] at hl; exact absurd hl (List.not_mem_nil)
  have hLb : Expr.LeavesBounded b := fun l hl => by
    rw [hnlb] at hl; exact absurd hl (List.not_mem_nil)
  have hin := Rules.RulesInputs.ofSem mp ψ
  obtain ⟨aa, haa⟩ := acceptedReads_of mp.base2 ψ hta hwa hba hLa
  obtain ⟨ba, hbaR⟩ := acceptedReads_of mp.base2 ψ htb hwb hbb hLb
  obtain ⟨-, -, hdq, ihi⟩ := Rules.checkSoundAt (V := V) hμ hin F
  obtain ⟨taa, htaa⟩ := inferReads_of hμ hin hta hwa hba hLa (CtxOk.nil hnla) haa
  obtain ⟨tba, htba⟩ := inferReads_of hμ hin htb hwb hbb hLb (CtxOk.nil hnlb) hbaR
  obtain ⟨hoka, -, -⟩ := ihi hta hwa hba hLa (CtxOk.nil hnla) haa htaa
  obtain ⟨hokb, -, -⟩ := ihi htb hwb hbb hLb (CtxOk.nil hnlb) hbaR htba
  refine ⟨aa, ba, haa, hbaR, fun ρ => hoka ρ (Sat_nil V ρ), fun ρ => hokb ρ (Sat_nil V ρ),
    fun ρ => ?_⟩
  exact hdq hd hwa hba hLa hwb hbb hLb (CtxOk.nil hnla) (CtxOk.nil hnlb) haa hbaR
    hoka hokb ρ (Sat_nil V ρ)

/-- **The same, across a level instantiation**: the readings at
`e.instantiateLevelParams ks us` are the readings at the substituted
valuation (`denoteMeta_instLevels`), so the transfer holds at every
instantiation of the checked terms' universe parameters — the form
`RecRuleLaw` reads a stored rule in. -/
theorem closedDefEq_read_eq_inst (hμ : μ.verifiedChecks = true) {env : Env}
    (mp : EnvModelM V μ env) {F : Nat} {a b ta tb : Expr}
    (hfa : a.hasFvar = false) (hba : a.looseBVarsBounded 0 = true)
    (hfb : b.hasFvar = false) (hbb : b.looseBVarsBounded 0 = true)
    (hta : ConLeche.inferTypeCore μ env F 0 a = .ok ta)
    (htb : ConLeche.inferTypeCore μ env F 0 b = .ok tb)
    (hd : ConLeche.isDefEqCore μ env F 0 a b = .ok true)
    (φ : Name → Nat) (ks : List Name) (us : List Level) :
    ∃ aa ba : AnnotTerm,
      denoteMeta mp.base2.acval env φ 0 (a.instantiateLevelParams ks us) = some aa ∧
      denoteMeta mp.base2.acval env φ 0 (b.instantiateLevelParams ks us) = some ba ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ aa) ∧ (∀ ρ : Nat → V, WellDenotedV V ρ ba) ∧
      ∀ ρ : Nat → V, interp V ρ aa = interp V ρ ba := by
  rw [denoteMeta_instLevels (acvalParamsAt_of_core mp.base2) φ,
    denoteMeta_instLevels (acvalParamsAt_of_core mp.base2) φ]
  exact closedDefEq_read_eq hμ mp hfa hba hfb hbb hta htb hd _

/-! ### At check 6's runs -/

/-- **G2 at a checked rule, at the run.**  `classRuleOk` passed: the
stored rule `rhsA` and the ANNOTATED generated rule `genA` read alike at
every level instantiation, in any model of the rule-less recursors'
environment the comparison ran in.  The generated rule's closedness is
the generator's (G1: `classGenRule` closes every variable it opens). -/
theorem classRuleOk_read_eq (hμ : μ.verifiedChecks = true) {F : Nat}
    {w : ConLeche.StructWalkers} {feT feR : ConLeche.FEnv} {cvR : ConstantVal}
    {pw : ConLeche.PropWhen} {n : Nat} {rhs gen rhsA : Expr}
    (h : ConLeche.classRuleOk (ConLeche.fueledOps μ F) w feT feR cvR pw n rhs gen = .ok rhsA)
    (hgf : gen.hasFvar = false) (hgb : gen.looseBVarsBounded 0 = true)
    (mpR : EnvModelM V μ feR.env) :
    ∃ genA : Expr, ConLeche.annotateCore μ feR.env F 0 gen = .ok genA ∧
      ∀ (φ : Name → Nat) (ks : List Name) (us : List Level),
      ∃ Ra Ga : AnnotTerm,
        denoteMeta mpR.base2.acval feR.env φ 0 (rhsA.instantiateLevelParams ks us) = some Ra ∧
        denoteMeta mpR.base2.acval feR.env φ 0 (genA.instantiateLevelParams ks us) = some Ga ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧ (∀ ρ : Nat → V, WellDenotedV V ρ Ga) ∧
        ∀ ρ : Nat → V, interp V ρ Ra = interp V ρ Ga := by
  obtain ⟨hlb, hfv, hann, -, ⟨t, hinf⟩, genA, tg, hgann, hginf, hdq⟩ :=
    ConLeche.classRuleOk_inv h
  obtain ⟨hrf, hrb⟩ := annotate_syntax hann hfv hlb
  obtain ⟨hGf, hGb⟩ := annotate_syntax hgann hgf hgb
  exact ⟨genA, hgann, fun φ ks us =>
    closedDefEq_read_eq_inst hμ mpR hrf hrb hGf hGb hinf hginf hdq φ ks us⟩

/-- **G2 at a checked recursor type, at the run.**  `classRecTyOk`
passed: the stored type (the checked constant's) and the ANNOTATED
generated type read alike at every level instantiation, in any model of
the constructors' environment.  The generated type's closedness is the
generator's (G1). -/
theorem classRecTyOk_read_eq (hμ : μ.verifiedChecks = true) {F : Nat}
    {fe : ConLeche.FEnv} {g : ConLeche.ClassGen} {k : Nat} {rc : ConLeche.RecShape}
    {rules : List ConLeche.RecRule} {c : Nat} {cvRi : ConstantVal}
    (h : ConLeche.classRecTyOk (ConLeche.fueledOps μ F) fe g k rc rules c = .ok cvRi)
    (hgen : ∀ gty, ConLeche.classGenRecTy g c = some gty →
      gty.hasFvar = false ∧ gty.looseBVarsBounded 0 = true)
    (mp : EnvModelM V μ fe.env) :
    ∃ gty gtyA : Expr, ConLeche.classGenRecTy g c = some gty ∧
      ConLeche.annotateCore μ fe.env F 0 gty = .ok gtyA ∧
      ∀ (φ : Name → Nat) (ks : List Name) (us : List Level),
      ∃ Ta Ga : AnnotTerm,
        denoteMeta mp.base2.acval fe.env φ 0 (cvRi.type.instantiateLevelParams ks us)
          = some Ta ∧
        denoteMeta mp.base2.acval fe.env φ 0 (gtyA.instantiateLevelParams ks us) = some Ga ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ta) ∧ (∀ ρ : Nat → V, WellDenotedV V ρ Ga) ∧
        ∀ ρ : Nat → V, interp V ρ Ta = interp V ρ Ga := by
  obtain ⟨hcv, gty, gtyA, s, u, hg, hgann, hginf, -, hdq⟩ := ConLeche.classRecTyOk_inv h
  obtain ⟨hlb, hfv, type, stype, u', hann, -, hinf, -, rfl⟩ := ConLeche.checkConstantValF_inv hcv
  obtain ⟨hrf, hrb⟩ := annotate_syntax hann hfv hlb
  obtain ⟨hgf, hgb⟩ := hgen gty hg
  obtain ⟨hGf, hGb⟩ := annotate_syntax hgann hgf hgb
  exact ⟨gty, gtyA, hg, hgann, fun φ ks us =>
    closedDefEq_read_eq_inst hμ mp hrf hrb hGf hGb hinf hginf hdq φ ks us⟩

/-! ## 2. The rules: a rule enters the model only through its reading -/

/-- An application spine's reading depends on its head only through
the head's reading. -/
theorem interp_mkAppN_congr {f g : AnnotTerm} {ρ : Nat → V}
    (h : interp V ρ f = interp V ρ g) (as : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as) = interp V ρ (AnnotTerm.mkAppN g as) := by
  rw [interp_mkAppN, interp_mkAppN, h]

/-- An application spine's grading depends on its head only through the
head's grading and reading. -/
theorem wellDenotedV_mkAppN_congr {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {f g : AnnotTerm},
      WellDenotedV V ρ g → interp V ρ f = interp V ρ g →
      WellDenotedV V ρ (AnnotTerm.mkAppN f as) → WellDenotedV V ρ (AnnotTerm.mkAppN g as)
  | [], _, _, hg, _, _ => hg
  | a :: as, f, g, hg, hfg, hf => by
    have happ : WellDenotedV V ρ (.app g a) := by
      have hfa : WellDenotedV V ρ (.app f a) := by
        -- the spine's head part is graded: peel the outer applications
        exact wellDenotedV_mkAppN_head as hf
      obtain ⟨⟨-, hwa, v, A, B, hmem, hA, hz⟩, ⟨-, hva⟩⟩ := hfa
      refine ⟨⟨hg.1, hwa, v, A, B, hfg ▸ hmem, hA, hz⟩, hg.2, hva⟩
    have hfg' : interp V ρ (.app f a) = interp V ρ (.app g a) := by
      simp only [interp_app, hfg]
    exact wellDenotedV_mkAppN_congr as happ hfg' hf
where
  /-- The head part of a graded spine is graded. -/
  wellDenotedV_mkAppN_head : ∀ (as : List AnnotTerm) {h : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN h as) → WellDenotedV V ρ h
    | [], _, hh => hh
    | a :: as, h, hh => by
      have h1 := wellDenotedV_mkAppN_head as (h := .app h a) hh
      exact ⟨h1.1.1, h1.2.1⟩

variable {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
  {envC : Env} {p : ConLeche.BlockParts}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
  {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
  {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
  {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}

/-- **G2 at a rule.**  `BlockRuleRhsOk` — the obligation a stored rule
owes the model (`blockRecRuleLaw_run`) — reads the rule's right-hand
side only through its closed reading.  So if the GENERATED rule `gen`
(in the stored rule's record: same constructor, field and parameter
counts, firing) meets it, every rule whose right-hand side reads alike,
and graded, meets it too.  The reading premise is what
`closedDefEq_read_eq_inst` delivers from check 6's `isDefEq`. -/
theorem blockRuleRhsOk_of_read_eq {leaf : (Name → Nat) → Nat → AnnotTerm}
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} {rl : ConLeche.RecRule}
    {gen : Expr}
    (hgen : BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
      (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0) leaf m₃ φ j i r { rl with rhs := gen })
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∃ Ra Ga : AnnotTerm,
        denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
          ((ConLeche.RecRule.rhs rl).instantiateLevelParams r.1.levelParams us) = some Ra ∧
        denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
          (gen.instantiateLevelParams r.1.levelParams us) = some Ga ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
        ∀ ρ : Nat → V, interp V ρ Ga = interp V ρ Ra) :
    BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
      (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0) leaf m₃ φ j i r rl := by
  intro us hus
  obtain ⟨Ga', hGa', -, hfire⟩ := hgen us hus
  obtain ⟨Ra, Ga, hRa, hGa, hokR, heq⟩ := hread us hus
  obtain rfl : Ga' = Ga := Option.some.inj (hGa'.symm.trans hGa)
  refine ⟨Ra, hRa, hokR, ?_⟩
  intro cvj cnP cnF hfind usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hN hidx hTVa
    hTVja hfitR hfitC
  obtain ⟨hdat, hok⟩ := hfire cvj cnP cnF hfind usj ρ xs ys TVa TVja restR restC hxl hyl husjl
    hψ hN hidx hTVa hTVja hfitR hfitC
  have happ := interp_mkAppN_congr (heq ρ)
  refine ⟨?_, fun hx hy => wellDenotedV_mkAppN_congr _ (hokR ρ) (heq ρ) (hok hx hy)⟩
  rcases hdat with hdat | ⟨hL, hR⟩
  · refine Or.inl fun a ha => ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := hdat a ha
    exact ⟨h1, h2, h3, h4, by rw [← h5, happ]⟩
  · exact Or.inr ⟨hL, by rw [← hR, happ]⟩

/-! ## 3. The types: a nonempty Π-reading determines its telescope -/

section Tele

/-- A graph determines its domain. -/
theorem graph_dom_eq {F : V → V} {A A' : V} (h : graph F A = graph F A') : A = A' := by
  refine ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have hm : kpair x (F x) ∈ˢ graph F A' := h ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp hm
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'
  · have hm : kpair x (F x) ∈ˢ graph F A := h.symm ▸ mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hp⟩ := mem_graph.mp hm
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx'

/-- **A nonempty graph-regime product determines its domain.** -/
theorem piSet_dom_eq {A A' f : V} {B B' : V → V} (hf : f ∈ˢ piSet A B)
    (heq : piSet A B = piSet A' B') : A = A' := by
  have hf' : f ∈ˢ piSet A' B' := heq ▸ hf
  exact graph_dom_eq ((eq_graph_app_of_mem_piSet hf).trans (eq_graph_app_of_mem_piSet hf').symm)

/-- **A nonempty graph-regime product determines its fibres** on its
domain: a member modified at one point is a member. -/
theorem piSet_fibre_sub {A A' f : V} {B B' : V → V} (hf : f ∈ˢ piSet A B)
    (heq : piSet A B = piSet A' B') {x : V} (hx : x ∈ˢ A) : B x ⊆ˢ B' x := by
  intro y hy
  classical
  let g : V → V := fun z => if z = x then y else app f z
  have hg : graph g A ∈ˢ piSet A B := graph_mem_piSet fun z hz => by
    by_cases hzx : z = x
    · subst hzx; simp only [g, if_pos rfl]; exact hy
    · simp only [g, if_neg hzx]; exact app_mem_of_mem_piSet hf hz
  have hg' : graph g A ∈ˢ piSet A' B' := heq ▸ hg
  have hxA' : x ∈ˢ A' := piSet_dom_eq hf heq ▸ hx
  have h := app_mem_of_mem_piSet hg' hxA'
  rw [app_graph hx] at h
  simpa [g] using h

theorem piSet_fibre_eq {A A' f : V} {B B' : V → V} (hf : f ∈ˢ piSet A B)
    (heq : piSet A B = piSet A' B') {x : V} (hx : x ∈ˢ A) : B x = B' x := by
  have hf' : f ∈ˢ piSet A' B' := heq ▸ hf
  have hx' : x ∈ˢ A' := piSet_dom_eq hf heq ▸ hx
  exact ext fun y => ⟨fun hy => piSet_fibre_sub hf heq hx y hy,
    fun hy => piSet_fibre_sub hf' heq.symm hx' y hy⟩

/-- **A telescope fit against one Π-tower is a spine fit against another
reading alike.**  `T` (the STORED type's reading) is fitted syntactically
by `zs` (`TeleFitPA`); the GENERATED telescope `ds` has nonzero bits
and reads, at its own frame `σ`, to the same NONEMPTY set.  Then the
readings of `zs` fit `ds`'s first `|zs|` domains, and what is left of
`T` reads as what is left of the tower. -/
theorem spineFit_of_teleFit_readEq {ρ : Nat → V} {T rest : AnnotTerm} {zs : List AnnotTerm}
    (hfit : TeleFitPA V ρ T zs rest) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {C : AnnotTerm} {σ : Nat → V},
      zs.length ≤ ds.length → (∀ d ∈ ds, d.2.1 ≠ 0) →
      interp V ρ T = interp V σ (mkPisAV ds C) → (∃ f, f ∈ˢ interp V ρ T) →
      SpineFit σ ((ds.take zs.length).map (·.2.2)) (zs.map (interp V ρ)) ∧
        interp V ρ rest
          = interp V (consList (zs.map (interp V ρ)) σ) (mkPisAV (ds.drop zs.length) C) := by
  induction hfit with
  | nil =>
    intro ds C σ _ _ heq _
    exact ⟨trivial, by simpa using heq⟩
  | @cons u v A B rest a as hmem htail ih =>
    intro ds C σ hlen hbits heq hne
    match ds, hlen, hbits, heq with
    | d :: ds', hlen, hbits, heq =>
      have hd : d.2.1 ≠ 0 := hbits d (.head _)
      obtain ⟨f, hf⟩ := hne
      simp only [mkPisAV, interp_pi] at heq hf
      rw [piR_pos hd] at heq
      -- the stored binder's bit is nonzero too: a truth value holds no graph
      have hv : v ≠ 0 := by
        rintro rfl
        have hf' : f ∈ˢ piSet _ _ := heq ▸ hf
        rw [piR_zero] at hf
        exact ne_pt_of_mem_piSet hf' (mem_truthVal.mp hf).2
      rw [piR_pos hv] at heq hf
      have hdom := piSet_dom_eq hf heq
      have hfib := piSet_fibre_eq hf heq hmem
      have hx : interp V ρ a ∈ˢ interp V σ d.2.2 := hdom ▸ hmem
      have heq' : interp V ρ (B.inst a)
          = interp V (cons (interp V ρ a) σ) (mkPisAV ds' C) := by
        rw [interp_inst0]; exact hfib
      have hne' : ∃ g, g ∈ˢ interp V ρ (B.inst a) :=
        ⟨app f (interp V ρ a), by rw [interp_inst0]; exact app_mem_of_mem_piSet hf hmem⟩
      obtain ⟨hsp, hrest⟩ := ih (ds := ds') (C := C) (σ := cons (interp V ρ a) σ)
        (by simp at hlen; omega) (fun d' hd' => hbits d' (.tail _ hd')) heq' hne'
      exact ⟨⟨hx, hsp⟩, by simpa using hrest⟩

end Tele

end ConLeche.Model
