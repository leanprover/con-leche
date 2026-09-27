module

public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Inductives.BlockHoleValid
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Model.IndDomGrade
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockData
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Annot.BitRename
public section

/-!
# The fields with holes are GRADED at the hole frame

Charter item 2: the block's operator is the interpretation of its
constructors' fields with holes.  For that operator to be a term the
members' formers can be built over (`LfpDatum.holeChains`, the leaf
`blockTyG` at them), the fields with holes must be graded at the
model's hole frame of EVERY tuple of the tuple space — not only at the
carrier's own family, which is all a stored reading reaches.  Both
halves come from U2 (`checkAbsCtorTys`, the install's positivity
stage), never from a field classification:

* **grading and bit validity**: U2 inferred the member-abstracted
  constructor type at the holes' context, so its reading — the Π-tower
  over the fields with holes, ending in the component's hole at the
  parameters and the result indices (`blockCtorHoleCtx`) — is graded
  there; the hole frame satisfies that context at every tuple;
* **the universe bound**: U2 checks every field's universe against the
  family's AT THE HOLES' CONTEXT (official's per-field bound, the
  members variables; `checkStructFieldSortsI`), so at a `Type`-valued
  family each field's reading lies in the family's universe
  (`teleBound_walk`).  The inference of the whole tower alone cannot
  give this: a Π-type with an empty codomain lies in every universe,
  whatever its domain.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestState
  BlockParts BlockShape instPisWith nestAbstract nestHoles openPisAtFvars fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Hereditary facts from per-prefix ones -/

/-- A field list is hereditarily graded (`FieldsOkB`) when each field
is graded, and bounded at a nonzero universe, at every fitting prefix. -/
theorem fieldsOkB_of_prefix {w : Nat} :
    ∀ (Fs : List AnnotTerm) (σ : Nat → V),
      (∀ i, i < Fs.length → ∀ as : List V, SpineFit σ (Fs.take i) as →
        WellDenoted V (consList as σ) (Fs.getD i default) ∧
        (w ≠ 0 → interp V (consList as σ) (Fs.getD i default) ∈ˢ (univ w : V))) →
      FieldsOkB w σ Fs
  | [], _, _ => trivial
  | F :: Fs, σ, h => by
    have h0 := h 0 (by simp) [] trivial
    refine ⟨h0.1, h0.2, fun a ha => fieldsOkB_of_prefix Fs (cons a σ) fun i hi as has => ?_⟩
    exact h (i + 1) (by simp; omega) (a :: as) ⟨ha, has⟩

/-- A field list is hereditarily bit-valid when each field is, at every
fitting prefix. -/
theorem fieldsValid_of_prefix :
    ∀ (Fs : List AnnotTerm) (σ : Nat → V),
      (∀ i, i < Fs.length → ∀ as : List V, SpineFit σ (Fs.take i) as →
        AnnotValid V (consList as σ) (Fs.getD i default)) →
      FieldsValid σ Fs
  | [], _, _ => trivial
  | F :: Fs, σ, h => by
    refine ⟨h 0 (by simp) [] trivial, fun a ha => fieldsValid_of_prefix Fs (cons a σ)
      fun i hi as has => ?_⟩
    exact h (i + 1) (by simp; omega) (a :: as) ⟨ha, has⟩

/-- A graded Π-tower's body is graded under all its binders. -/
theorem gradedV_mkPisAV_body :
    ∀ {ab : List (Nat × Nat × AnnotTerm)} {Δa : List AnnotTerm} {B : AnnotTerm},
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (mkPisAV ab B)) →
      ∀ ρ : Nat → V, Sat V ((ab.map (·.2.2)).reverse ++ Δa) ρ → WellDenotedV V ρ B
  | [], _, _, h, ρ, hρ => h ρ (by simpa using hρ)
  | _ :: _, _, _, h, ρ, hρ =>
    gradedV_mkPisAV_body (Rules.WellDenotedV.hoist_pi (V := V) h).2 ρ
      (by simpa [List.reverse_cons, List.append_assoc] using hρ)

/-! ## One constructor -/

/-- **A member constructor's fields with holes are graded at the hole
frame of every tuple of the tuple space** (see the module docstring):
hereditarily graded and — at a `Type`-valued family — bounded in the
family's universe, bit-valid, and the result index readings graded under
every fitting field spine.  From U2's run at the formers' environment. -/
theorem blockCtorHoleGrade_of_walk {env : Env} (mp : EnvModelM V .verified env)
    {ψ : Name → Nat} {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hres : p.resSort = d.resSort)
    (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    {tyN : Expr} {ksD : List ConLeche.PosKind} {ts : List ConLeche.PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
      cA.2 crest ksD tyN ts)
    (hnf : d.nfFF c j = tyN)
    {xq : List Expr × Expr} {sorts : List Level}
    (hxq : openPisAtFvars cA.2 tyN ((p.nestCtx fvsP env.find? env.consts).hiAt 0) = some xq)
    (hsorts : ConLeche.checkStructFieldSortsI (fueledOps .verified F) env
      (Level.isEquiv p.resSort .zero == some true) false p.resSort
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) xq.1 [] cA.2 = .ok sorts) :
    (FieldsBelow (d.nP + d.k) (d.absF ψ c j) ∧
      ∀ e ∈ d.absE ψ c j, Term.bvarsBelow (d.nP + d.k + (d.absF ψ c j).length) e.erase) ∧
    ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X : Nat → V, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
    FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
    FieldsValid (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
    ∀ fs : List V, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
      ∀ e ∈ d.absE ψ c j, WellDenotedV V (consList fs (d.toLfp.frame ψ ρp X)) e := by
  obtain ⟨-, ab, hhi, -, hca, hab, -, habLen, -, -, -, hfr, hCP, hgr, -, hsatFrame⟩ :=
    blockCtorHoleCtx (Rules.RulesInputs.ofSem mp ψ) hN hcore hnames hlps hnP hnIdxs hk
      hcv0 hop0 hholes hcj hCf hCb hcrest hinf hd hnf
  -- the bounds: the reading of a well-scoped term
  have hbelow : FieldsBelow (d.nP + d.k) (d.absF ψ c j) ∧
      ∀ e ∈ d.absE ψ c j, Term.bvarsBelow (d.nP + d.k + (d.absF ψ c j).length) e.erase := by
    obtain ⟨hdoms, hbody⟩ := bvarsBelow_mkPisAV_inv (bvarsBelow_of_reading hfr.1 hfr.2.1 hca)
    have hlen : (d.absF ψ c j).length = ab.length := by rw [← hab, List.length_map]
    refine ⟨by rw [← hab]; exact hdoms.fields, fun e he => ?_⟩
    rw [hlen]
    rw [AnnotTerm.erase_mkAppN] at hbody
    exact (bvarsBelow_mkAppN_inv hbody).2 _
      (List.mem_map.mpr ⟨e, List.mem_append_right _ he, rfl⟩)
  refine ⟨hbelow, fun ρp hs X hX => ?_⟩
  have hσ := hsatFrame ρp hs X hX
  generalize d.toLfp.frame ψ ρp X = σ at hσ ⊢
  -- the fields' own readings: `ab`'s domains
  have hFab : d.absF ψ c j = ab.map (·.2.2) := hab.symm
  have hget : ∀ i (hi : i < ab.length), (d.absF ψ c j).getD i default = (ab[i]'hi).2.2 := by
    intro i hi
    rw [hFab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  have htake : ∀ i, (d.absF ψ c j).take i = (ab.take i).map (·.2.2) := by
    intro i; rw [hFab, List.map_take]
  -- U2's grading, per field
  have hdom : ∀ i, i < ab.length → ∀ as : List V, SpineFit σ ((d.absF ψ c j).take i) as →
      WellDenotedV V (consList as σ) ((d.absF ψ c j).getD i default) := by
    intro i hi as has
    rw [hget i hi]
    refine wellDenotedV_mkPisAV_dom hgr i _ (List.getElem?_eq_getElem hi) _ ?_
    rw [← htake i]
    exact sat_of_spineFit hσ has
  -- U2's universe bound, per field
  have hbound : d.w ψ ≠ 0 → ∀ i, i < ab.length → ∀ as : List V,
      SpineFit σ ((d.absF ψ c j).take i) as →
      interp V (consList as σ) ((d.absF ψ c j).getD i default) ∈ˢ (univ (d.w ψ) : V) := by
    intro hw i hi as has
    have hnp : (Level.isEquiv p.resSort .zero == some true) = false := by
      cases h : (Level.isEquiv p.resSort .zero == some true)
      · rfl
      · exfalso
        have h0 := ConLeche.Level.isEquiv_sound (beq_iff_eq.mp h) ψ
        exact hw (by show d.resSort.eval ψ = 0; rw [← hres]; simpa [Level.eval] using h0)
    obtain ⟨hlenS, hfields⟩ := ConLeche.checkStructFieldSortsI_inv hsorts
    rw [hhi] at hxq hfields
    have hxq' : openPisAtFvars cA.2 tyN (d.nP + d.k) = some (xq.1, xq.2) := hxq
    obtain ⟨pps, b, hst, -, -, hbind⟩ := denoteMeta_openPis cA.2 hxq' hca
    rw [← habLen, stripPisAV_mkPisAV] at hst
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst).symm
    have hlenX : xq.1.length = cA.2 := ConLeche.Verify.openPisAtFvars_length _ hxq'
    have hTB := teleBound_walk (w := d.w ψ) rfl mp ψ cA.2 hxq' habLen hCP.toCtxOk hfr.1 hfr.2.1
      hfr.2.2
      (fun k a hka => by
        obtain ⟨q, hq, -, hqd⟩ := hbind k a hka
        rw [hqd, List.getD_eq_getElem?_getD, hq]
        rfl)
      (fun k a hka => by
        have hk' : k < cA.2 := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hka).1
        obtain ⟨fv, t, u, hfv, -, hinfk, hens, hleq, -⟩ := hfields k hk'
        obtain rfl := Option.some.inj (hka.symm.trans hfv)
        refine ⟨F, t, u, hinfk, hens, ?_⟩
        have hle := ConLeche.Level.leq_sound (hleq hnp) ψ
        show Level.eval ψ u ≤ d.resSort.eval ψ
        rw [← hres]; exact hle)
      i (by omega) (consList as σ) (by rw [← htake i]; exact sat_of_spineFit hσ has)
    rw [hget i hi]
    have h2 := hTB.2
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h2
  have hlenF : (d.absF ψ c j).length = ab.length := by rw [hFab, List.length_map]
  refine ⟨fieldsOkB_of_prefix _ σ fun i hi as has =>
      ⟨(hdom i (by omega) as has).1, fun hw => hbound hw i (by omega) as has⟩,
    fieldsValid_of_prefix _ σ fun i hi as has => (hdom i (by omega) as has).2,
    fun fs hfs e he => ?_⟩
  -- the result index readings: arguments of the graded body
  have hbody := gradedV_mkPisAV_body hgr (consList fs σ)
    (by rw [← hFab]; exact sat_of_spineFit hσ hfs)
  exact WellDenotedV_mkAppN_args _ hbody e (List.mem_append_right _ he)

/-! ## The block -/

/-- **Every member constructor's fields with holes are closed and graded
at the hole frame of every tuple**, from the install's positivity stage
(`DeclBlockRun` conjunct 3: `nestPos` and U2) at the formers'
environment — at ANY model of it holding the formers: the readings
mention no member constant. -/
theorem blockHoleGrade_of_run {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true) {env : Env}
    (mp : EnvModelM V μ env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    {hook : ConLeche.NestHook ConLeche.CheckM}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × List ConLeche.NestKey ×
      List (Nat × Nat × Expr)}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs hook = .ok posKs)
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hres : p.resSort = d.resSort)
    (hk : d.k = d.memberNames.length)
    (hinst : d.nInst = 0)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) (hlenCA : ctorsAs.length = d.k)
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true)
    (hnfs : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      d.nfFF c j = (posKs.2.1.getD c []).getD j default)
    (ψ : Name → Nat) {c : Nat} (hc : c < d.N) {j : Nat} (hj : j < (d.ctorsM c).length) :
    (FieldsBelow (d.nP + d.k) (d.absF ψ c j) ∧
      ∀ e ∈ d.absE ψ c j, Term.bvarsBelow (d.nP + d.k + (d.absF ψ c j).length) e.erase) ∧
    ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X : Nat → V, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
    FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
    FieldsValid (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
    ∀ fs : List V, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
      ∀ e ∈ d.absE ψ c j, WellDenotedV V (consList fs (d.toLfp.frame ψ ρp X)) e := by
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨kinds, nfs, keys, done⟩ := posKs
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hder⟩ :=
    checkBlockPositivity_derivM mp.base2.wf hrun
      (fun cv h => (mp.base2.wf _ (List.mem_of_find?_eq_some
        (hcore.1 0 cv (by rwa [List.head?_eq_getElem?] at h)).1)).1)
      (fun c cs hc j cA hj => by
        have hck : c < d.k := by rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hc).1
        rw [hctorsAs c hck] at hc
        obtain rfl := Option.some.inj hc
        exact (hclosed c j cA hj).1)
  have hck : c < d.k := by
    have : c < d.k + d.nInst := hc
    omega
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  obtain ⟨crest, ksr, tsr, hcrest, hd, -, ⟨ty, hty⟩, -, ⟨xq, sorts, hxq, hsorts⟩, -⟩ :=
    hder c (d.ctorsM c) (hctorsAs c hck) j _ hcj
  obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
  exact blockCtorHoleGrade_of_walk mp hN hcore hnames hlps hnP hnIdxs hres hk hcv0 hop0
    hholes hcj hCf hCb hcrest hty hd (hnfs c j _ hcj) hxq hsorts

/-- **The hole context is satisfied below the members' leaves**: a
member's leaf inhabits its former's type (`EnvModelM.mem_type`). -/
theorem blockHoleCtx_sat {μ : ConLeche.CheckMode} {env : Env} (mp : EnvModelM V μ env)
    {d : BlockData V} {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      FormerData mp.base2 cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) (ψ : Name → Nat) :
    ∀ hs : List V, hs.length = d.k →
      (∀ t, t < d.k → ∀ σ : Nat → V,
        interp V σ (mp.base2.acval (d.memberName t) ψ) = hs.getD t pt) →
      ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ → Sat V (d.holeCtx ψ).reverse (consList hs ρ) := by
  intro hs hsl hv ρ hρ
  have hhs : hs = (List.range d.k).map fun t => hs.getD t pt := by
    refine List.ext_getElem (by simp [hsl]) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rw [hhs]
  simp only [BlockData.holeCtx, List.reverse_append]
  refine sat_of_spineFit hρ (spineFit_range_closed d.k (fun t ht σ => ?_) ρ)
  obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
  obtain ⟨hfb, hFDt⟩ := hF t cvTb hcvb
  rw [← hv t ht σ, show d.memberName t = cvTb.name from hN.1 t cvTb hcvb]
  exact mp.mem_type _ (List.mem_of_find?_eq_some hfb) ψ _ (hFDt.read ψ) σ

section RunLink

variable {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true)
  {env : Env} (mp : EnvModelM V μ env) {F : Nat}
  {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
  {isRec : Bool} (hN : BlockNamesOk (V := V) d cvTas)
  (hF : ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
    env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
    FormerData mp.base2 cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c))
  {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
  {hook : ConLeche.NestHook ConLeche.CheckM}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × List ConLeche.NestKey ×
      List (Nat × Nat × Expr)}
  (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
    p cvTas ctorsAs hook = .ok posKs)
  (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
  (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs)
  (hk : d.k = d.memberNames.length) (hnd : d.memberNames.Nodup)
  (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) (hlenCA : ctorsAs.length = d.k)
  (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
    cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true)

include hμ mp hN hF hrun hnames hlps hnP hnIdxs hk hnd hctorsAs hlenCA hclosed in
/-- **The positivity run at a stored constructor, read at a model**:
the declared crest and the walk's normal form (the run's
output entry) read as Π-towers with the datum's body, the fields reading
alike on the hole context, the normal form naming only stored constants,
and the stored field shape facts of the normal form's fields against the
stored field readings — through THE producer (`storedFieldShapes_of_walk`),
its semantic link from `blockWalkCtx`. -/
theorem blockRunLink (ψ : Name → Nat)
    (hformers : ∀ t, t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ)
    {c j : Nat} {cA : ConstantVal × Nat} (hc : c < d.k) (hcj : (d.ctorsM c)[j]? = some cA)
    (hD : StoredCtorFacts mp.base2 (d.memberName c) lps cA.1 d.nP cA.2 (d.fvsPF c j)
      (d.xFvsF c j) (d.xrestF c j) (d.idxF c j) (d.dsF c j) (d.esF c j)) :
    ConstsBound env ((posKs.2.1.getD c []).getD j default) ∧
    ((posKs.2.1.getD c []).getD j default).nestOcc d.memberNames 0 0 = false ∧
    lpDefF lps ((posKs.2.1.getD c []).getD j default) = true ∧
    ∃ (A : Expr) (abD abN : List (Nat × Nat × AnnotTerm)),
      instPisWith (canonParams d.nP) (canonAbs d.memberNames lps d.nP d.k cA.1.type) = some A ∧
      denoteMeta mp.base2.acval env ψ (d.nP + d.k) A
        = some (mkPisAV abD (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      denoteMeta mp.base2.acval env ψ (d.nP + d.k) ((posKs.2.1.getD c []).getD j default)
        = some (mkPisAV abN (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
            (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ c j))) ∧
      abD.length = cA.2 ∧ abN.length = cA.2 ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      FieldsEqOn V (d.holeCtx ψ).reverse (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      StoredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => mp.base2.acval (d.memberName t) ψ)
        (d.params ψ).reverse (abN.map (·.2.2)) ((d.Fss c ψ).getD j []) := by
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨kinds, nfs, keys, done⟩ := posKs
  have hkL : p.memberNames.length = d.k := by rw [hnames, hk]
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hder⟩ :=
    checkBlockPositivity_derivM mp.base2.wf hrun
      (fun cv h => (mp.base2.wf _ (List.mem_of_find?_eq_some
        (hF 0 cv (by rwa [List.head?_eq_getElem?] at h)).1)).1)
      (fun c cs hc j cA hj => by
        have hck : c < d.k := by rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hc).1
        rw [hctorsAs c hck] at hc
        obtain rfl := Option.some.inj hc
        exact (hclosed c j cA hj).1)
  obtain ⟨crest, ksr, tsr, hcrest, hd, -, ⟨ty, hty⟩, hlpN, ⟨xq, sorts, hxq, hsorts⟩, -⟩ :=
    hder c (d.ctorsM c) (hctorsAs c hc) j cA hcj
  generalize (nfs.getD c []).getD j default = tyN at hd hlpN hxq hsorts ⊢
  have hCf : cA.1.type.hasFvar = false := hD.hasFvar
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hD.bounded
  -- the walk context's facts
  have hcv0' : cvTas[0]? = some cvTa0 := by rwa [List.head?_eq_getElem?] at hcv0
  have hT0f : cvTa0.type.hasFvar = false :=
    (mp.base2.wf _ (List.mem_of_find?_eq_some (hF 0 cvTa0 hcv0').1)).1
  have hplen : fvsP.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
  have hpar : ∀ (q : Nat) (x : Expr), fvsP[q]? = some x → ∃ ty, x = .fvar q ty := by
    intro q x hx
    obtain ⟨ty, h⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 q x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have hparW : ∀ x ∈ fvsP, Expr.WScoped p.nP x := by
    intro x hx
    have := (ConLeche.openPisAtFvars_WScoped p.nP cvTa0.type 0 hop0
      (Expr.WScoped.of_not_hasFvar hT0f)).1 x hx
    rwa [Nat.zero_add] at this
  have hform' : ∀ t, t < p.memberNames.length → ∃ cv caps bs s,
      env.find? (p.memberNames.getD t .anonymous) = some (.indInfo cv caps) ∧
      cv.levelParams = p.lps ∧
      cv.type.stripPis (p.nP + p.nIdxs.getD t 0) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ := by
    intro t ht
    rw [hkL] at ht
    rw [hnames, hlps, hnP, hnIdxs]
    exact hformers t ht
  have hin := Rules.RulesInputs.ofSem mp ψ
  have hhiQ : (p.nestCtx fvsP env.find? env.consts).hiAt 0 = d.nP + d.k := by
    simp only [ConLeche.NestCtx.hiAt, ConLeche.BlockParts.nestCtx, hkL, hnP, Nat.add_zero]
  -- THE producer, its link from the walk context
  obtain ⟨abD, abN, E, hRD, hRN, hlD, hlN, hE, hS⟩ :=
    storedFieldShapes_of_walk (ctx := p.nestCtx fvsP env.find? env.consts) mp.base2 ψ rfl hholes
      (show p.memberNames.Nodup by rw [hnames]; exact hnd) hplen hpar hparW hform'
      (show c < p.memberNames.length by rw [hkL]; exact hc)
      (show StoredCtorFacts mp.base2 (p.memberNames.getD c .anonymous) p.lps cA.1 p.nP cA.2 _ _ _ _ _ _
        by rw [hnames, hlps, hnP]; exact hD) hcrest hd ⟨_, xq, sorts, hxq, hsorts⟩
      (Δp := (d.params ψ).reverse) (Δh := (d.holeCtx ψ).reverse)
      (fun ca hca => by
        obtain ⟨abD, abN, B, -, hcaE, hNE, hlD, hlN, -, -, -, -, hfrN, -, -, hEq, hsubN, -, -⟩ :=
          blockWalkCtx hin hN hF hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hCf hCb hcrest hty hd
            (by rw [← hhiQ]; exact hca)
        exact ⟨abD, abN, B, hcaE, by rw [hhiQ]; exact hNE, hlD, hlN, hEq,
          by rw [hhiQ]; exact hfrN, hsubN⟩)
      (fun hs hsl hv ρ hρ => blockHoleCtx_sat mp hN hF ψ hs (hsl.trans hkL)
        (fun t ht σ => by
          have := hv t (show t < p.memberNames.length by rw [hkL]; exact ht) σ
          simp only [ConLeche.BlockParts.nestCtx] at this
          rwa [hnames] at this) ρ hρ)
  rw [hhiQ] at hRD hRN
  simp only [ConLeche.BlockParts.nestCtx] at hRD hRN hE hS
  -- the link, again, at the crest's reading
  obtain ⟨abD', abN', B, -, hcaE, hNE, hlD', hlN', hbits, -, -, -, -, -, -, hEq, -, hcbN, -⟩ :=
    blockWalkCtx hin hN hF hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hCf hCb hcrest hty hd hRD
  obtain ⟨h1, -⟩ := mkPisAV_inj (hlD.trans hlD'.symm) hcaE
  subst h1
  rw [hRN] at hNE
  obtain ⟨h2, -⟩ := mkPisAV_inj (hlN.trans hlN'.symm) (Option.some.inj hNE)
  subst h2
  -- the result indices are the datum's
  have hEssD : (d.Ess c ψ).getD j [] = d.esF c j ψ := essOfR_fixCtorDataList_getD hcj
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hEss : E = d.absE ψ c j := by
    have h1 : ((d.Fss c ψ).getD j []).length = cA.2 := by
      rw [hFssD, List.length_map, List.length_drop, hD.len ψ]; omega
    rw [hE, BlockData.absE, hEssD, h1, hkL]
  rw [hEss, hkL] at hRD hRN
  -- the canonical crest the walked term is up to erasure
  have hlenQ := ConLeche.nestHoles_length hholes
  obtain ⟨A, hA, herased⟩ := canonCrest_of_walk (ctx := p.nestCtx fvsP env.find? env.consts)
    (k := d.k) (fun i x hx => hpar i x hx) hplen
    (fun t x hx => by
      have ht : t < (p.nestCtx fvsP env.find? env.consts).names.length := by
        rw [← hlenQ]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cv, caps, -, hget⟩ := ConLeche.nestHoles_getElem? hholes ht
      rw [hget] at hx
      exact ⟨_, (Option.some.inj hx).symm⟩)
    (by rw [hlenQ]; exact hkL) hcrest
  have hA' : instPisWith (canonParams d.nP) (canonAbs d.memberNames lps d.nP d.k cA.1.type)
      = some A := by
    rw [← hnames, ← hlps, ← hnP]; exact hA
  rw [denoteMeta_erasedEq herased, hnP] at hRD
  rw [hnP] at hRN
  rw [hkL, hnP, hnIdxs, hFssD.symm] at hS
  -- the normal form mentions no member and has the block's levels
  have hoccN : tyN.nestOcc d.memberNames 0 0 = false := by
    obtain ⟨-, -, -, -, -, -, -, hha⟩ := hd
    have := holesApplied_nestOcc_zero _ hha
    simpa [ConLeche.BlockParts.nestCtx, hnames] using this
  have hlpN' : lpDefF lps tyN = true := by
    rw [← hlps]; exact lpDefF_of_allLevelParamsDefined _ hlpN
  refine ⟨hcbN, hoccN, hlpN', A, abD, abN, hA', hRD, hRN, hlD, hlN, hbits, hEq, ?_⟩
  refine ⟨hS.len, hS.holeApp, fun hs hhs hv => hS.override hs hhs fun t ht σ => ?_⟩
  rw [hnames]
  exact hv t ht σ

include hμ mp hN hF hrun hnames hlps hnP hnIdxs hk hnd hctorsAs hlenCA hclosed in
/-- **The reading fact at a uniform block's datum**, from the install's
positivity stage (`blockRunLink`) — at a datum whose normal forms are the
run's and whose fields with holes are the normal forms' readings at the
model (`hnf`, `habs`). -/
theorem blockAbsRead_of_run
    (hformers : ∀ (ψ : Name → Nat) (t : Nat), t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ)
    {c j : Nat} {cA : ConstantVal × Nat} (hc : c < d.k) (hcj : (d.ctorsM c)[j]? = some cA)
    (hD : StoredCtorFacts mp.base2 (d.memberName c) lps cA.1 d.nP cA.2 (d.fvsPF c j)
      (d.xFvsF c j) (d.xrestF c j) (d.idxF c j) (d.dsF c j) (d.esF c j))
    (hnf : d.nfFF c j = (posKs.2.1.getD c []).getD j default)
    (habs : ∀ ψ, d.absF ψ c j
      = nfFieldsRead mp.base2.acval env (d.nP + d.k) cA.2 (d.nfFF c j) ψ) :
    BlockAbsRead mp.base2 d lps c j cA := by
  obtain ⟨hcb, -⟩ := blockRunLink hμ mp hN hF hrun hnames hlps hnP hnIdxs hk hnd hctorsAs hlenCA hclosed (fun _ => 0)
    (hformers _) hc hcj hD
  refine ⟨by rw [hnf]; exact hcb, ?_⟩
  obtain ⟨-, -, -, A, -, -, hA, -⟩ := blockRunLink hμ mp hN hF hrun hnames hlps hnP hnIdxs hk hnd
    hctorsAs hlenCA hclosed (fun _ => 0) (hformers _) hc hcj hD
  refine ⟨A, hA, fun ψ => ?_⟩
  obtain ⟨-, -, -, A', abD, abN, hA', hRD, hRN, hlD, hlN, hbits, hEq, -⟩ :=
    blockRunLink hμ mp hN hF hrun hnames hlps hnP hnIdxs hk hnd hctorsAs hlenCA hclosed ψ (hformers ψ) hc hcj hD
  rw [hA] at hA'
  obtain rfl := Option.some.inj hA'
  rw [← hnf] at hRN
  have habN : abN.map (·.2.2) = d.absF ψ c j := by
    rw [habs ψ]; exact (nfFieldsRead_eq hRN hlN).symm
  refine ⟨abD, abN, hRD, hRN, hlD, hlN, hbits, habN, ?_⟩
  rw [← habN]
  exact hEq

end RunLink

/-- **The stored field shape facts at a uniform block's datum**, from the
install's positivity stage (`blockRunLink`): the normal form reads as the
Π-tower over the datum's fields with holes (the datum's reading fact), so
the producer's fields with holes ARE the datum's. -/
theorem blockStoredShapes_of_run {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true)
    {env : Env} (mp : EnvModelM V μ env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    {hook : ConLeche.NestHook ConLeche.CheckM}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × List ConLeche.NestKey ×
      List (Nat × Nat × Expr)}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs hook = .ok posKs)
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs)
    (hk : d.k = d.memberNames.length)
    (hnd : d.memberNames.Nodup)
    (hinst : d.nInst = 0)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) (hlenCA : ctorsAs.length = d.k)
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true)
    (hnfs : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      d.nfFF c j = (posKs.2.1.getD c []).getD j default)
    (ψ : Name → Nat)
    (hformers : ∀ t, t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ)
    {c : Nat} (hc : c < d.N) {j : Nat} (hj : j < (d.ctorsM c).length) :
    StoredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => mp.base2.acval (d.memberName t) ψ)
      (d.params ψ).reverse (d.absF ψ c j) ((d.Fss c ψ).getD j []) := by
  have hck : c < d.k := by
    have : c < d.k + d.nInst := hc
    omega
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  generalize hcA : (d.ctorsM c)[j] = cA at hcj
  obtain ⟨hCf, hCb⟩ := hclosed c j cA hcj
  have hD₀ : BlockCtorDataI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := (hcore.2 c j cA hcj).1
  obtain ⟨-, -, -, A, abD, abN, -, -, hRN, -, hlN, -, -, hS⟩ :=
    blockRunLink hμ mp hN hcore.1 hrun hnames hlps hnP hnIdxs hk hnd hctorsAs hlenCA hclosed ψ hformers hck hcj
      (hD₀.storedCtorFacts hCf hCb)
  -- the datum's reading of the same normal form
  obtain ⟨-, A₀, -, hR⟩ := (hcore.2 c j cA hcj).2
  obtain ⟨-, abN', -, hNr, -, hlN', -, habN, -⟩ := hR ψ
  rw [hnfs c j cA hcj, hRN] at hNr
  obtain ⟨rfl, -⟩ := mkPisAV_inj (hlN.trans hlN'.symm) (Option.some.inj hNr)
  rw [habN] at hS
  exact hS

/-! ## The hole chains are closed below the operator's frame -/

omit [SetTheory V] in
/-- A parallel substitution at the cut `k` keeps a term below `k + b`
when it was below `k + n` and every substituted term is below `b`. -/
theorem bvarsBelow_substAV (τ : Nat → AnnotTerm) {n b : Nat}
    (hτ : ∀ j, j < n → Term.bvarsBelow b (τ j).erase) :
    ∀ (e : AnnotTerm) (k : Nat), Term.bvarsBelow (k + n) e.erase →
      Term.bvarsBelow (k + b) (AnnotTerm.substAV τ e k).erase := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simp only [AnnotTerm.substAV, AnnotTerm.erase_bvar, Term.bvarsBelow] at h ⊢
    split
    · simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega
    · rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN k (τ (i - k)).erase b 0 (hτ _ (by omega))
      rwa [Nat.add_comm b k] at this
  | sort u => intro _ _; trivial
  | const c us => intro _ _; trivial
  | prf => intro _ _; trivial
  | app f a ihf iha =>
    intro k h
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam u A b' ihA ihb =>
    intro k h
    refine ⟨ihA k h.1, ?_⟩
    have := ihb (k + 1) (by rw [show k + 1 + n = k + n + 1 by omega]; exact h.2)
    rwa [show k + 1 + b = k + b + 1 by omega] at this
  | pi u v A B ihA ihB =>
    intro k h
    refine ⟨ihA k h.1, ?_⟩
    have := ihB (k + 1) (by rw [show k + 1 + n = k + n + 1 by omega]; exact h.2)
    rwa [show k + 1 + b = k + b + 1 by omega] at this
  | eqE a b' iha ihb =>
    intro k h
    exact ⟨iha k h.1, ihb k h.2⟩
  | fst e ih => intro k h; exact ih k h
  | snd e ih => intro k h; exact ih k h

omit [SetTheory V] in
/-- The hole substitution sends the holes and the parameters below the
operator's frame `(t, Y, parameters)`. -/
theorem holeTau_below {k nP : Nat} {H : Nat → AnnotTerm}
    (hH : ∀ m, m < k → Term.bvarsBelow (nP + 2) (H m).erase) :
    ∀ j, j < k + nP → Term.bvarsBelow (nP + 2) (holeTau k H j).erase := by
  intro j hj
  unfold holeTau
  split
  · exact hH _ (by omega)
  · simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega

omit [SetTheory V] in
/-- A constructor's fields with holes, as chain entries, are closed below
the operator's frame. -/
theorem fieldsBelow_holeEntsAV {k nP : Nat} {H : Nat → AnnotTerm}
    (hH : ∀ m, m < k → Term.bvarsBelow (nP + 2) (H m).erase) :
    ∀ (Fs : List AnnotTerm) (i : Nat), FieldsBelow (i + (k + nP)) Fs →
      FieldsBelow (nP + 2 + i) (holeEntsAV k H i Fs)
  | [], _, _ => trivial
  | F :: Fs, i, hF => by
    refine ⟨?_, ?_⟩
    · have := bvarsBelow_substAV (holeTau k H) (holeTau_below hH) F i hF.1
      rwa [Nat.add_comm i (nP + 2)] at this
    · have := fieldsBelow_holeEntsAV hH Fs (i + 1)
        (by rw [show i + 1 + (k + nP) = i + (k + nP) + 1 by omega]; exact hF.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 by omega] at this

omit [SetTheory V] in
/-- A field chain gives λ-domains at any annotation. -/
theorem lamDomsBelow_map {v : Nat} :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k Fs → LamDomsBelow k (Fs.map (v, ·))
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, lamDomsBelow_map h.2⟩

omit [SetTheory V] in
/-- **A member's hole term is closed below the operator's frame**, from
its parameter telescope closed and its index telescope below the
parameters. -/
theorem holeTmAV_below {u m nP : Nat} {Ps Is : List AnnotTerm} (hPlen : Ps.length = nP)
    (hP : FieldsBelow 0 Ps) (hI : FieldsBelow nP Is) :
    Term.bvarsBelow (nP + 2) (holeTmAV u m Ps Is).erase := by
  subst hPlen
  unfold holeTmAV
  have hP' : FieldsBelow (Ps.length + 2) (liftFields (Ps.length + 2) 0 Ps) := by
    have := FieldsBelow_liftFields (n := Ps.length + 2) (Nat.le_refl 0) hP
    rwa [Nat.zero_add] at this
  have hI' : FieldsBelow (Ps.length + 2 + Ps.length) (liftFields (Ps.length + 2) 0 Is) := by
    have := FieldsBelow_liftFields (n := Ps.length + 2) (Nat.zero_le Ps.length) hI
    rwa [show Ps.length + (Ps.length + 2) = Ps.length + 2 + Ps.length by omega] at this
  refine mkLamsAV_below (lamDomsBelow_map (fieldsBelow_append hP' ?_)) ?_
  · rw [liftFields_length]; exact hI'
  · simp only [List.length_map, List.length_append, liftFields_length,
      AnnotTerm.erase_app, Term.bvarsBelow]
    refine ⟨projAV_below (by simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega), ?_⟩
    have := mkTowerGo_below (w := u) hI'
    rw [liftFields_length] at this
    rwa [show Ps.length + 2 + Ps.length + Is.length = Ps.length + 2 + (Ps.length + Is.length)
      by omega] at this

namespace LfpDatum

variable {D : LfpDatum V}

omit [SetTheory V] in
/-- **The hole chains are closed below the operator's frame** — every
chain of every member, when the members' telescopes are, the fields with
holes are below the parameters and the holes, and the result index
readings below them and the fields. -/
theorem holeChains_below {ψ : Name → Nat} {nP : Nat}
    (hP : ∀ m, m < D.k → (D.pars m ψ).length = nP ∧ FieldsBelow 0 (D.pars m ψ))
    (hI : ∀ m, m < D.k → FieldsBelow nP (D.ids m ψ))
    {c : Nat} (hF : ∀ j, j < D.nctors c → FieldsBelow (nP + D.k) (D.fields ψ c j) ∧
      (∀ e ∈ D.resIdx ψ c j, Term.bvarsBelow (nP + D.k + (D.fields ψ c j).length) e.erase) ∧
      (D.resIdx ψ c j).length = (D.ids c ψ).length) :
    ∀ chain ∈ D.holeChains ψ c, FieldsBelow (nP + 2) chain := by
  have hH : ∀ m, m < D.k → Term.bvarsBelow (nP + 2) (D.holeTm ψ m).erase :=
    fun m hm => holeTmAV_below (hP m hm).1 (hP m hm).2 (hI m hm)
  intro chain hch
  unfold holeChains holeChs termChs at hch
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hch
  simp only [List.length_map, List.length_range] at hj
  have hj' : j < D.nctors c := List.mem_range.mp hj
  have hgF : (((List.range (D.nctors c)).map (D.fields ψ c)).map
      (holeEntsAV D.k (D.holeTm ψ) 0)).getD j []
        = holeEntsAV D.k (D.holeTm ψ) 0 (D.fields ψ c j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, List.getElem?_range hj']
    rfl
  have hgE : ((List.range ((List.range (D.nctors c)).map (D.fields ψ c)).length).map fun j =>
      holeEqsAV D.k (D.holeTm ψ) (D.ids c ψ).length
        (((List.range (D.nctors c)).map (D.fields ψ c)).getD j []).length
        (((List.range (D.nctors c)).map (D.resIdx ψ c)).getD j [])).getD j []
      = holeEqsAV D.k (D.holeTm ψ) (D.ids c ψ).length (D.fields ψ c j).length
          (D.resIdx ψ c j) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by simpa using hj')]
    simp only [Option.map_some, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj',
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj']
    rfl
  rw [hgF, hgE]
  obtain ⟨hFb, hEb, hElen⟩ := hF j hj'
  have hents := fieldsBelow_holeEntsAV hH (D.fields ψ c j) 0
    (by rw [Nat.zero_add, Nat.add_comm]; exact hFb)
  rw [Nat.add_zero] at hents
  refine FieldsBelow_append_idxEq hents fun e he => ?_
  unfold holeEqsAV at he
  obtain ⟨l, hlr, rfl⟩ := List.mem_map.mp he
  rw [holeEntsAV_length]
  refine ⟨?_, projAV_below (by simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega)⟩
  have hl : l < (D.resIdx ψ c j).length := by rw [hElen]; exact List.mem_range.mp hlr
  have hmem : (D.resIdx ψ c j).getD l default ∈ D.resIdx ψ c j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]; exact List.getElem_mem _
  have := bvarsBelow_substAV (holeTau D.k (D.holeTm ψ)) (holeTau_below hH) _
    (D.fields ψ c j).length
    (by rw [show (D.fields ψ c j).length + (D.k + nP) = nP + D.k + (D.fields ψ c j).length
          by omega]; exact hEb _ hmem)
  rwa [Nat.add_comm (D.fields ψ c j).length (nP + 2)] at this

end LfpDatum

/-! ## The block's hole chains, well-formed -/

/-- **The block's hole chains are graded, bit-valid and closed** — the
three facts a member's former leaf on them needs (`blockTyG_wellDenoted`,
its currency, its closedness) — from the per-constructor facts
`blockHoleGrade_of_run` gives and the members' telescopes. -/
theorem blockHoleChains_facts {env : Env} {m : EnvModel V env} {d : BlockData V}
    {lps : List Name} (hH : BlockHoleFacts m d lps) (ψ : Name → Nat)
    (hIdx : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp → ∀ c, c < d.N →
      IdxOk (d.uM c ψ) ρp (d.IdsM c ψ) ∧ FieldsValid ρp (d.IdsM c ψ))
    (hPars : ∀ mm, mm < d.k → FieldsBelow 0 (d.toLfp.pars mm ψ) ∧ ∀ σ : Nat → V,
      FieldsOkB 0 σ (d.toLfp.pars mm ψ) ∧ FieldsValid σ (d.toLfp.pars mm ψ))
    (hIdsB : ∀ c, c < d.k → FieldsBelow d.nP (d.IdsM c ψ))
    (hG : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      (FieldsBelow (d.nP + d.k) (d.absF ψ c j) ∧
        ∀ e ∈ d.absE ψ c j, Term.bvarsBelow (d.nP + d.k + (d.absF ψ c j).length) e.erase) ∧
      ∀ (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X : Nat → V, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
      FieldsValid (d.toLfp.frame ψ ρp X) (d.absF ψ c j) ∧
      ∀ fs : List V, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
        ∀ e ∈ d.absE ψ c j, WellDenotedV V (consList fs (d.toLfp.frame ψ ρp X)) e) :
    (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      BlockChainsOkG d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ)) ∧
    (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      ∀ Y, Y ∈ˢ famsSpaceB d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) →
      ∀ c, c < d.N → ∀ t : V, SumFieldsValid (cons t (cons Y ρp)) (d.toLfp.holeChains ψ c)) ∧
    (∀ c, c < d.N → ∀ chain ∈ d.toLfp.holeChains ψ c, FieldsBelow (d.nP + 2) chain) := by
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  have hres : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro c hc j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  have happ : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun c hc j hj => blockHolesApplied hH ψ hc hj
  have hok : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp → d.toLfp.HoleTmOk ψ ρp :=
    fun ρp hs mm hmm =>
      ⟨⟨(hH.parsLen ψ mm hmm).trans (hH.lenP ψ).symm, hH.parsSat ψ mm hmm ρp hs⟩,
        fun _ => (hIdx ρp hs mm (Nat.lt_of_lt_of_le hmm hkN)).1.2⟩
  refine ⟨fun ρp hs => ?_, fun ρp hs Y hY c hc t => ?_, fun c hc => ?_⟩
  · exact LfpDatum.holeChains_ok (hok ρp hs) hkN (fun c hc => (hIdx ρp hs c hc).1)
      (fun mm hmm => ((hPars mm hmm).2 _).1) happ hres
      (fun X hX c hc j hj => ⟨((hG c hc j hj).2 ρp hs X hX).1,
        fun fs hfs e he => (((hG c hc j hj).2 ρp hs X hX).2.2 fs hfs e he).1⟩)
  · exact LfpDatum.holeChains_valid (hok ρp hs) (fun mm hmm => ((hPars mm hmm).2 _).2)
      (fun mm hmm => (hIdx ρp hs mm (Nat.lt_of_lt_of_le hmm hkN)).2) happ
      (fun X hX c hc j hj => ⟨((hG c hc j hj).2 ρp hs X hX).2.1,
        fun fs hfs e he => (((hG c hc j hj).2 ρp hs X hX).2.2 fs hfs e he).2⟩) hY t hc
  · refine LfpDatum.holeChains_below (D := d.toLfp) (nP := d.nP)
      (fun mm hmm => ⟨hH.parsLen ψ mm hmm, (hPars mm hmm).1⟩) hIdsB (fun j hj => ?_)
    obtain ⟨⟨hFb, hEb⟩, -⟩ := hG c hc j hj
    exact ⟨hFb, hEb, hres c hc j hj⟩

/-! ## Congruences of the hole form -/

omit [SetTheory V] in
/-- The result index readings with holes are congruent in the readings. -/
theorem BlockData.absE_congr {d d' : BlockData V} {ψ ψ' : Name → Nat} {c j : Nat}
    (hk : d.k = d'.k) (hes : (d.Ess c ψ).getD j [] = (d'.Ess c ψ').getD j [])
    (hlen : ((d.Fss c ψ).getD j []).length = ((d'.Fss c ψ').getD j []).length) :
    d.absE ψ c j = d'.absE ψ' c j := by
  unfold BlockData.absE
  rw [hes, hlen, hk]

omit [SetTheory V] in
/-- **The hole chains are congruent** in the lfp datum's readings. -/
theorem LfpDatum.holeChains_congr {D D' : LfpDatum V} {ψ ψ' : Name → Nat} (hk : D.k = D'.k)
    (hu : ∀ m, D.u m ψ = D'.u m ψ') (hp : ∀ m, D.pars m ψ = D'.pars m ψ')
    (hi : ∀ c, D.ids c ψ = D'.ids c ψ') (hn : ∀ c, D.nctors c = D'.nctors c)
    (hf : ∀ c j, D.fields ψ c j = D'.fields ψ' c j)
    (he : ∀ c j, D.resIdx ψ c j = D'.resIdx ψ' c j) :
    D.holeChains ψ = D'.holeChains ψ' := by
  have hf' : ∀ c, D.fields ψ c = D'.fields ψ' c := fun c => funext (hf c)
  have he' : ∀ c, D.resIdx ψ c = D'.resIdx ψ' c := fun c => funext (he c)
  unfold LfpDatum.holeChains LfpDatum.holeTm
  simp only [hk, hu, hp, hi, hn, hf', he']

/-! ## A closed telescope's prefix -/

omit [SetTheory V] in
theorem fieldsBelow_take : ∀ {Fs : List AnnotTerm} {k : Nat} (n : Nat),
    FieldsBelow k Fs → FieldsBelow k (Fs.take n)
  | [], _, _, _ => by simp; trivial
  | _ :: _, _, 0, _ => trivial
  | _ :: Fs, _, n + 1, h => ⟨h.1, fieldsBelow_take (Fs := Fs) n h.2⟩

/-- **A graded closed telescope's first `n` domains** are closed and
hereditarily graded and bit-valid at every frame — a member's parameter
telescope, read off its former's type. -/
theorem teleTake_ok {pps : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm} (n : Nat)
    (hok : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV pps B)) (hb : DomsBelow 0 pps) :
    FieldsBelow 0 ((pps.take n).map (·.2.2)) ∧ ∀ σ : Nat → V,
      FieldsOkB 0 σ ((pps.take n).map (·.2.2)) ∧ FieldsValid σ ((pps.take n).map (·.2.2)) := by
  have hdom : ∀ σ : Nat → V, ∀ i, i < ((pps.take n).map (·.2.2)).length → ∀ as : List V,
      SpineFit σ (((pps.take n).map (·.2.2)).take i) as →
      WellDenotedV V (consList as σ) (((pps.take n).map (·.2.2)).getD i default) := by
    intro σ i hi as has
    have hi' : i < pps.length := by simp at hi; omega
    have hin : i < n := by simp at hi; omega
    have hget : ((pps.take n).map (·.2.2)).getD i default = (pps[i]'hi').2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hin,
        List.getElem?_eq_getElem hi']
      rfl
    rw [hget]
    refine wellDenotedV_mkPisAV_dom (Δa := []) (fun ρ _ => hok ρ) i _
      (List.getElem?_eq_getElem hi') _ ?_
    have h1 : ((pps.take n).map (·.2.2)).take i = (pps.take i).map (·.2.2) := by
      rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hin)]
    rw [h1] at has
    simpa using sat_of_spineFit (Sat_nil V σ) has
  have hb' := hb.fields
  refine ⟨by rw [List.map_take]; exact fieldsBelow_take n hb', fun σ =>
    ⟨fieldsOkB_of_prefix _ σ fun i hi as has => ⟨(hdom σ i hi as has).1, fun h => absurd rfl h⟩,
      fieldsValid_of_prefix _ σ fun i hi as has => (hdom σ i hi as has).2⟩⟩

end ConLeche.Model
