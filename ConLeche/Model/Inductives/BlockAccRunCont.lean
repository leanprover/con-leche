module

public import ConLeche.Model.Inductives.BlockAccRun
public import ConLeche.Model.Inductives.PosDerivAcc
public import ConLeche.Model.Inductives.BlockPosRunCont
import ConLeche.Model.Inductives.PosDerivShape
import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.StructEntryFree
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Rules.Inputs

public section

/-!
# Accessibility from the install's positivity derivation (lanes ACCMODEL, FLATACC, POSDERIV)

The block step of the accessibility route (maintainer rulings "(W) by
ACCESSIBILITY", 2026-09-24, and "use the positivity run, via a
declarative derivation", 2026-09-25): at a uniform block's install every
member constructor's field telescope is accessible along the
accessibility relation at the hole frame (`blockCtorAcc_of_walk`, from
the constructor's DERIVATION, `memberCtorD_acc`), which
`LfpDatum.accTuple_holeOp` turns into the hole operator's accessibility
with one bound of the level (`blockAccTuple_of_run`) and `closed_of_acc`
into (W).  At either position of the route switch:

* switch off (`blockAccTuple_of_run_flat`): every kind is flat, so the
  derivation meets no container and no coverage is needed;
* switch on (`nestedAccOwed`, the premise the nested block step takes):
  the container rules read coverage at the walk's carrier and the walk
  context's sort (`ContOk`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckM NestCtx NestHole NestState NestFieldKind
  BlockParts BlockShape instPisWith nestAbstract nestHoles nestMemberCtor openPisAtFvars fueledOps
  MemberCtorD PosKind PosTree)

universe w

variable {V : Type w} [SetTheory V]

/-! ## One constructor -/

/-- **A member constructor's field telescope is accessible along the
accessibility relation at the hole frame** (at a positive level), with
bounds reading only the agreeing positions, its ordinary fields' readings
likewise, and its result indices alike at any two hole frames — the
premises `LfpDatum.accTuple_holeOp` asks of one constructor.  From the
derivation (`memberCtorD_acc`, the container rules under `hcovk`), its
U2 typing, the datum's reading facts and grading, and U4. -/
theorem blockCtorAcc_of_walk {env : Env} {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    {ψ : Name → Nat} (hin : Rules.RulesInputs V mp.base2 ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {st₀ st₁ : NestState} {ks : List NestFieldKind} {tyN : Expr}
    (hm : nestMemberCtor (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts) cA.2
      crest st₀ = .ok (ks, tyN, st₁))
    {ksD : List PosKind} {ts : List PosTree}
    (hd : MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts) cA.2 crest
      ksD tyN ts)
    (hcovk : (∃ k ∈ ksD, k.flat = false) →
      ContOk mp ψ (d.w ψ) (p.nestCtx fvsP env.find? env.consts))
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    (hnf : d.nfFF c j = tyN)
    {ρp : Nat → V} (hs : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0)
    (hG : ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) :
    ∃ (ord : Nat → Bool) (Af : Nat → (Nat → V) → V),
      TeleAccP (d.w ψ) Af 0 (d.toLfp.MemberQ ψ) (d.toLfp.accRel ψ ρp) (d.absF ψ c j) ∧
      (∀ l τ τ', TAgr d.k ord l τ τ' → Af l τ = Af l τ') ∧
      (∀ (i : Nat) (G : AnnotTerm), (d.absF ψ c j)[i]? = some G → ord i = true →
        ∀ τ τ', TAgr d.k ord i τ τ' → interp V τ G = interp V τ' G) ∧
      (∀ X X', InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
        InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X' →
        ∀ fs, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
          SpineFit (d.toLfp.frame ψ ρp X') (d.absF ψ c j) fs →
          ∀ e ∈ d.absE ψ c j, interp V (consList fs (d.toLfp.frame ψ ρp X)) e
            = interp V (consList fs (d.toLfp.frame ψ ρp X')) e) := by
  obtain ⟨ab, abN, hhi, hca, hNr, hab, habLen, hlabN, hfr, hCP, hgr, hfrN, -, -, hEq,
    hsatFrame⟩ := blockCtorHoleCtx hin hN hcore hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hcj
      hCf hCb hcrest hinf hm hnf
  generalize hL : d.holeCtx ψ = L at hCP hgr hEq hsatFrame
  have hcN : (p.nestCtx fvsP env.find? env.consts).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find? env.consts).nP = d.nP := hnP
  have hcI : (p.nestCtx fvsP env.find? env.consts).nIdxs = d.nIdxs := hnIdxs
  rw [← hhi] at hca hgr hfr hCP hfrN hNr
  generalize hctx : p.nestCtx fvsP env.find? env.consts = ctx at *
  have hcNl : ctx.names.length = d.k := by rw [hcN, hk]
  -- the members' arities
  have har : ∀ t, t < d.k → (d.toLfp.pars t ψ).length + (d.toLfp.ids t ψ).length
      = ctx.nP + ctx.nIdxs.getD t 0 := by
    intro t ht
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    have hFDt := (hcore.1 t cvTb hcvb).2
    show (((d.ppsM t ψ).take d.nP).map (·.2.2)).length
      + (((d.ppsM t ψ).drop d.nP).map (·.2.2)).length = _
    simp only [List.length_map, List.length_take, List.length_drop, hFDt.len ψ, hcP, hcI]
    show _ = d.nP + d.nIdxAt t
    omega
  -- the relation, and the fields' values small
  have hR := holeRelA_accRel (m := mp.base2) hw hhi hcNl hcP har (hsatFrame ρp hs)
  have hG' : ∀ ρ ρ₀, d.toLfp.accRel ψ ρp ρ ρ₀ → FieldsOkB (d.w ψ) ρ (abN.map (·.2.2)) := by
    rintro _ _ ⟨X, Y, hX, -, rfl, -⟩
    rw [hab]
    exact hG X hX
  have hsm : TeleSmall (d.w ψ) ab.length (d.toLfp.accRel ψ ρp)
      (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - c)))
        (paramBvarsAt d.nP (ctx.hiAt 0 + cA.2) ++ d.absE ψ c j))) :=
    teleSmall_mkPisAV hw ab abN _ L.reverse _ hEq hR.dom fun ρ ρ₀ h => (hG' ρ ρ₀ h).toBound hw
  rw [habLen] at hsm
  -- the derivation
  obtain ⟨nds, cur, hteleD, htyN, hU4, hhead, hok, -⟩ := hd
  have hPi := memberCtorD_acc mp hin hw hteleD hhead hok hcovk hfr hCP hca hgr hR hsm
  rw [← habLen] at hPi
  obtain ⟨Af, htele, hinv, hQf⟩ := teleAccP_of_piAccThen hw ab abN _ (ctx.hiAt 0) 0
    (nds.map (·.1)) L.reverse _ (d.toLfp.MemberQ ψ) hEq hR.dom (fun ρ ρ₀ h => (hG' ρ ρ₀ h).toBound hw)
    (holeQ_top_iff hhi hcNl hcP har) (Nat.le_refl _) hPi
  -- the syntax: the opened normal form, U4
  obtain ⟨xs, rest', hopN, hkl, hnl, hxs⟩ := memberCtorD_open mp.base2.wf hfr.2.1 hteleD htyN
  have hU4' : ∀ i, i < cA.2 → (ksD.getD i .ordinary).guarded = true →
      ConLeche.structUsedLater tyN 0 i = false := by
    intro i hi hg
    cases hu : ConLeche.structUsedLater tyN 0 i
    · rfl
    · have := List.any_eq_false.mp hU4 i (List.mem_range.mpr hi)
      simp [hu, -List.getD_eq_getElem?_getD, hg] at this
  obtain ⟨pps, b, hst, -, hppl, hdoms⟩ := denoteMeta_openPis cA.2 hopN hNr
  rw [← hlabN, stripPisAV_mkPisAV] at hst
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst).symm
  have hxl : xs.length = cA.2 := ConLeche.Verify.openPisAtFvars_length cA.2 hopN
  classical
  let ord : Nat → Bool := fun l => !(ksD.getD l .ordinary).guarded
  refine ⟨ord, fun l => if l < cA.2 then Af l else fun _ => empty, ?_, ?_, ?_, ?_⟩
  · -- the telescope
    rw [← hab]
    refine TeleAccP.congr _ 0 _ _ (fun l' _ hl' => ?_) htele
    have : l' < cA.2 := by simpa [hlabN] using hl'
    simp only [if_pos this]
  · -- the fields' bounds read the agreeing positions
    intro l τ τ' hag
    by_cases hl : l < cA.2
    · simp only [if_pos hl]
      obtain ⟨x, hx⟩ : ∃ x, xs[l]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨k, nd, hkk, hnd, hE, -, -⟩ := hxs l x hx
      have hnd' : (nds.map (·.1))[l]? = some nd := by
        rw [List.getElem?_map]; exact hnd
      have hinvl := hinv l nd (by omega) hnd'
      rw [Nat.zero_add] at hinvl
      refine hinvl τ τ' fun i hi => ?_
      rcases hi with hi | ⟨hlt, hpar⟩
      rotate_left
      · refine (hag i).2 ?_
        rw [hhi, hcP] at hpar
        omega
      obtain ⟨hlt, hocc, hnh⟩ := hi
      by_cases hil : i < l
      · by_cases hoj : ord (l - 1 - i) = true
        · exact (hag i).1 hil hoj
        · exfalso
          have hno : (ksD.getD (l - 1 - i) .ordinary).guarded = true := by
            simpa [ord] using hoj
          have hU := hU4' (l - 1 - i) (by omega) hno
          have hfree := u4_nestOcc hopN hfrN.1 hU (by omega) (by omega) hx
          rw [erasedEq_nestOcc _ _ hE] at hfree
          rw [show ctx.hiAt 0 + l - 1 - i = ctx.hiAt 0 + (l - 1 - i) by omega,
            show ctx.hiAt 0 + l - i = ctx.hiAt 0 + (l - 1 - i) + 1 by omega, hfree] at hocc
          exact Bool.false_ne_true hocc
      · refine (hag i).2 ?_
        refine Nat.le_of_not_lt fun hlk => hnh ?_
        simp only [holeP, List.length_nil, hhi]
        omega
    · simp only [if_neg hl]
  · -- the ordinary fields read the agreeing positions
    intro i G hGi hoi τ τ' hag
    rw [← hab] at hGi
    have hi : i < cA.2 := by
      have := (List.getElem?_eq_some_iff.mp hGi).1
      simpa [hlabN] using this
    obtain ⟨x, hx⟩ : ∃ x, xs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨k, nd, hkk, -, hE, hord, hnip⟩ := hxs i x hx
    obtain ⟨p', hp', -, hread⟩ := hdoms i x hx
    rw [List.getElem?_map, hp', Option.map_some, Option.some.injEq] at hGi
    subst hGi
    have hkD : ksD.getD i .ordinary = k := by rw [List.getD_eq_getElem?_getD, hkk]; rfl
    have hkord : k = .ordinary := by
      have h' : (!(ksD.getD i .ordinary).guarded) = true := hoi
      rw [hkD] at h'
      have : k.guarded = false := by simpa using h'
      cases k with
      | ordinary => rfl
      | inProgress => exact absurd rfl hnip
      | _ => simp [PosKind.guarded] at this
    have hwx := openPisAtFvars_typeWScoped cA.2 hopN hfrN.1 i x hx
    have hholes' : NoBVar (holeP (ctx.hiAt 0 + i) ctx.nP (ctx.hiAt 0)) p'.2.2 := by
      refine denoteMeta_noBVar_of_nestOcc (m := mp.base2) (names := ctx.names) _ _ hwx
        (by simp [NestCtx.hiAt]) ?_ hread
      rw [erasedEq_nestOcc _ _ hE]
      exact hord hkord
    have hslots : NoBVar (fun q => ∃ jj, jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        p'.2.2 := by
      refine noBVar_exists' (P := fun jj q => jj < i ∧ ord jj = false ∧ LfpDatum.fieldSlot jj i q)
        fun jj => ?_
      by_cases hjj : jj < i ∧ ord jj = false
      · have h' : (!(ksD.getD jj .ordinary).guarded) = false := hjj.2
        have hno : (ksD.getD jj .ordinary).guarded = true := by simpa using h'
        exact NoBVar.mono (fun q hq => hq.2.2)
          (u4_fieldSlot (m := mp.base2) hopN hfrN.1 (hU4' jj (by omega) hno) (by omega) hjj.1 hx
            hread)
      · exact NoBVar.mono (fun q hq => absurd ⟨hq.1, hq.2.1⟩ hjj) hholes'
    refine interp_congr_noBVar _ (noBVar_or hholes' hslots) fun q hq => ?_
    by_cases hqi : q < i
    · refine (hag q).1 hqi (Classical.byContradiction fun hqo => ?_)
      exact hq (Or.inr ⟨i - 1 - q, by omega, by simpa using hqo, by
        simp only [LfpDatum.fieldSlot]; omega⟩)
    · refine (hag q).2 (Nat.le_of_not_lt fun hlt => hq (Or.inl ?_))
      simp only [holeP, hhi]
      omega
  · -- the result indices
    intro X X' hX hX' fs hf hf' e he
    rw [← hab] at hf hf'
    exact resC_of_resultIdxConst (by simp [paramBvarsAt, hcP]) hQf _ _
      ⟨X, X', hX, hX', rfl, rfl⟩ fs hf hf' e he


/-! ## The block -/

/-- **The hole operator of a uniform block is accessible, with one bound
of the level**, from the positivity stage's derivation of every member
constructor, at either position of the route switch (the container
rules read `hcovk`). -/
theorem blockAccTuple_of_run {env : Env} (mp : EnvModelM V .verified env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {m' : EnvModel V env} (hH : BlockHoleFacts m' d lps)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nst : Bool}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) env env.find?
      env.consts p cvTas ctorsAs nst = .ok (kinds, nfs))
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (hinst : d.nInst = 0) (hlenCA : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c))
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true)
    (hnfs : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      d.nfFF c j = (nfs.getD c []).getD j default)
    (ψ : Name → Nat) (ρp : Nat → V) (hs : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0)
    (hcovk : nst = true → ∀ fvsP, ContOk mp ψ (d.w ψ) (p.nestCtx fvsP env.find? env.consts))
    (hIdx : ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ))
    (hG : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) :
    ∃ A, A ∈ˢ (univ (d.toLfp.w ψ) : V) ∧
      AccTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) d.toLfp.N (d.toLfp.idx ψ ρp)
        (d.toLfp.holeOp ψ ρp) A := by
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv_gen hrun
  obtain ⟨cvTa0', fvsP', rest', holes', hcv0', hop0', hholes', hder⟩ :=
    checkBlockPositivity_derivM mp.base2.wf hrun
      (fun cv h => (mp.base2.wf _ (List.mem_of_find?_eq_some
        (hcore.1 0 cv (by rwa [List.head?_eq_getElem?] at h)).1)).1)
      (fun c cs hc j cA hj => by
        have hck : c < d.k := by rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hc).1
        rw [hctorsAs c hck] at hc
        obtain rfl := Option.some.inj hc
        exact (hclosed c j cA hj).1)
  rw [hcv0] at hcv0'
  obtain rfl := Option.some.inj hcv0'
  rw [hop0] at hop0'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using hop0'
  rw [hholes] at hholes'
  obtain rfl := Option.some.inj hholes'
  have hin := Rules.RulesInputs.ofSem mp ψ
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  -- every constructor's telescope, accessible
  have hper : ∀ c j, ∃ oa : (Nat → Bool) × (Nat → (Nat → V) → V),
      c < d.toLfp.N → j < d.toLfp.nctors c →
        TeleAccP (d.w ψ) oa.2 0 (d.toLfp.MemberQ ψ) (d.toLfp.accRel ψ ρp) (d.absF ψ c j) ∧
        (∀ l τ τ', TAgr d.k oa.1 l τ τ' → oa.2 l τ = oa.2 l τ') ∧
        (∀ (i : Nat) (G : AnnotTerm), (d.absF ψ c j)[i]? = some G → oa.1 i = true →
          ∀ τ τ', TAgr d.k oa.1 i τ τ' → interp V τ G = interp V τ' G) ∧
        (∀ X X', InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
          InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X' →
          ∀ fs, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
            SpineFit (d.toLfp.frame ψ ρp X') (d.absF ψ c j) fs →
            ∀ e ∈ d.absE ψ c j, interp V (consList fs (d.toLfp.frame ψ ρp X)) e
              = interp V (consList fs (d.toLfp.frame ψ ρp X')) e) := by
    intro c j
    by_cases hcj' : c < d.toLfp.N ∧ j < d.toLfp.nctors c
    · obtain ⟨hc, hj⟩ := hcj'
      have hck : c < d.k := by
        have : c < d.k + d.nInst := hc
        omega
      have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
      obtain ⟨crest, tyN, hcrest, hnfe, ⟨st₀, ks, st₁, hm, -⟩, ⟨ty, hty⟩, -⟩ :=
        hall c (d.ctorsM c) (hctorsAs c hck) j _ hcj
      obtain ⟨crest', ksr, tsr, hcrest', hd, -, hfl⟩ := hder c (d.ctorsM c) (hctorsAs c hck) j _ hcj
      rw [hcrest] at hcrest'
      obtain rfl := Option.some.inj hcrest'
      rw [hnfe] at hd
      obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
      have hcv : (∃ k ∈ ksr.map (·.erase), k.flat = false) →
          ContOk mp ψ (d.w ψ) (p.nestCtx fvsP env.find? env.consts) := by
        rintro ⟨k, hk', hkf⟩
        rcases Bool.eq_false_or_eq_true nst with hn | hn
        · exact hcovk hn fvsP
        · obtain ⟨k', hk'', rfl⟩ := List.mem_map.mp hk'
          rw [NestFieldKind.erase_flat, hfl hn k' hk''] at hkf
          exact nomatch hkf
      obtain ⟨ord, Af, h1, h2, h3, h4⟩ := blockCtorAcc_of_walk mp hin hN hcore hnames hlps hnP
        hnIdxs hk hcv0 hop0 hholes hcj hCf hCb hcrest hm hd hcv hty
        (by rw [hnfs c j _ hcj]; exact hnfe) hs hw (hG c hc j hj)
      exact ⟨(ord, Af), fun _ _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨(fun _ => true, fun _ _ => empty), fun hc hj => absurd ⟨hc, hj⟩ hcj'⟩
  -- the hole operator
  have hok : d.toLfp.HoleTmOk ψ ρp := fun m hm =>
    ⟨⟨(hH.parsLen ψ m hm).trans (hH.lenP ψ).symm, hH.parsSat ψ m hm ρp hs⟩,
      fun _ => (hIdx m (Nat.lt_of_lt_of_le hm hkN)).2⟩
  have happ : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun c hc j hj => blockHolesApplied hH ψ hc hj
  have hres : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro c hc j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  let oa : Nat → Nat → (Nat → Bool) × (Nat → (Nat → V) → V) :=
    fun c j => Classical.choose (hper c j)
  have hoa : ∀ c j, c < d.toLfp.N → j < d.toLfp.nctors c → _ :=
    fun c j => Classical.choose_spec (hper c j)
  exact LfpDatum.accTuple_holeOp hw hok hkN happ hres (fun c j => (oa c j).1)
    (fun c j => (oa c j).2) (fun c hc j hj => (hoa c j hc hj).2.1)
    (fun c hc j hj => (hoa c j hc hj).2.2.1) (fun c hc j hj => (hoa c j hc hj).1)
    (fun c hc j hj => (hoa c j hc hj).2.2.2)

/-- **The hole operator of a flat block is accessible, with one bound of
the level**, from the install's positivity run at the switch off (lane
FLATACC): the derivation's kinds are flat, so no coverage is needed. -/
theorem blockAccTuple_of_run_flat {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true)
    {env : Env} (mp : EnvModelM V μ env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    (hH : BlockHoleFacts mp.base2 d lps)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr)}
    (hrun : ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env
      env.find? env.consts p cvTas ctorsAs = .ok posKs)
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (hinst : d.nInst = 0) (hlenCA : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c))
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true)
    (hnfs : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      d.nfFF c j = (posKs.2.getD c []).getD j default)
    (ψ : Name → Nat) (ρp : Nat → V) (hs : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0)
    (hIdx : ∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ))
    (hG : ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) :
    ∃ A, A ∈ˢ (univ (d.toLfp.w ψ) : V) ∧
      AccTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) d.toLfp.N (d.toLfp.idx ψ ρp)
        (d.toLfp.holeOp ψ ρp) A := by
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  exact blockAccTuple_of_run mp hN hcore hH hrun hnames hlps hnP hnIdxs hk hinst hlenCA hctorsAs
    hclosed hnfs ψ ρp hs hw nofun hIdx hG

/-- **`NestedAccOwed`, PROVED** (lanes ACCMODEL, POSDERIV): the block
theorem with the container rules read at the walk's carrier (coverage)
and the walk context's sort (the block's level). -/
theorem nestedAccOwed {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true) (F : Nat) :
    NestedAccOwed V μ F := by
  intro env mp d lps cvTas p₁ isRec p ctorsAs posKs hN hcore hH hrun hnames hlps hnP hnIdxs hresS hk
    _ hinst hlenCA hctorsAs hclosed hnfs _ hcov ψ ρp hs hw hIdx _ hG
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨mk, hbk, hcovk⟩ := hcov
  have hcore' : BlockHoleCtxFacts mk.base2 d lps cvTas p₁ isRec := by rw [hbk]; exact hcore
  exact blockAccTuple_of_run mk hN hcore' hH hrun hnames hlps hnP hnIdxs hk hinst hlenCA hctorsAs
    hclosed hnfs ψ ρp hs hw (fun _ fvsP => ⟨contCover_of hcovk (fun _ => rfl) rfl,
      nestCtx_sort_eval hresS fvsP env.find? env.consts ψ⟩) hIdx hG

end ConLeche.Model
