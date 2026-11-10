module

public import ConLeche.Model.Modular.RestrictBase

public section

/-!
# A context's recursor rules and projection entries, read from their sources

The fourth part of `ctxModel` (`Model/Modular/Restrict.lean`): `RecRules` and `TowerOk` at the
context.  A recursor and a structure are inductive kinds, so the context stores its source's
copy; what a rule's law reads (the recursor's type, the rule's right-hand side and nested pins,
the constructor, its type and its family) and what an entry's law reads (the structure, its
constructor and their types, the entry's body) is read alike from the source (`CtxRead.scope`,
`CtxRead.deep`), so each law is the source's, transported (`RuleAg`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Semantics
open ConLeche.Term SetTheory

universe w

/-! ## One rule's law across an agreement -/

theorem constsResolve_openRev {E : Env} {e : Expr} (h : e.constsResolve E = true) :
    ∀ d n : Nat, (openRev d n e).constsResolve E = true := by
  intro d n
  induction n with
  | zero => exact h
  | succ n ih =>
    show ((openRev d n e).instantiate1 (.fvar (d + n) (.sort .zero)) 0).constsResolve E = true
    exact Expr.constsResolve_instantiate1 (by simp [Expr.constsResolve]) 0 ih

/-- A constructor's family reads the lookup at the name its type concludes in, where the two
copies there are alike. -/
theorem ctorFamily_alike {f g : Name → Option ConstantInfo} {cvj : ConstantVal}
    (h : ∀ T us, cvj.type.piResult.getAppFn = .const T us → LookAlike (f T) (g T)) :
    ctorFamily f cvj = ctorFamily g cvj := by
  unfold ctorFamily
  split
  · next T us hh =>
    obtain ⟨a, b, e1, e2, hab⟩ := h T us hh
    rw [e1, e2]
    rcases hab with rfl | ⟨-, h1, h2⟩
    · rfl
    · cases a <;> cases b <;> simp_all [ConstantInfo.isStmtKind]
  · rfl

section Law

variable {V : Type w} [SetTheory V] {env env' : Env} {m : EnvModel V env} {m' : EnvModel V env'}
  {φ : Name → Nat} {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rl : RecRule}

/-- What one rule's law reads, alike on both sides (the recursor and the rule the same). -/
structure RuleAg (m : EnvModel V env) (m' : EnvModel V env') (φ : Name → Nat) (n : Name)
    (cv : ConstantVal) (rP : Nat) (rl : RecRule) : Prop where
  hty : ∀ us : List Level,
    denote m'.acval env' φ 0 (cv.type.instantiateLevelParams cv.levelParams us)
      = denote m.acval env φ 0 (cv.type.instantiateLevelParams cv.levelParams us)
  hrhs : ∀ us : List Level,
    denote m'.acval env' φ 0 ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
      = denote m.acval env φ 0 ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
  hpins : ∀ lvls pins, RecRule.fire rl = .nested lvls pins → ∀ (i : Nat) (us : List Level),
    denote m'.acval env' φ rP
        (openRev 0 rP ((pins.getD i default).instantiateLevelParams cv.levelParams us))
      = denote m.acval env φ rP
        (openRev 0 rP ((pins.getD i default).instantiateLevelParams cv.levelParams us))
  hleaf : m'.acval n = m.acval n
  hcleaf : m'.acval (RecRule.ctor rl) = m.acval (RecRule.ctor rl)
  hctor : ∀ cvj cnP cnF, env'.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
    env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF)
  hcty : ∀ cvj cnP cnF, env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
    ∀ usj : List Level,
      denote m'.acval env' φ 0 (cvj.type.instantiateLevelParams cvj.levelParams usj)
        = denote m.acval env φ 0 (cvj.type.instantiateLevelParams cvj.levelParams usj)
  hfam : ∀ cvj cnP cnF, env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
    ∀ us : List Level, FamNZ (V := V) m'.acval env' φ cvj us = FamNZ (V := V) m.acval env φ cvj us

theorem recRuleExtra_ag (r : RuleAg m m' φ n cv rP rl)
    (hX : RecRuleExtra m φ n cv mI rP isK rl) : RecRuleExtra m' φ n cv mI rP isK rl := by
  intro us hus TVa hTVa
  rw [r.hty us] at hTVa
  obtain ⟨hK, hC⟩ := hX us hus TVa hTVa
  refine ⟨fun hk => ?_, fun cvj cnP cnF hfc => ?_⟩
  · obtain ⟨hnf, hK'⟩ := hK hk
    refine ⟨hnf, fun Ra hRa ρ xs a restR hxs hfit hw => ?_⟩
    rw [r.hrhs us] at hRa
    rw [r.hleaf]
    exact hK' Ra hRa ρ xs a restR hxs hfit hw
  · have hfcj := r.hctor cvj cnP cnF hfc
    obtain ⟨har, hrest⟩ := hC cvj cnP cnF hfcj
    refine ⟨har, fun hk => ?_⟩
    obtain ⟨hS, hT, hPU⟩ := hrest hk
    rw [r.hfam cvj cnP cnF hfcj]
    refine ⟨hS, fun hne usj hlj TVja hTVja ρ xs ys restR restC hxs hys hfR hfC hwx hwy hnept => ?_,
      fun usj hlj hsj TVja hTVja => ?_⟩
    · rw [r.hcty cvj cnP cnF hfcj usj] at hTVja
      rw [r.hcleaf] at hfR hnept ⊢
      obtain ⟨usj₂, ys₂, TVja₂, restC₂, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        hT hne usj hlj TVja hTVja ρ xs ys restR restC hxs hys hfR hfC hwx hwy hnept
      exact ⟨usj₂, ys₂, TVja₂, restC₂, h1, h2, by rw [r.hcty cvj cnP cnF hfcj usj₂]; exact h3,
        h4, h5, h6, h7, h8⟩
    · rw [r.hcty cvj cnP cnF hfcj usj] at hTVja
      obtain ⟨hP, hU⟩ := hPU usj hlj hsj TVja hTVja
      rw [r.hcleaf]
      refine ⟨hP, fun ρ xs ys restR restC hxs hys hfR hfC hwx hwy hA hB hD =>
        hU ρ xs ys restR restC hxs hys hfR hfC hwx hwy hA ?_ hD⟩
      intro lvls pins hfire hpt i hi vpa hvpa
      exact hB lvls pins hfire hpt i hi vpa (by rw [r.hpins lvls pins hfire i us]; exact hvpa)

theorem recRuleLaw_ag (r : RuleAg m m' φ n cv rP rl)
    (hL : RecRuleLaw m φ n cv mI rP isK rl) : RecRuleLaw m' φ n cv mI rP isK rl := by
  obtain ⟨hle, hmain, hX⟩ := hL
  refine ⟨hle, fun us hus => ?_, recRuleExtra_ag r hX⟩
  obtain ⟨Ra, hRa, hok, hpins, hlaw⟩ := hmain us hus
  refine ⟨Ra, by rw [r.hrhs us]; exact hRa, hok, fun lvls pins hfire i hi => ?_,
    fun cvj cnP cnF hfc usj ρ xs ys TVa TVja restR restC hxs hys hlj hsj hwy hpt hTVa hTVja
      hfR hfC => ?_⟩
  · obtain ⟨vpa, hvpa, hg⟩ := hpins lvls pins hfire i hi
    refine ⟨vpa, by rw [r.hpins lvls pins hfire i us]; exact hvpa,
      fun ρ zs TVa restR hz hw hTVa hfit => ?_⟩
    rw [r.hty us] at hTVa
    exact hg ρ zs TVa restR hz hw hTVa hfit
  · have hfcj := r.hctor cvj cnP cnF hfc
    rw [r.hty us] at hTVa
    rw [r.hcty cvj cnP cnF hfcj usj] at hTVja
    rw [r.hcleaf] at hfR hpt ⊢
    rw [r.hleaf]
    exact hlaw cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxs hys hlj hsj hwy hpt hTVa
      hTVja hfR hfC

end Law

namespace CtxSrc

variable {V : Type w} [SetTheory V] {C : Env} {E R : Name → Env}
  {aC : Name → (Name → Nat) → Term} (S : CtxSrc V C E R aC)
include S

/-- A constructor read alike: its family is read alike, so the family's lookup is alike. -/
theorem ctorFamily_eq {n x : Name} (hn : (C.find? n).isSome = true)
    (hx : ((R n).find? x).isSome = true) {cvj : ConstantVal} {cnP cnF : Nat}
    (hfc : C.find? x = some (.ctorInfo cvj cnP cnF)) :
    ctorFamily C.find? cvj = ctorFamily (E n).find? cvj := by
  have hty := S.deepType hn hx hfc rfl
  exact ctorFamily_alike fun T us hh =>
    S.look hn (Expr.find?_isSome_of_piResult_getAppFn_const hty hh)

/-- **A rule's law reads alike.** -/
theorem ruleAg {φ : Name → Nat} {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool}
    {rules : List RecRule} (hf : C.find? n = some (.recInfo cv mI rP isK rules))
    {rl : RecRule} (hrl : rl ∈ rules) :
    RuleAg (S.m n).base2 S.base φ n cv rP rl := by
  have hn := isSome_of hf
  obtain ⟨hrhsR, hcR, hpinsR⟩ := (S.scopeR hf).2.2.1 cv mI rP isK rules rfl rl hrl
  have htyR := resR (S.scopeR hf).1
  -- the family's reading, where the family is a former the source stores
  have hcfam : ∀ cvj cnP cnF, (E n).find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ cvT caps, ctorFamily (E n).find? cvj = some (cvT, caps) → ∀ us,
        denote aC C φ 0 (cvT.type.instantiateLevelParams cvT.levelParams us)
          = denote (S.m n).base2.acval (E n) φ 0
              (cvT.type.instantiateLevelParams cvT.levelParams us) := by
    intro cvj cnP cnF hfc cvT caps hfam us
    obtain ⟨T, us', hh, hfT⟩ := ctorFamily_find hfam
    have hfcC := S.findC hn hcR hfc rfl
    have hTR : ((R n).find? T).isSome = true :=
      Expr.find?_isSome_of_piResult_getAppFn_const (S.deepType hn hcR hfcC rfl) hh
    exact S.denote_inst hn (S.deepType hn hTR (S.findC hn hTR hfT rfl) rfl) φ 0 _ us
  refine ⟨fun us => S.denote_inst hn htyR φ 0 _ us, fun us => S.denote_inst hn (resR hrhsR) φ 0 _ us,
    fun lvls pins hfire i us => ?_, S.leafSelf hf, S.leaf n hn _ hcR,
    fun cvj cnP cnF hfc => S.findE hn hcR hfc rfl,
    fun cvj cnP cnF hfc usj => S.denote_inst hn (S.deepType hn hcR (S.findC hn hcR hfc rfl) rfl) φ 0 _ usj,
    fun cvj cnP cnF hfc us => ?_⟩
  · have hpR : (pins.getD i default).constsResolve (R n) = true := by
      by_cases hilt : i < pins.length
      · have he : pins.getD i default = pins[i] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]; rfl
        rw [he]
        exact resR (hpinsR lvls pins hfire _ (List.getElem_mem hilt))
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    exact S.denote_eq hn φ rP _ (constsResolve_openRev
      (by rw [Expr.constsResolve_instantiateLevelParams]; exact hpR) 0 rP)
  · have hfcC := S.findC hn hcR hfc rfl
    have hfam := S.ctorFamily_eq hn hcR hfcC
    refine propext ⟨FamNZ.congr hfam (fun cvT caps ta h hta => ?_),
      FamNZ.congr hfam.symm (fun cvT caps ta h hta => ?_)⟩
    · exact (hcfam cvj cnP cnF hfc cvT caps h us).trans hta
    · exact (hcfam cvj cnP cnF hfc cvT caps (hfam ▸ h) us).symm.trans hta

theorem rec_rules (φ : Name → Nat) : RecRules S.base φ := by
  intro n cv mI rP isK rules hf rl hrl
  exact recRuleLaw_ag (S.ruleAg hf hrl) ((S.m n).rec_rules φ n cv mI rP isK rules (S.src_ind hf rfl) rl hrl)

/-! ## The projection entries -/

theorem tower_ok (φ : Name → Nat) : TowerOk S.base φ := by
  refine ⟨fun T tbl ht => ?_, fun T i entry hfP => ?_⟩
  · obtain ⟨-, -, hT⟩ := Env.findTable?_mem ht
    have hR := S.read.self T hT
    have htE : (E T).findTable? T = some tbl := by rw [← S.table_eq hT hR]; exact ht
    obtain ⟨⟨cvT, capsT, hfT, hlT⟩, heta⟩ := ((S.m T).tower_ok φ).table T tbl htE
    have hfTC := S.findC hT hR hfT rfl
    obtain ⟨-, -, -, hind, -⟩ := S.scopeR hfTC
    obtain ⟨hcR, -⟩ := (hind cvT capsT rfl).2 tbl ht
    have hlT' : aC T = (S.m T).base2.acval T := S.leaf T hT T hR
    have hlC' : aC tbl.ctor = (S.m T).base2.acval tbl.ctor := S.leaf T hT _ hcR
    refine ⟨⟨cvT, capsT, hfTC, hlT⟩, fun cv' caps' hf' us hus => ?_⟩
    have hf'E := S.findE hT hR hf' rfl
    obtain ⟨hl1, hl2⟩ := heta cv' caps' hf'E us hus
    refine ⟨fun ρ ts x hlen hfit hmem => ?_, fun he => ?_⟩
    · rw [base_acval, hlT'] at hfit hmem
      rw [base_acval, hlC']
      exact hl1 ρ ts x hlen hfit hmem
    · refine (hl2 he).transport (fun cvC' nPc nFc h₂ => ?_) (fun cvC' nPc nFc TCa h hTCa => ?_)
        (by rw [base_acval, hlT']) (fun _ _ _ => rfl)
      · exact S.findE hT hcR h₂ rfl
      · exact (S.denote_inst hT (S.deepType hT hcR (S.findC hT hcR h rfl) rfl) φ 0 _ us).trans hTCa
  · obtain ⟨tbl, ht, hi, rfl⟩ := Env.findProj?_some hfP
    obtain ⟨-, hsn, hT⟩ := Env.findTable?_mem ht
    have hR := S.read.self T hT
    have hfPE : (E T).findProj? T i = some (tbl.entry i) := by
      rw [← S.findProj_eq hT hR]; exact hfP
    obtain ⟨h1, h2, h3, ⟨cvT, capsT, hfT, hlT⟩, cvC, hfC, hlC, hlaw⟩ :=
      ((S.m T).tower_ok φ).entry T i _ hfPE
    have hfTC := S.findC hT hR hfT rfl
    obtain ⟨-, -, -, hind, -⟩ := S.scopeR hfTC
    obtain ⟨hcR, hbR⟩ := (hind cvT capsT rfl).2 tbl ht
    have hctor : (tbl.entry i).ctor = tbl.ctor := rfl
    rw [hctor] at hfC
    have hfCC := S.findC hT hcR hfC rfl
    have hsnT : (tbl.entry i).structName = T := hsn
    have hTy : ∀ (cv' : ConstantVal) (caps' : IndCaps), (E T).find? T = some (.indInfo cv' caps') →
        ∀ us, denote aC C φ 0 (cv'.type.instantiateLevelParams cv'.levelParams us)
          = denote (S.m T).base2.acval (E T) φ 0 (cv'.type.instantiateLevelParams cv'.levelParams us) :=
      fun cv' caps' h us => S.denote_inst hT (S.deepType hT hR (S.findC hT hR h rfl) rfl) φ 0 _ us
    have hCy : ∀ us, denote aC C φ 0 (cvC.type.instantiateLevelParams cvC.levelParams us)
        = denote (S.m T).base2.acval (E T) φ 0 (cvC.type.instantiateLevelParams cvC.levelParams us) :=
      fun us => S.denote_inst hT (S.deepType hT hcR hfCC rfl) φ 0 _ us
    have hlT' : aC T = (S.m T).base2.acval T := S.leaf T hT T hR
    have hlC' : aC tbl.ctor = (S.m T).base2.acval tbl.ctor := S.leaf T hT _ hcR
    have hsz := ((S.m T).base2.wf.table (by
      rw [← S.table_eq hT hR]; exact ht)).2.1
    have hbmem : tbl.bodies.getD i default ∈ tbl.bodies.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsz]; exact hi)]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
    have hbody : ∀ us, denote aC C φ 0 (projTele (tbl.numParams + 1)
          ((tbl.bodies.getD i default).instantiateLevelParams tbl.levelParams us))
        = denote (S.m T).base2.acval (E T) φ 0 (projTele (tbl.numParams + 1)
          ((tbl.bodies.getD i default).instantiateLevelParams tbl.levelParams us)) := fun us =>
      S.denote_eq hT φ 0 _ (by
        rw [projTele_constsResolve, Expr.constsResolve_instantiateLevelParams]
        exact resR (hbR _ hbmem))
    have hguard : ∀ us, TowerGuardAt S.base φ (tbl.entry i) us cvC →
        TowerGuardAt (S.m T).base2 φ (tbl.entry i) us cvC := fun us =>
      TowerGuardAt.mono (by rw [hsnT, hfT, hfTC])
        (fun cv' caps' t h hrd => by
          rw [hsnT] at h; rw [base_acval, hTy cv' caps' h us]; exact hrd)
        (fun t hrd => by rw [base_acval, hCy us]; exact hrd)
    refine ⟨h1, h2, h3, ⟨cvT, capsT, hfTC, hlT⟩, cvC, by rw [hctor]; exact hfCC, hlC,
      fun us hus => ?_⟩
    · obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
      refine ⟨⟨Ta, by rw [base_acval]; exact (hbody us).trans hTa,
        fun ρ vs x rest hvs hw hne hwx hmem hpeel hg => ?_⟩,
        ⟨TCa, by rw [base_acval]; exact (hCy us).trans hTCa, fun ρ ys rest hys hw hfit hne => ?_⟩⟩
      · rw [base_acval, hlT'] at hw hne hmem
        exact hA ρ vs x rest hvs hw hne hwx hmem hpeel (hg.imp_left (hguard us))
      · rw [base_acval, hctor, hlC'] at hw hne ⊢
        exact hB ρ ys rest hys hw hfit hne

end CtxSrc

end ConLeche.Model.Modular
