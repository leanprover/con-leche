module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Semantics.LitParams
import ConLeche.Model.Rules.InferSoundKit

public section

/-!
# The soundness of the inference rules (task #305, lane S-infer)

One lemma per constructor of `Infer`, at the constructor's grade
(`InferSem m φ g …` dispatches to the establishment motive at `.full`
and the consumption motive at `.io`).  The io lemmas mine
`Model/Steps/InferIO.lean` (the application clause's `appSkip` is
`infer_app_claimIO`'s gated arm: `io_domain_transfer` against the
subject's own hereditary app slot); the full ones `Model/Steps/Infer.lean`.

The λ rule's chain case needs the SHAPE of the body's inferred type
(a ∀ at the inner λ's own annotation, `infer_lam_meta_copy`'s twin
`Infer.lam_shape`), which the master induction reads off the premise
derivation and hands in as `hshape`.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

/-! ## The grade kit

The establishment motive is the stronger one: it concludes the
subject's grading where the consumption motive takes it.  A leaf rule
(`sort`, `fvar`, `const`, `natLit`, `strLit`) establishes outright, so
its lemma is proved once at `InferSemFull` and dispatched. -/

/-- Establishment implies consumption: drop the concluded grading. -/
theorem InferSemFull.toIO {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSemIO m φ d e t := by
  intro hf Δa ea hC hea _
  obtain ⟨hft, hsub, ta, hta, -, hgt, hmem⟩ := h hf hC hea
  exact ⟨hft, hsub, ta, hta, hgt, hmem⟩

/-- A rule that establishes is sound at either grade. -/
theorem InferSemFull.toSem {g : Grade} {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSem m φ g d e t := by
  cases g with
  | full => exact h
  | io => exact h.toIO

/-- **The sort fact at a grade** (`sortSemAt_of_claims`,
`Steps/Infer.lean:798`, at the motives): a subject whose inferred type
reduces to `.sort u` reads into the universe — and is graded, which at
the io grade is the premise and at the full grade the first motive's
conclusion.  The totality factor the run version routes
(`InferReads`) is the existence form of `InferSem`. -/
theorem sortSem_of {g : Grade} {d : Nat} {e s : Expr} {u : Level}
    (hs : InferSem m φ g d e s) (hu : RedSem m φ d s (.sort u))
    (hfe : Frame d e) {Δa : List AnnotTerm} {ea : AnnotTerm}
    (hC : CtxOk m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea)
    (hgr : g = .io → Graded V Δa ea) :
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) := by
  have hstep : Graded V Δa ea ∧ Frame d s ∧ LeavesSub s e ∧
      ∃ sa, denoteMeta m.acval env φ d s = some sa ∧ Graded V Δa sa ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ sa := by
    cases g with
    | full =>
      obtain ⟨hfs, hsub, sa, hsa, hge, hgs, hmem⟩ := hs hfe hC hea
      exact ⟨hge, hfs, hsub, sa, hsa, hgs, hmem⟩
    | io =>
      have hge := hgr rfl
      obtain ⟨hfs, hsub, sa, hsa, hgs, hmem⟩ := hs hfe hC hea hge
      exact ⟨hge, hfs, hsub, sa, hsa, hgs, hmem⟩
  obtain ⟨hge, hfs, hsub, sa, hsa, hgs, hmem⟩ := hstep
  obtain ⟨-, -, ua, hua, -, heq⟩ := hu hfs (hC.of_subset hsub) hsa hgs
  rw [denoteMeta] at hua
  obtain rfl : ua = .sort (u.eval φ) := (Option.some.inj hua).symm
  intro ρ hρ
  refine ⟨hge ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp_sort] at hm
  exact hm

/-- `infer_sort_claim` / `infer_sort_claimIO`. -/
theorem Infer.sort_sound {g : Grade} {d : Nat} {u : Level} :
    InferSem m φ g d (.sort u) (.sort (.succ u)) := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  rw [denoteMeta] at hea
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  have hty : denoteMeta m.acval env φ d (.sort (.succ u))
      = some (.sort (Level.eval φ (.succ u))) := by rw [denoteMeta]
  refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    fun l hl => by simp [Expr.fvarLeaves] at hl,
    _, hty, fun _ _ => ⟨by simp, by simp⟩, fun _ _ => ⟨by simp, by simp⟩, ?_⟩
  intro ρ _
  exact (sound_sort V ρ (u.eval φ)).2

/-- `infer_fvar_claim(IO)`: `CtxOk`'s leaf package. -/
theorem Infer.fvar_sound {g : Grade} {d idx : Nat} {ty : Expr} (h : idx < d) :
    InferSem m φ g d (.fvar idx ty) ty := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  obtain ⟨-, -, tya, Aa, hden, hi, hlink, hokP⟩ := CtxOk.fvar_leaf hC
  rw [denoteMeta] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  simp only [Expr.WScoped] at hws
  have hmem : ∀ l ∈ ty.fvarLeaves, l ∈ (Expr.fvar idx ty).fvarLeaves := by
    intro l hl
    rw [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  refine ⟨⟨hws.2.mono (by omega), hLb (idx, ty) (by simp [Expr.fvarLeaves]),
      fun l hl => hLb l (hmem l hl)⟩,
    hmem, tya, hden, fun _ _ => ⟨by simp, by simp⟩, hokP, ?_⟩
  intro ρ hρ
  rw [interp_bvar, hlink ρ hρ]
  exact hρ (d - 1 - idx) Aa hi

/-- `infer_const_claim(IO)`: `ConstTy` + `LeafValid`. -/
theorem Infer.const_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci) (htower : ci.isTowerEntry = false)
    (hus : us.length = ci.toConstantVal.levelParams.length) :
    InferSem m φ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea hC hea
  rw [denoteMeta, hf] at hea
  dsimp only at hea
  rw [if_pos hus] at hea
  obtain rfl : ea = m.acval n
      (Level.substFn φ ci.toConstantVal.levelParams us) :=
    (Option.some.inj hea).symm
  obtain ⟨ta, hta, hok, hmem⟩ := hin.const_ty d n ci us hf htower hus
  obtain ⟨htc, -, -, htb, -⟩ := m.wf _ (Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact htc
  exact ⟨⟨Expr.WScoped.of_not_hasFvar hnf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact htb,
      Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; cases hl),
    ta, hta, fun ρ _ => ⟨m.acval_wellDenoted n _ ρ, hin.leaf_valid n _ ρ⟩,
    fun ρ _ => hok ρ, fun ρ _ => hmem ρ⟩

/-- `infer_natLit_claim(IO)`: `NatLeafHeads` + `LeafValid`. -/
theorem Infer.natLit_sound (hin : RulesInputs V m φ) {g : Grade} {d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    InferSem m φ g d (.lit (.natVal n)) (.const natName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  rw [denoteMeta, if_pos h] at hea
  obtain rfl : ea = natLitAV
      (m.acval natZeroName (Level.substFn φ [] []))
      (m.acval natSuccName (Level.substFn φ [] [])) n :=
    (Option.some.inj hea).symm
  cases hf : env.find? natName with
  | none =>
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at h
    obtain ⟨⟨h1, -⟩, -⟩ := h
    rw [hf] at h1
    exact nomatch h1
  | some ci =>
    have hlp : ci.toConstantVal.levelParams = [] :=
      natName_levelParams_nil h hf
    have hta : denoteMeta m.acval env φ d (.const natName [])
        = some (m.acval natName (Level.substFn φ [] [])) := by
      rw [denoteMeta, hf]
      dsimp only
      rw [if_pos (by simp [hlp]), hlp]
    have hrow : ∀ ρ : Nat → V,
        WellDenoted V ρ (natLitAV
            (m.acval natZeroName (Level.substFn φ [] []))
            (m.acval natSuccName (Level.substFn φ [] [])) n) ∧
          interp V ρ (natLitAV
              (m.acval natZeroName (Level.substFn φ [] []))
              (m.acval natSuccName (Level.substFn φ [] [])) n)
            ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) :=
      fun ρ => natLit_factsAV (m.acval_wellDenoted _ _ ρ)
        (m.acval_wellDenoted _ _ ρ) (hin.nat_heads h ρ).1
        (hin.nat_heads h ρ).2 n
    exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
        fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      _, hta,
      fun ρ _ => ⟨(hrow ρ).1, AnnotValid_natLitAV (hin.leaf_valid _ _ ρ)
        (hin.leaf_valid _ _ ρ) n⟩,
      fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩,
      fun ρ _ => (hrow ρ).2⟩

/-- `inferStrLitStep_of_claims` (`Steps/StrLit.lean:451`). -/
theorem Infer.strLit_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {s : String} (h : ConLeche.strLitSupported env = true) :
    InferSem m φ g d (.lit (.strVal s)) (.const stringName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  obtain ⟨-, ciS, -, -, -, -, -, -, -, -, -, hfS, -,
    -, -, -, -, -, hlpS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    ConLeche.strLitSupported_inv h
  have hta : denoteMeta m.acval env φ d (.const stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    have hc := denoteMeta_const (acval := m.acval) (φ := φ) (d := d)
      (us := []) hfS (by simp [hlpS])
    rwa [hlpS] at hc
  exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    (fun l hl => by simp [Expr.fvarLeaves] at hl),
    _, hta,
    fun ρ _ => (strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).1,
    fun ρ _ => ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩,
    fun ρ _ => (strLitFacts hin.const_ty hin.leaf_valid hin.nat_heads h hea ρ).2⟩

/-- `infer_forallE_claim(IO)` (`Steps/Infer.lean:254`, `InferIO.lean:339`):
the two sort facts (`sortSemAt_of_claims`'s content) and the bit law. -/
theorem Infer.forallE_sound (_hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {ty body s bs : Expr} {u v : Level} {mb : BinderMeta}
    (hs : InferSem m φ g d ty s) (hu : RedSem m φ d s (.sort u))
    (hbs : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bs)
    (hv : RedSem m φ (d + 1) bs (.sort v))
    (hz : Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.forallE ty body mb) (.sort (.imax u v)) := by
  have main : ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
      Frame d (.forallE ty body mb) →
      CtxOk m φ d Δa (.forallE ty body mb) →
      denoteMeta m.acval env φ d (.forallE ty body mb) = some ea →
      (g = .io → Graded V Δa ea) →
      Frame d (.sort (.imax u v)) ∧
        LeavesSub (.sort (.imax u v)) (.forallE ty body mb) ∧
        ∃ ta, denoteMeta m.acval env φ d (.sort (.imax u v)) = some ta ∧
          Graded V Δa ea ∧ Graded V Δa ta ∧
          ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea ∈ˢ interp V ρ ta := by
    intro Δa ea hfr hC hea hgr
    obtain ⟨hws, hb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbody : Expr.LeavesBounded body := fun l hl =>
      hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwopen, hbopen, hLopen⟩ :=
      frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
    obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denoteMeta_forallE_inv hea
    -- the io grade's premise, split hereditarily
    have hoist : g = .io →
        Graded V Δa tyA ∧ Graded V (tyA :: Δa) baA := fun hg =>
      WellDenotedV.hoist_pi (V := V) (hgr hg)
    have hdomU := sortSem_of hs hu ⟨hws.1, hb.1, hLty⟩ hC.forallE_ty htyA
      (fun hg => (hoist hg).1)
    have hCop : CtxOk m φ (d + 1) (tyA :: Δa)
        (body.instantiate1 (.fvar d ty)) :=
      CtxOk.openS hC.forallE_ty hC.forallE_body htyA
        (fun ρ hρ => (hdomU ρ hρ).1)
    have hcodU := sortSem_of hbs hv ⟨hwopen, hbopen, hLopen⟩ hCop hbaA
      (fun hg => (hoist hg).2)
    have hgea : Graded V Δa (.pi 0 (pwBit φ mb.pw) tyA baA) := by
      intro ρ hρ
      have hdom := hdomU ρ hρ
      have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
          WellDenotedV V (cons x ρ) baA ∧
            interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
        fun x hx => hcodU (cons x ρ) (Sat_cons V hρ hx)
      refine ⟨?_, ?_⟩
      · rw [WellDenoted_pi]
        exact ⟨hdom.1.1, fun x hx => (hcod x hx).1.1⟩
      · rw [AnnotValid_pi]
        refine ⟨hdom.1.2, fun x hx => (hcod x hx).1.2, ?_⟩
        intro hbit x hx
        exact pwBit_zero_mem_univZero hz hbit (hcod x hx).2
    refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
        fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      _, by rw [denoteMeta], hgea, fun _ _ => ⟨by simp, by simp⟩, ?_⟩
    intro ρ hρ
    have hdom := hdomU ρ hρ
    have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
        WellDenoted V (cons x ρ) baA ∧
          interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
      fun x hx =>
        ⟨(hcodU (cons x ρ) (Sat_cons V hρ hx)).1.1,
          (hcodU (cons x ρ) (Sat_cons V hρ hx)).2⟩
    have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
      hdom.1.1 (fun x hx => (hcod x hx).1) hdom.2
      (fun x hx => (hcod x hx).2)
    have hzag : pwBit φ mb.pw = 0 ↔ v.eval φ = 0 := by
      rw [← hz]; exact pwBit_zeronessOf φ v
    have hbridge :
        interp V ρ (.pi 0 (pwBit φ mb.pw) tyA baA)
          = interp V ρ (.pi (u.eval φ) (v.eval φ) tyA baA) := by
      rw [interp_pi, interp_pi]
      exact piR_zero_agree hzag fun x _ => rfl
    rw [hbridge]
    exact hrow.2
  cases g with
  | full =>
    intro hfr Δa ea hC hea
    exact main hfr hC hea (fun hg => by simp at hg)
  | io =>
    intro hfr Δa ea hC hea hge
    obtain ⟨hft, hsub, ta, hta, -, hgt, hmem⟩ := main hfr hC hea (fun _ => hge)
    exact ⟨hft, hsub, ta, hta, hgt, hmem⟩

/-- `infer_lam_claim(IO)` (`Steps/Infer.lean:358`, `InferIO.lean:456`):
the fibre regime fact from the leaf sort run or, at a chain node, from
the copied annotation (`piR_zero_mem_univZero`). -/
theorem Infer.lam_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {ty body s bt btt : Expr} {u v : Level} {mb : BinderMeta}
    (hs : g = .full → InferSemFull m φ d ty s)
    (hu : g = .full → RedSem m φ d s (.sort u))
    (hbt : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bt)
    (hshape : ∀ tyI bI mbI, body = .lam tyI bI mbI →
      ∃ btI, bt = .forallE (tyI.instantiate1 (.fvar d ty)) btI mbI)
    (hchain : ∀ pwI, body.lamPw = some pwI → mb.pw = pwI)
    (hbtt : body.lamPw = none → InferSemIO m φ (d + 1) bt btt)
    (hv : body.lamPw = none → RedSem m φ (d + 1) btt (.sort v))
    (hz : body.lamPw = none → Level.zeronessOf v = mb.pw) :
    InferSem m φ g d (.lam ty body mb) (.forallE ty (bt.abstract1 d) mb) := by
  sorry

/-- `infer_app_claim` / `infer_app_claimIO`'s kept arm
(`Steps/Infer.lean:842`, `InferIO.lean:609`). -/
theorem Infer.app_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {f a tf ty body ta : Expr} {mt : BinderMeta}
    (htf : InferSem m φ g d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hta : InferSem m φ g d a ta) (hd : DefEqSem m φ d ta ty) :
    InferSem m φ g d (.app f a) (body.instantiate1 a) := by
  sorry

/-- **The io licence** (`infer_app_claimIO`'s gated arm): the skipped
membership from the subject's own hereditary app slot,
`io_domain_transfer` + `piR_dom_unique` at a bit pinned positive by
`pwBit_ne_zero_of_isNever`. -/
theorem Infer.appSkip_sound (hin : RulesInputs V m φ) {d : Nat}
    {f a tf ty body : Expr} {mt : BinderMeta}
    (htf : InferSemIO m φ d f tf) (hw : RedSem m φ d tf (.forallE ty body mt))
    (hnev : mt.pw.isNever = true) :
    InferSemIO m φ d (.app f a) (body.instantiate1 a) := by
  sorry

/-- `inferProjStep_of_claims` / `inferProjStepIO_of_claims`
(`Steps/ProjRows.lean:71`, `:160`): the tower law's typing clause. -/
theorem Infer.proj_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSem m φ g d pe tpe) (hte : RedSem m φ d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hprop : Level.isEquiv entry.structSort .zero = some true →
      Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        = some true) :
    InferSem m φ g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  sorry

end ConLeche.Model.Rules
