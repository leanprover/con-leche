module

public import Fragment.Read
public import Fragment.Uniq

@[expose] public section

/-!
# Reading a block, continued: the former's and the constructors' sets

The type former's set lies in the type former's type and a
constructor's set in the constructor's type, read in any reader; the
field context agrees between any two readers; and the two facts the
constructor's type supplies beyond well-denotedness — every field's
index expressions fit (`idxFit_of_wd`) and the residual's do
(`hres_of_wd`) — and the motive's typing (`motiveOk_of_mem`).
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

omit [IndLib V] in
/-- Reading the first `n` pushed values. -/
theorem readEnv_consList_take {vs : List V} {n : Nat} (h : n ≤ vs.length) (ρ : Nat → V) :
    readEnv n (consList vs ρ) = vs.take n := by
  have : consList vs ρ = consList (vs.take n) (consList (vs.drop n) ρ) := by
    rw [← consList_append, List.take_append_drop]
  rw [this, readEnv_consList (by simp [h])]

omit [IndLib V] in
/-- Reading `n` pushed values past the first `k`. -/
theorem readEnv_shiftE_consList {vs : List V} {k n : Nat} (h : k + n ≤ vs.length) (ρ : Nat → V) :
    readEnv n (shiftE k 0 (consList vs ρ)) = (vs.drop k).take n := by
  have : consList vs ρ = consList (vs.take k) (consList (vs.drop k) ρ) := by
    rw [← consList_append, List.take_append_drop]
  rw [this, shiftE_consList' (by simp; omega), readEnv_consList_take (by simp; omega)]

namespace IndSpec

variable {S : IndSpec} {M : Name → List Nat → V} {φ : Name → Nat} {env : Env}

/-- The block's result universe at a reader's valuation. -/
theorem Reader.u₀_eq {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ') (hs : S.sort.paramsIn S.lparams = true) :
    S.u₀ (S.lparams.map φ) = Level.eval φ' S.sort := by
  unfold u₀
  exact Level.eval_congr (fun n hn => R.val_ψ n hn) hs

/-- A context of the specification, read in one reader under two base
environments, agrees. -/
theorem Reader.agree_base {M' : Name → List Nat → V} {φ' : Name → Nat}
    (_R : S.Reader (env := env) M φ M' φ') {Γ : List Expr} {k : Nat}
    (hΓ : ∀ i A, Γ[i]? = some A → Expr.Scoped env S.lparams (k + (Γ.length - 1 - i)) A)
    {vs : List V} (hk : vs.length = k) (ρ ρ' : Nat → V) :
    CtxAgree M' M' φ' φ' (consList vs ρ) (consList vs ρ') Γ := by
  intro i A hA ws hws
  have hl := FitsVals_length M' φ' hws
  have hi : i < Γ.length := (List.getElem?_eq_some_iff.mp hA).1
  refine interp_spec (hΓ i A hA) (fun _ _ _ => rfl) (fun _ _ => rfl) fun j hj => ?_
  rw [← consList_append, ← consList_append]
  exact consList_agree_lt j (by simp [hl, hk]; omega)

/-- **The former's set is in the former's type**, read anywhere. -/
theorem Reader.famSet_mem (hS : S.Scoped env) {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ') (ρ : Nat → V) :
    S.famSet M (S.lparams.map φ) ∈ˢ interp M' φ' ρ S.indType := by
  unfold indType
  rw [interp_mkPis, PropWhen.holds_never, R.famSet_eq hS]
  have hagree : CtxAgree M' M' φ' φ' base ρ (S.indices ++ S.params) := by
    refine CtxAgree_append ?_ fun ws hws => ?_
    · have := R.agree_base (Γ := S.params) (k := 0) (fun i A hA => by simpa [nP] using hS.1 i A hA)
        (vs := []) rfl base ρ
      simpa using this
    · have hl := FitsVals_length M' φ' hws
      exact R.agree_base (Γ := S.indices) (k := S.nP)
        (fun t T hT => by have := hS.2.1 t T hT; simpa [nI] using this) (by simpa [nP] using hl) base ρ
  rw [lamCtx_congr₂ hagree (G := fun ρ' =>
      S.Fam M (S.lparams.map φ) (readEnv S.nP (shiftE S.nI 0 ρ')) (readEnv S.nI ρ')) fun vs hvs => by
    have hl := FitsVals_length M' φ' hvs
    have e1 : S.nI = S.indices.length := rfl
    have e2 : S.nP = S.params.length := rfl
    simp only [List.length_append] at hl
    rw [readEnv_shiftE_consList (by omega), readEnv_shiftE_consList (by omega),
      readEnv_consList_take (by omega), readEnv_consList_take (by omega)]]
  refine lamCtx_mem_piCtx M' φ' (fun vs _ => ?_) fun h => nomatch h
  rw [interp_sort, ← R.u₀_eq hS.2.2.1]
  exact S.Fam_mem_univ M _ _ _

/-- **The field context agrees between two readers** once its domains
are well-denoted in one of them (the invariant supplies the index
expressions' fits, and then every domain reads by β in both). -/
theorem ReaderG.agree_fieldCtx (hS : S.Scoped env) {M₁ M₂ : Name → List Nat → V} {φ₁ φ₂ : Name → Nat}
    (R₁ : S.ReaderG (env := env) M φ M₁ φ₁) (R₂ : S.ReaderG (env := env) M φ M₂ φ₂)
    {ps : List V} {ρ₁ ρ₂ : Nat → V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps) :
    ∀ {fields : List Field},
      (∀ i f, fields[i]? = some f → S.fieldScoped env (fields.length - 1 - i) f) →
      CtxWD M₂ φ₂ (consList ps ρ₂) (S.fieldCtx fields) →
      CtxAgree M₁ M₂ φ₁ φ₂ (consList ps ρ₁) (consList ps ρ₂) (S.fieldCtx fields)
  | [], _, _ => fun i A hA => by simp [fieldCtx] at hA
  | f :: rest, hsc, hwd => by
    have hsc' : ∀ i f', rest[i]? = some f' → S.fieldScoped env (rest.length - 1 - i) f' := by
      intro i f' hf'
      have := hsc (i + 1) f' (by simpa using hf')
      simpa [Nat.sub_sub, Nat.add_comm] using this
    simp only [fieldCtx] at hwd ⊢
    rw [CtxWD_cons] at hwd
    have ih := R₁.agree_fieldCtx hS R₂ (ρ₁ := ρ₁) hps hp hsc' hwd.1
    refine CtxAgree.of_cons ih fun vs hvs => ?_
    have hvs₂ := (FitsVals_congr₂ ih).mp hvs
    have hfit := (R₂.fits_fieldCtx hS hsc' hps hp hwd.1 (vs := vs)).1.mp hvs₂
    have hl := S.FitsFields_length M _ hfit
    have hf : S.fieldScoped env rest.length f := by have := hsc 0 f rfl; simpa using this
    obtain ⟨hidx, hread₂⟩ := R₂.fieldDom_wd hS hf hl hps hp (hwd.2 vs hvs₂)
    rw [hread₂, R₁.fieldDom_fit hS hf hl hps hp hidx]

/-- **Every field's index expressions fit**, from the constructor's
type being well-denoted. -/
theorem ReaderG.idxFit_of_wd (hS : S.Scoped env) {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.ReaderG (env := env) M φ M' φ') {c : CtorSpec} (hc : c ∈ S.ctors) {ρ : Nat → V}
    (hwd : WellDenoted M' φ' ρ (S.ctorType c)) {ps : List V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps) :
    CtxWD M' φ' (consList ps ρ) (S.fieldCtx c.fields) ∧
    ∀ fs, S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
        (S.Mem M (S.lparams.map φ)) ps c.fields fs →
      (FitsVals M' φ' (consList ps ρ) (S.fieldCtx c.fields) fs) ∧
      (∀ k f, c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
        IdxFitAt S M φ ps (earlier fs k) f) ∧
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
        (S.idxVals M (S.lparams.map φ) (consList fs (envP ps)) c.idx) := by
  unfold ctorType at hwd
  rw [WellDenoted_mkPis] at hwd
  obtain ⟨hctx, hbody⟩ := hwd
  obtain ⟨hpar, hfld⟩ := CtxWD_append' hctx
  have hp' : FitsVals M' φ' ρ S.params ps := (R.fits_params hS).mpr hp
  have hwdF := hfld ps hp'
  refine ⟨hwdF, fun fs hfit => ?_⟩
  have hsc := (hS.2.2.2.1 c hc).1
  have hfs := (R.fits_fieldCtx hS hsc hps hp hwdF (vs := fs)).1.mpr hfit
  refine ⟨hfs, (R.fits_fieldCtx hS hsc hps hp hwdF).2 hfit, ?_⟩
  have hl := S.FitsFields_length M _ hfit
  have hb := (hbody (fs ++ ps) ((FitsVals_append M' φ' (by rw [hl, S.length_fieldCtx])).mpr
    ⟨hp', hfs⟩)).1
  rw [consList_append] at hb
  have := (R.famAt_wd hS (o := c.fields.length) (ρ'' := consList fs (consList ps ρ)) (ps := ps)
    (by rw [← hl, shiftE_consList, readEnv_consList hps]) (hS.2.2.2.1 c hc).2.2.1 hb).2.1
  rwa [R.idxVals_eq (hS.2.2.2.1 c hc).2.2.2 (by simp [hl, hps]; omega)] at this

/-- **A constructor's set is in the constructor's type**, read
anywhere the type is well-denoted. -/
theorem Reader₂.ctorSet_mem (hS : S.Scoped env) {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R₂ : S.Reader₂ (env := env) M φ M' φ') (hfresh : env.find? S.name = none)
    {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) {ρ : Nat → V}
    (hwd : WellDenoted M' φ' ρ (S.ctorType c)) (hnr : S.NoRecDep)
    (hb : ∀ ps, FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      S.DomsBounded M (S.lparams.map φ) ps)
    (hcb : ∀ ps, FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps →
      S.ContInBound M (S.lparams.map φ) ps) :
    S.ctorSet M (S.lparams.map φ) j c ∈ˢ interp M' φ' ρ (S.ctorType c) := by
  have R := R₂.R
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have R₁ := S.reader₁ (M := M) (φ := φ) hfresh R.good
  have hwd' := hwd
  unfold ctorType at hwd' ⊢
  rw [WellDenoted_mkPis] at hwd'
  obtain ⟨hctx, hbody⟩ := hwd'
  obtain ⟨hpar, hfld⟩ := CtxWD_append' hctx
  rw [interp_mkPis, R.pw_holds hS.2.2.1]
  unfold ctorSet
  -- from the block's own reading to this one
  have hagree : CtxAgree (S.M₁ M) M' (S.ψ (S.lparams.map φ)) φ' base ρ
      (S.fieldCtx c.fields ++ S.params) := by
    refine CtxAgree_append ?_ fun ps hps₁ => ?_
    · intro i A hA vs hvs
      have hl := FitsVals_length _ _ hvs
      have hi : i < S.params.length := (List.getElem?_eq_some_iff.mp hA).1
      have h1 := R₁.read (ps := []) (ρ := base) (hS.1 i A hA) (vs := vs)
        (by simp only [hl, List.length_drop, List.length_nil, Nat.add_zero, nP]; omega)
      have h2 := R.read (ps := []) (ρ := ρ) (hS.1 i A hA) (vs := vs)
        (by simp only [hl, List.length_drop, List.length_nil, Nat.add_zero, nP]; omega)
      simp only [consList_nil] at h1 h2
      rw [h1, h2]
    · have hp := (R₁.fits_params hS).mp hps₁
      have hpsl : ps.length = S.nP := by have := FitsVals_length _ _ hps₁; simpa [nP] using this
      have := R₁.agree_fieldCtx hS R hpsl hp (hS.2.2.2.1 c hcm).1
        (hfld ps ((R.fits_params hS).mpr hp)) (ρ₁ := base)
      simpa [envP] using this
  rw [lamCtx_congr₂ hagree (G := fun ρ' => S.ctorVal (S.lparams.map φ) j (readEnv c.fields.length ρ'))
    fun vs hvs => by
    have hl := FitsVals_length _ _ hvs
    simp only [List.length_append, S.length_fieldCtx] at hl
    rw [readEnv_consList_take (by omega), readEnv_consList_take (by omega)]]
  refine lamCtx_mem_piCtx M' φ' (fun vs hvs => ?_) fun hz vs hvs => ?_
  -- the values: fields over parameters (for both the membership and,
  -- at a proposition, the fibre being a truth value)
  all_goals
    have hlv := FitsVals_length M' φ' hvs
    obtain ⟨fs, ps, rfl, hlf⟩ : ∃ fs ps, vs = fs ++ ps ∧ fs.length = (S.fieldCtx c.fields).length := by
      refine ⟨vs.take (S.fieldCtx c.fields).length, vs.drop (S.fieldCtx c.fields).length,
        (List.take_append_drop _ _).symm, ?_⟩
      simp at hlv; simp [hlv]
    obtain ⟨hps₁, hfs₁⟩ := (FitsVals_append M' φ' hlf).mp hvs
    have hp := (R.fits_params hS).mp hps₁
    have hpsl : ps.length = S.nP := by have := FitsVals_length _ _ hps₁; simpa [nP] using this
    obtain ⟨hwdF, hall⟩ := R.idxFit_of_wd hS hcm hwd hpsl hp
    have hfit := (R.fits_fieldCtx hS (hS.2.2.2.1 c hcm).1 hpsl hp hwdF (vs := fs)).1.mp hfs₁
    have hlf' : fs.length = c.fields.length := by rw [hlf, S.length_fieldCtx]
    have hbody' := (hbody (fs ++ ps) hvs).1
    rw [consList_append] at hbody' ⊢
    rw [(R.famAt_wd hS (o := c.fields.length) (ρ'' := consList fs (consList ps ρ)) (ps := ps)
      (by rw [← hlf', shiftE_consList, readEnv_consList hpsl]) (hS.2.2.2.1 c hcm).2.2.1 hbody').2.2,
      R.idxVals_eq (hS.2.2.2.1 c hcm).2.2.2 (by simp [hlf', hpsl]; omega)]
  · rw [readEnv_consList hlf']
    exact S.ctorVal_mem_Fam M _ hc hfit hnr (hb ps hp) (hcb ps hp)
  · have := S.Fam_mem_univ M (S.lparams.map φ) ps (S.idxVals M (S.lparams.map φ) (consList fs (envP ps)) c.idx)
    rwa [(S.z_iff _).mp hz] at this

/-- **The motive's typing**: a member of the motive's type sends
fitting indices and a member of the fibre into the elimination
universe. -/
theorem Reader.motiveOk_of_mem (hS : S.Scoped env) {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ') {ps : List V} {ρ : Nat → V} {m : V}
    (hps : ps.length = S.nP) (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hm : m ∈ˢ interp M' φ' (consList ps ρ) S.motiveTy) :
    ∀ is, FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices is →
      ∀ t, t ∈ˢ S.Fam M (S.lparams.map φ) ps is →
        appList m (is.reverse ++ [t]) ∈ˢ (univ (Level.eval φ' S.ℓ) : V) := by
  intro is his t ht
  rw [R.read_motiveTy hS hps hp] at hm
  have hl : is.length = S.nI := by have := FitsVals_length M _ his; simpa [nI] using this
  have := appList_mem_of_piCtx M _ hm his
  rw [readEnv_consList hl] at this
  rw [appList_append, appList_cons, appList_nil]
  exact app_mem_piSet this ht

end IndSpec

end Fragment
