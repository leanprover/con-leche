import Setlec.Kernel.Checker
import Setlec.Model.Annotate
import Setlec.Model.BasisInstall

/-!
# Consistency of the checker

The headline results:

* `checkDecl_sound`: checking a declaration preserves having a model.
* `checkDecls_sound`: every environment accepted by `checkDecls` has a
  set-theoretic model (`EnvModel`).

Both are parametric in a model `V` of the target set theory: assuming
Tarski–Grothendieck set theory is consistent (i.e. a `SetTheory` instance
exists), no accepted environment can prove `False` — the concrete
"no proof of `Empty` is accepted" corollary lands once `Empty` is in the
supported fragment.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

private theorem find?_none_ne {env : Env} {n : Name} (h : env.find? n = none) :
    ∀ c ∈ env.consts, c.name ≠ n := by
  intro c hc
  have := List.find?_eq_none.mp h c hc
  simpa using this

/-- The sibling-availability data `BasisBlocks` preservation needs when
extending by one (fresh) constant: if the constant is a recursor-kind
record, the members of its block are already stored. -/
private def SibFinds (env : Env) (c₀ : ConstantInfo) : Prop :=
  ∀ cv nP nM nm ni rules, c₀ = .recInfo cv nP nM nm ni rules →
    (c₀.name = eqName.str "rec" →
      env.find? eqName = some eqA ∧ env.find? eqReflName = some eqReflA) ∧
    (c₀.name = natName.str "rec" →
      env.find? natName = some natA ∧
      env.find? natZeroName = some natZeroA ∧
      env.find? natSuccName = some natSuccA) ∧
    (c₀.name = psigmaName.str "rec" →
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA) ∧
    (c₀.name = punitName.str "rec" →
      env.find? punitName = some punitA ∧
      env.find? punitUnitName = some punitUnitA)

private theorem BasisBlocks.cons {env : Env} {c₀ : ConstantInfo}
    (hb : BasisBlocks env) (hfind' : env.find? c₀.name = none)
    (hsib : SibFinds env c₀) :
    BasisBlocks (⟨c₀ :: env.consts⟩ : Env) := by
  have keep : ∀ {s : Name} {X : ConstantInfo}, env.find? s = some X →
      Env.find? ⟨c₀ :: env.consts⟩ s = some X := by
    intro s X hs
    rw [Env.find?_cons_of_isSome hfind' (by rw [hs]; rfl)]
    exact hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨hs, -, -, -⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.1 cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, hs, -, -⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2, h3⟩ := hs hn
      exact ⟨keep h1, keep h2, keep h3⟩
    · next hn =>
      obtain ⟨h1, h2, h3⟩ := hb.right.left cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2, keep h3⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, hs, -⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right.left cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, -, hs⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right.right cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2⟩

/-- Inversion for `checkConstantVal`. -/
private theorem checkConstantVal_inv {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal env cv = .ok cv') :
    env.find? cv.name = none ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      annotate env 0 cv.type = .ok type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      inferType env 0 type = .ok stype ∧
      ensureSort env 0 stype = .ok u ∧
      cv' = { cv with type := type } := by
  simp only [checkConstantVal, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  cases hann : annotate env 0 cv.type with
  | error e => rw [hann] at h; exact nomatch h
  | ok type =>
  rw [hann] at h
  try dsimp only at h
  by_cases htp : type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  cases hst : inferType env 0 type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSort env 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, hnd, hlb, by simpa using hif, type, stype, u, rfl, htp, htr, hst, hsort,
    h.symm⟩

/-- The common model-extension argument, for a new constant `c₀` with an
annotated, checked type and value. -/
private theorem extend_model {env : Env} (m : EnvModel V env)
    {name : Name} {lps : List Name} {type value : Expr}
    (hfind' : env.find? name = none)
    (htp : type.allLevelParamsDefined lps = true)
    (htf : type.hasFvar = false)
    (htr : type.constsResolve env = true)
    (htb : type.looseBVarsBounded 0 = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hvf : value.hasFvar = false)
    (hvr : value.constsResolve env = true)
    (hvb : value.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value)
    (c₀ : ConstantInfo)
    (hc₀cv : c₀.toConstantVal = ⟨name, lps, type⟩)
    (hc₀name : c₀.name = name)
    (hc₀val : ∀ cv2 value2, c₀ = ConstantInfo.defnInfo cv2 value2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀nb : c₀.isBasis = false) :
    Nonempty (EnvModel V ⟨c₀ :: env.consts⟩) := by
  have hfresh := find?_none_ne hfind'
  obtain ⟨val', hval'⟩ : ∃ val' : ConstVal V, val' = fun n ψ =>
      if n = name
      then (interpClosed V m.val env ψ value).getD SetTheory.empty
      else m.val n ψ := ⟨_, rfl⟩
  have hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ := by
    intro n hn ψ
    have : n ≠ name := by
      intro heq; rw [heq, hfind'] at hn; simp at hn
    simp [hval', this]
  have hc₀fresh : env.find? c₀.name = none := by rw [hc₀name]; exact hfind'
  have htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := val') hc₀fresh hres]
    exact interp_cval_ext hagree e 0 (rho0 V)
  have hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ 0 (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hc₀fresh e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm) e 0 (rho0 V) ha
  have hwf' : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons m.wf ?_
    rw [ConstWF, hc₀cv]
    refine ⟨htf, htp, Expr.constsResolve_mono htr, htb, ?_, ?_⟩
    · intro cv2 value2 heq
      obtain ⟨rfl, rfl⟩ := hc₀val cv2 value2 heq
      exact ⟨hvf, hvp, Expr.constsResolve_mono hvr, hvb⟩
    · intro cv nP nM nm ni rules heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- val_params
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      have hncv : n = name := by rw [← hn, hc₀name]
      subst hncv
      simp only [hval', if_pos rfl]
      have : interpClosed V m.val env ψ₁ value = interpClosed V m.val env ψ₂ value := by
        unfold interpClosed
        refine interp_params_ext m.val_params ?_ value 0 (rho0 V) hvp
        intro p hp
        refine hψ p ?_
        rw [hc₀cv]
        exact hp
      rw [this]
    · next hn =>
      have hne : n ≠ name := by
        intro heq
        rw [heq, hfind'] at hf
        exact nomatch hf
      simp only [hval', if_neg hne]
      exact m.val_params n ci hf ψ₁ ψ₂ hψ
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨v, T, hv, hT, hmem⟩ := hkey ψ
      refine ⟨T, ?_, ?_⟩
      · rw [hc₀cv]
        exact (htrans type htr ψ).trans hT
      · rw [hc₀name]
        simp only [hval', if_pos rfl, hv, Option.getD_some]
        exact hmem
    · obtain ⟨t, ht, hmem⟩ := m.mem_type c hc ψ
      obtain ⟨-, -, hres, -⟩ := m.wf c hc
      refine ⟨t, ?_, ?_⟩
      · rw [htrans c.toConstantVal.type hres ψ]
        exact ht
      · have hne : c.name ≠ name := hfresh c hc
        simp [hval', hne, hmem]
  · -- defn_eq
    intro cv2 value2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · obtain ⟨hcv2, hval2⟩ := hc₀val cv2 value2 heq.symm
      obtain ⟨v, T, hv, -, -⟩ := hkey ψ
      rw [hval2, htrans value hvr ψ, hv, hcv2]
      simp [hval', hv]
    · obtain ⟨-, -, -, -, hvalwf, -⟩ := m.wf _ hmem2
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 rfl
      have := m.defn_eq cv2 value2 hmem2 ψ
      rw [htrans _ hres2 ψ, this]
      have hne : cv2.name ≠ name :=
        hfresh (.defnInfo cv2 value2) hmem2
      simp [hval', hne]
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨?_, ?_⟩
      · rw [hc₀cv]
        exact hAtrans type htr ψ (hAty ψ)
      · intro cv2 value2 heq
        obtain ⟨-, hval2⟩ := hc₀val cv2 value2 heq
        rw [hval2]
        exact hAtrans value hvr ψ (hAval ψ)
    · obtain ⟨-, -, htyres, -, hvalwf, -⟩ := m.wf c hc
      obtain ⟨hA1, hA2⟩ := m.annot_ok c hc ψ
      refine ⟨hAtrans _ htyres ψ hA1, ?_⟩
      intro cv2 value2 heq
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 heq
      exact hAtrans _ hres2 ψ (hA2 cv2 value2 heq)
  · -- ind_ok: the fresh constant is a definition or theorem, so every
    -- inductive-kind lookup still resolves to the old environment, and
    -- the valuation agrees there.
    refine ⟨?_, ?_, ?_, ?_, BasisBlocks.cons m.ind_ok.right.right.right.right
      hc₀fresh (fun cv nP nM nm ni rules heq => by
        rw [heq] at hc₀nb
        simp [ConstantInfo.isBasis] at hc₀nb)⟩
    · intro cv hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : psigmaName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = psigmaName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hlp, hfacts⟩ := m.ind_ok.1 cv hfp
        refine ⟨hlp, fun ψ => ?_⟩
        have hvagree : val' psigmaName ψ = m.val psigmaName ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hfacts ψ
    · intro cv nP nF hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : psigmaMkName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.ctorInfo cv nP nF).name = psigmaMkName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hnP, hnF, hlp, hfacts⟩ := m.ind_ok.right.left cv nP nF hfp
        refine ⟨hnP, hnF, hlp, fun ψ => ?_⟩
        have hvagree : val' psigmaMkName ψ = m.val psigmaMkName ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hfacts ψ
    · intro cv hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : punitName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = punitName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hvagree : val' punitName ψ = m.val punitName ψ := by
          simp [hval', hne]
        rw [hvagree] at hx
        exact m.ind_ok.right.right.left cv hfp ψ x hx
    · intro n ci hfp hbasis
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        rw [hc₀nb] at hbasis
        exact nomatch hbasis
      · next hn =>
        have hne : n ≠ name := by
          intro hcontra
          rw [hcontra, hfind'] at hfp
          exact nomatch hfp
        obtain ⟨hpi, hpv⟩ := m.ind_ok.right.right.right.left n ci hfp hbasis
        refine ⟨hpi, fun ψ => ?_⟩
        have hvagree : val' n ψ = m.val n ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hpv ψ

/-- Extend a model by one pinned basis constant with a hand-supplied
value.  The membership and annotation facts are stated over the *old*
valuation (basis types only mention previously installed constants);
the conclusion exposes the new valuation's equations so block
installation can chain. -/
private theorem extend_basis_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (v₀ : (Name → Nat) → V)
    (hfind' : env.find? ci.name = none)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hnotdefn : ∀ cv2 value2, ci ≠ .defnInfo cv2 value2)
    (hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧ v₀ ψ ∈ˢ T)
    (hparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → v₀ ψ₁ = v₀ ψ₂)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) ci.toConstantVal.type)
    (hnewty : ∀ cv, ci = .indInfo cv → ci.name = psigmaName →
      cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairTyFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewmk : ∀ cv nP nF, ci = .ctorInfo cv nP nF → ci.name = psigmaMkName →
      nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairMkFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewunit : ∀ cv, ci = .indInfo cv → ci.name = punitName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → x = pt)
    (hpin : ci.isBasis = true → ci = pinnedInfo ci.name ∧
      ∀ ψ : Name → Nat, v₀ ψ = pinnedVal V ci.name ψ)
    (hsib : SibFinds env ci) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = v₀ ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hfresh := find?_none_ne hfind'
  obtain ⟨val', hval'⟩ : ∃ val' : ConstVal V, val' = fun n ψ =>
      if n = ci.name then v₀ ψ else m.val n ψ := ⟨_, rfl⟩
  have hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ := by
    intro n hn ψ
    have : n ≠ ci.name := by
      intro hcontra
      rw [hcontra, hfind'] at hn
      exact nomatch hn
    simp [hval', this]
  have htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨ci :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := val') hfind' hres]
    exact interp_cval_ext hagree e 0 (rho0 V)
  have hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨ci :: env.consts⟩ : Env) ψ 0 (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm) e 0 (rho0 V) ha
  have hwf' : EnvWF ⟨ci :: env.consts⟩ := EnvWF.cons m.wf hwf
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- val_params
    intro n ci2 hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      have hn' : n = ci.name := hn.symm ▸ rfl
      subst hn'
      simp only [hval', if_pos rfl]
      exact hparams ψ₁ ψ₂ hψ
    · next hn =>
      have hne : n ≠ ci.name := fun hc => hn (hc ▸ rfl)
      simp only [hval', if_neg hne]
      exact m.val_params n ci2 hf ψ₁ ψ₂ hψ
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨T, hT, hv⟩ := hkey ψ
      refine ⟨T, ?_, ?_⟩
      · rw [htrans _ htyres0 ψ]
        exact hT
      · have : val' c.name ψ = v₀ ψ := by simp [hval']
        rw [this]
        exact hv
    · obtain ⟨T, hT, hv⟩ := m.mem_type c hc ψ
      obtain ⟨-, -, hres, -, -, -⟩ := m.wf c hc
      refine ⟨T, ?_, ?_⟩
      · rw [htrans _ hres ψ]
        exact hT
      · have hne : c.name ≠ ci.name := hfresh c hc ∘ fun h => h
        simp only [hval', if_neg hne]
        exact hv
  · -- defn_eq
    intro cv2 value2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · exact absurd heq.symm (hnotdefn cv2 value2)
    · obtain ⟨-, -, -, -, hvalwf, -⟩ := m.wf _ hmem2
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 rfl
      have := m.defn_eq cv2 value2 hmem2 ψ
      rw [htrans _ hres2 ψ, this]
      have hne : cv2.name ≠ ci.name := by
        have := hfresh (.defnInfo cv2 value2) hmem2
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
      simp [hval', hne]
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨hAtrans _ htyres0 ψ (hAty ψ), ?_⟩
      intro cv2 value2 heq
      exact absurd heq (hnotdefn cv2 value2)
    · obtain ⟨-, -, htyres, -, hvalwf, -⟩ := m.wf c hc
      obtain ⟨hA1, hA2⟩ := m.annot_ok c hc ψ
      refine ⟨hAtrans _ htyres ψ hA1, ?_⟩
      intro cv2 value2 heq
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 heq
      exact hAtrans _ hres2 ψ (hA2 cv2 value2 heq)
  · -- ind_ok
    refine ⟨?_, ?_, ?_, ?_, BasisBlocks.cons m.ind_ok.right.right.right.right
      hfind' hsib⟩
    · intro cv hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨hlp, hfacts⟩ := hnewty cv rfl hn
        refine ⟨hlp, fun ψ => ?_⟩
        have hval'eq : val' psigmaName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq]
        exact hfacts ψ
      · next hn =>
        have hne : psigmaName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = psigmaName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hlp, hfacts⟩ := m.ind_ok.1 cv hfp
        refine ⟨hlp, fun ψ => ?_⟩
        have hval'eq : val' psigmaName ψ = m.val psigmaName ψ := by
          simp [hval', hne]
        rw [hval'eq]
        exact hfacts ψ
    · intro cv nP nF hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨h1, h2, h3, h4⟩ := hnewmk cv nP nF rfl hn
        refine ⟨h1, h2, h3, fun ψ => ?_⟩
        have hval'eq : val' psigmaMkName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq]
        exact h4 ψ
      · next hn =>
        have hne : psigmaMkName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.ctorInfo cv nP nF).name = psigmaMkName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨h1, h2, h3, h4⟩ := m.ind_ok.right.left cv nP nF hfp
        refine ⟨h1, h2, h3, fun ψ => ?_⟩
        have hval'eq : val' psigmaMkName ψ = m.val psigmaMkName ψ := by
          simp [hval', hne]
        rw [hval'eq]
        exact h4 ψ
    · intro cv hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        have hval'eq : val' punitName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq] at hx
        exact hnewunit cv rfl hn ψ x hx
      · next hn =>
        have hne : punitName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = punitName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hval'eq : val' punitName ψ = m.val punitName ψ := by
          simp [hval', hne]
        rw [hval'eq] at hx
        exact m.ind_ok.right.right.left cv hfp ψ x hx
    · intro n ci' hfp hbasis
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨hpi, hpv⟩ := hpin hbasis
        refine ⟨by rw [← hn]; exact hpi, fun ψ => ?_⟩
        have hval'eq : val' n ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq, hpv ψ, hn]
      · next hn =>
        have hne : n ≠ ci.name := by
          intro hcontra
          rw [hcontra, hfind'] at hfp
          exact nomatch hfp
        obtain ⟨hpi, hpv⟩ := m.ind_ok.right.right.right.left n ci' hfp hbasis
        refine ⟨hpi, fun ψ => ?_⟩
        have hval'eq : val' n ψ = m.val n ψ := by
          simp [hval', hne]
        rw [hval'eq]
        exact hpv ψ
  · -- the new constant's value
    intro ψ
    simp [hval']
  · -- untouched values
    intro n ψ hne
    simp [hval', hne]

/-- The common inversion + semantic-fact assembly for a checked value
against a checked (annotated) type. -/
private theorem value_facts {env : Env} (m : EnvModel V env)
    {value value' type vtype : Expr}
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotate env 0 value = .ok value')
    (hvt : inferType env 0 value' = .ok vtype)
    (hde : isDefEq env 0 vtype type = .ok true)
    (htf : type.hasFvar = false)
    (htb : type.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T) :
    value'.hasFvar = false ∧
    (∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value') ∧
    (∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value' = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T) := by
  have hwv : WScoped 0 value := WScoped.of_not_hasFvar hivf
  have hvf' : value'.hasFvar = false := by
    rw [← Expr.LeafEquiv.hasFvar_eq value value' (annotate_leafEquiv value hannv hwv hlbv)]
    exact hivf
  have hbv' : value'.looseBVarsBounded 0 = true := annotate_looseBVars value hannv hlbv
  have hAv : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value' := fun ψ =>
    annotate_sound m value hannv hwv hlbv (Expr.LeavesBounded.of_not_hasFvar hivf)
      (rho0 V) (FvarsOk.of_not_hasFvar hivf)
  refine ⟨hvf', hAv, fun ψ => ?_⟩
  obtain ⟨⟨v, tv, hv, htv, hmem⟩, hwvt, hAvt⟩ :=
    inferType_sound (φ := ψ) m hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
      (FvarsOk.of_not_hasFvar hvf') (hAv ψ)
  obtain ⟨T, hT⟩ := hkeyT ψ
  have hbvt : vtype.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf checkFuel hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
  have hLbvt : Expr.LeavesBounded vtype := fun l hl =>
    Expr.LeavesBounded.of_not_hasFvar hvf' l
      (inferTypeCore_fvarLeaves m.wf checkFuel hvt (WScoped.of_not_hasFvar hvf') l hl)
  have htveq : tv = T :=
    isDefEq_sound (φ := ψ) m hde hwvt (WScoped.of_not_hasFvar htf)
      hbvt htb hLbvt (Expr.LeavesBounded.of_not_hasFvar htf)
      (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hvt
        (WScoped.of_not_hasFvar hvf')) (FvarsOk.of_not_hasFvar hvf'))
      (FvarsOk.of_not_hasFvar htf)
      hAvt (hAty ψ) htv hT
  exact ⟨v, T, hv, hT, htveq ▸ hmem⟩

private theorem max_ne_zero_r'' {u v : Nat} (h : v ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u v))

/-- Checking a declaration preserves having a model. -/
theorem checkDecl_sound {env env' : Env} {d : Declaration}
    (h : checkDecl env d = .ok env') (m : EnvModel V env) : Nonempty (EnvModel V env') := by
  cases d with
  | axiomDecl cv => exact nomatch h
  | basisDecl kind =>
    match kind, h with
    | .natK, h => ?_
    | .psigmaK, h => ?_
    | .eqK, h => ?_
    | .punitK, h => ?_
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: Nat
      by_cases h1 : (env.find? natA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Nat.zero
      by_cases h2 : ((⟨natA :: env.consts⟩ : Env).find? natZeroA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Nat.succ
      by_cases h3 : ((⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 4: Nat.rec
      by_cases h4 : ((⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find? natRecA.name).isNone
      case neg => simp [h4, pure, Except.pure] at h
      simp only [h4, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the four model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m natA (fun _ => omega)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => nat_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 natZeroA
        (fun _ => natzero)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natZeroA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natZeroA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natZero_key rfl (fun ψ' => hval1 ψ'))
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natZeroA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      have hvalN2 : ∀ ψ' : Name → Nat, m2.val natName ψ' = omega := fun ψ' => by
        rw [hpres2 natName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 natSuccA
        (fun ψ => natSuccVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natSuccA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natSuccA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natSucc_key rfl hvalN2)
        (fun _ _ _ => rfl)
        (fun ψ => annotOk_natSucc_type rfl hvalN2)
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      have hvalN3 : ∀ ψ' : Name → Nat, m3.val natName ψ' = omega := fun ψ' => by
        rw [hpres3 natName ψ' (by decide)]
        exact hvalN2 ψ'
      have hvalZ3 : ∀ ψ' : Name → Nat, m3.val natZeroName ψ' = natzero := fun ψ' => by
        rw [hpres3 natZeroName ψ' (by decide)]
        exact hval2 ψ'
      obtain ⟨m4, hval4, hpres4⟩ := extend_basis_one m3 natRecA
        (fun ψ => natRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h4)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [natRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natRec_key rfl hvalN3 rfl hvalZ3 rfl (fun ψ' => hval3 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [natRecVal]
          rw [hψ uN (by simp [natRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_natRec_type rfl hvalN3 rfl hvalZ3 rfl
          (fun ψ' => hval3 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_neg (by decide), Env.find?_cons, if_pos (by decide)],
            by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
      exact ⟨m4⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: PSigma'
      by_cases h1 : (env.find? psigmaA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: PSigma'.mk
      by_cases h2 : ((⟨psigmaA :: env.consts⟩ : Env).find? psigmaMkA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: PSigma'.rec
      by_cases h3 : ((⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- the semantic pair facts the environment invariant records
      have htyfacts : ∀ ψ' : Name → Nat,
          PairTyFacts V (psigmaVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_⟩
        · intro vE A₀ B₀ x hmem hx
          simp only [psigmaVal] at hmem
          exact lam_pi_dom hmem
            (max_ne_zero_r'' (Nat.succ_ne_zero (Nat.max (ψ' uN) (ψ' vN)))) hx
        · intro vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaVal_app hvA] at hmem
          exact lam_pi_dom hmem (Nat.succ_ne_zero _) hx
        · intro vA vB hvA hvB
          exact psigmaVal_fold hvA hvB
      have hmkfacts : ∀ ψ' : Name → Nat,
          PairMkFacts V (psigmaMkVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hw vE A₀ B₀ x hmem hx
          simp only [psigmaMkVal] at hmem
          refine lam_pi_dom hmem ?_ hx
          rw [if_neg hw]
          exact max_ne_zero_r'' (Nat.succ_ne_zero (ψ' vN))
        · intro hw vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaMkVal_app hvA] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB vE A₂ B₂ x hvA hvB hmem hx
          rw [psigmaMkVal_app₂ hvA hvB] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB va vE A₃ B₃ x hvA hvB hva hmem hx
          rw [psigmaMkVal_app₃ hvA hvB hva] at hmem
          exact lam_pi_dom hmem hw hx
        · intro vA vB va vb hvA hvB hva hvb
          exact psigmaMkVal_fold hvA hvB hva hvb
        · intro hw x y z w'
          simp only [psigmaMkVal]
          rw [if_pos hw, lam_zero, app_pt, app_pt, app_pt, app_pt]
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m psigmaA
        (fun ψ => psigmaVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigma_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaVal]
          rw [hψ uN (by simp [psigmaA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigma_type)
        (fun cv hx _ => ⟨by cases hx; rfl, htyfacts⟩)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 psigmaMkA
        (fun ψ => psigmaMkVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaMkA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaMkA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigmaMk_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaMkVal]
          rw [hψ uN (by simp [psigmaMkA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaMkA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaMk_type rfl (fun ψ' => hval1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => by
          cases hx
          exact ⟨rfl, rfl, rfl, hmkfacts⟩)
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      have hvalS2 : ∀ ψ' : Name → Nat, m2.val psigmaName ψ' = psigmaVal V ψ' :=
        fun ψ' => by
          rw [hpres2 psigmaName ψ' (by decide)]
          exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 psigmaRecA
        (fun ψ => psigmaRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [psigmaRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigmaRec_key rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaRecVal]
          rw [hψ uN (by simp [psigmaRecA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaRecA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaRec_type rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide)⟩)
      exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: Eq
      by_cases h1 : (env.find? eqA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Eq.refl
      by_cases h2 : ((⟨eqA :: env.consts⟩ : Env).find? eqReflA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Eq.rec
      by_cases h3 : ((⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m eqA (fun ψ => eqVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eq_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqVal]
          rw [hψ uN (by simp [eqA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eq_type)
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 eqReflA
        (fun ψ => eqReflVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqReflA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqReflA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eqRefl_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqReflVal]
          rw [hψ uN (by simp [eqReflA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRefl_type rfl (fun ψ' => hval1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      have hvalE2 : ∀ ψ' : Name → Nat, m2.val eqName ψ' = eqVal V ψ' := fun ψ' => by
        rw [hpres2 eqName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 eqRecA
        (fun ψ => eqRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [eqRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eqRec_key rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqRecVal]
          rw [hψ u1N (by simp [eqRecA, ConstantInfo.toConstantVal, u1N]),
            hψ uN (by simp [eqRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRec_type rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
      exact ⟨m3⟩
    simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
    -- step 1: PUnit
    by_cases h1 : (env.find? punitA.name).isNone
    case neg => simp [h1, pure, Except.pure] at h
    simp only [h1, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 2: PUnit.unit
    by_cases h2 : ((⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name).isNone
    case neg => simp [h2, pure, Except.pure] at h
    simp only [h2, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 3: PUnit.rec
    by_cases h3 : ((⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitRecA.name).isNone
    case neg => simp [h3, pure, Except.pure] at h
    simp only [h3, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    -- chain the three model extensions
    obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m punitA (fun _ => unitSet)
      (Option.isNone_iff_eq_none.mp h1)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitA])⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punit_key)
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv hx hn => absurd hn (by decide))
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv _ _ ψ x hx => mem_unitSet hx)
      (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
    obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 punitUnitA (fun _ => pt)
      (Option.isNone_iff_eq_none.mp h2)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitUnitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitUnitA])⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punitUnit_key rfl (fun ψ' => hval1 ψ'))
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitUnitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv hx _ => nomatch hx)
      (fun cv nP nF hx hn => absurd hn (by decide))
      (fun cv hx _ => nomatch hx)
      (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
    have hvalP2 : ∀ ψ' : Name → Nat, m2.val punitName ψ' = unitSet := fun ψ' => by
      rw [hpres2 punitName ψ' (by decide)]
      exact hval1 ψ'
    obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 punitRecA
      (fun ψ => punitRecVal V ψ)
      (Option.isNone_iff_eq_none.mp h3)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [punitRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punitRec_key rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun ψ₁ ψ₂ hψ => by
        simp only [punitRecVal]
        rw [hψ u1N (by simp [punitRecA, ConstantInfo.toConstantVal, u1N]),
          hψ uN (by simp [punitRecA, ConstantInfo.toConstantVal, uN])])
      (fun ψ => annotOk_punitRec_type rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun cv hx _ => nomatch hx)
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv hx _ => nomatch hx)
      (fun _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩⟩)
    exact ⟨m3⟩
  | defnDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    -- semantic facts about the annotated type
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false := by
      rw [← Expr.LeafEquiv.hasFvar_eq cv.type type (annotate_leafEquiv cv.type hann hwt hlbt)]
      exact hitf
    have hbt' : type.looseBVarsBounded 0 = true := annotate_looseBVars cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferType_sound (φ := ψ) m hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotate_looseBVars cv.type hann hlbt)
      hvp hvf' hvr (annotate_looseBVars value hannv hlbv) hkey hAty hAval
      (ConstantInfo.defnInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 heq => by injection heq with h1 h2; exact ⟨h1.symm, h2.symm⟩)
      rfl
  | thmDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    -- the theorem-specific proposition check re-runs inference on the type
    cases hst2 : inferType env 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSort env 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false := by
      rw [← Expr.LeafEquiv.hasFvar_eq cv.type type (annotate_leafEquiv cv.type hann hwt hlbt)]
      exact hitf
    have hbt' : type.looseBVarsBounded 0 = true := annotate_looseBVars cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferType_sound (φ := ψ) m hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotate_looseBVars cv.type hann hlbt)
      hvp hvf' hvr (annotate_looseBVars value hannv hlbv) hkey hAty hAval
      (ConstantInfo.thmInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 heq => nomatch heq)
      rfl

private theorem foldlM_sound {env' : Env} :
    ∀ (ds : List Declaration) (env : Env), Nonempty (EnvModel V env) →
      ds.foldlM checkDecl env = .ok env' → Nonempty (EnvModel V env')
  | [], env, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_sound ds env1 (checkDecl_sound hd m) h

/-- Soundness: every accepted environment has a set-theoretic model. -/
theorem checkDecls_sound {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env') : Nonempty (EnvModel V env') :=
  foldlM_sound ds Env.empty ⟨EnvModel.empty V⟩ h

end Setlec
