import Setlec.SetR.Sound.Motives

/-!
# Soundness cases — the structural core (task #148, T4, batches a+b)

The standalone case lemmas (one per constructor, shaped exactly as the
recursor minor premises — constructor hypotheses first, then IHs at the
`*S` motives; `Setlec/SetR/Weaken.lean` is the pattern) for the
structural rules: `Red`'s refl/trans/appFn/beta/zeta/projArg, `Infer`'s
sort/bvar/const/pi/lam/app/letE, `DefEq`'s structural core and the
binder/spine/projection congruences plus D14, and the `Tele`/`DefEqL`
constructors.

Re-hung content: `whnfCore_claims`' β/ζ cases (`app_lamC` +
`AnnotOkV_inst0`), `infer_claims`' ∀/λ/app/letE cases (`piC_mem_univ`,
`lamC_mem`, `app_mem_piC`), `defeq_claims`' congruence cases
(`piC_congr`/`lamC_congr`) — each freed of the Expr-side
scoping/definedness plumbing per the architecture record.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-! ### `Red`, structural -/

theorem sndRedRefl {Δ : List VExpr} {v : VExpr} : RedS V Δ v v :=
  fun _ _ => ⟨rfl, id⟩

theorem sndRedTrans {Δ : List VExpr} {v w x : VExpr}
    (_ : Red μ env cval φ Δ v w) (_ : Red μ env cval φ Δ w x)
    (ih1 : RedS V Δ v w) (ih2 : RedS V Δ w x) : RedS V Δ v x := by
  intro ρ hΔ
  obtain ⟨he1, ha1⟩ := ih1 ρ hΔ
  obtain ⟨he2, ha2⟩ := ih2 ρ hΔ
  exact ⟨he1.trans he2, fun h => ha2 (ha1 h)⟩

theorem sndRedAppFn {Δ : List VExpr} {f f' a : VExpr}
    (_ : Red μ env cval φ Δ f f') (ih : RedS V Δ f f') :
    RedS V Δ (.app f a) (.app f' a) := by
  intro ρ hΔ
  obtain ⟨he, ha⟩ := ih ρ hΔ
  refine ⟨by simp only [interp_app, he], fun h => ?_⟩
  rw [AnnotOkV_app] at h ⊢
  obtain ⟨hf, haok, A, B, hpi, hdom⟩ := h
  exact ⟨ha hf, haok, A, B, he ▸ hpi, hdom⟩

theorem sndRedBeta {Δ : List VExpr} {A b a ta : VExpr}
    (_ : Infer μ env cval φ Δ a ta) (_ : DefEq μ env cval φ Δ ta A)
    (ih1 : InfS V Δ a ta) (ih2 : DeqS V Δ ta A) :
    RedS V Δ (.app (.lam A b) a) (b.inst a) := by
  intro ρ hΔ
  obtain ⟨haok, hamem⟩ := ih1 ρ hΔ
  have hdom : interp V ρ a ∈ˢ interp V ρ A := (ih2 ρ hΔ) ▸ hamem
  have heq : interp V ρ (.app (.lam A b) a) = interp V ρ (b.inst a) := by
    rw [interp_app, interp_lam, app_lamC hdom, interp_inst0]
  refine ⟨heq, fun h => ?_⟩
  rw [AnnotOkV_app, AnnotOkV_lam] at h
  exact (AnnotOkV_inst0 V haok).mpr (h.1.2 _ hdom)

theorem sndRedZeta {Δ : List VExpr} {T v b : VExpr} :
    RedS V Δ (.letE T v b) (b.inst v) := by
  intro ρ _
  refine ⟨by rw [interp_letE, interp_inst0], fun h => ?_⟩
  rw [AnnotOkV_letE] at h
  exact (AnnotOkV_inst0 V h.2.1).mpr h.2.2

theorem sndRedProjArg {Δ : List VExpr} {e e' : VExpr} {i : Nat}
    (_ : Red μ env cval φ Δ e e') (ih : RedS V Δ e e') :
    RedS V Δ (.proj i e) (.proj i e') := by
  intro ρ hΔ
  obtain ⟨he, ha⟩ := ih ρ hΔ
  refine ⟨by simp only [interp_proj, he], fun h => ?_⟩
  rw [AnnotOkV_proj] at h ⊢
  obtain ⟨hok, hi, u, v, A, Bf, hmem, hA, hB⟩ := h
  exact ⟨ha hok, hi, u, v, A, Bf, he ▸ hmem, hA, hB⟩

/-! ### `Infer` -/

theorem sndInfSort {Δ : List VExpr} {u : Nat} :
    InfS V Δ (.sort u) (.sort (u + 1)) := by
  intro ρ _
  exact ⟨by simp, univ_mem_univ u⟩

theorem sndInfBvar {Δ : List VExpr} {i : Nat} {A : VExpr}
    (h : Δ[i]? = some A) : InfS V Δ (.bvar i) (A.liftN (i + 1)) := by
  intro ρ hΔ
  refine ⟨by simp, ?_⟩
  rw [interp_liftN, shiftE_zero]
  exact hΔ i A h

theorem sndInfConst (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {n : Name} {ci : ConstantInfo} {us : List Level}
    {T : VExpr}
    (h1 : env.find? n = some ci)
    (h2 : us.length = ci.toConstantVal.levelParams.length)
    (h3 : denoteClosed cval env φ
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) = some T)
    (_ : VExpr.Closed T) :
    InfS V Δ (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      T := by
  intro ρ _
  exact ⟨henv.annot_okV n _ ρ, (henv.mem_type n ci h1 us h2 T h3 ρ).1⟩

theorem sndInfPi {Δ : List VExpr} {A B tA tB : VExpr} {u v : Nat}
    (_ : Infer μ env cval φ Δ A tA)
    (_ : DefEq μ env cval φ Δ tA (.sort u))
    (_ : Infer μ env cval φ (A :: Δ) B tB)
    (_ : DefEq μ env cval φ (A :: Δ) tB (.sort v))
    (ihA : InfS V Δ A tA) (ihtA : DeqS V Δ tA (.sort u))
    (ihB : InfS V (A :: Δ) B tB)
    (ihtB : DeqS V (A :: Δ) tB (.sort v)) :
    InfS V Δ (.pi A B) (.sort (imax u v)) := by
  intro ρ hΔ
  obtain ⟨hAok, hAmem⟩ := ihA ρ hΔ
  have hAu : interp V ρ A ∈ˢ (univ u : V) := by
    have h := ihtA ρ hΔ
    rw [interp_sort] at h
    exact h ▸ hAmem
  have hfib : ∀ x, x ∈ˢ interp V ρ A →
      interp V (cons V x ρ) B ∈ˢ (univ v : V) := by
    intro x hx
    have hs := Sat_cons V hΔ hx
    have h := ihtB (cons V x ρ) hs
    rw [interp_sort] at h
    exact h ▸ (ihB (cons V x ρ) hs).2
  refine ⟨?_, ?_⟩
  · rw [AnnotOkV_pi]
    exact ⟨hAok, fun x hx => (ihB (cons V x ρ) (Sat_cons V hΔ hx)).1⟩
  · rw [interp_pi, interp_sort]
    exact piC_mem_univ hAu hfib

theorem sndInfLam {Δ : List VExpr} {A b tA B B' tB : VExpr} {u v : Nat}
    (_ : Infer μ env cval φ Δ A tA)
    (_ : DefEq μ env cval φ Δ tA (.sort u))
    (_ : Infer μ env cval φ (A :: Δ) b B)
    (_ : μ.verified = true → b.isLam = false →
      DefEq μ env cval φ (A :: Δ) B B')
    (_ : μ.verified = true → b.isLam = false →
      Infer μ env cval φ (A :: Δ) B' tB)
    (_ : μ.verified = true → b.isLam = false →
      DefEq μ env cval φ (A :: Δ) tB (.sort v))
    (ihA : InfS V Δ A tA) (_ihtA : DeqS V Δ tA (.sort u))
    (ihb : InfS V (A :: Δ) b B)
    (_ihL : μ.verified = true → b.isLam = false →
      DeqS V (A :: Δ) B B')
    (_ihB : μ.verified = true → b.isLam = false →
      InfS V (A :: Δ) B' tB)
    (_ihv : μ.verified = true → b.isLam = false →
      DeqS V (A :: Δ) tB (.sort v)) :
    InfS V Δ (.lam A b) (.pi A B) := by
  intro ρ hΔ
  obtain ⟨hAok, -⟩ := ihA ρ hΔ
  refine ⟨?_, ?_⟩
  · rw [AnnotOkV_lam]
    exact ⟨hAok, fun x hx => (ihb (cons V x ρ) (Sat_cons V hΔ hx)).1⟩
  · rw [interp_lam, interp_pi]
    exact lamC_mem fun x hx => (ihb (cons V x ρ) (Sat_cons V hΔ hx)).2

theorem sndInfApp {Δ : List VExpr} {f a tf A B ta : VExpr}
    (_ : Infer μ env cval φ Δ f tf)
    (_ : DefEq μ env cval φ Δ tf (.pi A B))
    (_ : Infer μ env cval φ Δ a ta)
    (_ : DefEq μ env cval φ Δ ta A)
    (ihf : InfS V Δ f tf) (ihtf : DeqS V Δ tf (.pi A B))
    (iha : InfS V Δ a ta) (ihd : DeqS V Δ ta A) :
    InfS V Δ (.app f a) (B.inst a) := by
  intro ρ hΔ
  obtain ⟨hfok, hfmem⟩ := ihf ρ hΔ
  obtain ⟨haok, hamem⟩ := iha ρ hΔ
  have hfpi : interp V ρ f ∈ˢ
      piC (interp V ρ A) (fun x => interp V (cons V x ρ) B) := by
    have h := ihtf ρ hΔ
    rw [interp_pi] at h
    exact h ▸ hfmem
  have hdom : interp V ρ a ∈ˢ interp V ρ A := (ihd ρ hΔ) ▸ hamem
  refine ⟨?_, ?_⟩
  · rw [AnnotOkV_app]
    exact ⟨hfok, haok, _, _, hfpi, hdom⟩
  · rw [interp_app, interp_inst0]
    exact app_mem_piC hfpi hdom

theorem sndInfLetE {Δ : List VExpr} {T v b tT tv B : VExpr} {u : Nat}
    (_ : Infer μ env cval φ Δ T tT)
    (_ : DefEq μ env cval φ Δ tT (.sort u))
    (_ : Infer μ env cval φ Δ v tv)
    (_ : DefEq μ env cval φ Δ tv T)
    (_ : Infer μ env cval φ Δ (b.inst v) B)
    (ihT : InfS V Δ T tT) (_ihtT : DeqS V Δ tT (.sort u))
    (ihv : InfS V Δ v tv) (_ihd : DeqS V Δ tv T)
    (ihb : InfS V Δ (b.inst v) B) :
    InfS V Δ (.letE T v b) B := by
  intro ρ hΔ
  obtain ⟨hbok, hbmem⟩ := ihb ρ hΔ
  refine ⟨?_, ?_⟩
  · rw [AnnotOkV_letE]
    exact ⟨(ihT ρ hΔ).1, (ihv ρ hΔ).1,
      (AnnotOkV_inst0 V (ihv ρ hΔ).1).mp hbok⟩
  · rw [interp_letE, ← interp_inst0]
    exact hbmem

/-! ### `DefEq`, structural core and congruences -/

theorem sndDeqRefl {Δ : List VExpr} {v : VExpr} : DeqS V Δ v v :=
  fun _ _ => rfl

theorem sndDeqSymm {Δ : List VExpr} {a b : VExpr}
    (_ : DefEq μ env cval φ Δ a b) (ih : DeqS V Δ a b) :
    DeqS V Δ b a :=
  fun ρ hΔ => (ih ρ hΔ).symm

theorem sndDeqTrans {Δ : List VExpr} {a b c : VExpr}
    (_ : DefEq μ env cval φ Δ a b) (_ : DefEq μ env cval φ Δ b c)
    (ih1 : DeqS V Δ a b) (ih2 : DeqS V Δ b c) : DeqS V Δ a c :=
  fun ρ hΔ => (ih1 ρ hΔ).trans (ih2 ρ hΔ)

theorem sndDeqOfRed {Δ : List VExpr} {a a' : VExpr}
    (_ : Red μ env cval φ Δ a a') (ih : RedS V Δ a a') :
    DeqS V Δ a a' :=
  fun ρ hΔ => (ih ρ hΔ).1

theorem sndDeqPiCong {Δ : List VExpr} {A₁ A₂ B₁ B₂ : VExpr}
    (_ : DefEq μ env cval φ Δ A₁ A₂)
    (_ : DefEq μ env cval φ (A₁ :: Δ) B₁ B₂)
    (ih1 : DeqS V Δ A₁ A₂) (ih2 : DeqS V (A₁ :: Δ) B₁ B₂) :
    DeqS V Δ (.pi A₁ B₁) (.pi A₂ B₂) := by
  intro ρ hΔ
  rw [interp_pi, interp_pi, ← ih1 ρ hΔ]
  exact piC_congr fun x hx => ih2 (cons V x ρ) (Sat_cons V hΔ hx)

theorem sndDeqLamCong {Δ : List VExpr} {A₁ A₂ b₁ b₂ : VExpr}
    (_ : DefEq μ env cval φ Δ A₁ A₂)
    (_ : DefEq μ env cval φ (A₁ :: Δ) b₁ b₂)
    (ih1 : DeqS V Δ A₁ A₂) (ih2 : DeqS V (A₁ :: Δ) b₁ b₂) :
    DeqS V Δ (.lam A₁ b₁) (.lam A₂ b₂) := by
  intro ρ hΔ
  rw [interp_lam, interp_lam, ← ih1 ρ hΔ]
  exact lamC_congr fun x hx => ih2 (cons V x ρ) (Sat_cons V hΔ hx)

theorem sndDeqAppCong {Δ : List VExpr} {h₁ h₂ : VExpr}
    {as₁ as₂ : List VExpr}
    (_ : as₁.length = as₂.length)
    (_ : DefEq μ env cval φ Δ h₁ h₂)
    (_ : DefEqL μ env cval φ Δ as₁ as₂)
    (ih1 : DeqS V Δ h₁ h₂) (ih2 : DeqLS V Δ as₁ as₂) :
    DeqS V Δ (VExpr.mkAppN h₁ as₁) (VExpr.mkAppN h₂ as₂) := by
  intro ρ hΔ
  have hfold : ∀ (as : List VExpr) (x : V),
      as.foldl (fun r a => SetTheory.app r (interp V ρ a)) x
        = (as.map (interp V ρ)).foldl SetTheory.app x := by
    intro as x
    rw [List.foldl_map]
  rw [interp_mkAppN, interp_mkAppN, ih1 ρ hΔ, hfold, hfold, ih2 ρ hΔ]

theorem sndDeqLitSuccApp {Δ : List VExpr} {x : VExpr} {k : Nat}
    (_ : natLitSupported env = true)
    (_ : DefEq μ env cval φ Δ (natLitV cval φ k) x)
    (ih : DeqS V Δ (natLitV cval φ k) x) :
    DeqS V Δ (natLitV cval φ (k + 1)) (.app (succV cval φ) x) := by
  intro ρ hΔ
  show interp V ρ (.app (succV cval φ) (natLitV cval φ k)) = _
  rw [interp_app, interp_app, ih ρ hΔ]

theorem sndDeqProjCong {Δ : List VExpr} {e₁ e₂ : VExpr} {i : Nat}
    (_ : DefEq μ env cval φ Δ e₁ e₂) (ih : DeqS V Δ e₁ e₂) :
    DeqS V Δ (.proj i e₁) (.proj i e₂) := by
  intro ρ hΔ
  simp only [interp_proj, ih ρ hΔ]

/-! ### `Tele` / `DefEqL` -/

theorem sndTeleNil {Δ : List VExpr} {T : VExpr} : TeleS V Δ T [] T := by
  intro ρ _
  exact ⟨.nil, fun a ha => absurd ha (List.not_mem_nil), id⟩

theorem sndTeleCons {Δ : List VExpr} {A B a ta rest : VExpr}
    {as : List VExpr}
    (_ : Infer μ env cval φ Δ a ta) (_ : DefEq μ env cval φ Δ ta A)
    (_ : Tele μ env cval φ Δ (B.inst a) as rest)
    (ih1 : InfS V Δ a ta) (ih2 : DeqS V Δ ta A)
    (ih3 : TeleS V Δ (B.inst a) as rest) :
    TeleS V Δ (.pi A B) (a :: as) rest := by
  intro ρ hΔ
  obtain ⟨haok, hamem⟩ := ih1 ρ hΔ
  have hdom : interp V ρ a ∈ˢ interp V ρ A := (ih2 ρ hΔ) ▸ hamem
  obtain ⟨hfit, hargs, hrest⟩ := ih3 ρ hΔ
  refine ⟨.cons hdom hfit, ?_, ?_⟩
  · intro a' ha'
    rcases List.mem_cons.mp ha' with rfl | h
    · exact haok
    · exact hargs a' h
  · intro hpi
    rw [AnnotOkV_pi] at hpi
    exact hrest ((AnnotOkV_inst0 V haok).mpr (hpi.2 _ hdom))

theorem sndDeqLNil {Δ : List VExpr} : DeqLS V Δ [] [] :=
  fun _ _ => rfl

theorem sndDeqLCons {Δ : List VExpr} {a b : VExpr} {as bs : List VExpr}
    (_ : DefEq μ env cval φ Δ a b) (_ : DefEqL μ env cval φ Δ as bs)
    (ih1 : DeqS V Δ a b) (ih2 : DeqLS V Δ as bs) :
    DeqLS V Δ (a :: as) (b :: bs) := by
  intro ρ hΔ
  simp only [List.map_cons, ih1 ρ hΔ, ih2 ρ hΔ]

end Cases

end Setlec.SetR
