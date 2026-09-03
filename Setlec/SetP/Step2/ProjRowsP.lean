import Setlec.SetP.Step2.CapsRowsP
import Setlec.SetP.Step2.ProjPinsP

/-!
# The two semantic projection rows (task #161, PROJ/STR install tier)

`InferProjStepP` (`Step2/InferP.lean`) and `ProjStepP`
(`Step2/WhnfP.lean`), discharged.  Both are **pinned-basis** work: the
projection table admits only `pairFstEntry`/`pairSndEntry`
(`projEntry_pins`), so no stored family, no capability record and no
`EnvS2PM` field enters either proof — the recipe is the caps tier's
pinned-pair row (`pairEtaIrrelP_of_claims`) over the `psigmaV2` /
`psigmaMkV2` laws in `Interp2/Value.lean`.

## What each row costs

`InferProjStepP` is the cheap half.  The subject's inferred type
whnfs to `PSigma' A B`, `mem_psigmaV2_app` inverts that one
application into the three facts the pair space is made of, and then
everything is a `Value.lean` law: `sfst_mem2` for the first
component's membership, `ssnd_mem2` for the second's, and
`AnnotOk2_proj`'s own existential is *exactly* the triple
`mem_psigmaV2_app` returns.  The returned type is `projResidualP`'s
computed residual, so there is no `piResidualV` walk at all.

`ProjStepP`'s firing branch is the expensive half, and the reason is
structural rather than accidental: `whnfCore`'s projection clause has
**no type for the scrutinee in its premises**.  What it has is
`projCert`'s `inferTypeCore` run on the constructor application, and
the four typing memberships `sfst_mk2`/`ssnd_mk2` need have to be
walked out of that run — v1 does the same walk generically
(`tele_of_inferSpineR`); here it is done concretely, because the
constructor is pinned at arity four and each partial type is its own
whnf (`whnf_forallE_eq`).

A rigidity shortcut was looked for and does **not** exist: the
constructor's grading alone puts `interp2 vp` in *some* sigma set, but
in the `Prop` regime `psigmaMkV2` collapses the whole tower to `pt`,
so an ill-typed spine's value is a member of a sigma set just as a
well-typed one's is.  The memberships have to come from the run.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ProjEntry
  inferTypeCore whnf whnfCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The pinned pair type's leaf -/

/-- The pinned `PSigma'` leaf's value, by erasure injectivity (the
`unitIrrelPQ`/`pairEta` species). -/
theorem acval_psigma_leaf {m : EnvS2Core V env}
    (hpsig : env.find? Setlec.psigmaName = some Setlec.psigmaA)
    (ψ : Name → Nat) :
    m.acval Setlec.psigmaName ψ = .const .psigma [ψ uN, ψ vN] :=
  erase_eq_const (by
    rw [m.acval_erase,
      (m.base.basis_pinned _ _ hpsig (by decide)).2 _ _ rfl])

/-! ## One certified argument, and the pinned constructor's shape -/

/-- **One step of a certified application spine**: the argument
inhabits the domain the run checked it against.  `certs_teleP`'s inner
step, isolated — `InferReadsP` for the argument's type reading,
`InferClaims2P` for its membership, `DefEqClaims2P` for the
certificate. -/
theorem spineStepP {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel)
    {d : Nat} {Δa : List AVExpr} {a ty ta : Expr} {Aa TYa : AVExpr}
    (hta : inferTypeCore μ env fuel d a = .ok ta)
    (hde : Setlec.isDefEqCore μ env fuel d ta ty = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOkP m φ d Δa a)
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hLty : Expr.LeavesBounded ty) (hCty : CtxOkP m φ d Δa ty)
    (hda : denoteP m.acval env φ d a = some Aa)
    (hdty : denoteP m.acval env φ d ty = some TYa)
    (hokTY : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ TYa)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ Aa ∈ˢ interp2 V ρ TYa := by
  obtain ⟨taa, htaa⟩ :=
    hreads hta hwa hba hLa (LeafReadsP.of_ctxOkP hCa) hda
  obtain ⟨-, hokTa, hmemA⟩ := ihi hta hwa hba hLa hCa hda htaa
  have hwta : Expr.WScoped d ta :=
    Setlec.inferTypeCore_WScoped m.base.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars m.base.wf fuel hta hwa hba hLa
  have hLta : Expr.LeavesBounded ta := fun l hl =>
    hLa l (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hta hwa l hl)
  have hCta : CtxOkP m φ d Δa ta :=
    hCa.of_subset (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hta hwa)
  have heq := ihd hde hwta hbta hLta hwty hbty hLty hCta hCty htaa hdty
    hokTa hokTY ρ hρ
  exact heq ▸ hmemA ρ hρ

/-- **The pinned constructor's instantiated type, in shape.**  The
binder names and metas are quantified away — only the `x` binder's
prop-ness bit is read (it is `never`, so the fibre product is in the
graph regime and `psigmaFibreSpace` is exactly what the domain reads
to). -/
theorem psigmaMkTyShape (l0 l1 : Level) (φ : Name → Nat) :
    ∃ (nα nβ nx nf ns : Name)
      (mbα mbβ mbf mbs mbx : Setlec.BinderMeta),
      mbx.pw.holds φ = false ∧
      Setlec.psigmaMkA.toConstantVal.type.instantiateLevelParams
          Setlec.psigmaMkA.toConstantVal.levelParams [l0, l1]
        = Expr.forallE nα (.sort l0)
            (.forallE nβ (.forallE nx (.bvar 0) (.sort l1) mbx)
              (.forallE nf (.bvar 1)
                (.forallE ns (.app (.bvar 1) (.bvar 0))
                  (.app (.app (.const Setlec.psigmaName [l0, l1])
                    (.bvar 3)) (.bvar 2)) mbs) mbf) mbβ) mbα := by
  refine ⟨_, _, _, _, _, _, _, _, _, _, ?_, rfl⟩
  show (Setlec.Level.substPW [uN, vN] [l0, l1] Setlec.PropWhen.never).holds φ
    = false
  rw [Setlec.Level.holds_substPW]
  rfl

/-- **The pinned constructor spine's four typing memberships**, walked
out of the checker's own `inferTypeCore` run on the constructor
application.  This is `tele_of_inferSpineR`'s content at the P
currency, done concretely: `PSigma'.mk` is pinned at arity four, each
partial type is a syntactic `∀` (hence its own `whnf`,
`whnf_forallE_eq`), and each domain's reading is computed from the
arguments already in hand.  The `x` binder's `never` bit is what makes
the second domain read to `psigmaFibreSpace` (`piR_zero_agree`: only
the bit's *zeroness* is visible to `piR`). -/
theorem psigmaMkSpineP {m : EnvS2Core V env}
    (ihd : DefEqClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel)
    {d : Nat} {Δa : List AVExpr} {l0 l1 : Level} {a0 a1 a2 a3 te : Expr}
    {A0 A1 A2 A3 : AVExpr}
    (hfmk : env.find? Setlec.psigmaMkName = some Setlec.psigmaMkA)
    (hite : inferTypeCore μ env fuel d
      (.app (.app (.app (.app (.const Setlec.psigmaMkName [l0, l1]) a0)
        a1) a2) a3) = .ok te)
    (hf0 : Expr.WScoped d a0 ∧ a0.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a0 ∧ CtxOkP m φ d Δa a0)
    (hf1 : Expr.WScoped d a1 ∧ a1.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a1 ∧ CtxOkP m φ d Δa a1)
    (hf2 : Expr.WScoped d a2 ∧ a2.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a2 ∧ CtxOkP m φ d Δa a2)
    (hf3 : Expr.WScoped d a3 ∧ a3.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a3 ∧ CtxOkP m φ d Δa a3)
    (hd0 : denoteP m.acval env φ d a0 = some A0)
    (hd1 : denoteP m.acval env φ d a1 = some A1)
    (hd2 : denoteP m.acval env φ d a2 = some A2)
    (hd3 : denoteP m.acval env φ d a3 = some A3)
    (hok0 : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ A0)
    (hok1 : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ A1)
    (hok2 : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ A2) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ A0 ∈ˢ (univ (Level.eval φ l0) : V) ∧
        interp2 V ρ A1 ∈ˢ
          psigmaFibreSpace V (Level.eval φ l1) (interp2 V ρ A0) ∧
        interp2 V ρ A2 ∈ˢ interp2 V ρ A0 ∧
        interp2 V ρ A3 ∈ˢ
          SetTheory.app (interp2 V ρ A1) (interp2 V ρ A2) := by
  obtain ⟨hw0e, hb0, hL0, hC0⟩ := hf0
  obtain ⟨hw1e, hb1, hL1, hC1⟩ := hf1
  obtain ⟨hw2e, hb2, hL2, hC2⟩ := hf2
  obtain ⟨hw3e, hb3, hL3, hC3⟩ := hf3
  have hb0k : ∀ k, Expr.looseBVarsBounded k a0 = true := fun k =>
    Setlec.Expr.looseBVarsBounded_mono (Nat.zero_le k) hb0
  have hb1k : ∀ k, Expr.looseBVarsBounded k a1 = true := fun k =>
    Setlec.Expr.looseBVarsBounded_mono (Nat.zero_le k) hb1
  -- peel the four applications
  obtain ⟨tf3, n3, ty3, body3, mb3, htf3, hwq3, -, ta3, hta3, hde3⟩ :=
    Setlec.inferTypeCore_app_inv' hite
  obtain ⟨tf2, n2, ty2, body2, mb2, htf2, hwq2, rfl, ta2, hta2, hde2⟩ :=
    Setlec.inferTypeCore_app_inv' htf3
  obtain ⟨tf1, n1, ty1, body1, mb1, htf1, hwq1, rfl, ta1, hta1, hde1⟩ :=
    Setlec.inferTypeCore_app_inv' htf2
  obtain ⟨tf0, n0, ty0, body0, mb0, htf0, hwq0, rfl, ta0, hta0, hde0⟩ :=
    Setlec.inferTypeCore_app_inv' htf1
  obtain ⟨ciMk, hfMk', rfl⟩ := Setlec.inferTypeCore_const_inv htf0
  obtain rfl : ciMk = Setlec.psigmaMkA :=
    Option.some.inj (hfMk'.symm.trans hfmk)
  obtain ⟨nα, nβ, nx, nf, ns, mbα, mbβ, mbf, mbs, mbx, hmbx, hshape⟩ :=
    psigmaMkTyShape l0 l1 φ
  -- level 0: the domain is `Sort l0`
  rw [hshape] at hwq0
  injection Setlec.whnf_forallE_eq hwq0 with e0a e0b e0c e0d
  subst e0b; subst e0c
  -- level 1: the domain is the fibre former's type
  rw [show (Expr.forallE nβ (.forallE nx (.bvar 0) (.sort l1) mbx)
        (.forallE nf (.bvar 1)
          (.forallE ns (.app (.bvar 1) (.bvar 0))
            (.app (.app (.const Setlec.psigmaName [l0, l1]) (.bvar 3))
              (.bvar 2)) mbs) mbf) mbβ).instantiate1 a0
      = Expr.forallE nβ (.forallE nx a0 (.sort l1) mbx)
          (.forallE nf a0
            (.forallE ns (.app (.bvar 1) (.bvar 0))
              (.app (.app (.const Setlec.psigmaName [l0, l1]) a0)
                (.bvar 2)) mbs) mbf) mbβ from rfl] at hwq1
  injection Setlec.whnf_forallE_eq hwq1 with e1a e1b e1c e1d
  subst e1b; subst e1c
  -- level 2: the domain is the first parameter
  rw [show (Expr.forallE nf a0
        (.forallE ns (.app (.bvar 1) (.bvar 0))
          (.app (.app (.const Setlec.psigmaName [l0, l1]) a0)
            (.bvar 2)) mbs) mbf).instantiate1 a1
      = Expr.forallE nf a0
          (.forallE ns (.app a1 (.bvar 0))
            (.app (.app (.const Setlec.psigmaName [l0, l1]) a0) a1) mbs)
          mbf from by
    show Expr.forallE nf (a0.instantiate1 a1 0) _ _ = _
    rw [Setlec.Expr.instantiate1_eq_self (hb0k 0)]
    show Expr.forallE nf a0 (Expr.forallE ns _
      (.app (.app (.const Setlec.psigmaName [l0, l1])
        (a0.instantiate1 a1 2)) _) _) _ = _
    rw [Setlec.Expr.instantiate1_eq_self (hb0k 2)]
    rfl] at hwq2
  injection Setlec.whnf_forallE_eq hwq2 with e2a e2b e2c e2d
  rw [e2b] at hde2
  subst e2c
  -- level 3: the domain is the fibre at the first field
  rw [show (Expr.forallE ns (.app a1 (.bvar 0))
        (.app (.app (.const Setlec.psigmaName [l0, l1]) a0) a1)
        mbs).instantiate1 a2
      = Expr.forallE ns (.app a1 a2)
          (.app (.app (.const Setlec.psigmaName [l0, l1]) a0) a1)
          mbs from by
    show Expr.forallE ns (.app (a1.instantiate1 a2 0) _)
      (.app (.app (.const Setlec.psigmaName [l0, l1])
        (a0.instantiate1 a2 1)) (a1.instantiate1 a2 1)) _ = _
    rw [Setlec.Expr.instantiate1_eq_self (hb0k 1),
      Setlec.Expr.instantiate1_eq_self (hb1k 1),
      Setlec.Expr.instantiate1_eq_self (hb1k 0)]
    rfl] at hwq3
  injection Setlec.whnf_forallE_eq hwq3 with e3a e3b e3c e3d
  subst e3b
  -- the four domains' frames and readings
  have hCsort : ∀ (u : Level) (e : Expr), CtxOkP m φ d Δa e →
      CtxOkP m φ d Δa (Expr.sort u) := fun u e hCe =>
    ⟨hCe.1, fun l hl => by simp [Expr.fvarLeaves] at hl⟩
  have hokSort : ∀ (u : Nat) (σ : Nat → V),
      AnnotOkP V σ ((.sort u) : AVExpr) := by
    intro u σ
    exact ⟨by rw [AnnotOk2]; trivial, by rw [AnnotValidV]; trivial⟩
  -- step 0
  have hA : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ A0 ∈ˢ (univ (Level.eval φ l0) : V) := by
    intro σ hσ
    have := spineStepP ihd ihi hreads hta0 hde0 hw0e hb0 hL0 hC0
      (by simp [Expr.WScoped]) rfl
      (fun l hl => by simp [Expr.fvarLeaves] at hl) (hCsort l0 a0 hC0)
      hd0 denoteP_sortQ (fun σ' _ => hokSort _ σ') σ hσ
    rwa [interp2_sort] at this
  -- step 1
  have hB : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ A1 ∈ˢ
        psigmaFibreSpace V (Level.eval φ l1) (interp2 V σ A0) := by
    intro σ hσ
    have hdty1 : denoteP m.acval env φ d
        (Expr.forallE nx a0 (.sort l1) mbx)
        = some ((.pi 0 (pwBit φ mbx.pw) A0
            (.sort (Level.eval φ l1))) : AVExpr) := by
      rw [denoteP_forallE, hd0,
        show (Expr.sort l1).instantiate1 (.fvar d nx a0) = Expr.sort l1
          from rfl, denoteP_sort]
      rfl
    have hbx : pwBit φ mbx.pw ≠ 0 := by
      rw [Ne, pwBit_eq_zero_iff, hmbx]; simp
    have hokty1 : ∀ σ' : Nat → V, Sat2 V Δa σ' →
        AnnotOkP V σ' ((.pi 0 (pwBit φ mbx.pw) A0
          (.sort (Level.eval φ l1))) : AVExpr) := by
      intro σ' hσ'
      refine ⟨?_, ?_⟩
      · rw [AnnotOk2_pi]
        exact ⟨(hok0 σ' hσ').1, fun x _ => (hokSort _ (cons x σ')).1⟩
      · rw [AnnotValidV_pi]
        exact ⟨(hok0 σ' hσ').2, fun x _ => (hokSort _ (cons x σ')).2,
          fun h0 => absurd h0 hbx⟩
    have := spineStepP ihd ihi hreads hta1 hde1 hw1e hb1 hL1 hC1
      (by simpa [Expr.WScoped] using hw0e)
      (by simpa [Expr.looseBVarsBounded] using hb0)
      (fun l hl => hL0 l (by simpa [Expr.fvarLeaves] using hl))
      (hC0.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl))
      hd1 hdty1 hokty1 σ hσ
    rw [interp2_pi] at this
    have hfibeq : psigmaFibreSpace V (Level.eval φ l1) (interp2 V σ A0)
        = piR (pwBit φ mbx.pw) (interp2 V σ A0)
          fun x => interp2 V (cons x σ)
            ((.sort (Level.eval φ l1)) : AVExpr) := by
      rw [psigmaFibreSpace]
      refine piR_zero_agree ?_ ?_
      · constructor
        · intro h0; exact absurd h0 (Nat.succ_ne_zero _)
        · intro h0; exact absurd h0 hbx
      · intro x _; rw [interp2_sort]
    rw [hfibeq]
    exact this
  -- step 2
  have ha : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ A2 ∈ˢ interp2 V σ A0 :=
    fun σ hσ => spineStepP ihd ihi hreads hta2 hde2 hw2e hb2 hL2 hC2
      hw0e hb0 hL0 hC0 hd2 hd0 hok0 σ hσ
  -- step 3
  intro ρ hρ
  refine ⟨hA ρ hρ, hB ρ hρ, ha ρ hρ, ?_⟩
  have hdty3 : denoteP m.acval env φ d (Expr.app a1 a2)
      = some ((.app A1 A2) : AVExpr) := by
    rw [denoteP_app, hd1, hd2]; rfl
  have hokty3 : ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ ((.app A1 A2) : AVExpr) := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨(hok1 σ hσ).1, (hok2 σ hσ).1, Level.eval φ l1 + 1,
        interp2 V σ A0, (fun _ => (univ (Level.eval φ l1) : V)),
        hB σ hσ, ha σ hσ, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    · rw [AnnotValidV_app]; exact ⟨(hok1 σ hσ).2, (hok2 σ hσ).2⟩
  have hleafApp : ∀ l ∈ (Expr.app a1 a2).fvarLeaves,
      l ∈ a1.fvarLeaves ∨ l ∈ a2.fvarLeaves := by
    intro l hl
    simpa [Expr.fvarLeaves] using hl
  have := spineStepP ihd ihi hreads hta3 hde3 hw3e hb3 hL3 hC3
    (by simp only [Expr.WScoped]; exact ⟨hw1e, hw2e⟩)
    (by simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hb1, hb2⟩)
    (fun l hl => by
      rcases hleafApp l hl with h | h
      · exact hL1 l h
      · exact hL2 l h)
    ⟨hC1.1, fun l hl => by
      rcases hleafApp l hl with h | h
      · exact hC1.2 l h
      · exact hC2.2 l h⟩
    hd3 hdty3 hokty3 ρ hρ
  rwa [interp2_app] at this

/-! ## `InferProjStepP` -/

/-- **`InferProjStepP`, discharged.**  The subject's type reduces to
the pinned pair applied to its two parameters; `mem_psigmaV2_app`
inverts that into the three facts `AnnotOk2_proj` asks for, and the
returned type is `projResidualP`'s computed residual — the first
parameter, or the second applied to the first projection. -/
theorem inferProjStepP_of_claims {m : EnvS2Core V env}
    (ihw : WhnfClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    InferProjStepP m μ φ fuel := by
  intro d i sn pe t Δa ea ta h hws hb hLb hC hea hta
  obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat, hlenArgs,
    hlenUs, A, B, hAB, hcase⟩ := Setlec.inferTypeCore_proj_inv h
  -- the subject's frames
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkP m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hi2, rfl⟩ := denoteP_proj_inv hea
  -- its inferred type: reading, grading, membership
  obtain ⟨tpea, htpea⟩ :=
    hreads htpe hws hb hLpe (LeafReadsP.of_ctxOkP hCpe) hvp
  obtain ⟨hokPe, hokTpe, hmemPe⟩ := ihi htpe hws hb hLpe hCpe hvp htpea
  have hwtpe : Expr.WScoped d tpe :=
    Setlec.inferTypeCore_WScoped m.base.wf fuel htpe hws
  have hbtpe : tpe.looseBVarsBounded 0 = true :=
    Setlec.inferTypeCore_looseBVars m.base.wf fuel htpe hws hb hLpe
  have hLtpe : Expr.LeavesBounded tpe := fun l hl =>
    hLpe l (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel htpe hws l hl)
  have hCtpe : CtxOkP m φ d Δa tpe :=
    hCpe.of_subset
      (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel htpe hws)
  -- reduced to the family instance
  obtain ⟨tea, htea⟩ := hwreads hwte hwtpe hbtpe hLtpe htpea
  obtain ⟨hokTe, heqTe⟩ :=
    ihw hwte hwtpe hbtpe hLtpe hCtpe htpea htea hokTpe
  have hbte : te.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.base.wf fuel hwte hbtpe
  -- the entry's pins, and the returned type
  obtain ⟨rfl, -, -, -, -, -, hlU, -, hpsig, -⟩ :=
    projPinsP m.base.proj_ok hfe hnat
  -- the reduced type's spine
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Setlec.Expr.mkAppN_getApp te).symm, hfn] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denoteP_mkAppN_inv htea
  rw [denoteP_const hpsig (by rw [hlenUs, hlU]; rfl)] at hvT
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      Level.substFn φ Setlec.psigmaA.toConstantVal.levelParams us = ψ :=
    ⟨_, rfl⟩
  rw [hψ] at hvT
  obtain rfl : vT = m.acval Setlec.psigmaName ψ := (Option.some.inj hvT).symm
  rw [hAB] at hspt
  cases hspt with | @cons _ Aa _ vs' hAa hsp1 => ?_
  cases hsp1 with | @cons _ Ba _ _ hBa hsp2 => ?_
  cases hsp2
  subst hteq
  -- the pinned leaf, and the pair-space inversion
  have hleafI : m.acval Setlec.psigmaName ψ
      = .const .psigma [ψ uN, ψ vN] := acval_psigma_leaf hpsig ψ
  have hpack : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ Aa ∈ˢ (univ (ψ uN) : V) ∧
      interp2 V σ Ba ∈ˢ psigmaFibreSpace V (ψ vN) (interp2 V σ Aa) ∧
      interp2 V σ vp ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN))
        (interp2 V σ Aa) fun y => SetTheory.app (interp2 V σ Ba) y := by
    intro σ hσ
    refine mem_psigmaV2_app V ?_
    have hm := (heqTe σ hσ) ▸ hmemPe σ hσ
    rw [show AVExpr.mkAppN (m.acval Setlec.psigmaName ψ) [Aa, Ba]
        = AVExpr.app (.app (m.acval Setlec.psigmaName ψ) Aa) Ba from rfl,
      interp2_app, interp2_app, hleafI, interp2_const] at hm
    exact hm
  -- the two parameters' gradings
  obtain ⟨-, hoT⟩ := hoistP_spine [Aa, Ba] hokTe
  have hokAa : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ Aa :=
    hoT Aa (by simp)
  have hokBa : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ Ba :=
    hoT Ba (by simp)
  -- the subject's own grading (`AnnotOk2_proj` is the pack, verbatim)
  have hokProj : ∀ j : Nat, j < 2 → ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ ((.proj j vp) : AVExpr) := by
    intro j hj σ hσ
    obtain ⟨hA, hB, hsig⟩ := hpack σ hσ
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_proj]
      exact ⟨(hokPe σ hσ).1, hj, _, _, _, _, hsig, hA,
        fun x hx => psigmaFibre_apply V hB hx⟩
    · rw [AnnotValidV_proj]; exact (hokPe σ hσ).2
  have hokSubj : ∀ σ : Nat → V, Sat2 V Δa σ →
      AnnotOkP V σ ((.proj i vp) : AVExpr) := hokProj i hi2
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the first component
    obtain rfl : ta = Aa := Option.some.inj (hta.symm.trans hAa)
    refine ⟨hokSubj, hokAa, fun σ hσ => ?_⟩
    obtain ⟨hA, -, hsig⟩ := hpack σ hσ
    rw [interp2_proj, if_pos rfl]
    exact sfst_mem2 V hA hsig
  · -- the second component: the fibre at the first projection
    have hcompute : denoteP m.acval env φ d
        (Expr.app B (.proj Setlec.psigmaName 0 pe))
        = some ((.app Ba (.proj 0 vp)) : AVExpr) := by
      rw [denoteP_app, hBa, denoteP_proj, hvp]
      rfl
    obtain rfl : ta = .app Ba (.proj 0 vp) :=
      Option.some.inj (hta.symm.trans hcompute)
    refine ⟨hokSubj, fun σ hσ => ?_, fun σ hσ => ?_⟩
    · obtain ⟨hA, hB, hsig⟩ := hpack σ hσ
      refine ⟨?_, ?_⟩
      · rw [AnnotOk2_app]
        refine ⟨(hokBa σ hσ).1, (hokProj 0 (by omega) σ hσ).1, (ψ vN) + 1,
          interp2 V σ Aa, (fun _ => (univ (ψ vN) : V)), hB, ?_,
          fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
        rw [interp2_proj, if_pos rfl]
        exact sfst_mem2 V hA hsig
      · rw [AnnotValidV_app]
        exact ⟨(hokBa σ hσ).2, (hokProj 0 (by omega) σ hσ).2⟩
    · obtain ⟨hA, hB, hsig⟩ := hpack σ hσ
      rw [interp2_proj, if_neg (by omega), interp2_app, interp2_proj,
        if_pos rfl]
      exact ssnd_mem2 V hA hB hsig

/-! ## `ProjStepP` -/

/-- The pinned `PSigma'.mk` leaf's value, by erasure injectivity. -/
theorem acval_psigmaMk_leaf {m : EnvS2Core V env}
    (hfmk : env.find? Setlec.psigmaMkName = some Setlec.psigmaMkA)
    (ψ : Name → Nat) :
    m.acval Setlec.psigmaMkName ψ = .const .psigmaMk [ψ uN, ψ vN] :=
  erase_eq_const (by
    rw [m.acval_erase,
      (m.base.basis_pinned _ _ hfmk (by decide)).2 _ _ rfl])

/-- **`ProjStepP`, discharged.**  The stuck branch is a congruence
under `.proj`; the firing branch identifies the reduct's value with
`sfst`/`ssnd` of the constructor application through `sfst_mk2`/
`ssnd_mk2`, whose four typing premises are `psigmaMkSpineP`'s walk of
`projCert`'s own `inferTypeCore` run. -/
theorem projStepP_of_claims {m : EnvS2Core V env}
    (ihwc : WhnfCoreClaims2P μ m φ fuel) (ihw : WhnfClaims2P μ m φ fuel)
    (ihd : DefEqClaims2P μ m φ fuel) (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    ProjStepP μ m φ fuel := by
  intro d sn i pe e' Δa h hws hb hLb ea ea' hC hea hea' hokA
  obtain ⟨e₂, e₃, hwpe, hlit, hcase⟩ := Setlec.whnf_proj_inv h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkP m φ d Δa pe :=
    hC.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)
  obtain ⟨vp, hvp, hi2, rfl⟩ := denoteP_proj_inv hea
  have hokVp : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ vp := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · have h1 := (hokA σ hσ).1; rw [AnnotOk2_proj] at h1; exact h1.1
    · have h2 := (hokA σ hσ).2; rwa [AnnotValidV_proj] at h2
  -- the reduced scrutinee
  obtain ⟨v₂, hv₂⟩ := hwreads hwpe hws hb hLpe hvp
  obtain ⟨hok₂, heq₂⟩ := ihw hwpe hws hb hLpe hCpe hvp hv₂ hokVp
  have hw₂ : Expr.WScoped d e₂ := Setlec.whnf_WScoped m.base.wf fuel hwpe hws
  have hb₂ : e₂.looseBVarsBounded 0 = true :=
    Setlec.whnf_looseBVars m.base.wf fuel hwpe hb
  have hL₂ : Expr.LeavesBounded e₂ := fun l hl =>
    hLpe l (Setlec.whnf_fvarLeaves m.base.wf fuel hwpe l hl)
  have hC₂ : CtxOkP m φ d Δa e₂ :=
    hCpe.of_subset (Setlec.whnf_fvarLeaves m.base.wf fuel hwpe)
  -- the string-literal expansion, if it fired
  obtain ⟨v₃, hv₃, hok₃, heq₃, hw₃, hb₃, hL₃, hC₃⟩ :
      ∃ v₃, denoteP m.acval env φ d e₃ = some v₃ ∧
        (∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ v₃) ∧
        (∀ σ : Nat → V, Sat2 V Δa σ →
          interp2 V σ vp = interp2 V σ v₃) ∧
        Expr.WScoped d e₃ ∧ e₃.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₃ ∧ CtxOkP m φ d Δa e₃ := by
    rcases Setlec.projLitToCtorP_inv hlit with rfl | ⟨st, rfl, hg, hred⟩
    · exact ⟨v₂, hv₂, hok₂, heq₂, hw₂, hb₂, hL₂, hC₂⟩
    · obtain ⟨hSC, hwc, hbc, hLc, hfv⟩ := denotePStrLit_of_guard d st hg hv₂
      have hCc : CtxOkP m φ d Δa (Setlec.strLitToConstructor st) :=
        ⟨hCpe.1, fun l hl => by rw [hfv] at hl; exact nomatch hl⟩
      obtain ⟨v₃, hv₃⟩ := hwreads hred hwc hbc hLc hSC
      obtain ⟨hok₃, heq₃⟩ := ihw hred hwc hbc hLc hCc hSC hv₃ hok₂
      exact ⟨v₃, hv₃, hok₃,
        fun σ hσ => (heq₂ σ hσ).trans (heq₃ σ hσ),
        Setlec.whnf_WScoped m.base.wf fuel hred hwc,
        Setlec.whnf_looseBVars m.base.wf fuel hred hbc,
        fun l hl => hLc l (Setlec.whnf_fvarLeaves m.base.wf fuel hred l hl),
        hCc.of_subset (Setlec.whnf_fvarLeaves m.base.wf fuel hred)⟩
  rcases hcase with rfl |
    ⟨us, entry, hfn, hfe, hnat, hilt, hlenA, hlenU, hwcf, hcert⟩
  · -- stuck: the projection of the reduced scrutinee
    obtain ⟨v₃', hv₃', -, rfl⟩ := denoteP_proj_inv hea'
    obtain rfl : v₃' = v₃ := Option.some.inj (hv₃'.symm.trans hv₃)
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · refine ⟨?_, ?_⟩
      · have h1 := (hokA σ hσ).1
        rw [AnnotOk2_proj] at h1 ⊢
        obtain ⟨-, -, u, v, A, Bf, hsig, hA, hfib⟩ := h1
        exact ⟨(hok₃ σ hσ).1, hi2, u, v, A, Bf,
          (heq₃ σ hσ) ▸ hsig, hA, hfib⟩
      · rw [AnnotValidV_proj]; exact (hok₃ σ hσ).2
    · rw [interp2_proj, interp2_proj, heq₃ σ hσ]
  · -- the table fires
    obtain ⟨-, hidx, -, hnP, hnF, hctor, hlU, hpin, -, hfmk⟩ :=
      projPinsP m.base.proj_ok hfe hnat
    obtain ⟨l0, l1, rfl⟩ := Setlec.List.length_two (by rw [hlenU, hlU])
    obtain ⟨a0, a1, a2, a3, hargs⟩ :=
      Setlec.List.length_four (by rw [hlenA, hnP, hnF])
    have he₃ : e₃ = Expr.mkAppN (.const Setlec.psigmaMkName [l0, l1])
        [a0, a1, a2, a3] := by
      rw [← hargs, ← hctor, ← hfn]
      exact (Setlec.Expr.mkAppN_getApp e₃).symm
    -- the spine's frames and readings
    have hfr := frame_spineP hw₃ hb₃ hL₃ hC₃
    rw [hargs] at hfr
    have hv₃' := hv₃
    rw [he₃] at hv₃'
    obtain ⟨vf, vs, hvf, hspa, hveq⟩ := denoteP_mkAppN_inv hv₃'
    rw [denoteP_const hfmk (by rfl)] at hvf
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
        Level.substFn φ Setlec.psigmaMkA.toConstantVal.levelParams
          [l0, l1] = ψ := ⟨_, rfl⟩
    rw [hψ] at hvf
    obtain rfl : vf = m.acval Setlec.psigmaMkName ψ :=
      (Option.some.inj hvf).symm
    cases hspa with | @cons _ A0 _ _ hdA0 hs1 => ?_
    cases hs1 with | @cons _ A1 _ _ hdA1 hs2 => ?_
    cases hs2 with | @cons _ A2 _ _ hdA2 hs3 => ?_
    cases hs3 with | @cons _ A3 _ _ hdA3 hs4 => ?_
    cases hs4
    -- the leaf, and the level arguments
    have hleafM : m.acval Setlec.psigmaMkName ψ
        = .const .psigmaMk [ψ uN, ψ vN] := acval_psigmaMk_leaf hfmk ψ
    have hu0 : ψ uN = Level.eval φ l0 := by rw [← hψ]; rfl
    have hv0 : ψ vN = Level.eval φ l1 := by rw [← hψ]; rfl
    -- the four spine gradings
    have hok₃' : ∀ σ : Nat → V, Sat2 V Δa σ →
        AnnotOkP V σ (AVExpr.mkAppN (m.acval Setlec.psigmaMkName ψ)
          [A0, A1, A2, A3]) := by
      intro σ hσ; rw [← hveq]; exact hok₃ σ hσ
    obtain ⟨-, hoA⟩ := hoistP_spine [A0, A1, A2, A3] hok₃'
    -- the four typings, from the certificate's own infer run
    obtain ⟨ta, te, -, hite⟩ := Setlec.projCert_inv hcert
    rw [he₃] at hite
    have hpack := psigmaMkSpineP ihd ihi hreads hfmk hite
      (hfr a0 (by simp)) (hfr a1 (by simp)) (hfr a2 (by simp))
      (hfr a3 (by simp)) hdA0 hdA1 hdA2 hdA3
      (hoA A0 (by simp)) (hoA A1 (by simp)) (hoA A2 (by simp))
    -- the reduct's value
    have hval : ∀ σ : Nat → V, Sat2 V Δa σ →
        interp2 V σ vp = SetTheory.app (SetTheory.app (SetTheory.app
          (SetTheory.app (psigmaMkV2 V (ψ uN) (ψ vN)) (interp2 V σ A0))
            (interp2 V σ A1)) (interp2 V σ A2)) (interp2 V σ A3) := by
      intro σ hσ
      rw [heq₃ σ hσ, hveq]
      show interp2 V σ ((.app (.app (.app (.app
        (m.acval Setlec.psigmaMkName ψ) A0) A1) A2) A3) : AVExpr) = _
      rw [interp2_app, interp2_app, interp2_app, interp2_app, hleafM,
        interp2_const]
      rfl
    -- the selected field
    have hsel : ∀ j : Nat, entry.numParams + j
        = 2 + j := by intro j; rw [hnP]
    rcases hpin with rfl | rfl
    · -- first component
      obtain rfl : i = 0 := hidx.symm
      rw [hargs, hsel 0] at hwcf
      have hgetD : ([a0, a1, a2, a3] : List Expr).getD (2 + 0) (.bvar 0)
          = a2 := rfl
      rw [hgetD] at hwcf
      obtain ⟨hokE, heqE⟩ := ihwc hwcf (hfr a2 (by simp)).1
        (hfr a2 (by simp)).2.1 (hfr a2 (by simp)).2.2.1
        (hfr a2 (by simp)).2.2.2 hdA2 hea' (hoA A2 (by simp))
      refine ⟨hokE, fun σ hσ => ?_⟩
      obtain ⟨hA, hB, ha, hbb⟩ := hpack σ hσ
      rw [interp2_proj, if_pos rfl, hval σ hσ, ← heqE σ hσ]
      exact sfst_mk2 V (hu0 ▸ hA) (by rw [hv0]; exact hB) ha hbb
    · -- second component
      obtain rfl : i = 1 := hidx.symm
      rw [hargs, hsel 1] at hwcf
      have hgetD : ([a0, a1, a2, a3] : List Expr).getD (2 + 1) (.bvar 0)
          = a3 := rfl
      rw [hgetD] at hwcf
      obtain ⟨hokE, heqE⟩ := ihwc hwcf (hfr a3 (by simp)).1
        (hfr a3 (by simp)).2.1 (hfr a3 (by simp)).2.2.1
        (hfr a3 (by simp)).2.2.2 hdA3 hea' (hoA A3 (by simp))
      refine ⟨hokE, fun σ hσ => ?_⟩
      obtain ⟨hA, hB, ha, hbb⟩ := hpack σ hσ
      rw [interp2_proj, if_neg (by omega), hval σ hσ, ← heqE σ hσ]
      exact ssnd_mk2 V (hu0 ▸ hA) (by rw [hv0]; exact hB) ha hbb

end Setlec.SetR.Interp2
