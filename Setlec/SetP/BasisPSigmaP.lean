import Setlec.SetP.BasisEqP
import Setlec.SetBase.BasisRules
import Setlec.SetBase.PSigmaTower

/-!
# The `PSigma'` block, P tier (task #161, ENDGAME H)

The basis tier's last block, and the only one that installs
`projInfo` constants — so the only one whose `caps_ok` row is taken
through `capsOkP_cons_fresh` (a kind no stored family mentions)
rather than the reserved-name route.

Three of its five constants are the tier's three remaining hand-built
towers (the ENDGAME E seal's item 3): `PSigma'.rec` and the pair's two
projections are not `pinnedDirectT`.  All three are *forced*, not
chosen:

* `PSigma'.rec`'s motive lands in `Sort 0` and every one of its
  binders is pinned `.ifAllZero []`, so the whole constant is in the
  squash regime and the `Quot.ind` kit applies verbatim — its tower's
  value is the canonical proof and its row's fired equality is
  `pt = pt`;
* the two projections' binders are all `.never`, so their towers are
  graph-regime throughout, and their bodies are the layer's own
  `.proj` former.

`PSigma'.mk` is the tier's only `.ifAllZero [u, v]` pin (ENDGAME G
§2), and `pwBit_ifAllZero_pair` meets `Nat.max u v = 0` on the nose.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr psigmaRecValT pairProjValT)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

section PSigma

open Setlec (psigmaA psigmaMkA psigmaRecA pairFstA pairSndA psigmaName
  psigmaMkName)

variable {m : EnvS2Core V env} {A : (Name → Nat) → AVExpr}

/-! ## The block's two pinned leaves and applied formers -/

theorem denoteP_psigmaLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = psigmaName)
    (hP : env.find? psigmaName = some psigmaA) (d : Nat) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const psigmaName [.param uN, .param vN])
      = some (AVExpr.const .psigma [ψ uN, ψ vN]) := by
  refine denoteP_pinned_const (m := m) hne hP (by decide) (by rfl) ?_ d
  simp +decide [Setlec.TTVerify.pinnedDirectT]
  refine ⟨?_, ?_⟩
  · show Level.substFn ψ [uN, vN]
      [Level.param uN, Level.param vN] uN = ψ uN
    rfl
  · show Level.substFn ψ [uN, vN]
      [Level.param uN, Level.param vN] vN = ψ vN
    rfl

theorem denoteP_psigmaMkLeaf {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = psigmaMkName)
    (hM : env.find? psigmaMkName = some psigmaMkA) (d : Nat) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const psigmaMkName [.param uN, .param vN])
      = some (AVExpr.const .psigmaMk [ψ uN, ψ vN]) := by
  refine denoteP_pinned_const (m := m) hne hM (by decide) (by rfl) ?_ d
  simp +decide [Setlec.TTVerify.pinnedDirectT]
  refine ⟨?_, ?_⟩
  · show Level.substFn ψ [uN, vN]
      [Level.param uN, Level.param vN] uN = ψ uN
    rfl
  · show Level.substFn ψ [uN, vN]
      [Level.param uN, Level.param vN] vN = ψ vN
    rfl

/-- `@PSigma'.{u,v} α β`, at two de Bruijn slots. -/
def psigmaAppP (u v i j : Nat) : AVExpr :=
  .app (.app (.const .psigma [u, v]) (.bvar i)) (.bvar j)

/-- `@PSigma'.mk.{u,v} α β a b`, at four de Bruijn slots. -/
def psigmaMkAppP (u v i j k l : Nat) : AVExpr :=
  .app (.app (.app (.app (.const .psigmaMk [u, v]) (.bvar i))
    (.bvar j)) (.bvar k)) (.bvar l)

/-- The fibre binder's domain reading: `α → Sort v`, graph-regime
(its codomain is a *type*). -/
def psigmaFibreTyP (ψ : Name → Nat) : AVExpr :=
  .pi 0 1 (.bvar 0) (.sort (ψ vN))

theorem psigmaFibreTyP_interp (ψ : Name → Nat) (ρ : Nat → V)
    (Aset : V) :
    interp2 V (cons Aset ρ) (psigmaFibreTyP ψ)
      = psigmaFibreSpace V (ψ vN) Aset := by
  rw [psigmaFibreTyP, interp2_pi, psigmaFibreSpace]
  simp only [interp2_bvar, cons]
  refine piR_zero_agree (Iff.intro (fun h => absurd h Nat.one_ne_zero)
    (fun h => absurd h (Nat.succ_ne_zero _))) fun _ _ => ?_
  rw [interp2_sort]

theorem psigmaFibreTyP_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (psigmaFibreTyP ψ) :=
  ⟨⟨trivial, fun _ _ => trivial⟩,
    ⟨trivial, fun _ _ => trivial,
      fun h => absurd h Nat.one_ne_zero⟩⟩

theorem bitAgree_psigmaFibreTyP (ψ : Name → Nat) (u : Nat) :
    AVExpr.BitAgree (psigmaFibreTyP ψ)
      (arrowA u (ψ vN + 1) (.bvar 0) (.sort (ψ vN))) :=
  .pi (Iff.intro (fun h => absurd h Nat.one_ne_zero)
      (fun h => absurd h (Nat.succ_ne_zero _)))
    (.bvar 0) (.sort _)

theorem psigmaApp_data {u v i j : Nat} {ρ : Nat → V} {Aset B : V}
    (hi : ρ i = Aset) (hj : ρ j = B)
    (hA : Aset ∈ˢ (univ u : V)) (hB : B ∈ˢ psigmaFibreSpace V v Aset) :
    AnnotOk2 V ρ (psigmaAppP u v i j) ∧
      AnnotValidV V ρ (psigmaAppP u v i j) ∧
      interp2 V ρ (psigmaAppP u v i j)
        = sigmaSet (Nat.max u v) Aset (fun x => app B x) := by
  have hAi : interp2 V ρ (AVExpr.bvar i) = Aset := by
    rw [interp2_bvar, hi]
  have hBj : interp2 V ρ (AVExpr.bvar j) = B := by
    rw [interp2_bvar, hj]
  have hA' : Aset ∈ˢ interp2 V ρ (AVExpr.sort u) := by
    rw [interp2_sort]; exact hA
  have hB' : B ∈ˢ interp2 V (cons Aset ρ)
      (arrowA u (v + 1) (.bvar 0) (.sort v)) := by
    rw [show interp2 V (cons Aset ρ)
        (arrowA u (v + 1) (.bvar 0) (.sort v))
      = psigmaFibreSpace V v Aset from by
        rw [arrowA, interp2_pi, psigmaFibreSpace]
        simp only [interp2_bvar, cons, AVExpr.lift, AVExpr.liftN,
          interp2_sort]]
    exact hB
  refine ⟨?_, ⟨⟨trivial, trivial⟩, trivial⟩, ?_⟩
  · rw [psigmaAppP, AnnotOk2_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨trivial, trivial, ?_⟩
      have h := bconst_app_data V .psigma [u, v] ρ (A := .sort u) rfl hA'
      rw [← hAi] at h
      exact h
    · have h := bconst_app_data2 V .psigma [u, v] ρ (A := .sort u)
        (A2 := arrowA u (v + 1) (.bvar 0) (.sort v)) rfl hA' hB'
      rw [← hAi, ← hBj] at h
      simpa [interp2_const, bval2, Setlec.TT.lv] using h
  · rw [psigmaAppP]
    simp only [interp2_app, interp2_const, bval2, Setlec.TT.lv,
      List.getD_cons_zero, List.getD_cons_succ, hAi, hBj]
    exact psigmaV2_app V hA hB

theorem psigmaMkApp_data {u v i j k l : Nat} {ρ : Nat → V}
    {Aset B a b : V}
    (hi : ρ i = Aset) (hj : ρ j = B) (hk : ρ k = a) (hl : ρ l = b)
    (hA : Aset ∈ˢ (univ u : V)) (hB : B ∈ˢ psigmaFibreSpace V v Aset)
    (ha : a ∈ˢ Aset) (hb : b ∈ˢ app B a) :
    AnnotOk2 V ρ (psigmaMkAppP u v i j k l) ∧
      AnnotValidV V ρ (psigmaMkAppP u v i j k l) ∧
      interp2 V ρ (psigmaMkAppP u v i j k l)
        = app (app (app (app (psigmaMkV2 V u v) Aset) B) a) b := by
  have hAi : interp2 V ρ (AVExpr.bvar i) = Aset := by
    rw [interp2_bvar, hi]
  have hBj : interp2 V ρ (AVExpr.bvar j) = B := by
    rw [interp2_bvar, hj]
  have hak : interp2 V ρ (AVExpr.bvar k) = a := by
    rw [interp2_bvar, hk]
  have hbl : interp2 V ρ (AVExpr.bvar l) = b := by
    rw [interp2_bvar, hl]
  have hA' : Aset ∈ˢ interp2 V ρ (AVExpr.sort u) := by
    rw [interp2_sort]; exact hA
  have hB' : B ∈ˢ interp2 V (cons Aset ρ)
      (arrowA u (v + 1) (.bvar 0) (.sort v)) := by
    rw [show interp2 V (cons Aset ρ)
        (arrowA u (v + 1) (.bvar 0) (.sort v))
      = psigmaFibreSpace V v Aset from by
        rw [arrowA, interp2_pi, psigmaFibreSpace]
        simp only [interp2_bvar, cons, AVExpr.lift, AVExpr.liftN,
          interp2_sort]]
    exact hB
  have ha' : a ∈ˢ interp2 V (cons B (cons Aset ρ)) (AVExpr.bvar 1) := by
    simpa [interp2_bvar, cons] using ha
  have hb' : b ∈ˢ interp2 V (cons a (cons B (cons Aset ρ)))
      (.app (.bvar 1) (.bvar 0)) := by
    simpa [interp2_app, interp2_bvar, cons] using hb
  refine ⟨?_, ⟨⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial⟩, trivial⟩, ?_⟩
  · rw [psigmaMkAppP, AnnotOk2_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨?_, trivial, ?_⟩
      · rw [AnnotOk2_app]
        refine ⟨?_, trivial, ?_⟩
        · rw [AnnotOk2_app]
          refine ⟨trivial, trivial, ?_⟩
          have h := bconst_app_data V .psigmaMk [u, v] ρ (A := .sort u)
            rfl hA'
          rw [← hAi] at h
          exact h
        · have h := bconst_app_data2 V .psigmaMk [u, v] ρ
            (A := .sort u)
            (A2 := arrowA u (v + 1) (.bvar 0) (.sort v)) rfl hA' hB'
          rw [← hAi, ← hBj] at h
          simpa [interp2_const, bval2, Setlec.TT.lv] using h
      · have h := bconst_app_data3 V .psigmaMk [u, v] ρ (A := .sort u)
          (A2 := arrowA u (v + 1) (.bvar 0) (.sort v)) (A3 := .bvar 1)
          rfl hA' hB' ha'
        rw [← hAi, ← hBj, ← hak] at h
        simpa [interp2_const, bval2, Setlec.TT.lv] using h
    · have h := bconst_app_data4 V .psigmaMk [u, v] ρ (A := .sort u)
        (A2 := arrowA u (v + 1) (.bvar 0) (.sort v)) (A3 := .bvar 1)
        (A4 := .app (.bvar 1) (.bvar 0)) rfl hA' hB' ha' hb'
      rw [← hAi, ← hBj, ← hak, ← hbl] at h
      simpa [interp2_const, bval2, Setlec.TT.lv] using h
  · rw [psigmaMkAppP]
    simp only [interp2_app, interp2_const, bval2, Setlec.TT.lv,
      List.getD_cons_zero, List.getD_cons_succ, hAi, hBj, hak, hbl]

/-! ## `PSigma'` and `PSigma'.mk` -/

/-- `PSigma'`'s type reading. -/
def psigmaTyP (ψ : Name → Nat) : AVExpr :=
  .pi 0 1 (.sort (ψ uN))
    (.pi 0 1 (psigmaFibreTyP ψ) (.sort (Nat.max (ψ uN) (ψ vN))))

/-- `PSigma'.mk`'s type reading. -/
def psigmaMkTyP (b : Nat) (ψ : Name → Nat) : AVExpr :=
  .pi 0 b (.sort (ψ uN))
    (.pi 0 b (psigmaFibreTyP ψ)
      (.pi 0 b (.bvar 1)
        (.pi 0 b (.app (.bvar 1) (.bvar 0))
          (psigmaAppP (ψ uN) (ψ vN) 3 2))))

theorem denoteP_psigmaA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨psigmaA :: env.consts⟩ ψ 0
        psigmaA.toConstantVal.type = some (psigmaTyP ψ) := by
  simp [psigmaA, ConstantInfo.toConstantVal, denoteP_forallE,
    denoteP_sort, denoteP_fvar, Expr.instantiate1, psigmaTyP,
    psigmaFibreTyP, pwBit_never, Level.eval, uN, vN]

theorem bitAgree_psigmaA (ψ : Name → Nat) :
    AVExpr.BitAgree (psigmaTyP ψ) (BConst.type2 .psigma [ψ uN, ψ vN]) := by
  have h1 : (1 : Nat) = 0 ↔ Nat.max (ψ uN) (ψ vN) + 1 = 0 :=
    Iff.intro (fun h => absurd h Nat.one_ne_zero)
      (fun h => absurd h (Nat.succ_ne_zero _))
  exact .pi h1 (.sort _)
    (.pi h1 (bitAgree_psigmaFibreTyP ψ (ψ uN)) (.sort _))

/-- **`PSigma'.mk`'s type reading.**  Stated at any extension whose
cons is neither `PSigma'` nor `PSigma'.mk`, because the recursor's row
reads it as its fired constructor's telescope. -/
theorem denoteP_psigmaMkTy {c₀ : ConstantInfo} (ψ : Name → Nat)
    (hne : ¬ c₀.name = psigmaName)
    (hP : env.find? psigmaName = some psigmaA) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ 0
        psigmaMkA.toConstantVal.type
      = some (psigmaMkTyP (pwBit ψ (.ifAllZero [uN, vN])) ψ) := by
  have hPc : ∀ d : Nat,
      denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const psigmaName [.param uN, .param vN])
        = some (AVExpr.const .psigma [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaLeaf (m := m) (A := A) ψ hne hP d
  rw [show psigmaMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "fst") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "snd")
                (.app (.bvar 1) (.bvar 0))
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 3)) (.bvar 2))
                { bi := .default, pw := .ifAllZero [uN, vN] })
              { bi := .default, pw := .ifAllZero [uN, vN] })
            { bi := .implicit, pw := .ifAllZero [uN, vN] })
          { bi := .implicit, pw := .ifAllZero [uN, vN] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, psigmaMkTyP, psigmaFibreTyP, psigmaAppP,
    pwBit_never, hPc, Level.eval]

theorem denoteP_psigmaMkA_type (ψ : Name → Nat)
    (hP : env.find? psigmaName = some psigmaA) :
    denoteP (acvalWith m.acval psigmaMkA.name A)
        ⟨psigmaMkA :: env.consts⟩ ψ 0 psigmaMkA.toConstantVal.type
      = some (psigmaMkTyP (pwBit ψ (.ifAllZero [uN, vN])) ψ) :=
  denoteP_psigmaMkTy (m := m) (A := A) ψ (by decide) hP

theorem bitAgree_psigmaMkA (ψ : Name → Nat) :
    AVExpr.BitAgree (psigmaMkTyP (pwBit ψ (.ifAllZero [uN, vN])) ψ)
      (BConst.type2 .psigmaMk [ψ uN, ψ vN]) := by
  have hz : pwBit ψ (Setlec.PropWhen.ifAllZero [uN, vN]) = 0
      ↔ Nat.max (ψ uN) (ψ vN) = 0 := by
    rw [pwBit_ifAllZero_pair]
    refine Iff.intro (fun h => by rw [h.1, h.2]; rfl) (fun h => ?_)
    exact ⟨Nat.le_zero.mp (h ▸ Nat.le_max_left (ψ uN) (ψ vN)),
      Nat.le_zero.mp (h ▸ Nat.le_max_right (ψ uN) (ψ vN))⟩
  rw [psigmaMkTyP]
  exact .pi hz (.sort _)
    (.pi hz (bitAgree_psigmaFibreTyP ψ (ψ uN))
      (.pi hz (.bvar 1)
        (.pi hz (.app (.bvar 1) (.bvar 0))
          (.app (.app (.const _ _) (.bvar 3)) (.bvar 2)))))

/-! ### The two pinned installs -/

theorem extendPSigmaP (mp : EnvS2PM V μ env)
    (hfresh : env.find? psigmaName = none)
    (hwf : EnvWF ⟨psigmaA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨psigmaA :: env.consts⟩) := by
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .psigma [ψ uN, ψ vN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHeadP.ofBasis hwf (fun _ => trivial) (fun _ => rfl)
      (fun ψ t hp => by
        rw [show Setlec.TTVerify.pinnedDirectT psigmaA.name ψ
          = some (VExpr.const .psigma [ψ uN, ψ vN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteP_psigmaA_type ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [denoteP_psigmaA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_psigmaA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .psigma [ψ uN, ψ vN] ρ)
  · intro ψ ta h ρ
    rw [denoteP_psigmaA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_psigmaA ψ) ρ]
    exact bval2_mem_type V .psigma [ψ uN, ψ vN] ρ

theorem extendPSigmaMkP (mp : EnvS2PM V μ env)
    (hP : env.find? psigmaName = some psigmaA)
    (hfresh : env.find? psigmaMkName = none)
    (hwf : EnvWF ⟨psigmaMkA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨psigmaMkA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_psigmaMkA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .psigmaMk [ψ uN, ψ vN]) ψ hP
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .psigmaMk [ψ uN, ψ vN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    (ConsHeadP.ofBasis hwf (fun _ => trivial) (fun _ => rfl)
      (fun ψ t hp => by
        rw [show Setlec.TTVerify.pinnedDirectT psigmaMkA.name ψ
          = some (VExpr.const .psigmaMk [ψ uN, ψ vN]) from rfl] at hp
        rw [← Option.some.inj hp]
        rfl)
      (fun _ h => nomatch h) (fun _ _ _ _ h => nomatch h))
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_psigmaMkA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .psigmaMk [ψ uN, ψ vN] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_psigmaMkA ψ) ρ]
    exact bval2_mem_type V .psigmaMk [ψ uN, ψ vN] ρ

/-! ## The pair's two projections

The block's `projInfo` conses.  Their binders are all `.never`, so
both towers are graph-regime throughout and the readings' squash
clauses are all vacuous; the content is the `.proj` node's own
`AnnotOk2` clause, whose sigma witness is the third binder's domain. -/

/-- The projections' annotated valuation: the layer's `.proj` former
under the two parameter binders. -/
def pairProjValT2 (i : Nat) (ψ : Name → Nat) : AVExpr :=
  .lam 1 (.sort (ψ uN))
    (.lam 1 (psigmaFibreTyP ψ)
      (.lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0) (.proj i (.bvar 0))))

@[simp] theorem pairProjValT2_erase (i : Nat) (ψ : Name → Nat) :
    (pairProjValT2 i ψ).erase = pairProjValT i ψ := rfl

theorem pairProjValT2_congr {i : Nat} {ψ₁ ψ₂ : Name → Nat}
    (hu : ψ₁ uN = ψ₂ uN) (hv : ψ₁ vN = ψ₂ vN) :
    pairProjValT2 i ψ₁ = pairProjValT2 i ψ₂ := by
  rw [pairProjValT2, pairProjValT2, psigmaFibreTyP, psigmaAppP,
    psigmaFibreTyP, psigmaAppP, hu, hv]

/-- The two type readings: `.bvar 2` at `fst`, the fibre at the first
projection at `snd`. -/
def pairProjTyP (i : Nat) (ψ : Name → Nat) : AVExpr :=
  .pi 0 1 (.sort (ψ uN))
    (.pi 0 1 (psigmaFibreTyP ψ)
      (.pi 0 1 (psigmaAppP (ψ uN) (ψ vN) 1 0)
        (if i = 0 then .bvar 2 else .app (.bvar 1) (.proj 0 (.bvar 0)))))

/-- The `.proj` node's grading data, at the block's own sigma. -/
theorem pairProj_data {u v i : Nat} {ρ : Nat → V} {Aset B p : V}
    (hi : i < 2) (hp : ρ 0 = p)
    (hA : Aset ∈ˢ (univ u : V)) (hB : B ∈ˢ psigmaFibreSpace V v Aset)
    (hpm : p ∈ˢ sigmaSet (Nat.max u v) Aset (fun x => app B x)) :
    AnnotOkP V ρ (.proj i (.bvar 0)) ∧
      interp2 V ρ (.proj i (.bvar 0))
        = (if i = 0 then sfst p else ssnd p) := by
  have h0 : interp2 V ρ (AVExpr.bvar 0) = p := by rw [interp2_bvar, hp]
  refine ⟨⟨?_, trivial⟩, by rw [interp2_proj, h0]⟩
  rw [AnnotOk2_proj]
  exact ⟨trivial, hi, u, v, Aset, fun x => app B x,
    by rw [h0]; exact hpm, hA,
    fun x hx => psigmaFibre_apply V hB hx⟩

theorem pairProjTyP_data {i : Nat} (hi : i < 2) (ψ : Name → Nat)
    (ρ : Nat → V) :
    AnnotOkP V ρ (pairProjTyP i ψ) ∧
      AnnotOkP V ρ (pairProjValT2 i ψ) ∧
      interp2 V ρ (pairProjValT2 i ψ)
        ∈ˢ interp2 V ρ (pairProjTyP i ψ) := by
  have hstep : ∀ Aset B : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      interp2 V (cons B (cons Aset ρ))
          (psigmaAppP (ψ uN) (ψ vN) 1 0)
        = sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset (fun x => app B x) ∧
      AnnotOkP V (cons B (cons Aset ρ))
        (psigmaAppP (ψ uN) (ψ vN) 1 0) := by
    intro Aset B hA hB
    obtain ⟨hok, hval, hint⟩ := psigmaApp_data
      (ρ := cons B (cons Aset ρ)) (i := 1) (j := 0)
      (by simp [cons]) (by simp [cons]) hA hB
    exact ⟨hint, hok, hval⟩
  have hbody : ∀ Aset B p : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      p ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset (fun x => app B x) →
      AnnotOkP V (cons p (cons B (cons Aset ρ)))
          (if i = 0 then .bvar 2
            else .app (.bvar 1) (.proj 0 (.bvar 0))) ∧
        interp2 V (cons p (cons B (cons Aset ρ)))
            (if i = 0 then .bvar 2
              else .app (.bvar 1) (.proj 0 (.bvar 0)))
          = (if i = 0 then Aset else app B (sfst p)) ∧
        AnnotOkP V (cons p (cons B (cons Aset ρ)))
          (AVExpr.proj i (.bvar 0)) ∧
        interp2 V (cons p (cons B (cons Aset ρ)))
            (AVExpr.proj i (.bvar 0))
          ∈ˢ (if i = 0 then Aset else app B (sfst p)) := by
    intro Aset B p hA hB hp
    obtain ⟨hpok, -⟩ := pairProj_data (u := ψ uN) (v := ψ vN)
      (i := 0) (ρ := cons p (cons B (cons Aset ρ)))
      (by decide) (by simp [cons]) hA hB hp
    obtain ⟨hiok, hiint⟩ := pairProj_data (u := ψ uN) (v := ψ vN)
      (i := i) (ρ := cons p (cons B (cons Aset ρ)))
      hi (by simp [cons]) hA hB hp
    have hpint : interp2 V (cons p (cons B (cons Aset ρ)))
        (AVExpr.proj 0 (.bvar 0)) = sfst p := by
      rw [interp2_proj, if_pos rfl]
      simp [interp2_bvar, cons]
    by_cases h0 : i = 0
    · subst h0
      refine ⟨⟨trivial, trivial⟩, by simp [interp2_bvar, cons], hiok, ?_⟩
      rw [hiint]
      exact sfst_mem2 V hA hp
    · simp only [if_neg h0]
      have hBb : interp2 V (cons p (cons B (cons Aset ρ)))
          (AVExpr.bvar 1) = B := by simp [interp2_bvar, cons]
      refine ⟨⟨?_, ⟨trivial, hpok.2⟩⟩, ?_, hiok, ?_⟩
      · rw [AnnotOk2_app]
        exact ⟨trivial, hpok.1, ψ vN + 1, Aset,
          fun _ => (univ (ψ vN) : V),
          by rw [hBb]; exact hB, by rw [hpint]; exact sfst_mem2 V hA hp,
          fun h => absurd h (Nat.succ_ne_zero _)⟩
      · rw [interp2_app, hBb, hpint]
      · rw [hiint, if_neg h0]
        exact ssnd_mem2 V hA hB hp
  have hTy : interp2 V ρ (pairProjTyP i ψ)
      = piR 1 (univ (ψ uN) : V) (fun Aset =>
        piR 1 (psigmaFibreSpace V (ψ vN) Aset) (fun B =>
          piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
              (fun x => app B x))
            (fun p => if i = 0 then Aset else app B (sfst p)))) := by
    rw [pairProjTyP, interp2_pi, interp2_sort]
    refine piR_congr fun Aset hA => ?_
    rw [interp2_pi, psigmaFibreTyP_interp]
    refine piR_congr fun B hB => ?_
    rw [interp2_pi, (hstep Aset B hA hB).1]
    exact piR_congr fun p hp => (hbody Aset B p hA hB hp).2.1
  refine ⟨?_, ?_⟩
  · rw [pairProjTyP]
    refine AnnotOkP_pi_bit (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
      (fun Aset hA => ?_) (fun h => absurd h Nat.one_ne_zero)
    rw [interp2_sort] at hA
    refine AnnotOkP_pi_bit (Aa := psigmaFibreTyP ψ)
      (psigmaFibreTyP_okP ψ _) (fun B hB => ?_)
      (fun h => absurd h Nat.one_ne_zero)
    rw [psigmaFibreTyP_interp] at hB
    refine AnnotOkP_pi_bit (hstep Aset B hA hB).2 (fun p hp => ?_)
      (fun h => absurd h Nat.one_ne_zero)
    rw [(hstep Aset B hA hB).1] at hp
    exact (hbody Aset B p hA hB hp).1
  · have h3 : ∀ Aset B : V, Aset ∈ˢ (univ (ψ uN) : V) →
        B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
        AnnotOkP V (cons B (cons Aset ρ))
            (.lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0)
              (.proj i (.bvar 0))) ∧
          interp2 V (cons B (cons Aset ρ))
              (.lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0)
                (.proj i (.bvar 0)))
            ∈ˢ piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
                (fun x => app B x))
              (fun p => if i = 0 then Aset else app B (sfst p)) := by
      intro Aset B hA hB
      have hw := AnnotOkP_lam_mem (V := V) (b := 1)
        (Aa := psigmaAppP (ψ uN) (ψ vN) 1 0)
        (bd := AVExpr.proj i (.bvar 0)) (ρ := cons B (cons Aset ρ))
        (F := fun p => if i = 0 then Aset else app B (sfst p))
        (hstep Aset B hA hB).2
        (fun p hp => by
          rw [(hstep Aset B hA hB).1] at hp
          exact ⟨(hbody Aset B p hA hB hp).2.2.1,
            (hbody Aset B p hA hB hp).2.2.2⟩)
        (fun h => absurd h Nat.one_ne_zero)
      rw [(hstep Aset B hA hB).1] at hw
      exact hw
    have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
        AnnotOkP V (cons Aset ρ)
            (.lam 1 (psigmaFibreTyP ψ)
              (.lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0)
                (.proj i (.bvar 0)))) ∧
          interp2 V (cons Aset ρ)
              (.lam 1 (psigmaFibreTyP ψ)
                (.lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0)
                  (.proj i (.bvar 0))))
            ∈ˢ piR 1 (psigmaFibreSpace V (ψ vN) Aset) (fun B =>
              piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
                  (fun x => app B x))
                (fun p => if i = 0 then Aset else app B (sfst p))) := by
      intro Aset hA
      have hw := AnnotOkP_lam_mem (V := V) (b := 1)
        (Aa := psigmaFibreTyP ψ)
        (bd := .lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0)
          (.proj i (.bvar 0))) (ρ := cons Aset ρ)
        (F := fun B => piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
            (fun x => app B x))
          (fun p => if i = 0 then Aset else app B (sfst p)))
        (psigmaFibreTyP_okP ψ _)
        (fun B hB => by
          rw [psigmaFibreTyP_interp] at hB
          exact h3 Aset B hA hB)
        (fun h => absurd h Nat.one_ne_zero)
      rw [psigmaFibreTyP_interp] at hw
      exact hw
    have hw := AnnotOkP_lam_mem (V := V) (b := 1)
      (Aa := .sort (ψ uN))
      (bd := .lam 1 (psigmaFibreTyP ψ)
        (.lam 1 (psigmaAppP (ψ uN) (ψ vN) 1 0) (.proj i (.bvar 0))))
      (ρ := ρ)
      (F := fun Aset => piR 1 (psigmaFibreSpace V (ψ vN) Aset)
        (fun B => piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
            (fun x => app B x))
          (fun p => if i = 0 then Aset else app B (sfst p))))
      ⟨trivial, trivial⟩
      (fun Aset hA => by
        rw [interp2_sort] at hA
        exact h2 Aset hA)
      (fun h => absurd h Nat.one_ne_zero)
    rw [interp2_sort] at hw
    rw [hTy, pairProjValT2]
    exact ⟨hw.1, hw.2⟩

/-- **`PSigma'.fst`'s type reading.** -/
theorem denoteP_pairFstA_type (ψ : Name → Nat)
    (hP : env.find? psigmaName = some psigmaA) :
    denoteP (acvalWith m.acval pairFstA.name A)
        ⟨pairFstA :: env.consts⟩ ψ 0 pairFstA.toConstantVal.type
      = some (pairProjTyP 0 ψ) := by
  have hPc : ∀ d : Nat,
      denoteP (acvalWith m.acval pairFstA.name A)
        ⟨pairFstA :: env.consts⟩ ψ d
        (.const psigmaName [.param uN, .param vN])
        = some (AVExpr.const .psigma [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaLeaf (m := m) (A := A) ψ (by decide) hP d
  rw [show pairFstA.toConstantVal.type
    = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
        (Expr.forallE (Name.anonymous.str "β")
          (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
            (.sort (.param vN)) { bi := .default, pw := .never })
          (Expr.forallE (Name.anonymous.str "t")
            (.app (.app (.const psigmaName [.param uN, .param vN])
              (.bvar 1)) (.bvar 0))
            (.bvar 2) { bi := .default, pw := .never })
          { bi := .implicit, pw := .never })
        { bi := .implicit, pw := .never } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, pairProjTyP, psigmaFibreTyP, psigmaAppP,
    pwBit_never, hPc, Level.eval]

/-- **`PSigma'.snd`'s type reading** — the tier's one `.proj` node in
a stored type. -/
theorem denoteP_pairSndA_type (ψ : Name → Nat)
    (hP : env.find? psigmaName = some psigmaA) :
    denoteP (acvalWith m.acval pairSndA.name A)
        ⟨pairSndA :: env.consts⟩ ψ 0 pairSndA.toConstantVal.type
      = some (pairProjTyP 1 ψ) := by
  have hPc : ∀ d : Nat,
      denoteP (acvalWith m.acval pairSndA.name A)
        ⟨pairSndA :: env.consts⟩ ψ d
        (.const psigmaName [.param uN, .param vN])
        = some (AVExpr.const .psigma [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaLeaf (m := m) (A := A) ψ (by decide) hP d
  rw [show pairSndA.toConstantVal.type
    = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
        (Expr.forallE (Name.anonymous.str "β")
          (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
            (.sort (.param vN)) { bi := .default, pw := .never })
          (Expr.forallE (Name.anonymous.str "t")
            (.app (.app (.const psigmaName [.param uN, .param vN])
              (.bvar 1)) (.bvar 0))
            (.app (.bvar 1) (.proj psigmaName 0 (.bvar 0)))
            { bi := .default, pw := .never })
          { bi := .implicit, pw := .never })
        { bi := .implicit, pw := .never } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    denoteP_proj, Expr.instantiate1, pairProjTyP, psigmaFibreTyP,
    psigmaAppP, pwBit_never, hPc, Level.eval]

/-- **`PSigma'.fst`, installed at the P tier** — a `projInfo` cons, so
`caps_ok` goes through the *kind* disjunct, not the reserved-name
one. -/
theorem extendPairFstP (mp : EnvS2PM V μ env)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hfresh : env.find? pairFstA.name = none)
    (hwf : EnvWF ⟨pairFstA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨pairFstA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_pairFstA_type (m := mp.base2) (A := pairProjValT2 0) ψ hP
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := pairProjValT2 0) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inr (And.intro (fun _ _ h => nomatch h)
      (And.intro (fun _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h))))
    (Or.inl (fun _ h => nomatch h))
    (⟨hwf,
      (fun ψ => by
        rw [pairProjValT2_erase 0 ψ]; exact pairProjValT_closed 0 ψ),
      (fun hres => absurd hres (by decide)),
      (fun entry heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact ⟨Or.inl rfl, hP, hM⟩),
      (fun _ entry heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        rfl),
      (fun entry heq => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        rfl),
      (fun _ _ _ _ h => nomatch h)⟩)
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k)
        (by rw [pairProjValT2_erase]; exact pairProjValT_closed 0 ψ)) 1)
    ?_
    (fun ψ ρ => (pairProjTyP_data (by decide) ψ ρ).2.1.1)
    (fun ψ ρ => (pairProjTyP_data (by decide) ψ ρ).2.1.2)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    exact pairProjValT2_congr
      (hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self))
      (hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (pairProjTyP_data (by decide) ψ ρ).1
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (pairProjTyP_data (by decide) ψ ρ).2.2

/-- **`PSigma'.snd`, installed at the P tier.** -/
theorem extendPairSndP (mp : EnvS2PM V μ env)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hfresh : env.find? pairSndA.name = none)
    (hwf : EnvWF ⟨pairSndA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨pairSndA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_pairSndA_type (m := mp.base2) (A := pairProjValT2 1) ψ hP
  refine nonempty_of_exists (declStepPM_of_basis_cons mp
    (A := pairProjValT2 1) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inr (And.intro (fun _ _ h => nomatch h)
      (And.intro (fun _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h))))
    (Or.inl (fun _ h => nomatch h))
    (⟨hwf,
      (fun ψ => by
        rw [pairProjValT2_erase 1 ψ]; exact pairProjValT_closed 1 ψ),
      (fun hres => absurd hres (by decide)),
      (fun entry heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact ⟨Or.inr rfl, hP, hM⟩),
      (fun _ entry heq _ => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        rfl),
      (fun entry heq => by
        obtain rfl := ConstantInfo.projInfo.inj heq
        rfl),
      (fun _ _ _ _ h => nomatch h)⟩)
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k)
        (by rw [pairProjValT2_erase]; exact pairProjValT_closed 1 ψ)) 1)
    ?_
    (fun ψ ρ => (pairProjTyP_data (by decide) ψ ρ).2.1.1)
    (fun ψ ρ => (pairProjTyP_data (by decide) ψ ρ).2.1.2)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_)
  · intro ψ₁ ψ₂ hp
    exact pairProjValT2_congr
      (hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self))
      (hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (pairProjTyP_data (by decide) ψ ρ).1
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (pairProjTyP_data (by decide) ψ ρ).2.2

/-! ## `PSigma'.rec`

Its motive lands in `Sort 0` and all five of its binders are pinned
`.ifAllZero []`, so the whole constant is in the squash regime — the
`Quot.ind` kit applies verbatim, and the only content anywhere is that
the major premise's fibre is inhabited, which is structure η
(`psigmaEta_law2`) applied to the minor premise at the subject's two
projections. -/

/-- `PSigma'.rec`'s motive binder domain reading. -/
def psigmaMotiveTyP (u v : Nat) : AVExpr :=
  .pi 0 1 (psigmaAppP u v 1 0) (.sort 0)

/-- `PSigma'.rec`'s minor binder domain reading. -/
def psigmaMinorTyP (u v : Nat) : AVExpr :=
  .pi 0 0 (.bvar 2)
    (.pi 0 0 (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 2) (psigmaMkAppP u v 4 3 1 0)))

/-- `PSigma'.rec`'s type reading. -/
def psigmaRecTyP (ψ : Name → Nat) : AVExpr :=
  .pi 0 0 (.sort (ψ uN))
    (.pi 0 0 (psigmaFibreTyP ψ)
      (.pi 0 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
        (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
          (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
            (.app (.bvar 2) (.bvar 0))))))

/-- `PSigma'.rec`'s annotated valuation: the minor premise at the
subject's two projections. -/
def psigmaRecValT2 (ψ : Name → Nat) : AVExpr :=
  .lam 0 (.sort (ψ uN))
    (.lam 0 (psigmaFibreTyP ψ)
      (.lam 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
        (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
          (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
            (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
              (.proj 1 (.bvar 0)))))))

@[simp] theorem psigmaRecValT2_erase (ψ : Name → Nat) :
    (psigmaRecValT2 ψ).erase = psigmaRecValT ψ := rfl

theorem psigmaRecValT2_congr {ψ₁ ψ₂ : Name → Nat}
    (hu : ψ₁ uN = ψ₂ uN) (hv : ψ₁ vN = ψ₂ vN) :
    psigmaRecValT2 ψ₁ = psigmaRecValT2 ψ₂ := by
  rw [psigmaRecValT2, psigmaRecValT2, psigmaFibreTyP, psigmaFibreTyP,
    hu, hv]

/-- `PSigma'.rec`'s rule's RHS reading. -/
def psigmaRecRaP (ψ : Name → Nat) : AVExpr :=
  .lam 0 (.sort (ψ uN))
    (.lam 0 (psigmaFibreTyP ψ)
      (.lam 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
        (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
          (.lam 0 (.bvar 3)
            (.lam 0 (.app (.bvar 3) (.bvar 0))
              (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)))))))

/-- The motive space: `PSigma' α β → Prop`. -/
noncomputable def psigmaMotiveSpace (V : Type w) [SetTheory V]
    (u v : Nat) (Aset B : V) : V :=
  piR 1 (sigmaSet (Nat.max u v) Aset (fun x => app B x))
    fun _ => (univ 0 : V)

/-- The minor space: `∀ a b, M ⟨a, b⟩`. -/
noncomputable def psigmaMinorSpace (V : Type w) [SetTheory V]
    (u v : Nat) (Aset B M : V) : V :=
  piR 0 Aset fun a => piR 0 (app B a) fun b =>
    app M (app (app (app (app (psigmaMkV2 V u v) Aset) B) a) b)

theorem psigmaMotiveTyP_data {ψ : Name → Nat} {Aset B : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V))
    (hB : B ∈ˢ psigmaFibreSpace V (ψ vN) Aset) :
    interp2 V (cons B (cons Aset ρ)) (psigmaMotiveTyP (ψ uN) (ψ vN))
        = psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B ∧
      AnnotOkP V (cons B (cons Aset ρ))
        (psigmaMotiveTyP (ψ uN) (ψ vN)) := by
  obtain ⟨hok, hval, hint⟩ := psigmaApp_data
    (ρ := cons B (cons Aset ρ)) (i := 1) (j := 0)
    (by simp [cons]) (by simp [cons]) hA hB
  refine ⟨?_, ⟨hok, fun _ _ => trivial⟩,
    ⟨hval, fun _ _ => trivial, fun h => absurd h Nat.one_ne_zero⟩⟩
  rw [psigmaMotiveTyP, interp2_pi, hint, psigmaMotiveSpace]
  exact piR_congr fun _ _ => interp2_sort V _ _

theorem psigmaMinorTyP_data {ψ : Name → Nat} {Aset B M : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V))
    (hB : B ∈ˢ psigmaFibreSpace V (ψ vN) Aset)
    (hM : M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B) :
    interp2 V (cons M (cons B (cons Aset ρ)))
        (psigmaMinorTyP (ψ uN) (ψ vN))
        = psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M ∧
      AnnotOkP V (cons M (cons B (cons Aset ρ)))
        (psigmaMinorTyP (ψ uN) (ψ vN)) := by
  have hdom : interp2 V (cons M (cons B (cons Aset ρ)))
      (AVExpr.bvar 2) = Aset := by simp [interp2_bvar, cons]
  have hM0 : M ∈ˢ piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
      (fun x => app B x)) fun _ => (univ 0 : V) := hM
  have hinner : ∀ a : V, a ∈ˢ Aset →
      interp2 V (cons a (cons M (cons B (cons Aset ρ))))
          (.app (.bvar 2) (.bvar 0)) = app B a ∧
        AnnotOkP V (cons a (cons M (cons B (cons Aset ρ))))
          (.app (.bvar 2) (.bvar 0)) := by
    intro a ha
    have hBb : interp2 V (cons a (cons M (cons B (cons Aset ρ))))
        (AVExpr.bvar 2) = B := by simp [interp2_bvar, cons]
    have hab : interp2 V (cons a (cons M (cons B (cons Aset ρ))))
        (AVExpr.bvar 0) = a := by simp [interp2_bvar, cons]
    refine ⟨by rw [interp2_app, hBb, hab], ?_, ⟨trivial, trivial⟩⟩
    rw [AnnotOk2_app]
    exact ⟨trivial, trivial, ψ vN + 1, Aset,
      fun _ => (univ (ψ vN) : V), by rw [hBb]; exact hB,
      by rw [hab]; exact ha, fun h => absurd h (Nat.succ_ne_zero _)⟩
  have hbody : ∀ a b : V, a ∈ˢ Aset → b ∈ˢ app B a →
      interp2 V (cons b (cons a (cons M (cons B (cons Aset ρ)))))
          (.app (.bvar 2) (psigmaMkAppP (ψ uN) (ψ vN) 4 3 1 0))
        = app M (app (app (app (app (psigmaMkV2 V (ψ uN) (ψ vN)) Aset)
            B) a) b) ∧
        AnnotOkP V (cons b (cons a (cons M (cons B (cons Aset ρ)))))
          (.app (.bvar 2) (psigmaMkAppP (ψ uN) (ψ vN) 4 3 1 0)) ∧
        app M (app (app (app (app (psigmaMkV2 V (ψ uN) (ψ vN)) Aset)
            B) a) b) ∈ˢ (univZero : V) := by
    intro a b ha hb
    obtain ⟨hmok, hmval, hmint⟩ := psigmaMkApp_data
      (ρ := cons b (cons a (cons M (cons B (cons Aset ρ)))))
      (i := 4) (j := 3) (k := 1) (l := 0)
      (by simp [cons]) (by simp [cons]) (by simp [cons])
      (by simp [cons]) hA hB ha hb
    have hMb : interp2 V (cons b (cons a (cons M (cons B
        (cons Aset ρ))))) (AVExpr.bvar 2) = M := by
      simp [interp2_bvar, cons]
    have hmk : app (app (app (app (psigmaMkV2 V (ψ uN) (ψ vN)) Aset) B)
        a) b ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
          (fun x => app B x) := by
      exact psigmaMkV2_mem V hA hB ha hb
    have hMv : app M (app (app (app (app (psigmaMkV2 V (ψ uN) (ψ vN))
        Aset) B) a) b) ∈ˢ (univ 0 : V) :=
      app_mem_piR_pos Nat.one_ne_zero hM0 hmk
    refine ⟨by rw [interp2_app, hMb, hmint], ?_, ?_⟩
    · refine ⟨?_, ⟨trivial, hmval⟩⟩
      rw [AnnotOk2_app]
      exact ⟨trivial, hmok, 1,
        sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset (fun x => app B x),
        fun _ => (univ 0 : V), by rw [hMb]; exact hM0,
        by rw [hmint]; exact hmk, fun h => absurd h Nat.one_ne_zero⟩
    · rw [← univ_zero]; exact hMv
  refine ⟨?_, ?_⟩
  · rw [psigmaMinorTyP, interp2_pi, hdom, psigmaMinorSpace]
    refine piR_congr fun a ha => ?_
    rw [interp2_pi, (hinner a ha).1]
    exact piR_congr fun b hb => (hbody a b ha hb).1
  · rw [psigmaMinorTyP]
    refine (AnnotOkP_pi_zero (Aa := .bvar 2) ⟨trivial, trivial⟩
      ?_ ?_).1
    all_goals (
      intro a ha
      rw [hdom] at ha
      have hlev := AnnotOkP_pi_zero
        (Aa := .app (.bvar 2) (.bvar 0)) (hinner a ha).2
        (fun b hb => by
          rw [(hinner a ha).1] at hb
          exact (hbody a b ha hb).2.1)
        (fun b hb => by
          rw [(hinner a ha).1] at hb
          rw [(hbody a b ha hb).1]
          exact (hbody a b ha hb).2.2))
    case _ => exact hlev.1
    case _ => exact hlev.2

/-- **The major premise's fibre is inhabited** — structure η at the
minor premise and the subject's two projections.  This is
`PSigma'.rec`'s entire content, and the reason the layer does not
carry the constant (`psigmaRec_derivable`). -/
theorem psigmaRec_fibre {u v : Nat} {Aset B M mn p : V}
    (hA : Aset ∈ˢ (univ u : V)) (hB : B ∈ˢ psigmaFibreSpace V v Aset)
    (hM : M ∈ˢ psigmaMotiveSpace V u v Aset B)
    (hmn : mn ∈ˢ psigmaMinorSpace V u v Aset B M)
    (hp : p ∈ˢ sigmaSet (Nat.max u v) Aset (fun x => app B x)) :
    app (app mn (sfst p)) (ssnd p) ∈ˢ app M p ∧
      app M p ∈ˢ (univ 0 : V) := by
  have hM0 : M ∈ˢ piR 1 (sigmaSet (Nat.max u v) Aset
      (fun x => app B x)) fun _ => (univ 0 : V) := hM
  have hmn0 : mn ∈ˢ piR 0 Aset (fun a => piR 0 (app B a) fun b =>
      app M (app (app (app (app (psigmaMkV2 V u v) Aset) B) a) b)) :=
    hmn
  have hfst : sfst p ∈ˢ Aset := sfst_mem2 V hA hp
  have hsnd : ssnd p ∈ˢ app B (sfst p) := ssnd_mem2 V hA hB hp
  have hMp : app M p ∈ˢ (univ 0 : V) :=
    app_mem_piR_pos Nat.one_ne_zero hM0 hp
  refine ⟨?_, hMp⟩
  have h1 := app_mem_piR hmn0 hfst
    (fun _ a ha => by
      refine piR_zero_mem_univZero)
  have h2 := app_mem_piR h1 hsnd
    (fun _ b hb => by
      rw [← univ_zero]
      exact app_mem_piR_pos Nat.one_ne_zero hM0
        (psigmaMkV2_mem V hA hB hfst hb))
  rwa [psigmaEta_law2 V hA hB hp] at h2

/-- **`PSigma'.rec`'s type reading.** -/
theorem denoteP_psigmaRecA_type (ψ : Name → Nat)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA) :
    denoteP (acvalWith m.acval psigmaRecA.name A)
        ⟨psigmaRecA :: env.consts⟩ ψ 0 psigmaRecA.toConstantVal.type
      = some (psigmaRecTyP ψ) := by
  have hPc : ∀ d : Nat,
      denoteP (acvalWith m.acval psigmaRecA.name A)
        ⟨psigmaRecA :: env.consts⟩ ψ d
        (.const psigmaName [.param uN, .param vN])
        = some (AVExpr.const .psigma [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaLeaf (m := m) (A := A) ψ (by decide) hP d
  have hMc : ∀ d : Nat,
      denoteP (acvalWith m.acval psigmaRecA.name A)
        ⟨psigmaRecA :: env.consts⟩ ψ d
        (.const psigmaMkName [.param uN, .param vN])
        = some (AVExpr.const .psigmaMk [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaMkLeaf (m := m) (A := A) ψ (by decide) hM d
  rw [show psigmaRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 1)) (.bvar 0))
                (.sort .zero) { bi := .default, pw := .never })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "fst") (.bvar 2)
                  (Expr.forallE (Name.anonymous.str "snd")
                    (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 2)
                      (.app (.app (.app (.app (.const psigmaMkName
                        [.param uN, .param vN]) (.bvar 4)) (.bvar 3))
                        (.bvar 1)) (.bvar 0)))
                    { bi := .default, pw := .ifAllZero [] })
                  { bi := .default, pw := .ifAllZero [] })
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.const psigmaName [.param uN, .param vN])
                    (.bvar 3)) (.bvar 2))
                  (.app (.bvar 2) (.bvar 0))
                  { bi := .default, pw := .ifAllZero [] })
                { bi := .default, pw := .ifAllZero [] })
              { bi := .implicit, pw := .ifAllZero [] })
            { bi := .implicit, pw := .ifAllZero [] })
          { bi := .implicit, pw := .ifAllZero [] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, psigmaRecTyP, psigmaFibreTyP, psigmaMotiveTyP,
    psigmaMinorTyP, psigmaAppP, psigmaMkAppP, pwBit_never,
    pwBit_ifAllZero_nil, hPc, hMc, Level.eval]

/-- **`PSigma'.rec`'s rule's RHS reading.** -/
theorem denoteP_psigmaRec_rhs (ψ : Name → Nat)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA) :
    denoteP (acvalWith m.acval psigmaRecA.name A)
        ⟨psigmaRecA :: env.consts⟩ ψ 0 psigmaRecRule.rhs
      = some (psigmaRecRaP ψ) := by
  have hPc : ∀ d : Nat,
      denoteP (acvalWith m.acval psigmaRecA.name A)
        ⟨psigmaRecA :: env.consts⟩ ψ d
        (.const psigmaName [.param uN, .param vN])
        = some (AVExpr.const .psigma [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaLeaf (m := m) (A := A) ψ (by decide) hP d
  have hMc : ∀ d : Nat,
      denoteP (acvalWith m.acval psigmaRecA.name A)
        ⟨psigmaRecA :: env.consts⟩ ψ d
        (.const psigmaMkName [.param uN, .param vN])
        = some (AVExpr.const .psigmaMk [ψ uN, ψ vN]) := fun d =>
    denoteP_psigmaMkLeaf (m := m) (A := A) ψ (by decide) hM d
  simp only [psigmaRecRule]
  simp [denoteP_lam, denoteP_forallE, denoteP_sort, denoteP_app,
    denoteP_fvar, Expr.instantiate1, psigmaRecRaP, psigmaFibreTyP,
    psigmaMotiveTyP, psigmaMinorTyP, psigmaAppP, psigmaMkAppP,
    pwBit_never, pwBit_ifAllZero_nil, hPc, hMc, Level.eval]

/-- The block's three walks share this: at a fixed parameter
quadruple, the five domains' readings and the body's. -/
theorem psigmaRec_domains {ψ : Name → Nat} {Aset B M mn : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V))
    (hB : B ∈ˢ psigmaFibreSpace V (ψ vN) Aset)
    (hM : M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B) :
    interp2 V (cons mn (cons M (cons B (cons Aset ρ))))
        (psigmaAppP (ψ uN) (ψ vN) 3 2)
        = sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset (fun x => app B x) ∧
      AnnotOkP V (cons mn (cons M (cons B (cons Aset ρ))))
        (psigmaAppP (ψ uN) (ψ vN) 3 2) ∧
      ∀ p : V, p ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
          (fun x => app B x) →
        interp2 V (cons p (cons mn (cons M (cons B (cons Aset ρ)))))
            (.app (.bvar 2) (.bvar 0)) = app M p ∧
          AnnotOkP V (cons p (cons mn (cons M (cons B (cons Aset ρ)))))
            (.app (.bvar 2) (.bvar 0)) := by
  obtain ⟨hok, hval, hint⟩ := psigmaApp_data
    (ρ := cons mn (cons M (cons B (cons Aset ρ)))) (i := 3) (j := 2)
    (by simp [cons]) (by simp [cons]) hA hB
  have hM0 : M ∈ˢ piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
      (fun x => app B x)) fun _ => (univ 0 : V) := hM
  refine ⟨hint, ⟨hok, hval⟩, fun p hp => ?_⟩
  have hMb : interp2 V (cons p (cons mn (cons M (cons B
      (cons Aset ρ))))) (AVExpr.bvar 2) = M := by
    simp [interp2_bvar, cons]
  have hpb : interp2 V (cons p (cons mn (cons M (cons B
      (cons Aset ρ))))) (AVExpr.bvar 0) = p := by
    simp [interp2_bvar, cons]
  refine ⟨by rw [interp2_app, hMb, hpb], ?_, ⟨trivial, trivial⟩⟩
  rw [AnnotOk2_app]
  exact ⟨trivial, trivial, 1,
    sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset (fun x => app B x),
    fun _ => (univ 0 : V), by rw [hMb]; exact hM0,
    by rw [hpb]; exact hp, fun h => absurd h Nat.one_ne_zero⟩

/-! ### The tower and the RHS, graded

Both are five (resp. six) squash-regime `λ`s whose bodies are the
canonical proof — the minor premise itself is, because its space is a
`piR 0`.  `AnnotOkP_lam_zero_pt` and `AnnotOkP_app_pt` do the whole
walk. -/

theorem psigmaRecValT2_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (psigmaRecValT2 ψ) = (pt : V) := by
  rw [psigmaRecValT2, interp2_lam, lamR_zero]

theorem psigmaRecRaP_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (psigmaRecRaP ψ) = (pt : V) := by
  rw [psigmaRecRaP, interp2_lam, lamR_zero]

/-- The tower's and the type reading's shared walk: at a fixed
parameter quadruple and subject, the body's grading and value. -/
theorem psigmaRec_body {ψ : Name → Nat} {Aset B M mn p : V}
    (ρ : Nat → V) (hA : Aset ∈ˢ (univ (ψ uN) : V))
    (hB : B ∈ˢ psigmaFibreSpace V (ψ vN) Aset)
    (hM : M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B)
    (hmn : mn ∈ˢ psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
    (hp : p ∈ˢ sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
      (fun x => app B x)) :
    AnnotOkP V (cons p (cons mn (cons M (cons B (cons Aset ρ)))))
        (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
          (.proj 1 (.bvar 0))) ∧
      interp2 V (cons p (cons mn (cons M (cons B (cons Aset ρ)))))
          (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
            (.proj 1 (.bvar 0))) = (pt : V) ∧
      (pt : V) ∈ˢ app M p := by
  obtain ⟨hfib, -⟩ := psigmaRec_fibre hA hB hM hmn hp
  have hmnpt : mn = pt := eq_pt_of_mem_piR_zero hmn
  obtain ⟨h0ok, h0int⟩ := pairProj_data (u := ψ uN) (v := ψ vN)
    (i := 0) (ρ := cons p (cons mn (cons M (cons B (cons Aset ρ)))))
    (by decide) (by simp [cons]) hA hB hp
  obtain ⟨h1ok, h1int⟩ := pairProj_data (u := ψ uN) (v := ψ vN)
    (i := 1) (ρ := cons p (cons mn (cons M (cons B (cons Aset ρ)))))
    (by decide) (by simp [cons]) hA hB hp
  simp only [if_neg (by decide : ¬ (1 = 0))] at h1int
  have hmnb : interp2 V (cons p (cons mn (cons M (cons B
      (cons Aset ρ))))) (AVExpr.bvar 1) = pt := by
    rw [interp2_bvar]
    show cons p (cons mn (cons M (cons B (cons Aset ρ)))) 1 = pt
    rw [show cons p (cons mn (cons M (cons B (cons Aset ρ)))) 1 = mn
      from rfl]
    exact hmnpt
  have hstep1 := AnnotOkP_app_pt (S := Aset)
    (f := AVExpr.bvar 1) (a := AVExpr.proj 0 (.bvar 0))
    ⟨trivial, trivial⟩ hmnb h0ok
    (by rw [h0int]; exact sfst_mem2 V hA hp)
  have hstep2 := AnnotOkP_app_pt (S := app B (sfst p))
    (a := AVExpr.proj 1 (.bvar 0)) hstep1.1 hstep1.2 h1ok
    (by rw [h1int]; exact ssnd_mem2 V hA hB hp)
  refine ⟨hstep2.1, hstep2.2, ?_⟩
  rw [hmnpt, app_pt, app_pt] at hfib
  exact hfib

theorem psigmaRecValT2_data (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (psigmaRecValT2 ψ) ∧
      interp2 V ρ (psigmaRecValT2 ψ)
        ∈ˢ interp2 V ρ (psigmaRecTyP ψ) := by
  have hTy : interp2 V ρ (psigmaRecTyP ψ)
      = piR 0 (univ (ψ uN) : V) (fun Aset =>
        piR 0 (psigmaFibreSpace V (ψ vN) Aset) (fun B =>
          piR 0 (psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B) (fun M =>
            piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
              (fun mn => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
                  (fun x => app B x))
                (fun p => app M p))))) := by
    rw [psigmaRecTyP, interp2_pi, interp2_sort]
    refine piR_congr fun Aset hA => ?_
    rw [interp2_pi, psigmaFibreTyP_interp]
    refine piR_congr fun B hB => ?_
    rw [interp2_pi, (psigmaMotiveTyP_data ρ hA hB).1]
    refine piR_congr fun M hM => ?_
    rw [interp2_pi, (psigmaMinorTyP_data ρ hA hB hM).1]
    refine piR_congr fun mn hmn => ?_
    rw [interp2_pi, (psigmaRec_domains ρ hA hB hM).1]
    exact piR_congr fun p hp => (psigmaRec_domains ρ hA hB hM).2.2 p hp
      |>.1
  have h5 : ∀ Aset B M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B →
      mn ∈ˢ psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M →
      AnnotOkP V (cons mn (cons M (cons B (cons Aset ρ))))
          (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
            (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
              (.proj 1 (.bvar 0)))) ∧
        interp2 V (cons mn (cons M (cons B (cons Aset ρ))))
            (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
              (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                (.proj 1 (.bvar 0))))
          ∈ˢ piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
              (fun x => app B x)) (fun p => app M p) := by
    intro Aset B M mn hA hB hM hmn
    have hw := AnnotOkP_lam_mem (V := V) (b := 0)
      (Aa := psigmaAppP (ψ uN) (ψ vN) 3 2)
      (bd := .app (.app (.bvar 1) (.proj 0 (.bvar 0)))
        (.proj 1 (.bvar 0)))
      (ρ := cons mn (cons M (cons B (cons Aset ρ))))
      (F := fun p => app M p) (psigmaRec_domains ρ hA hB hM).2.1
      (fun p hp => by
        rw [(psigmaRec_domains ρ hA hB hM).1] at hp
        exact ⟨(psigmaRec_body ρ hA hB hM hmn hp).1, by
          rw [(psigmaRec_body ρ hA hB hM hmn hp).2.1]
          exact (psigmaRec_body ρ hA hB hM hmn hp).2.2⟩)
      (fun _ p hp => by
        rw [(psigmaRec_domains ρ hA hB hM).1] at hp
        rw [← univ_zero]
        exact app_mem_piR_pos Nat.one_ne_zero
          (show M ∈ˢ piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
            (fun x => app B x)) fun _ => (univ 0 : V) from hM) hp)
    rw [(psigmaRec_domains ρ hA hB hM).1] at hw
    exact hw
  have h4 : ∀ Aset B M : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B →
      AnnotOkP V (cons M (cons B (cons Aset ρ)))
          (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
            (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
              (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                (.proj 1 (.bvar 0))))) ∧
        interp2 V (cons M (cons B (cons Aset ρ)))
            (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
              (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                  (.proj 1 (.bvar 0)))))
          ∈ˢ piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
            (fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
                (fun x => app B x)) (fun p => app M p)) := by
    intro Aset B M hA hB hM
    have hw := AnnotOkP_lam_mem (V := V) (b := 0)
      (Aa := psigmaMinorTyP (ψ uN) (ψ vN))
      (ρ := cons M (cons B (cons Aset ρ)))
      (F := fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
          (fun x => app B x)) (fun p => app M p))
      (psigmaMinorTyP_data ρ hA hB hM).2
      (fun mn hmn => by
        rw [(psigmaMinorTyP_data ρ hA hB hM).1] at hmn
        exact h5 Aset B M mn hA hB hM hmn)
      (fun _ _ _ => piR_zero_mem_univZero)
    rw [(psigmaMinorTyP_data ρ hA hB hM).1] at hw
    exact hw
  have h3 : ∀ Aset B : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      AnnotOkP V (cons B (cons Aset ρ))
          (.lam 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
            (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
              (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                  (.proj 1 (.bvar 0)))))) ∧
        interp2 V (cons B (cons Aset ρ))
            (.lam 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
              (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
                (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                  (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                    (.proj 1 (.bvar 0))))))
          ∈ˢ piR 0 (psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B)
            (fun M => piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
              (fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
                  (fun x => app B x)) (fun p => app M p))) := by
    intro Aset B hA hB
    have hw := AnnotOkP_lam_mem (V := V) (b := 0)
      (Aa := psigmaMotiveTyP (ψ uN) (ψ vN))
      (ρ := cons B (cons Aset ρ))
      (F := fun M => piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
        (fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
            (fun x => app B x)) (fun p => app M p)))
      (psigmaMotiveTyP_data ρ hA hB).2
      (fun M hM => by
        rw [(psigmaMotiveTyP_data ρ hA hB).1] at hM
        exact h4 Aset B M hA hB hM)
      (fun _ _ _ => piR_zero_mem_univZero)
    rw [(psigmaMotiveTyP_data ρ hA hB).1] at hw
    exact hw
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      AnnotOkP V (cons Aset ρ)
          (.lam 0 (psigmaFibreTyP ψ)
            (.lam 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
              (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
                (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                  (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                    (.proj 1 (.bvar 0))))))) ∧
        interp2 V (cons Aset ρ)
            (.lam 0 (psigmaFibreTyP ψ)
              (.lam 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
                (.lam 0 (psigmaMinorTyP (ψ uN) (ψ vN))
                  (.lam 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                    (.app (.app (.bvar 1) (.proj 0 (.bvar 0)))
                      (.proj 1 (.bvar 0)))))))
          ∈ˢ piR 0 (psigmaFibreSpace V (ψ vN) Aset) (fun B =>
            piR 0 (psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B) (fun M =>
              piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
                (fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
                    (fun x => app B x)) (fun p => app M p)))) := by
    intro Aset hA
    have hw := AnnotOkP_lam_mem (V := V) (b := 0)
      (Aa := psigmaFibreTyP ψ) (ρ := cons Aset ρ)
      (F := fun B => piR 0 (psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B)
        (fun M => piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
          (fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
              (fun x => app B x)) (fun p => app M p))))
      (psigmaFibreTyP_okP ψ _)
      (fun B hB => by
        rw [psigmaFibreTyP_interp] at hB
        exact h3 Aset B hA hB)
      (fun _ _ _ => piR_zero_mem_univZero)
    rw [psigmaFibreTyP_interp] at hw
    exact hw
  have hw := AnnotOkP_lam_mem (V := V) (b := 0) (Aa := .sort (ψ uN))
    (ρ := ρ)
    (F := fun Aset => piR 0 (psigmaFibreSpace V (ψ vN) Aset) (fun B =>
      piR 0 (psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B) (fun M =>
        piR 0 (psigmaMinorSpace V (ψ uN) (ψ vN) Aset B M)
          (fun _ => piR 0 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
              (fun x => app B x)) (fun p => app M p)))))
    ⟨trivial, trivial⟩
    (fun Aset hA => by
      rw [interp2_sort] at hA
      exact h2 Aset hA)
    (fun _ _ _ => piR_zero_mem_univZero)
  rw [interp2_sort] at hw
  rw [hTy, psigmaRecValT2]
  exact ⟨hw.1, hw.2⟩

/-- **`PSigma'.rec`'s type reading is graded.** -/
theorem psigmaRecTyP_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (psigmaRecTyP ψ) := by
  have h5 : ∀ Aset B M mn : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B →
      AnnotOkP V (cons mn (cons M (cons B (cons Aset ρ))))
          (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
            (.app (.bvar 2) (.bvar 0))) ∧
        interp2 V (cons mn (cons M (cons B (cons Aset ρ))))
            (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
              (.app (.bvar 2) (.bvar 0))) ∈ˢ (univZero : V) := by
    intro Aset B M mn hA hB hM
    refine AnnotOkP_pi_zero (psigmaRec_domains ρ hA hB hM).2.1
      (fun p hp => ?_) (fun p hp => ?_)
    · rw [(psigmaRec_domains ρ hA hB hM).1] at hp
      exact ((psigmaRec_domains ρ hA hB hM).2.2 p hp).2
    · rw [(psigmaRec_domains ρ hA hB hM).1] at hp
      rw [((psigmaRec_domains ρ hA hB hM).2.2 p hp).1, ← univ_zero]
      exact app_mem_piR_pos Nat.one_ne_zero
        (show M ∈ˢ piR 1 (sigmaSet (Nat.max (ψ uN) (ψ vN)) Aset
          (fun x => app B x)) fun _ => (univ 0 : V) from hM) hp
  have h4 : ∀ Aset B M : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      M ∈ˢ psigmaMotiveSpace V (ψ uN) (ψ vN) Aset B →
      AnnotOkP V (cons M (cons B (cons Aset ρ)))
          (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
            (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
              (.app (.bvar 2) (.bvar 0)))) ∧
        interp2 V (cons M (cons B (cons Aset ρ)))
            (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
              (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                (.app (.bvar 2) (.bvar 0)))) ∈ˢ (univZero : V) :=
    fun Aset B M hA hB hM =>
      AnnotOkP_pi_zero (psigmaMinorTyP_data ρ hA hB hM).2
        (fun mn _ => (h5 Aset B M mn hA hB hM).1)
        (fun mn _ => (h5 Aset B M mn hA hB hM).2)
  have h3 : ∀ Aset B : V, Aset ∈ˢ (univ (ψ uN) : V) →
      B ∈ˢ psigmaFibreSpace V (ψ vN) Aset →
      AnnotOkP V (cons B (cons Aset ρ))
          (.pi 0 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
            (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
              (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                (.app (.bvar 2) (.bvar 0))))) ∧
        interp2 V (cons B (cons Aset ρ))
            (.pi 0 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
              (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
                (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                  (.app (.bvar 2) (.bvar 0))))) ∈ˢ (univZero : V) := by
    intro Aset B hA hB
    refine AnnotOkP_pi_zero (psigmaMotiveTyP_data ρ hA hB).2
      (fun M hM => ?_) (fun M hM => ?_)
    · rw [(psigmaMotiveTyP_data ρ hA hB).1] at hM
      exact (h4 Aset B M hA hB hM).1
    · rw [(psigmaMotiveTyP_data ρ hA hB).1] at hM
      exact (h4 Aset B M hA hB hM).2
  have h2 : ∀ Aset : V, Aset ∈ˢ (univ (ψ uN) : V) →
      AnnotOkP V (cons Aset ρ)
          (.pi 0 0 (psigmaFibreTyP ψ)
            (.pi 0 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
              (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
                (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                  (.app (.bvar 2) (.bvar 0)))))) ∧
        interp2 V (cons Aset ρ)
            (.pi 0 0 (psigmaFibreTyP ψ)
              (.pi 0 0 (psigmaMotiveTyP (ψ uN) (ψ vN))
                (.pi 0 0 (psigmaMinorTyP (ψ uN) (ψ vN))
                  (.pi 0 0 (psigmaAppP (ψ uN) (ψ vN) 3 2)
                    (.app (.bvar 2) (.bvar 0))))))
          ∈ˢ (univZero : V) := by
    intro Aset hA
    refine AnnotOkP_pi_zero (psigmaFibreTyP_okP ψ _)
      (fun B hB => ?_) (fun B hB => ?_)
    · rw [psigmaFibreTyP_interp] at hB
      exact (h3 Aset B hA hB).1
    · rw [psigmaFibreTyP_interp] at hB
      exact (h3 Aset B hA hB).2
  rw [psigmaRecTyP]
  refine (AnnotOkP_pi_zero (Aa := .sort (ψ uN)) ⟨trivial, trivial⟩
    (fun Aset hA => ?_) (fun Aset hA => ?_)).1
  · rw [interp2_sort] at hA; exact (h2 Aset hA).1
  · rw [interp2_sort] at hA; exact (h2 Aset hA).2

/-- **`PSigma'.rec`'s RHS tower is graded** — six squash-regime `λ`s,
every body the canonical proof (the minor premise itself is). -/
theorem psigmaRecRaP_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (psigmaRecRaP ψ) := by
  rw [psigmaRecRaP]
  refine AnnotOkP_lam_zero_pt ⟨trivial, trivial⟩ ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro Aset hA
  rw [interp2_sort] at hA
  refine AnnotOkP_lam_zero_pt (psigmaFibreTyP_okP ψ _) ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro B hB
  rw [psigmaFibreTyP_interp] at hB
  refine AnnotOkP_lam_zero_pt (psigmaMotiveTyP_data ρ hA hB).2 ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro M hM
  rw [(psigmaMotiveTyP_data ρ hA hB).1] at hM
  refine AnnotOkP_lam_zero_pt (psigmaMinorTyP_data ρ hA hB hM).2 ?_
    (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro mn hmn
  rw [(psigmaMinorTyP_data ρ hA hB hM).1] at hmn
  have hmnpt : mn = pt := eq_pt_of_mem_piR_zero hmn
  have hdom : interp2 V (cons mn (cons M (cons B (cons Aset ρ))))
      (AVExpr.bvar 3) = Aset := by simp [interp2_bvar, cons]
  refine AnnotOkP_lam_zero_pt (Aa := .bvar 3) ⟨trivial, trivial⟩
    ?_ (fun _ _ => by rw [interp2_lam, lamR_zero])
  intro a ha
  rw [hdom] at ha
  have hBb : interp2 V (cons a (cons mn (cons M (cons B
      (cons Aset ρ))))) (AVExpr.bvar 3) = B := by
    simp [interp2_bvar, cons]
  have hab : interp2 V (cons a (cons mn (cons M (cons B
      (cons Aset ρ))))) (AVExpr.bvar 0) = a := by
    simp [interp2_bvar, cons]
  have hdok : AnnotOkP V (cons a (cons mn (cons M (cons B
      (cons Aset ρ))))) (.app (.bvar 3) (.bvar 0)) := by
    refine ⟨?_, ⟨trivial, trivial⟩⟩
    rw [AnnotOk2_app]
    exact ⟨trivial, trivial, ψ vN + 1, Aset,
      fun _ => (univ (ψ vN) : V), by rw [hBb]; exact hB,
      by rw [hab]; exact ha, fun h => absurd h (Nat.succ_ne_zero _)⟩
  have hdint : interp2 V (cons a (cons mn (cons M (cons B
      (cons Aset ρ))))) (.app (.bvar 3) (.bvar 0)) = app B a := by
    rw [interp2_app, hBb, hab]
  have hbody : ∀ b : V, b ∈ˢ app B a →
      AnnotOkP V (cons b (cons a (cons mn (cons M (cons B
          (cons Aset ρ))))))
          (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) ∧
        interp2 V (cons b (cons a (cons mn (cons M (cons B
            (cons Aset ρ))))))
          (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0)) = (pt : V) := by
    intro b hb
    have hmb : interp2 V (cons b (cons a (cons mn (cons M (cons B
        (cons Aset ρ)))))) (AVExpr.bvar 2) = pt := by
      rw [interp2_bvar]
      show cons b (cons a (cons mn (cons M (cons B (cons Aset ρ)))))
        2 = pt
      rw [show cons b (cons a (cons mn (cons M (cons B
        (cons Aset ρ))))) 2 = mn from rfl]
      exact hmnpt
    have h1 := AnnotOkP_app_pt (S := Aset) (f := AVExpr.bvar 2)
      (a := AVExpr.bvar 1) ⟨trivial, trivial⟩ hmb ⟨trivial, trivial⟩
      (by simp [interp2_bvar, cons]; exact ha)
    exact AnnotOkP_app_pt (S := app B a) (a := AVExpr.bvar 0)
      h1.1 h1.2 ⟨trivial, trivial⟩
      (by simp [interp2_bvar, cons]; exact hb)
  refine AnnotOkP_lam_zero_pt hdok ?_ ?_
  · intro b hb
    rw [hdint] at hb
    exact (hbody b hb).1
  · intro b hb
    rw [hdint] at hb
    exact (hbody b hb).2

/-- **`PSigma'.rec`'s `RecRuleLawP` row.**  The rule is `.plain`, so
both `.nested` conjuncts are `nomatch`; both sides of the fired
equality are the canonical proof, and the transport takes its six
domains straight off the two telescope fits. -/
theorem psigmaRecLawP {m : EnvS2Core V env}
    (m₂ : EnvS2Core V ⟨psigmaRecA :: env.consts⟩)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hac : m₂.acval = acvalWith m.acval psigmaRecA.name psigmaRecValT2)
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ psigmaRecA.name psigmaRecA.toConstantVal 4 4
      psigmaRecRule := by
  refine ⟨Nat.le_refl 4, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ psigmaRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denoteP m₂.acval ⟨psigmaRecA :: env.consts⟩ φ 0
      (psigmaRecRule.rhs.instantiateLevelParams
        psigmaRecA.toConstantVal.levelParams us)
      = some (psigmaRecRaP ψ) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteP_psigmaRec_rhs (m := m) _ hP hM]
  refine ⟨_, hRa, fun ρ => psigmaRecRaP_okP ψ ρ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev hplain hnested hpin hTVa hTVja hfitR hfitC
  have hM' : (⟨psigmaRecA :: env.consts⟩ : Env).find? psigmaMkName
      = some psigmaMkA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hM
  rw [show RecRule.ctor psigmaRecRule = psigmaMkName from rfl,
    hM'] at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = psigmaMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 2 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain ⟨x1, x2, x3, x4, rfl⟩ : ∃ p q r s, xs = [p, q, r, s] := by
    match xs, hxs with
    | [p, q, r, s], _ => exact ⟨p, q, r, s, rfl⟩
  obtain ⟨y1, y2, y3, y4, rfl⟩ : ∃ p q r s, ys = [p, q, r, s] := by
    match ys, hys with
    | [p, q, r, s], _ => exact ⟨p, q, r, s, rfl⟩
  have hTyRead : denoteP m₂.acval ⟨psigmaRecA :: env.consts⟩ φ 0
      (psigmaRecA.toConstantVal.type.instantiateLevelParams
        psigmaRecA.toConstantVal.levelParams us)
      = some (psigmaRecTyP ψ) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteP_psigmaRecA_type (m := m) _ hP hM]
  obtain rfl : TVa = _ :=
    (Option.some.inj (hTyRead.symm.trans hTVa)).symm
  have hCtorRead : denoteP m₂.acval ⟨psigmaRecA :: env.consts⟩ φ 0
      (psigmaMkA.toConstantVal.type.instantiateLevelParams
        psigmaMkA.toConstantVal.levelParams usj)
      = some (psigmaMkTyP
          (pwBit (Level.substFn φ psigmaMkA.toConstantVal.levelParams
            usj) (.ifAllZero [uN, vN]))
          (Level.substFn φ psigmaMkA.toConstantVal.levelParams
            usj)) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteP_psigmaMkTy (m := m) _ (by decide) hP]
  obtain rfl : TVja = _ :=
    (Option.some.inj (hCtorRead.symm.trans hTVja)).symm
  have hrecL : m₂.acval psigmaRecA.name
      (Level.substFn φ psigmaRecA.toConstantVal.levelParams us)
      = psigmaRecValT2 ψ := by
    rw [hac, acvalWith_self, hψ]
  rw [psigmaRecTyP] at hfitR
  cases hfitR with | cons f1 hfitR =>
  cases hfitR with | cons f2 hfitR =>
  cases hfitR with | cons f3 hfitR =>
  cases hfitR with | cons f4 hfitR =>
  cases hfitR with | cons f5 _ =>
  rw [psigmaMkTyP] at hfitC
  cases hfitC with | cons g1 hfitC =>
  cases hfitC with | cons g2 hfitC =>
  cases hfitC with | cons g3 hfitC =>
  cases hfitC with | cons g4 _ =>
  refine ⟨?_, ?_⟩
  · -- the fired equality: both sides are the canonical proof
    simp only [show RecRule.ctor psigmaRecRule = psigmaMkName from rfl,
      show psigmaRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AVExpr.mkAppN_cons, AVExpr.mkAppN_nil, hrecL, interp2_app,
      psigmaRecValT2_interp, psigmaRecRaP_interp, app_pt]
  · -- the transport: six squash-regime applications
    intro hxsA hysA
    simp only [show psigmaRecRule.ctorParams = 2 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      AVExpr.mkAppN_cons, AVExpr.mkAppN_nil]
    have h1 := AnnotOkP_app_pt (psigmaRecRaP_okP ψ ρ)
      (psigmaRecRaP_interp ψ ρ) (hxsA x1 (by simp)) f1
    have h2 := AnnotOkP_app_pt h1.1 h1.2 (hxsA x2 (by simp)) f2
    have h3 := AnnotOkP_app_pt h2.1 h2.2 (hxsA x3 (by simp)) f3
    have h4 := AnnotOkP_app_pt h3.1 h3.2 (hxsA x4 (by simp)) f4
    have h5 := AnnotOkP_app_pt h4.1 h4.2 (hysA y3 (by simp)) g3
    exact (AnnotOkP_app_pt h5.1 h5.2 (hysA y4 (by simp)) g4).1

/-- **`PSigma'.rec`, installed at the P tier.** -/
theorem extendPSigmaRecP (mp : EnvS2PM V μ env)
    (hP : env.find? psigmaName = some psigmaA)
    (hM : env.find? psigmaMkName = some psigmaMkA)
    (hfresh : env.find? psigmaRecA.name = none)
    (hwf : EnvWF ⟨psigmaRecA :: env.consts⟩) :
    Nonempty (EnvS2PM V μ ⟨psigmaRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_psigmaRecA_type (m := mp.base2) (A := psigmaRecValT2)
      ψ hP hM
  refine nonempty_of_exists (declStepPM_of_basis_rec_cons mp
    (A := psigmaRecValT2) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    (ConsHeadP.ofBasis hwf
      (fun ψ => by rw [psigmaRecValT2_erase ψ]; exact psigmaRecValT_closed ψ)
      (fun _ => rfl)
      (fun ψ t hp => by
        rw [show Setlec.TTVerify.pinnedDirectT psigmaRecA.name ψ
          = none from rfl] at hp
        exact nomatch hp)
      (fun _ h => nomatch h)
      (fun _ _ _ _ heq r hr => by
        injection heq with _ _ _ h4
        rw [← h4] at hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact ⟨_, _, _, hM⟩
        · exact nomatch hr'))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k)
        (by rw [psigmaRecValT2_erase]
            exact psigmaRecValT_closed ψ)) 1)
    ?_
    (fun ψ ρ => (psigmaRecValT2_data ψ ρ).1.1)
    (fun ψ ρ => (psigmaRecValT2_data ψ ρ).1.2)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_)
  · intro ψ₁ ψ₂ hp
    exact psigmaRecValT2_congr
      (hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self))
      (hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self))
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact psigmaRecTyP_okP ψ ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (psigmaRecValT2_data ψ ρ).2
  · intro m₂ hac φ
    refine recRulesP_cons_rec mp hfresh psigmaRecA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact psigmaRecLawP (m := mp.base2) m₂ hP hM hac φ
    · exact nomatch hr'

/-- **The `PSigma'` block, installed at the P tier.**  `BasisStepPB`'s
`psigmaK` branch — and with it the bundle's last. -/
theorem declBasisPB_psigmaK {env₁ : Env} (mp : EnvS2PM V μ env)
    (h : Setlec.SetR.BasisInstallR env
      Setlec.BasisKind.psigmaK.declsA env₁) :
    Nonempty (EnvS2PM V μ env₁) := by
  rw [show Setlec.BasisKind.psigmaK.declsA
    = [psigmaA, psigmaMkA, psigmaRecA, pairFstA, pairSndA]
    from rfl] at h
  obtain ⟨h1, h2, h3, h4, h5, hnil⟩ := h
  subst hnil
  have hf1 : env.find? psigmaA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨psigmaA :: env.consts⟩ :=
    EnvWF.cons mp.base2.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨mp1⟩ := extendPSigmaP mp hf1  hwf1
  have hP1 : (⟨psigmaA :: env.consts⟩ : Env).find? psigmaName
      = some psigmaA := by
    rw [Setlec.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨psigmaA :: env.consts⟩ : Env).find? psigmaMkA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨psigmaMkA :: psigmaA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ psigmaMkA.toConstantVal.type = true
    have hf : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find?
        psigmaName = some psigmaA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP1
    rw [show psigmaMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "β")
            (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
              (.sort (.param vN)) { bi := .default, pw := .never })
            (Expr.forallE (Name.anonymous.str "fst") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "snd")
                (.app (.bvar 1) (.bvar 0))
                (.app (.app (.const psigmaName
                    [.param uN, .param vN]) (.bvar 3)) (.bvar 2))
                { bi := .default, pw := .ifAllZero [uN, vN] })
              { bi := .default, pw := .ifAllZero [uN, vN] })
            { bi := .implicit, pw := .ifAllZero [uN, vN] })
          { bi := .implicit, pw := .ifAllZero [uN, vN] } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨mp2⟩ := extendPSigmaMkP mp1 hP1 hf2  hwf2
  have hP2 : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find?
      psigmaName = some psigmaA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP1
  have hM2 : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find?
      psigmaMkName = some psigmaMkA := by
    rw [Setlec.Env.find?_cons]; exact if_pos rfl
  have hPv2 : ∀ ψ : Name → Nat,
      mp2.base2.cvalE psigmaName ψ
        = VExpr.const .psigma [ψ uN, ψ vN] := fun ψ =>
    EnvS2Core.cvalE_pinned mp2.base2 (by decide) (by rw [hP2]; rfl) ψ
      (by simp +decide [Setlec.TTVerify.pinnedDirectT])
  have hMv2 : ∀ ψ : Name → Nat,
      mp2.base2.cvalE psigmaMkName ψ
        = VExpr.const .psigmaMk [ψ uN, ψ vN] := fun ψ =>
    EnvS2Core.cvalE_pinned mp2.base2 (by decide) (by rw [hM2]; rfl) ψ
      (by simp +decide [Setlec.TTVerify.pinnedDirectT])
  have hf3 : (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find?
      psigmaRecA.name = none := Option.isNone_iff_eq_none.mp h3
  have hwf3 : EnvWF ⟨psigmaRecA :: psigmaMkA :: psigmaA
      :: env.consts⟩ := by
    have hfP : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩
        : Env).find? psigmaName = some psigmaA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP2
    have hfM : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩
        : Env).find? psigmaMkName = some psigmaMkA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hM2
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ _ heq => nomatch heq)⟩
    · show Expr.constsResolve _ psigmaRecA.toConstantVal.type = true
      rw [show psigmaRecA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
              (Expr.forallE (Name.anonymous.str "β")
                (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
                  (.sort (.param vN)) { bi := .default, pw := .never })
                (Expr.forallE (Name.anonymous.str "motive")
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.const psigmaName
                      [.param uN, .param vN]) (.bvar 1)) (.bvar 0))
                    (.sort .zero) { bi := .default, pw := .never })
                  (Expr.forallE (Name.anonymous.str "mk")
                    (Expr.forallE (Name.anonymous.str "fst") (.bvar 2)
                      (Expr.forallE (Name.anonymous.str "snd")
                        (.app (.bvar 2) (.bvar 0))
                        (.app (.bvar 2)
                          (.app (.app (.app (.app
                            (.const psigmaMkName
                              [.param uN, .param vN]) (.bvar 4))
                            (.bvar 3)) (.bvar 1)) (.bvar 0)))
                        { bi := .default, pw := .ifAllZero [] })
                      { bi := .default, pw := .ifAllZero [] })
                    (Expr.forallE (Name.anonymous.str "t")
                      (.app (.app (.const psigmaName
                        [.param uN, .param vN]) (.bvar 3)) (.bvar 2))
                      (.app (.bvar 2) (.bvar 0))
                      { bi := .default, pw := .ifAllZero [] })
                    { bi := .default, pw := .ifAllZero [] })
                  { bi := .implicit, pw := .ifAllZero [] })
                { bi := .implicit, pw := .ifAllZero [] })
              { bi := .implicit, pw := .ifAllZero [] } from rfl]
      simp [Expr.constsResolve, hfP, hfM]
    · intro cv mI rP rules heq
      injection heq with h1' _ _ h4'
      subst h1'; subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact ⟨rfl, rfl, by
          show Expr.constsResolve _ (RecRule.rhs psigmaRecRule) = true
          simp [Expr.constsResolve, psigmaRecRule, hfP, hfM], rfl,
          fun lvls pins heqf => nomatch heqf⟩
      · exact nomatch hr'
  obtain ⟨mp3⟩ := extendPSigmaRecP mp2 hP2 hM2 hf3 hwf3
  have hP3 : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩
      : Env).find? psigmaName = some psigmaA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP2
  have hM3 : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩
      : Env).find? psigmaMkName = some psigmaMkA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hM2
  have hf4 : (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩
      : Env).find? pairFstA.name = none :=
    Option.isNone_iff_eq_none.mp h4
  have hwf4 : EnvWF ⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA
      :: env.consts⟩ := by
    have hfP : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA
        :: env.consts⟩ : Env).find? psigmaName = some psigmaA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP3
    refine EnvWF.cons hwf3 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ pairFstA.toConstantVal.type = true
    rw [show pairFstA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
                (.sort (.param vN)) { bi := .default, pw := .never })
              (Expr.forallE (Name.anonymous.str "t")
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 1)) (.bvar 0))
                (.bvar 2) { bi := .default, pw := .never })
              { bi := .implicit, pw := .never })
            { bi := .implicit, pw := .never } from rfl]
    simp [Expr.constsResolve, hfP]
  obtain ⟨mp4⟩ := extendPairFstP mp3 hP3 hM3 hf4 hwf4
  have hP4 : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA
      :: env.consts⟩ : Env).find? psigmaName = some psigmaA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP3
  have hM4 : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA
      :: env.consts⟩ : Env).find? psigmaMkName = some psigmaMkA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hM3
  have hf5 : (⟨pairFstA :: psigmaRecA :: psigmaMkA :: psigmaA
      :: env.consts⟩ : Env).find? pairSndA.name = none :=
    Option.isNone_iff_eq_none.mp h5
  have hwf5 : EnvWF ⟨pairSndA :: pairFstA :: psigmaRecA :: psigmaMkA
      :: psigmaA :: env.consts⟩ := by
    have hfP : (⟨pairSndA :: pairFstA :: psigmaRecA :: psigmaMkA
        :: psigmaA :: env.consts⟩ : Env).find? psigmaName
        = some psigmaA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP4
    refine EnvWF.cons hwf4 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ pairSndA.toConstantVal.type = true
    rw [show pairSndA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "x") (.bvar 0)
                (.sort (.param vN)) { bi := .default, pw := .never })
              (Expr.forallE (Name.anonymous.str "t")
                (.app (.app (.const psigmaName [.param uN, .param vN])
                  (.bvar 1)) (.bvar 0))
                (.app (.bvar 1) (.proj psigmaName 0 (.bvar 0)))
                ⟨.default, .never⟩)
              { bi := .implicit, pw := .never })
            { bi := .implicit, pw := .never } from rfl]
    simp [Expr.constsResolve, hfP]
  exact extendPairSndP mp4 hP4 hM4 hf5 hwf5

end PSigma

end Setlec.SetR.Interp2
