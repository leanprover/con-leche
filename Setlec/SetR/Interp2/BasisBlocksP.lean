import Setlec.SetR.Interp2.LevelsP

/-!
# The remaining basis blocks, P tier (task #161, ENDGAME G)

`Interp2/BasisEmptyP.lean` executed the ENDGAME E/F recipe at the
smallest block and closed `BasisStepPB`'s `emptyK` branch.  This file
carries the same recipe across the other five, mirroring v1's single
`Install/BasisS.lean` rather than splitting per block — the shared
leaf-reading kit below is used at every one of them.

Three pieces of kit that `BasisEmptyP.lean` did not need, because
`Empty` binds no level parameter and `Empty.rec` has no rules:

* `denoteP_pinned_const` — a *leveled* pinned leaf's reading, the
  generalisation of `BasisEmptyP.lean`'s `hEc`;
* `denoteP_instLevels` (`Interp2/LevelsP.lean`) — so that a recursor
  row's instantiated subjects (`RecRuleLawP` reads
  `rhs.instantiateLevelParams` and `cv.type.instantiateLevelParams`)
  are the *raw* readings at a substituted assignment.  One reading
  lemma per constant then serves both `EnvS2PM.type_reads` and the
  row's `TVa`;
* `declStepPM_of_basis_rec_cons` (`Interp2/BasisStepP.lean`) — the six
  collapsed rows at a recursor cons, whose seventh is bespoke.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule uN u1N vN)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The leaf kit

`BasisEmptyP.lean`'s `hEc` at a constant that actually binds levels. -/

/-- **A stored pinned constant's reading, at a level list.**  The
extension's fresh leaf is stepped over by `acvalWith_ne`, the prefix
lookup by `Env.find?_cons`, and the leaf itself is
`acval_basis_pinned`. -/
theorem denoteP_pinned_const {m : EnvS2Core V env}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    {n : Name} {ci : ConstantInfo} {ψ : Name → Nat} {ls : List Level}
    (hne : ¬ c₀.name = n)
    (hf : env.find? n = some ci)
    (hres : Setlec.reservedBasisNames.contains n = true)
    (hlen : ls.length = ci.toConstantVal.levelParams.length)
    {c : Setlec.TT.BConst} {us : List Nat}
    (hpd : Setlec.TTVerify.pinnedDirectT n
      (Level.substFn ψ ci.toConstantVal.levelParams ls)
        = some (VExpr.const c us)) (d : Nat) :
    denoteP (acvalWith m.acval c₀.name A) ⟨c₀ :: env.consts⟩ ψ d
        (.const n ls) = some (AVExpr.const c us) := by
  have hf' : (⟨c₀ :: env.consts⟩ : Env).find? n = some ci := by
    rw [Setlec.Env.find?_cons, if_neg hne]; exact hf
  rw [denoteP_const hf' hlen, acvalWith_ne (fun h => hne h.symm),
    acval_basis_pinned (m := m) hf hres hpd]

/-! ## `PUnit`

Three constants, one firing rule.  The block is the recipe's second
application and the lane's first `RecRuleLawP` row. -/

section PUnit

open Setlec (punitA punitUnitA punitRecA punitName punitUnitName)

variable {m : EnvS2Core V env} {A : (Name → Nat) → AVExpr}

/-- `PUnit`'s type reading: `Sort u`, which is `BConst.type2 .punit
[ψ u]` on the nose. -/
theorem denoteP_punitA_type
    {acval : Name → (Name → Nat) → AVExpr} (ψ : Name → Nat) :
    denoteP acval ⟨punitA :: env.consts⟩ ψ 0 punitA.toConstantVal.type
      = some (BConst.type2 .punit [ψ uN]) := by
  rw [show punitA.toConstantVal.type = Expr.sort (.param uN) from rfl,
    denoteP_sort]
  rfl

/-- `PUnit.unit`'s type reading: the `PUnit` leaf, which is
`BConst.type2 .punitUnit [ψ u]` on the nose. -/
theorem denoteP_punitUnitA_type (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA) :
    denoteP (acvalWith m.acval punitUnitA.name A)
        ⟨punitUnitA :: env.consts⟩ ψ 0
        punitUnitA.toConstantVal.type
      = some (BConst.type2 .punitUnit [ψ uN]) := by
  rw [show punitUnitA.toConstantVal.type
      = Expr.const punitName [Level.param uN] from rfl]
  refine denoteP_pinned_const (m := m) (by decide) hP (by decide)
    (by rfl) ?_ 0
  simp +decide [Setlec.TTVerify.pinnedDirectT, Setlec.TT.lv]
  show Level.substFn ψ [uN] [Level.param uN] uN = ψ uN
  simp [Level.substFn]
  rfl

/-- The pinned `PUnit`/`PUnit.unit` leaves at the `PUnit.rec`
extension, at any level. -/
theorem denoteP_punitRec_leaves (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA) :
    (∀ (d : Nat) (l : Level),
      denoteP (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ d (.const punitName [l])
        = some (AVExpr.const .punit [l.eval ψ])) ∧
    (∀ (d : Nat) (l : Level),
      denoteP (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ d (.const punitUnitName [l])
        = some (AVExpr.const .punitUnit [l.eval ψ])) := by
  constructor
  · intro d l
    refine denoteP_pinned_const (m := m) (by decide) hP (by decide)
      (by rfl) ?_ d
    simp +decide [Setlec.TTVerify.pinnedDirectT]
    show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
    simp [Level.substFn]
  · intro d l
    refine denoteP_pinned_const (m := m) (by decide) hU (by decide)
      (by rfl) ?_ d
    simp +decide [Setlec.TTVerify.pinnedDirectT]
    show Level.substFn ψ [uN] [l] uN = Level.eval ψ l
    simp [Level.substFn]

/-- **`PUnit.rec`'s type reading.**  Three binders, three stored pins;
the numerals are `pwBit`s of exactly those pins. -/
theorem denoteP_punitRecA_type (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA) :
    denoteP (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ 0 punitRecA.toConstantVal.type
      = some (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
          (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN])
            (.sort (ψ u1N)))
          (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
            (.app (.bvar 0) (.const .punitUnit [ψ uN]))
            (.pi 0 (pwBit ψ (.ifAllZero [u1N])) (.const .punit [ψ uN])
              (.app (.bvar 2) (.bvar 0))))) := by
  obtain ⟨hPc, hUc⟩ := denoteP_punitRec_leaves (m := m) (A := A) ψ hP hU
  rw [show punitRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t")
            (.const punitName [.param uN]) (.sort (.param u1N))
            { bi := .default, pw := .never })
          (Expr.forallE (Name.anonymous.str "unit")
            (.app (.bvar 0) (.const punitUnitName [.param uN]))
            (Expr.forallE (Name.anonymous.str "t")
              (.const punitName [.param uN])
              (.app (.bvar 2) (.bvar 0))
              { bi := .default, pw := .ifAllZero [u1N] })
            { bi := .default, pw := .ifAllZero [u1N] })
          { bi := .implicit, pw := .ifAllZero [u1N] } from rfl]
  simp [denoteP_forallE, denoteP_sort, denoteP_app, denoteP_fvar,
    Expr.instantiate1, hPc, hUc, Level.eval]

/-- **The reading agrees with `BConst.type2`.**  Four codomain
numerals: three `pwBit_ifAllZero_single` at the motive level, and the
motive-space binder's `pwBit_never` against `v + 1`. -/
theorem bitAgree_punitRecA (ψ : Name → Nat) :
    AVExpr.BitAgree
      (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
        (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN])
          (.sort (ψ u1N)))
        (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
          (.app (.bvar 0) (.const .punitUnit [ψ uN]))
          (.pi 0 (pwBit ψ (.ifAllZero [u1N])) (.const .punit [ψ uN])
            (.app (.bvar 2) (.bvar 0)))))
      (BConst.type2 .punitRec [ψ uN, ψ u1N]) := by
  have hz : pwBit ψ (Setlec.PropWhen.ifAllZero [u1N]) = 0 ↔ ψ u1N = 0 :=
    pwBit_ifAllZero_single ψ u1N
  refine .pi hz (.pi ?_ (.const _ _) (.sort _))
    (.pi hz (.app (.bvar 0) (.const _ _))
      (.pi hz (.const _ _) (.app (.bvar 2) (.bvar 0))))
  rw [pwBit_never]
  simp

/-! ### The block's one firing rule -/

/-- `PUnit.rec`'s single stored rule, named. -/
def punitRecRule : RecRule :=
  { ctor := punitUnitName, nfields := 0, ctorParams := 0,
    fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "motive")
      (Expr.forallE (Name.anonymous.str "t")
        (.const punitName [.param uN]) (.sort (.param u1N))
        { bi := .default, pw := .never })
      (Expr.lam (Name.anonymous.str "unit")
        (.app (.bvar 0) (.const punitUnitName [.param uN]))
        (.bvar 0) { bi := .default, pw := .ifAllZero [u1N] })
      { bi := .default, pw := .ifAllZero [u1N] } }

theorem punitRecA_eq :
    punitRecA = .recInfo punitRecA.toConstantVal 2 2 [punitRecRule] :=
  rfl

/-- **`PUnit.rec`'s rule's RHS reading**, at any assignment. -/
theorem denoteP_punitRec_rhs (ψ : Name → Nat)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA) :
    denoteP (acvalWith m.acval punitRecA.name A)
        ⟨punitRecA :: env.consts⟩ ψ 0 punitRecRule.rhs
      = some (.lam (pwBit ψ (.ifAllZero [u1N]))
          (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN])
            (.sort (ψ u1N)))
          (.lam (pwBit ψ (.ifAllZero [u1N]))
            (.app (.bvar 0) (.const .punitUnit [ψ uN]))
            (.bvar 0))) := by
  obtain ⟨hPc, hUc⟩ := denoteP_punitRec_leaves (m := m) (A := A) ψ hP hU
  rw [show punitRecRule.rhs = Expr.lam (Name.anonymous.str "motive")
      (Expr.forallE (Name.anonymous.str "t")
        (.const punitName [.param uN]) (.sort (.param u1N))
        { bi := .default, pw := .never })
      (Expr.lam (Name.anonymous.str "unit")
        (.app (.bvar 0) (.const punitUnitName [.param uN]))
        (.bvar 0) { bi := .default, pw := .ifAllZero [u1N] })
      { bi := .default, pw := .ifAllZero [u1N] } from rfl]
  simp [denoteP_lam, denoteP_forallE, denoteP_sort, denoteP_app,
    denoteP_fvar, Expr.instantiate1, hPc, hUc, Level.eval]

/-- `PUnit.rec`'s rule's RHS reading, named. -/
def punitRaP (ψ : Name → Nat) : AVExpr :=
  .lam (pwBit ψ (.ifAllZero [u1N]))
    (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN]) (.sort (ψ u1N)))
    (.lam (pwBit ψ (.ifAllZero [u1N]))
      (.app (.bvar 0) (.const .punitUnit [ψ uN])) (.bvar 0))

theorem punitRaP_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp2 V ρ (punitRaP ψ)
      = lamR (pwBit ψ (.ifAllZero [u1N]))
          (piR 1 (unitSet : V) fun _ => univ (ψ u1N))
          (fun M => lamR (pwBit ψ (.ifAllZero [u1N])) (app M pt)
            fun z => z) := by
  simp [punitRaP, interp2_lam, interp2_pi, interp2_app, interp2_bvar,
    interp2_const, interp2_sort, cons, pwBit_never, bval2]

/-- `PUnit.rec`'s RHS reading is graded, at every environment. -/
theorem punitRaP_okP (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkP V ρ (punitRaP ψ) := by
  constructor
  · refine ⟨⟨trivial, fun _ _ => trivial⟩, fun M hM => ?_, ?_⟩
    · refine ⟨⟨trivial, trivial, 1, unitSet, fun _ => univ (ψ u1N),
        ?_, pt_mem_unitSet, fun h => absurd h Nat.one_ne_zero⟩,
        fun _ _ => trivial, ?_⟩
      · simpa [interp2_bvar, cons, interp2_pi, interp2_const,
          interp2_sort, pwBit_never, bval2] using hM
      · refine ⟨fun x => interp2 V (cons M ρ)
            (.app (.bvar 0) (.const .punitUnit [ψ uN])),
          fun x hx => by simpa [interp2_bvar, cons] using hx,
          fun hz x _ => ?_⟩
        have hMp : app M pt ∈ˢ (univ (ψ u1N) : V) := by
          refine app_mem_piR_pos (A := (unitSet : V))
            (B := fun _ => univ (ψ u1N)) Nat.one_ne_zero ?_
            (pt_mem_unitSet (V := V))
          simpa [interp2_pi, interp2_const, interp2_sort, pwBit_never,
            bval2] using hM
        rw [(pwBit_ifAllZero_single ψ u1N).mp hz, univ_zero] at hMp
        simpa [interp2_app, interp2_bvar, interp2_const, cons, bval2]
          using hMp
    · refine ⟨fun M => piR (pwBit ψ (.ifAllZero [u1N])) (app M pt)
          (fun _ => app M pt),
        fun M hM => ?_,
        fun hz M hM => by rw [hz]; exact piR_zero_mem_univZero⟩
      have : interp2 V (cons M ρ)
          (AVExpr.lam (pwBit ψ (.ifAllZero [u1N]))
            (.app (.bvar 0) (.const .punitUnit [ψ uN])) (.bvar 0))
          = lamR (pwBit ψ (.ifAllZero [u1N])) (app M pt) fun z => z := by
        simp [interp2_lam, interp2_app, interp2_bvar, interp2_const,
          cons, bval2]
      rw [this]
      exact lamR_mem fun _ hx => hx
  · exact ⟨⟨trivial, fun _ _ => trivial, fun h => nomatch h⟩,
      fun _ _ => ⟨⟨trivial, trivial⟩, fun _ _ => trivial⟩⟩

/-- **`PUnit.rec`'s `RecRuleLawP` row.**  The basis tier's first, and
`.plain` (ENDGAME F §3), so both `.nested` conjuncts are vacuous and
the live content is the fired equality — `punitRecV2_app` against two
`app_lamR_pos` — plus the transport.

The `v = 0` branch is not a special case that needed a lemma: at a
`Prop`-valued motive `punitRecV2_app`'s own squash regime and the
reading's `lamR 0 = pt` land on the same point, and `mem_univ_zero`
identifies the minor premise with it. -/
theorem punitRecLawP {m : EnvS2Core V env}
    (m₂ : EnvS2Core V ⟨punitRecA :: env.consts⟩)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hac : m₂.acval = acvalWith m.acval punitRecA.name
      (fun ψ => AVExpr.const .punitRec [ψ uN, ψ u1N]))
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ punitRecA.name punitRecA.toConstantVal 2 2
      punitRecRule := by
  refine ⟨Nat.le_refl 2, fun us hus => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ punitRecA.toConstantVal.levelParams us :=
    ⟨_, rfl⟩
  have hRa : denoteP m₂.acval ⟨punitRecA :: env.consts⟩ φ 0
      (punitRecRule.rhs.instantiateLevelParams
        punitRecA.toConstantVal.levelParams us)
      = some (punitRaP ψ) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac, hψ,
      denoteP_punitRec_rhs (m := m) _ hP hU]
    rfl
  refine ⟨punitRaP ψ, hRa, punitRaP_okP ψ, ?_, ?_⟩
  · intro _ _ h
    exact nomatch h
  intro cvj cnP cnF hfj usj ρ xs ys TVa TVja restR restC hxs hys husj
    hlev hplain hnested hpin hTVa hTVja hfitR hfitC
  -- the rule's constructor is `PUnit.unit`, stored in the prefix
  have hU' : (⟨punitRecA :: env.consts⟩ : Env).find? punitUnitName
      = some punitUnitA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hU
  rw [show RecRule.ctor punitRecRule = punitUnitName from rfl, hU']
    at hfj
  obtain ⟨rfl, rfl, rfl⟩ :
      cvj = punitUnitA.toConstantVal ∧ cnP = 0 ∧ cnF = 0 := by
    injection Option.some.inj hfj with a1 a2 a3
    exact ⟨a1.symm, a2.symm, a3.symm⟩
  obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
  obtain ⟨M, mm, rfl⟩ : ∃ a b, xs = [a, b] := by
    match xs, hxs with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  -- the two leaves the conclusion mentions
  have hrecL : m₂.acval punitRecA.name
      (Level.substFn φ punitRecA.toConstantVal.levelParams us)
      = AVExpr.const .punitRec [ψ uN, ψ u1N] := by
    rw [hac, acvalWith_self, hψ]
  have hctorL : m₂.acval punitUnitName
      (Level.substFn φ punitUnitA.toConstantVal.levelParams usj)
      = AVExpr.const .punitUnit
        [Level.substFn φ punitUnitA.toConstantVal.levelParams usj uN] := by
    rw [hac, acvalWith_ne (by decide)]
    refine acval_basis_pinned (m := m) hU (by decide) ?_
    simp +decide [Setlec.TTVerify.pinnedDirectT]
  -- the recursor's own type, identified with the given reading
  obtain rfl : TVa = .pi 0 (pwBit ψ (.ifAllZero [u1N]))
      (.pi 0 (pwBit ψ .never) (.const .punit [ψ uN]) (.sort (ψ u1N)))
      (.pi 0 (pwBit ψ (.ifAllZero [u1N]))
        (.app (.bvar 0) (.const .punitUnit [ψ uN]))
        (.pi 0 (pwBit ψ (.ifAllZero [u1N])) (.const .punit [ψ uN])
          (.app (.bvar 2) (.bvar 0)))) := by
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ, hac,
      denoteP_punitRecA_type (m := m) _ hP hU, ← hψ] at hTVa
    exact (Option.some.inj hTVa).symm
  -- the fit's two memberships
  cases hfitR with | cons h1 hfitR =>
  cases hfitR with | cons h2 hfitR =>
  have hM : interp2 V ρ M ∈ˢ piR 1 (unitSet : V)
      fun _ => univ (ψ u1N) := by
    simpa [interp2_pi, interp2_const, interp2_sort, pwBit_never, bval2]
      using h1
  have hm : interp2 V ρ mm ∈ˢ app (interp2 V ρ M) (pt : V) := by
    simpa [AVExpr.inst, AVExpr.liftN_zero, interp2_app, interp2_bvar,
      interp2_const, cons, bval2] using h2
  have hMpt : app (interp2 V ρ M) (pt : V) ∈ˢ (univ (ψ u1N) : V) :=
    app_mem_piR_pos (A := (unitSet : V)) (B := fun _ => univ (ψ u1N))
      Nat.one_ne_zero hM (pt_mem_unitSet (V := V))
  have hMmot : interp2 V ρ M ∈ˢ punitMotiveSpace V (ψ u1N) := by
    rw [punitMotiveSpace,
      ← piR_zero_agree (v := 1) (v' := ψ u1N + 1)
        (show (1 : Nat) = 0 ↔ ψ u1N + 1 = 0 by simp) (fun _ _ => rfl)]
    exact hM
  refine ⟨?_, ?_⟩
  · -- the fired equality
    simp only [show RecRule.ctor punitRecRule = punitUnitName from rfl,
      show punitRecRule.ctorParams = 0 from rfl,
      List.take, List.drop, List.cons_append, List.nil_append,
      List.append_nil, AVExpr.mkAppN_cons, AVExpr.mkAppN_nil,
      hrecL, hctorL, interp2_app, interp2_const, bval2, Setlec.TT.lv,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [punitRecV2_app V hMmot hm (pt_mem_unitSet (V := V)),
      punitRaP_interp]
    by_cases hz : pwBit ψ (Setlec.PropWhen.ifAllZero [u1N]) = 0
    · rw [hz, lamR_zero, app_pt, app_pt]
      rw [(pwBit_ifAllZero_single ψ u1N).mp hz] at hMpt
      exact mem_univ_zero hMpt hm
    · rw [app_lamR_pos hz hM, app_lamR_pos hz hm]
  · -- the transport
    intro hxsA _
    have hMA : AnnotOkP V ρ M := hxsA M (by simp)
    have hmA : AnnotOkP V ρ mm := hxsA mm (by simp)
    have hRm : interp2 V ρ (punitRaP ψ)
        ∈ˢ piR (pwBit ψ (.ifAllZero [u1N]))
          (piR 1 (unitSet : V) fun _ => univ (ψ u1N))
          (fun M' => piR (pwBit ψ (.ifAllZero [u1N])) (app M' pt)
            fun _ => app M' pt) := by
      rw [punitRaP_interp]
      exact lamR_mem fun _ _ => lamR_mem fun _ hx => hx
    have hfib : pwBit ψ (Setlec.PropWhen.ifAllZero [u1N]) = 0 →
        ∀ x, x ∈ˢ (piR 1 (unitSet : V) fun _ => univ (ψ u1N)) →
          piR (pwBit ψ (.ifAllZero [u1N])) (app x pt)
            (fun _ => app x pt) ∈ˢ (univZero : V) := by
      intro hz _ _
      rw [hz]; exact piR_zero_mem_univZero
    have hstep : app (interp2 V ρ (punitRaP ψ)) (interp2 V ρ M)
        ∈ˢ piR (pwBit ψ (.ifAllZero [u1N])) (app (interp2 V ρ M) pt)
          (fun _ => app (interp2 V ρ M) pt) :=
      app_mem_piR hRm hM hfib
    simp only [List.take, show punitRecRule.ctorParams = 0 from rfl]
    refine ⟨⟨⟨punitRaP_okP ψ ρ |>.1, hMA.1, _, _, _, hRm, hM, hfib⟩,
      hmA.1, _, _, _, hstep, hm, ?_⟩,
      ⟨⟨(punitRaP_okP ψ ρ).2, hMA.2⟩, hmA.2⟩⟩
    intro hz _ _
    rw [(pwBit_ifAllZero_single ψ u1N).mp hz, univ_zero] at hMpt
    exact hMpt

/-! ### The three installs -/

/-- **`PUnit`, installed at the P tier.** -/
theorem extendPUnitP (mp : EnvS2PM V μ env)
    (hfresh : env.find? punitName = none)
    (hbase : EnvS V ⟨punitA :: env.consts⟩)
    (hag : ∀ n, n ≠ punitA.name → mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval punitA.name ψ
      = VExpr.const .punit [ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨punitA :: env.consts⟩) := by
  refine declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .punit [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, denoteP_punitA_type ψ⟩) ?_ ?_
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [denoteP_punitA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact AnnotOkP_bconst_type V .punit [ψ uN] ρ
  · intro ψ ta h ρ
    rw [denoteP_punitA_type ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval2_mem_type V .punit [ψ uN] ρ

/-- **`PUnit.unit`, installed at the P tier.** -/
theorem extendPUnitUnitP (mp : EnvS2PM V μ env)
    (hP : env.find? punitName = some punitA)
    (hfresh : env.find? punitUnitName = none)
    (hbase : EnvS V ⟨punitUnitA :: env.consts⟩)
    (hag : ∀ n, n ≠ punitUnitA.name →
      mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval punitUnitA.name ψ
      = VExpr.const .punitUnit [ψ uN]) :
    Nonempty (EnvS2PM V μ ⟨punitUnitA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_punitUnitA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .punitUnit [ψ uN]) ψ hP
  refine declStepPM_of_basis_cons mp
    (A := fun ψ => AVExpr.const .punitUnit [ψ uN]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ h => nomatch h)
    (Or.inl (by decide)) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact AnnotOkP_bconst_type V .punitUnit [ψ uN] ρ
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact bval2_mem_type V .punitUnit [ψ uN] ρ

/-- **`PUnit.rec`, installed at the P tier** — the lane's first
recursor cons: six rows collapse, the seventh is `punitRecLawP`. -/
theorem extendPUnitRecP (mp : EnvS2PM V μ env)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hfresh : env.find? punitRecA.name = none)
    (hbase : EnvS V ⟨punitRecA :: env.consts⟩)
    (hag : ∀ n, n ≠ punitRecA.name →
      mp.base2.base.cval n = hbase.cval n)
    (hcv : ∀ ψ, hbase.cval punitRecA.name ψ
      = VExpr.const .punitRec [ψ uN, ψ u1N]) :
    Nonempty (EnvS2PM V μ ⟨punitRecA :: env.consts⟩) := by
  have hty := fun ψ =>
    denoteP_punitRecA_type (m := mp.base2)
      (A := fun ψ => AVExpr.const .punitRec [ψ uN, ψ u1N]) ψ hP hU
  refine declStepPM_of_basis_rec_cons mp
    (A := fun ψ => AVExpr.const .punitRec [ψ uN, ψ u1N]) hfresh
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (fun _ h => nomatch h))
    hbase hag
    (fun ψ => by rw [hcv ψ]; rfl)
    (fun _ _ => rfl) ?_
    (fun _ _ => trivial) (fun _ _ => trivial)
    (fun ψ => ⟨_, hty ψ⟩) ?_ ?_ ?_
  · intro ψ₁ ψ₂ hp
    rw [hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self),
      hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)]
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    exact (bitAgree_okP (bitAgree_punitRecA ψ) ρ).mpr
      (AnnotOkP_bconst_type V .punitRec [ψ uN, ψ u1N] ρ)
  · intro ψ ta h ρ
    rw [hty ψ] at h
    obtain rfl := (Option.some.inj h).symm
    rw [AVExpr.BitAgree.interp2_eq V (bitAgree_punitRecA ψ) ρ]
    exact bval2_mem_type V .punitRec [ψ uN, ψ u1N] ρ
  · intro m₂ hac φ
    refine recRulesP_cons_rec mp hfresh punitRecA_eq m₂ hac φ ?_
    intro rl hrl _
    rcases List.mem_cons.mp hrl with rfl | hr'
    · exact punitRecLawP (m := mp.base2) m₂ hP hU hac φ
    · exact nomatch hr'

/-- **The `PUnit` block, installed at the P tier.**  `BasisStepPB`'s
`punitK` branch — the two lanes in lockstep, exactly as
`declBasisPB_emptyK`. -/
theorem declBasisPB_punitK {env₂ : Env} (mp : EnvS2PM V μ env)
    (h : Setlec.SetR.BasisInstallR env
      Setlec.BasisKind.punitK.declsA env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  rw [show Setlec.BasisKind.punitK.declsA
    = [punitA, punitUnitA, punitRecA] from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hf1 : env.find? punitA.name = none :=
    Option.isNone_iff_eq_none.mp h1
  have hwf1 : EnvWF ⟨punitA :: env.consts⟩ :=
    EnvWF.cons mp.base2.base.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, hm1⟩ := extendPUnitS mp.base2.base hf1 hwf1
  obtain ⟨mp1⟩ := extendPUnitP mp hf1 m1
    (fun n hn => by rw [hm1, cvalWith_ne hn])
    (fun ψ => by rw [hm1, cvalWith_self]; rfl)
  have hP1 : (⟨punitA :: env.consts⟩ : Env).find? punitName
      = some punitA := by
    rw [Setlec.Env.find?_cons]; exact if_pos rfl
  have hf2 : (⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name
      = none := Option.isNone_iff_eq_none.mp h2
  have hwf2 : EnvWF ⟨punitUnitA :: punitA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ punitUnitA.toConstantVal.type = true
    have hf : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
        punitName = some punitA := by
      rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP1
    simp only [show punitUnitA.toConstantVal.type
        = Expr.const punitName [.param uN] from rfl,
      Expr.constsResolve, hf]
    rfl
  obtain ⟨m2, hm2⟩ := extendPUnitUnitS mp1.base2.base hP1 hf2 hwf2
  obtain ⟨mp2⟩ := extendPUnitUnitP mp1 hP1 hf2 m2
    (fun n hn => by rw [hm2, cvalWith_ne hn])
    (fun ψ => by rw [hm2, cvalWith_self]; rfl)
  have hP2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitName = some punitA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP1
  have hU2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitUnitName = some punitUnitA := by
    rw [Setlec.Env.find?_cons]; exact if_pos rfl
  have hf3 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitRecA.name = none := Option.isNone_iff_eq_none.mp h3
  have hfP : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩
      : Env).find? punitName = some punitA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hP2
  have hfU : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩
      : Env).find? punitUnitName = some punitUnitA := by
    rw [Setlec.Env.find?_cons, if_neg (by decide)]; exact hU2
  have hwf3 : EnvWF
      ⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ := by
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ _ heq => nomatch heq)⟩
    · show Expr.constsResolve _ punitRecA.toConstantVal.type = true
      rw [show punitRecA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN]) (.sort (.param u1N))
                { bi := .default, pw := .never })
              (Expr.forallE (Name.anonymous.str "unit")
                (.app (.bvar 0) (.const punitUnitName [.param uN]))
                (Expr.forallE (Name.anonymous.str "t")
                  (.const punitName [.param uN])
                  (.app (.bvar 2) (.bvar 0))
                  { bi := .default, pw := .ifAllZero [u1N] })
                { bi := .default, pw := .ifAllZero [u1N] })
              { bi := .implicit, pw := .ifAllZero [u1N] } from rfl]
      simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
        Bool.and_self]
    · intro cv mI rP rules heq
      injection heq with h1' h2' h3' h4'
      subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ punitRecRule.rhs = true
          rw [show punitRecRule.rhs = Expr.lam
              (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN]) (.sort (.param u1N))
                { bi := .default, pw := .never })
              (Expr.lam (Name.anonymous.str "unit")
                (.app (.bvar 0) (.const punitUnitName [.param uN]))
                (.bvar 0) { bi := .default, pw := .ifAllZero [u1N] })
              { bi := .default, pw := .ifAllZero [u1N] } from rfl]
          simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
            Bool.and_self]
      · exact nomatch hr'
  obtain ⟨m3, hm3⟩ := extendPUnitRecS mp2.base2.base hP2 hU2 hf3 hwf3
  exact extendPUnitRecP mp2 hP2 hU2 hf3 m3
    (fun n hn => by rw [hm3, cvalWith_ne hn])
    (fun ψ => by rw [hm3, cvalWith_self])

end PUnit

end Setlec.SetR.Interp2
