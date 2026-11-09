module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Semantics.LitParams
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Frame
import ConLeche.Semantics.LitStep
import ConLeche.Semantics.Skeleton
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Rules.Rigid

public section

/-!
# The soundness of the inference rules (task #305)

One lemma per constructor of `Infer`, at the constructor's grade
(`InferSem m φ g …` dispatches to the establishment motive at `.full`
and the consumption motive at `.io`).  The io grade is Lean's
`infer_only` (task #342 S4): its application runs no certificate and
its λ no domain check, and its claim is the hereditary `IORel` (task
#346; `IORel.lean`), with the neutral clause `IORelN`.

The motives are per valuation (task #342, L9): the context discipline
outside `ρ` is the structural `CtxOkS`, and the leaves' grading
(`LeavesGr`), `Sat` and, at the io grade, the subject's grading are
premises at the one valuation `ρ`.  They take the
conditional reduction and comparison claims (`RedSem`, `DefEqSem`),
whose subjects here are always types: an inferred type and its weak
head normal form, a Π's domain, a sort.  Their "not the point" premises
are discharged by `WellDenotedTy.ne_pt`.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

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
  intro hf Δa ea hC hea
  obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hf hC hea
  exact ⟨hft, hsub, ta, hta, fun ρ hρ hL _ =>
    IORelN.of_mem hta (hrow ρ hρ hL).2.1 (hrow ρ hρ hL).2.2⟩

/-- A rule that establishes is sound at either grade. -/
theorem InferSemFull.toSem {g : Grade} {d : Nat} {e t : Expr}
    (h : InferSemFull m φ d e t) : InferSem m φ g d e t := by
  cases g with
  | full => exact h
  | io => exact h.toIO

/-- **The full grade's view of the inference motive**, in the uniform
shape `InferSem.of_uniform` builds: at each valuation `ρ` where the
context is satisfied and the subject's leaves are graded, the subject's
grading, the type's grading and the membership.  The io grade's claim
is the hereditary `IORel` instead (task #342 L18), read case by case. -/
theorem InferSem.apply {d : Nat} {e t : Expr}
    (h : InferSem m φ .full d e t) (hfe : Frame d e) {Δa : List Term}
    {ea : Term} (hC : CtxOkS m φ d Δa e)
    (hea : denote m.acval env φ d e = some ea) :
    Frame d t ∧ LeavesSub t e ∧
      ∃ ta, denote m.acval env φ d t = some ta ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
          (Grade.full = .io → WellDenoted V ρ ea) →
          WellDenoted V ρ ea ∧ WellDenotedTy V ρ ta ∧
            interp V ρ ea ∈ˢ interp V ρ ta := by
  obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
  exact ⟨hft, hsub, ta, hta, fun ρ hρ hL _ => hrow ρ hρ hL⟩

/-- `InferSem.apply`'s converse: the uniform statement builds the
motive at either grade. -/
theorem InferSem.of_uniform {g : Grade} {d : Nat} {e t : Expr}
    (h : ∀ {Δa : List Term} {ea : Term}, Frame d e →
      CtxOkS m φ d Δa e → denote m.acval env φ d e = some ea →
      Frame d t ∧ LeavesSub t e ∧
        ∃ ta, denote m.acval env φ d t = some ta ∧
          ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
            (g = .io → WellDenoted V ρ ea) →
            WellDenoted V ρ ea ∧ WellDenotedTy V ρ ta ∧
              interp V ρ ea ∈ˢ interp V ρ ta) :
    InferSem m φ g d e t := by
  cases g with
  | full =>
    intro hfe Δa ea hC hea
    obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
    exact ⟨hft, hsub, ta, hta, fun ρ hρ hL =>
      hrow ρ hρ hL (fun hg => by simp at hg)⟩
  | io =>
    intro hfe Δa ea hC hea
    obtain ⟨hft, hsub, ta, hta, hrow⟩ := h hfe hC hea
    exact ⟨hft, hsub, ta, hta, fun ρ hρ hL hge =>
      IORelN.of_mem hta (hrow ρ hρ hL (fun _ => hge)).2.1
        (hrow ρ hρ hL (fun _ => hge)).2.2⟩

/-- **The sort fact at a grade** (`sortSemAt_of_claims` at the
motives): a subject whose inferred type reduces to `.sort u` reads into
the universe — and is graded, which at the io grade is the premise and
at the full grade the first motive's conclusion — at every valuation
where the context is satisfied and the subject's leaves are graded.
At the io grade the claim is `IORel`: the subject is a type there ("not
pt" source (1)), and a sort is no ∀ — the inferred type reduces to a
sort, and a ∀ reduces only to itself (`Red.rigid`) — so it is a member. -/
theorem sortSem_of {g : Grade} {d : Nat} {e s : Expr} {u : Level}
    (hs : InferSem m φ g d e s) (hu : RedSem m φ d s (.sort u))
    (hur : g = .io → Red env d s (.sort u))
    (hfe : Frame d e) {Δa : List Term} {ea : Term}
    (hC : CtxOkS m φ d Δa e)
    (hea : denote m.acval env φ d e = some ea) :
    ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d e ρ →
      (g = .io → WellDenotedTy V ρ ea) →
      WellDenoted V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V) := by
  cases g with
  | full =>
    obtain ⟨hfs, hsub, sa, hsa, hrow⟩ := hs.apply hfe hC hea
    obtain ⟨-, -, ua, hua, hred⟩ := hu hfs (hC.of_subset hsub) hsa
    rw [denote] at hua
    obtain rfl : ua = .sort (u.eval φ) := (Option.some.inj hua).symm
    intro ρ hρ hL _
    obtain ⟨hge, hgs, hm⟩ := hrow ρ hρ hL (fun hg => nomatch hg)
    -- "not pt" source (1): the inferred type `sa` is a type
    have heq := (hred ρ hρ (hL.of_subset hsub) hgs.1 hgs.ne_pt).2
    refine ⟨hge, ?_⟩
    rw [heq, interp_sort] at hm
    exact hm
  | io =>
    obtain ⟨hfs, hsub, sa, hsa, hrow⟩ := hs hfe hC hea
    obtain ⟨-, -, ua, hua, hred⟩ := hu hfs (hC.of_subset hsub) hsa
    rw [denote] at hua
    obtain rfl : ua = .sort (u.eval φ) := (Option.some.inj hua).symm
    intro ρ hρ hL hgr
    have hty := hgr rfl
    rcases (hrow ρ hρ hL hty.1).1 with h | h | h
    · -- "not pt" source (1): the subject is a type
      exact absurd h hty.ne_pt
    · obtain ⟨hgs, hm⟩ := h.of_reading hsa
      -- "not pt" source (1): the inferred type `sa` is a type
      have heq := (hred ρ hρ (hL.of_subset hsub) hgs.1 hgs.ne_pt).2
      rw [heq, interp_sort] at hm
      exact ⟨hty.1, hm⟩
    · obtain ⟨_, _, rfl⟩ := h.forallE
      exact nomatch Red.rigid (hur rfl) trivial

/-- A sort has the successor sort. -/
theorem Infer.sort_sound {g : Grade} {d : Nat} {u : Level} :
    InferSem m φ g d (.sort u) (.sort (.succ u)) := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  rw [denote] at hea
  obtain rfl : ea = .sort (u.eval φ) := (Option.some.inj hea).symm
  have hty : denote m.acval env φ d (.sort (.succ u))
      = some (.sort (Level.eval φ (.succ u))) := by rw [denote]
  refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    fun l hl => by simp [Expr.fvarLeaves] at hl,
    _, hty, fun ρ _ _ => ⟨by simp, ⟨by simp, IsTy_univ _⟩,
      (sound_sort V ρ (u.eval φ)).2⟩⟩

/-- A free variable: `CtxOkS`'s leaf package, the type's grading from
`LeavesGr` at the valuation. -/
theorem Infer.fvar_sound {g : Grade} {d idx : Nat} {ty : Expr} (h : idx < d) :
    InferSem m φ g d (.fvar idx ty) ty := by
  refine InferSemFull.toSem ?_
  intro hf Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hf
  have hleaf : (idx, ty) ∈ (Expr.fvar idx ty).fvarLeaves := by
    simp [Expr.fvarLeaves]
  obtain ⟨-, -, tya, Aa, hden, hi, hlink⟩ :
      idx < d ∧ Expr.fvarsBelow idx ty ∧
        ∃ tya Aa,
          denote m.acval env φ d ty = some tya ∧
          Δa[d - 1 - idx]? = some Aa ∧
          (∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ tya
              = interp V (fun j => ρ (j + (d - 1 - idx) + 1)) Aa) :=
    hC.2 _ hleaf
  rw [denote] at hea
  obtain rfl : ea = .bvar (d - 1 - idx) := (Option.some.inj hea).symm
  simp only [Expr.WScoped] at hws
  have hmem : ∀ l ∈ ty.fvarLeaves, l ∈ (Expr.fvar idx ty).fvarLeaves := by
    intro l hl
    rw [Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hl
  refine ⟨⟨hws.2.mono (by omega), hLb (idx, ty) (by simp [Expr.fvarLeaves]),
      fun l hl => hLb l (hmem l hl)⟩,
    hmem, tya, hden, fun ρ hρ hL => ⟨by simp, hL _ hleaf tya hden, ?_⟩⟩
  rw [interp_bvar, hlink ρ hρ]
  exact hρ (d - 1 - idx) Aa hi

/-- A constant: `ConstType`. -/
theorem Infer.const_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci)
    (hus : us.length = ci.toConstantVal.levelParams.length) :
    InferSem m φ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea hC hea
  rw [denote, hf] at hea
  dsimp only at hea
  rw [ite_eq_left hus] at hea
  obtain rfl : ea = m.acval n
      (Level.substFn φ ci.toConstantVal.levelParams us) :=
    (Option.some.inj hea).symm
  obtain ⟨ta, hta, hok, hmem⟩ := hin.const_ty d n ci us hf hus
  obtain ⟨htc, -, -, htb, -⟩ := m.wf.consts _ (Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact htc
  exact ⟨⟨Expr.WScoped.of_not_hasFvar hnf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact htb,
      Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; cases hl),
    ta, hta, fun ρ _ _ => ⟨m.acval_wellDenoted n _ ρ,
      hok ρ, hmem ρ⟩⟩

/-- A `Nat` literal: `NatHeads`. -/
theorem Infer.natLit_sound (hin : RulesInputs V m φ) {g : Grade} {d n : Nat}
    (h : ConLeche.natLitSupported env = true) :
    InferSem m φ g d (.lit (.natVal n)) (.const natName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  rw [denote, ite_eq_left h] at hea
  obtain rfl : ea = natLitT
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
    have hta : denote m.acval env φ d (.const natName [])
        = some (m.acval natName (Level.substFn φ [] [])) := by
      rw [denote, hf]
      dsimp only
      rw [ite_eq_left (by simp [hlp]), hlp]
    have hrow : ∀ ρ : Nat → V,
        WellDenoted V ρ (natLitT
            (m.acval natZeroName (Level.substFn φ [] []))
            (m.acval natSuccName (Level.substFn φ [] [])) n) ∧
          interp V ρ (natLitT
              (m.acval natZeroName (Level.substFn φ [] []))
              (m.acval natSuccName (Level.substFn φ [] [])) n)
            ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) :=
      fun ρ => natLit_factsAV (m.acval_wellDenoted _ _ ρ)
        (m.acval_wellDenoted _ _ ρ) (hin.nat_heads h ρ).1
        (hin.nat_heads h ρ).2.1 (hin.nat_heads h ρ).2.2 n
    exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
        fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      _, hta,
      fun ρ _ _ => ⟨(hrow ρ).1,
        ⟨m.acval_wellDenoted _ _ ρ,
          (hin.nat_heads h ρ).2.2⟩,
        (hrow ρ).2⟩⟩

/-- A string literal: `strLitFacts`. -/
theorem Infer.strLit_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {s : String} (h : ConLeche.strLitSupported env = true) :
    InferSem m φ g d (.lit (.strVal s)) (.const stringName []) := by
  refine InferSemFull.toSem ?_
  intro _ Δa ea _ hea
  obtain ⟨-, ciS, -, -, -, -, -, -, -, -, -, hfS, -,
    -, -, -, -, -, hlpS, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    ConLeche.strLitSupported_inv h
  have hta : denote m.acval env φ d (.const stringName [])
      = some (m.acval ConLeche.stringName (Level.substFn φ [] [])) := by
    have hc := denote_const (acval := m.acval) (φ := φ) (d := d)
      (us := []) hfS (by simp [hlpS])
    rwa [hlpS] at hc
  exact ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    (fun l hl => by simp [Expr.fvarLeaves] at hl),
    _, hta,
    fun ρ _ _ => ⟨(strLitFacts hin.const_ty hin.nat_heads h hea ρ).1,
      ⟨m.acval_wellDenoted _ _ ρ,
        (strLitFacts hin.const_ty hin.nat_heads h hea ρ).2.2⟩,
      (strLitFacts hin.const_ty hin.nat_heads h hea ρ).2.1⟩⟩

/-- A Π-type: the two sort facts (`sortSemAt_of_claims`'s content). -/
theorem Infer.forallE_sound {g : Grade} {d : Nat}
    {ty body s bs : Expr} {u v : Level}
    (hs : InferSem m φ g d ty s) (hu : RedSem m φ d s (.sort u))
    (hur : g = .io → Red env d s (.sort u))
    (hbs : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bs)
    (hv : RedSem m φ (d + 1) bs (.sort v))
    (hvr : g = .io → Red env (d + 1) bs (.sort v)) :
    InferSem m φ g d (.forallE ty body) (.sort (.imax u v)) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denote_forallE_inv hea
  have hdomU := sortSem_of hs hu hur ⟨hws.1, hb.1, hLty⟩ hC.forallE_ty htyA
  have hCop : CtxOkS m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkS.openS hC.forallE_ty hC.forallE_body htyA
  have hcodU := sortSem_of hbs hv hvr ⟨hwopen, hbopen, hLopen⟩ hCop hbaA
  refine ⟨⟨by simp [Expr.WScoped], by simp [Expr.looseBVarsBounded],
      fun l hl => by simp [Expr.fvarLeaves] at hl⟩,
    (fun l hl => by simp [Expr.fvarLeaves] at hl),
    _, by rw [denote], ?_⟩
  intro ρ hρ hL hgr
  -- the domain: its own sort run; at the io grade off the subject
  have hdom := hdomU ρ hρ hL.forallE_ty (fun hg => (hgr hg).pi_dom)
  have hdomTy : WellDenotedTy V ρ tyA := ⟨hdom.1, IsTy_of_mem_univ hdom.2⟩
  -- the codomain, at every point of the domain
  have hcod : ∀ x, x ∈ˢ interp V ρ tyA →
      WellDenoted V (cons x ρ) baA ∧
        interp V (cons x ρ) baA ∈ˢ (univ (v.eval φ) : V) :=
    fun x hx => hcodU (cons x ρ) (Sat_cons V hρ hx)
      (LeavesGr.open hC.forallE_ty hC.forallE_body hL.forallE_ty
        hL.forallE_body htyA hdomTy)
      (fun hg => ⟨(hgr hg).pi_body x hx, (hgr hg).pi_fib x hx⟩)
  have hrow := sound_pi V (u := u.eval φ) (v := v.eval φ)
    hdom.1 (fun x hx => (hcod x hx).1) hdom.2
    (fun x hx => (hcod x hx).2)
  refine ⟨hrow.1, ⟨by simp, by exact IsTy_univ _⟩, ?_⟩
  exact hrow.2

/-- A λ: the body's inferred types are types, so the abstraction is a
member of their function space (`lamV_mem`). -/
theorem Infer.lam_soundFull {d : Nat}
    {ty body s bt : Expr} {u : Level}
    (hs : InferSemFull m φ d ty s)
    (hu : RedSem m φ d s (.sort u))
    (hbt : InferSem m φ .full (d + 1) (body.instantiate1 (.fvar d ty)) bt) :
    InferSem m φ .full d (.lam ty body) (.forallE ty (bt.abstract1 d)) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading
  rw [denote] at hea
  rcases htyA : denote m.acval env φ d ty with _ | tyA
  · rw [htyA] at hea; exact nomatch hea
  rw [htyA] at hea
  rcases hba : denote m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .lam tyA ba :=
    (Option.some.inj hea).symm
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hCop : CtxOkS m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkS.openS hC.lam_ty hC.lam_body htyA
  -- the opened body's inferred type
  obtain ⟨hbtf, hbtsub, btA, hbtA, hrowB⟩ :=
    hbt.apply ⟨hwopen, hbopen, hLopen⟩ hCop hba
  obtain ⟨hwbt, hbtb, hLbt⟩ := hbtf
  -- the abstraction round trip, for the ∀-type's reading
  have hleaf : Expr.LeafCond d ty (body.instantiate1 (.fvar d ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact rfl
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl => hleaf l (hbtsub l hl))
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    ConLeche.abstract1_instantiate1 bt 0 hcons hbtb
  have hta : denote m.acval env φ d (.forallE ty (bt.abstract1 d))
      = some (.pi tyA btA) := by
    rw [denote, htyA, hround, hbtA]
    rfl
  have hCbt : CtxOkS m φ (d + 1) (tyA :: Δa) bt := hCop.of_subset hbtsub
  -- the conclusion's frame and leaves
  have hsubT : ∀ l ∈ (Expr.forallE ty (bt.abstract1 d)).fvarLeaves,
      l ∈ (Expr.lam ty body).fvarLeaves := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with h2 | h2
    · exact Or.inl h2
    · obtain ⟨hlbt, hlne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne bt 0 hwbt l h2
      rcases Expr.fvarLeaves_instantiate1 body 0 (hbtsub l hlbt) with h3 | h3
      · exact Or.inr h3
      · rw [Expr.fvarLeaves] at h3
        rcases List.mem_cons.mp h3 with rfl | h4
        · exact absurd rfl hlne
        · exact Or.inl h4
  have hwT : Expr.WScoped d (.forallE ty (bt.abstract1 d)) := by
    simp only [Expr.WScoped]
    exact ⟨hws.1, ConLeche.WScoped.abstract1 0 hwbt⟩
  have hbT : (Expr.forallE ty (bt.abstract1 d)).looseBVarsBounded 0
      = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hb.1, ConLeche.looseBVarsBounded_abstract1 bt 0 hbtb⟩
  refine ⟨⟨hwT, hbT, fun l hl => hLb l (hsubT l hl)⟩,
    hsubT, _, hta, ?_⟩
  intro ρ hρ hL hgr
  -- the domain's grading: established at the full grade by its own
  -- sort run, consumed at the io grade off the subject (`lam_dom`)
  have hokty : WellDenotedTy V ρ tyA := by
    have h := sortSem_of (g := .full) hs hu (fun hg => nomatch hg) ⟨hws.1, hb.1, hLty⟩
      hC.lam_ty htyA ρ hρ hL.lam_ty (fun hg => nomatch hg)
    exact ⟨h.1, IsTy_of_mem_univ h.2⟩
  -- the opened body at every point of the domain
  have hLop : ∀ x, LeavesGr m φ (d + 1) (body.instantiate1 (.fvar d ty))
      (cons x ρ) := fun _ =>
    LeavesGr.open hC.lam_ty hC.lam_body hL.lam_ty hL.lam_body htyA hokty
  have hrow : ∀ x, x ∈ˢ interp V ρ tyA →
      WellDenoted V (cons x ρ) ba ∧ WellDenotedTy V (cons x ρ) btA ∧
        interp V (cons x ρ) ba ∈ˢ interp V (cons x ρ) btA := fun x hx =>
    hrowB (cons x ρ) (Sat_cons V hρ hx) (hLop x)
      (fun hg => nomatch hg)
  refine ⟨?_, ?_, ?_⟩
  · -- the λ's own grading
    rw [WellDenoted_lam]
    exact ⟨hokty.1, hokty.2, fun x hx => (hrow x hx).1,
      fun x => interp V (cons x ρ) btA,
      fun x hx => (hrow x hx).2.2,
      fun x hx => (hrow x hx).2.1.2⟩
  · -- the copied ∀-type's grading
    refine ⟨?_, IsTy_piV⟩
    rw [WellDenoted_pi]
    exact ⟨hokty.1, hokty.2, fun x hx => (hrow x hx).2.1.1,
      fun x hx => (hrow x hx).2.1.2⟩
  · -- the membership row
    exact (sound_lam V hokty.1 hokty.2
      (fun x hx => (hrow x hx).1)
      (fun x hx => (hrow x hx).2.2)
      (fun x hx => (hrow x hx).2.1.2)).2

/-- **A λ at the io grade** (the fragment's `InferIO.lam_sound`): no
domain check.  Where every body value is the point, so is the
abstraction; otherwise it is the graph of its body values over its own
domain, a graded type off the subject's grading (`lam_dom`), and its
every application is a body value, which satisfies the body's claim:
the hereditary claim at the ∀ of the body's type. -/
theorem Infer.lam_soundIO {d : Nat} {ty body bt : Expr}
    (hbt : InferSemIO m φ (d + 1) (body.instantiate1 (.fvar d ty)) bt) :
    InferSemIO m φ d (.lam ty body) (.forallE ty (bt.abstract1 d)) := by
  intro hfr Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLty : Expr.LeavesBounded ty := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded body := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨tyA, ba, htyA, hba, rfl⟩ := denote_lam_inv hea
  obtain ⟨hwopen, hbopen, hLopen⟩ :=
    frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbody
  have hCop : CtxOkS m φ (d + 1) (tyA :: Δa)
      (body.instantiate1 (.fvar d ty)) :=
    CtxOkS.openS hC.lam_ty hC.lam_body htyA
  -- the opened body's inferred type
  obtain ⟨hbtf, hbtsub, btA, hbtA, hrowB⟩ :=
    hbt ⟨hwopen, hbopen, hLopen⟩ hCop hba
  obtain ⟨hwbt, hbtb, hLbt⟩ := hbtf
  -- the abstraction round trip
  have hleaf : Expr.LeafCond d ty (body.instantiate1 (.fvar d ty)) := by
    intro l hl hd
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact absurd hd (by
        have := Expr.fvarLeaves_lt_of_wscoped hws.2 l h2
        omega)
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact rfl
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hws.1 l h3
          omega)
  have hcons : Expr.fvarConsistent d ty bt :=
    Expr.fvarConsistent_of_leafCond bt (fun l hl => hleaf l (hbtsub l hl))
  have hround : (bt.abstract1 d).instantiate1 (.fvar d ty) = bt :=
    ConLeche.abstract1_instantiate1 bt 0 hcons hbtb
  have hta : denote m.acval env φ d (.forallE ty (bt.abstract1 d))
      = some (.pi tyA btA) := by
    rw [denote, htyA, hround, hbtA]
    rfl
  have hsubT : ∀ l ∈ (Expr.forallE ty (bt.abstract1 d)).fvarLeaves,
      l ∈ (Expr.lam ty body).fvarLeaves := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with h2 | h2
    · exact Or.inl h2
    · obtain ⟨hlbt, hlne⟩ := ConLeche.Expr.fvarLeaves_abstract1_ne bt 0 hwbt l h2
      rcases Expr.fvarLeaves_instantiate1 body 0 (hbtsub l hlbt) with h3 | h3
      · exact Or.inr h3
      · rw [Expr.fvarLeaves] at h3
        rcases List.mem_cons.mp h3 with rfl | h4
        · exact absurd rfl hlne
        · exact Or.inl h4
  have hwT : Expr.WScoped d (.forallE ty (bt.abstract1 d)) := by
    simp only [Expr.WScoped]
    exact ⟨hws.1, ConLeche.WScoped.abstract1 0 hwbt⟩
  have hbT : (Expr.forallE ty (bt.abstract1 d)).looseBVarsBounded 0
      = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hb.1, ConLeche.looseBVarsBounded_abstract1 bt 0 hbtb⟩
  refine ⟨⟨hwT, hbT, fun l hl => hLb l (hsubT l hl)⟩,
    hsubT, _, hta, ?_⟩
  intro ρ hρ hL hgr
  -- the domain's grading, off the subject's ("not pt" source (1))
  have hokty : WellDenotedTy V ρ tyA := hgr.lam_dom
  have hLop : ∀ x, LeavesGr m φ (d + 1) (body.instantiate1 (.fvar d ty))
      (cons x ρ) := fun _ =>
    LeavesGr.open hC.lam_ty hC.lam_body hL.lam_ty hL.lam_body htyA hokty
  have hrow : ∀ x, x ∈ˢ interp V ρ tyA →
      IORel m φ (d + 1) bt (cons x ρ) (interp V (cons x ρ) ba) := fun x hx =>
    (hrowB (cons x ρ) (Sat_cons V hρ hx) (hLop x) (hgr.lam_body x hx)).1
  -- a λ is not neutral
  refine ⟨?_, fun h => by simp [ConLeche.Expr.ioNeutral, ConLeche.Expr.getAppFn] at h⟩
  rw [interp_lam]
  by_cases hall : ∀ x, x ∈ˢ interp V ρ tyA → interp V (cons x ρ) ba = pt
  · exact Or.inl (lamV_eq_pt hall)
  obtain ⟨x₀, hx₀, hx₀'⟩ : ∃ x, x ∈ˢ interp V ρ tyA ∧ interp V (cons x ρ) ba ≠ pt :=
    Classical.byContradiction fun hn => hall fun x hx =>
      Classical.byContradiction fun hx' => hn ⟨x, hx, hx'⟩
  rw [lamV_eq_graph (lamV_ne_pt_of hx₀ hx₀')]
  refine Or.inr (Or.inr ?_)
  rw [IOHered_forallE]
  obtain ⟨-, -, -, Bl, hBl, -⟩ := cast (WellDenoted_lam V ρ tyA ba) hgr
  refine ⟨tyA, htyA, hokty, ⟨Bl, graph_mem_piSet hBl⟩,
    ⟨x₀, hx₀, by rw [app_graph hx₀]; exact hx₀'⟩, fun x hx => ?_⟩
  rw [app_graph hx, hround]
  exact hrow x hx

/-- A λ, at either grade. -/
theorem Infer.lam_sound {g : Grade} {d : Nat}
    {ty body s bt : Expr} {u : Level}
    (hs : g = .full → InferSemFull m φ d ty s)
    (hu : g = .full → RedSem m φ d s (.sort u))
    (hbt : InferSem m φ g (d + 1) (body.instantiate1 (.fvar d ty)) bt) :
    InferSem m φ g d (.lam ty body) (.forallE ty (bt.abstract1 d)) := by
  cases g with
  | full => exact Infer.lam_soundFull (hs rfl) (hu rfl) hbt
  | io => exact Infer.lam_soundIO hbt

/-- An application, certified (the full grade's arm). -/
theorem Infer.app_soundCert {d : Nat}
    {f a tf ty body ta : Expr}
    (htf : InferSem m φ .full d f tf) (hw : RedSem m φ d tf (.forallE ty body))
    (hta : InferSem m φ .full d a ta) (hd : DefEqSem m φ d ta ty) :
    InferSem m φ .full d (.app f a) (body.instantiate1 a) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading splits
  rw [denote] at hea
  rcases hfa : denote m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  -- the head, its type, and the ∀ it reduces to (readings)
  obtain ⟨htff, htfsub, tfa, htfa, hrowF⟩ :=
    htf.apply ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa
  obtain ⟨hpif, hpisub, pa, hpa, hredf⟩ :=
    hw htff (hC.app_fn.of_subset htfsub) htfa
  obtain ⟨hwfe, hbfe, hLfe⟩ := hpif
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  have hLty' : Expr.LeavesBounded ty := fun l hl =>
    hLfe l (by simp [Expr.fvarLeaves, hl])
  have hCpi : CtxOkS m φ d Δa (.forallE ty body) :=
    (hC.app_fn.of_subset htfsub).of_subset hpisub
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denote_forallE_inv hpa
  -- the argument's type (reading)
  obtain ⟨htaf, htasub, tyaA, htyaA, hrowA⟩ :=
    hta.apply ⟨hws.2, hb.2, hLa⟩ hC.app_arg haa
  -- the returned type's reading, `denote_beta` backwards
  have hcross : denote m.acval env φ d (body.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denote_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  refine ⟨⟨Expr.WScoped.instantiate1_gen hws.2 0 hwfe.2,
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbfe.2,
      fun l hl => ?_⟩, fun l hl => ?_, _, hcross, ?_⟩
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hLfe l (by simp [Expr.fvarLeaves, h2])
    · exact hLa l h2
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · rw [Expr.fvarLeaves]
      exact List.mem_append_left _ (htfsub l (hpisub l
        (by simp [Expr.fvarLeaves, h2])))
    · rw [Expr.fvarLeaves]
      exact List.mem_append_right _ h2
  intro ρ hρ hL hgr
  -- the head at `ρ`, and its type's reduct
  obtain ⟨hgfa, hgtfa, hrowfM⟩ :=
    hrowF ρ hρ hL.app_fn (fun hg => (hgr hg).app_fn)
  have hLtf : LeavesGr m φ d tf ρ := hL.app_fn.of_subset htfsub
  -- "not pt" source (1): the head's inferred type `tfa` is a type
  obtain ⟨hokpa, hredfρ⟩ := hredf ρ hρ hLtf hgtfa.1 hgtfa.ne_pt
  -- the ∀'s reading, split
  have hAty : WellDenotedTy V ρ Aa := hokpa.pi_dom
  have hokBa : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) Ba :=
    hokpa.pi_body
  have hBty : ∀ x, x ∈ˢ interp V ρ Aa → IsTy (interp V (cons x ρ) Ba) :=
    (cast (WellDenoted_pi V ρ Aa Ba) hokpa).2.2.2
  -- the argument at `ρ`, and the domain agreement
  obtain ⟨hgaa, hgtyaA, hrowaM⟩ :=
    hrowA ρ hρ hL.app_arg (fun hg => (hgr hg).app_arg)
  -- "not pt" source (1): the argument's inferred type `tyaA` is a type
  -- "not pt" source (1): the ∀'s domain `Aa` is a type
  have hdom : interp V ρ tyaA = interp V ρ Aa :=
    hd htaf ⟨hwfe.1, hbfe.1, hLty'⟩ (hC.app_arg.of_subset htasub)
      hCpi.forallE_ty htyaA hAa ρ hρ (hL.app_arg.of_subset htasub)
      (hLtf.of_subset hpisub).forallE_ty hgtyaA.1 hAty.1
      hgtyaA.ne_pt hAty.ne_pt
  have ha2 : interp V ρ aa ∈ˢ interp V ρ Aa := by
    rw [← hdom]
    exact hrowaM
  have hf2 : interp V ρ fa ∈ˢ interp V ρ (.pi Aa Ba) := by
    rw [← hredfρ]
    exact hrowfM
  exact ⟨(sound_app V hgfa hgaa hf2 ha2 hAty.2).1,
    (WellDenotedTy_inst0 hgaa).mpr ⟨hokBa _ ha2, hBty _ ha2⟩,
    (sound_app V hgfa hgaa hf2 ha2 hAty.2).2⟩

/-- **`let`, by substitution**: the body's claim at its value is the
`let`'s (`interp_zeta`).  The value's grading — part of the `let`'s —
is the subject's at the io grade and the value's own full-grade
inference at the full grade (the establishment motive concludes it).
The type's sort and the value/type comparison are not consumed: no
claim reads a `let`'s type, and the body is typed at the value itself. -/
theorem Infer.letE_sound {g : Grade} {d : Nat} {ty v body tv t : Expr}
    (htv : g = .full → InferSemFull m φ d v tv)
    (hb : InferSem m φ g d (body.instantiate1 v) t) :
    InferSem m φ g d (.letE ty v body) t := by
  cases g with
  | full =>
    refine InferSem.of_uniform ?_
    intro Δa ea hfr hC hea
    obtain ⟨-, va, ba, -, hva, hba, rfl⟩ := denote_letE_inv hea
    obtain ⟨hfr', hsub, hred⟩ := zeta_syntax hfr hva hba
    obtain ⟨hfv, hsubv⟩ := letE_val_frame hfr
    obtain ⟨hft, htsub, ta, hta, hrow⟩ :=
      hb.apply hfr' (hC.of_subset hsub) hred
    refine ⟨hft, fun l hl => hsub l (htsub l hl), ta, hta, ?_⟩
    intro ρ hρ hL _
    have hgv : WellDenoted V ρ va := by
      obtain ⟨-, -, _, -, hrowv⟩ := htv rfl hfv (hC.of_subset hsubv) hva
      exact (hrowv ρ hρ (hL.of_subset hsubv)).1
    obtain ⟨hge, hgt, hmem⟩ := hrow ρ hρ (hL.of_subset hsub) (fun hg => nomatch hg)
    refine ⟨(WellDenoted_zeta _ hgv).mpr hge, hgt, ?_⟩
    rw [interp_zeta]
    exact hmem
  | io =>
    intro hfr Δa ea hC hea
    obtain ⟨-, va, ba, -, hva, hba, rfl⟩ := denote_letE_inv hea
    obtain ⟨hfr', hsub, hred⟩ := zeta_syntax hfr hva hba
    obtain ⟨hft, htsub, ta, hta, hrow⟩ := hb hfr' (hC.of_subset hsub) hred
    refine ⟨hft, fun l hl => hsub l (htsub l hl), ta, hta, ?_⟩
    intro ρ hρ hL hgr
    have hgv : WellDenoted V ρ va := hgr.letE_val
    have h := hrow ρ hρ (hL.of_subset hsub) ((WellDenoted_zeta _ hgv).mp hgr)
    rw [interp_zeta]
    -- a `let` is not neutral
    exact ⟨h.1, fun h' => by simp [ConLeche.Expr.ioNeutral, ConLeche.Expr.getAppFn] at h'⟩

/-- **The io grade's application, uncertified** (Lean's `infer_only`;
the fragment's `InferIO.app_sound`).  The claim is the hereditary
`IORel`.  Where the head is the point, so is the application.  Where it
is not, the subject's own app slot is in the graph regime, and a graph
determines its domain (`slotTransfer`): if the head is a member of its
type ("not pt" source (1): that type is a type, so its reduct to the ∀
is an equation), the argument lies in the ∀'s domain and the
application in its body; if the head's claim is hereditary ("not pt"
source (4)), the type is syntactically the ∀ (`Red.rigid`), the graph's
domain is its domain, and the claim at the opened body, at the
argument's value, is the claim at the body instantiated with the
argument (`IORel_substFvarAt`). -/
theorem Infer.app_soundIO {d : Nat}
    {f a tf ty body : Expr}
    (htf : InferSemIO m φ d f tf) (hw : RedSem m φ d tf (.forallE ty body))
    (hwr : Red env d tf (.forallE ty body)) :
    InferSemIO m φ d (.app f a) (body.instantiate1 a) := by
  intro hfr Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  -- the subject's reading splits
  rw [denote] at hea
  rcases hfa : denote m.acval env φ d f with _ | fa
  · rw [hfa] at hea; exact nomatch hea
  rw [hfa] at hea
  rcases haa : denote m.acval env φ d a with _ | aa
  · rw [haa] at hea; exact nomatch hea
  rw [haa] at hea
  obtain rfl : ea = .app fa aa := (Option.some.inj hea).symm
  obtain ⟨htff, htfsub, tfa, htfa, hrowF⟩ :=
    htf ⟨hws.1, hb.1, hLf⟩ hC.app_fn hfa
  obtain ⟨hpif, hpisub, pa, hpa, hredf⟩ :=
    hw htff (hC.app_fn.of_subset htfsub) htfa
  obtain ⟨hwfe, hbfe, hLfe⟩ := hpif
  simp only [Expr.WScoped] at hwfe
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbfe
  obtain ⟨Aa, Ba, hAa, hBa, rfl⟩ := denote_forallE_inv hpa
  have hcross : denote m.acval env φ d (body.instantiate1 a)
      = some (Ba.inst aa) := by
    rw [denote_beta (ty := ty) m.acval_closed
      (acval_inst_self m) hwfe.2.fvarsBelow hws.2 hb.2 haa 0, hBa]
    rfl
  refine ⟨⟨Expr.WScoped.instantiate1_gen hws.2 0 hwfe.2,
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbfe.2,
      fun l hl => ?_⟩, fun l hl => ?_, _, hcross, ?_⟩
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hLfe l (by simp [Expr.fvarLeaves, h2])
    · exact hLa l h2
  · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · rw [Expr.fvarLeaves]
      exact List.mem_append_left _ (htfsub l (hpisub l
        (by simp [Expr.fvarLeaves, h2])))
    · rw [Expr.fvarLeaves]
      exact List.mem_append_right _ h2
  intro ρ hρ hL hge
  have hokf : WellDenoted V ρ fa := hge.app_fn
  have hoka : WellDenoted V ρ aa := hge.app_arg
  obtain ⟨v, A, B, hfslot, haslot, -⟩ := (cast (WellDenoted_app V ρ fa aa) hge).2.2
  rw [interp_app]
  by_cases hfp : interp V ρ fa = pt
  · rw [hfp, app_pt]; exact IORelN.pt
  obtain ⟨hrelF, hneuF⟩ := hrowF ρ hρ hL.app_fn hokf
  by_cases hm : IOMem m φ d tf ρ (interp V ρ fa)
  · -- the head is a member of its type
    obtain ⟨hgtfa, hrowfM⟩ := hm.of_reading htfa
    -- "not pt" source (1): the head's inferred type `tfa` is a type
    obtain ⟨hokpa, hredfρ⟩ :=
      hredf ρ hρ (hL.app_fn.of_subset htfsub) hgtfa.1 hgtfa.ne_pt
    have hf' : interp V ρ fa ∈ˢ piV (interp V ρ Aa) fun x => interp V (cons x ρ) Ba := by
      have h2 := hrowfM
      rw [hredfρ, interp_pi] at h2
      exact h2
    have hgr : interp V ρ fa ∈ˢ piR 1 (interp V ρ Aa) fun x => interp V (cons x ρ) Ba := by
      rw [piR_pos Nat.one_ne_zero]; exact mem_piSet_of_mem_piV hf' hfp
    have ha2 : interp V ρ aa ∈ˢ interp V ρ Aa :=
      Rules.slotTransfer Nat.one_ne_zero hgr hfslot haslot
    refine IORelN.of_mem hcross
      ((WellDenotedTy_inst0 hoka).mpr ⟨hokpa.pi_body _ ha2, hokpa.pi_fib _ ha2⟩) ?_
    rw [interp_inst0]
    exact app_mem_piV hf' ha2
  rcases hrelF with h | h | h
  · exact absurd h hfp
  · exact absurd h hm
  · -- "not pt" source (4): the head's claim is hereditary, its type the ∀;
    -- the head is then not neutral, nor is the application
    refine ⟨?main, fun hneu => ?neu⟩
    case neu =>
      have hfneu : f.ioNeutral = true := by
        simpa [ConLeche.Expr.ioNeutral, ConLeche.Expr.getAppFn] using hneu
      rcases hneuF hfneu with h' | h'
      · exact absurd h' hfp
      · exact absurd h' hm
    obtain ⟨ty', body', rfl⟩ := h.forallE
    have heq := Red.rigid hwr trivial
    injection heq with hty hbody
    subst hty hbody
    rw [IOHered_forallE] at h
    obtain ⟨tya, htya, -, ⟨B', hB'⟩, -, hall⟩ := h
    have hgr : interp V ρ fa ∈ˢ piR 1 (interp V ρ tya) B' := by
      rw [piR_pos Nat.one_ne_zero]; exact hB'
    have ha2 : interp V ρ aa ∈ˢ interp V ρ tya :=
      Rules.slotTransfer Nat.one_ne_zero hgr hfslot haslot
    have hsub := IORel_substFvarAt hws.2 hb.2 haa (body.instantiate1 (.fvar d ty)) d ρ
      (SetTheory.app (interp V ρ fa) (interp V ρ aa)) (Nat.le_refl d)
      (ConLeche.Expr.fvarsBelow_instantiate1 0 hwfe.2.fvarsBelow)
      (by rw [Nat.sub_self, shiftE_zero_zero]; exact hoka)
      (by rw [Nat.sub_self, shiftE_zero_zero, instE_zero]; exact hall _ ha2)
    rwa [ConLeche.Expr.substFvarAt_instantiate1_self body 0 hwfe.2.fvarsBelow] at hsub

/-- **An application** (`Infer.app`): the full grade's certificate, or
the io grade's none. -/
theorem Infer.app_sound {g : Grade} {d : Nat}
    {f a tf ty body ta : Expr}
    (htf : InferSem m φ g d f tf) (hw : RedSem m φ d tf (.forallE ty body))
    (hwr : g = .io → Red env d tf (.forallE ty body))
    (hta : g = .full → InferSemFull m φ d a ta)
    (hd : g = .full → DefEqSem m φ d ta ty) :
    InferSem m φ g d (.app f a) (body.instantiate1 a) := by
  cases g with
  | full => exact Infer.app_soundCert htf hw (hta rfl) (hd rfl)
  | io => exact Infer.app_soundIO htf hw (hwr rfl)

/-- A projection at the full grade: the tower law's typing clause. -/
theorem Infer.proj_soundFull (hin : RulesInputs V m φ) {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSem m φ .full d pe tpe) (hte : RedSem m φ d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hg : ProjGuardSem m φ entry us) :
    InferSem m φ .full d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  refine InferSem.of_uniform ?_
  intro Δa ea hfr hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkS m φ d Δa pe := hC.proj_arg
  obtain ⟨vp, -, hvp, -, rfl⟩ := denote_proj_inv hea
  -- the scrutinee's inferred type, and its reduct (readings)
  obtain ⟨htpef, htpesub, tpea, htpea, hrowP⟩ :=
    htpe.apply ⟨hws, hb, hLpe⟩ hCpe hvp
  obtain ⟨htef, htesub, tea, htea, hredT⟩ :=
    hte htpef (hCpe.of_subset htpesub) htpea
  obtain ⟨hwte', hbte, hLte⟩ := htef
  -- the tower law's typing clause
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, cvC, hfC, hlpsC, hlaw, -⟩ :=
    hin.tower_ok sn i entry hent
  have hguard : TowerGuardAt m φ entry us cvC := hg _ _ _ hfC (by rw [hlpsC]; exact hus)
    (fun cvT' caps' hT' => by
      obtain ⟨hsn₀, -⟩ := hin.tower_ok sn i entry hent
      rw [hsn₀, hfT] at hT'
      obtain rfl : cvT = cvT' := by
        injection hT' with h'; injection h' with a b
      rw [hlpsT]; exact hus)
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hus
  -- the reduced type's spine, at the former's leaf
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Expr.mkAppN_getApp te).symm, hhead] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denote_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hus
  rw [denote_const hfT hlenT] at hvT
  have hvT' : vT = m.acval sn (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  -- the residual: the entry type's peel, read
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denote_typeAt_peel hent hTa hlen hframes (hspt.snoc hvp)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlen
  -- the returned type's leaves: the spine's or the subject's
  have hleaves : ∀ l ∈ (entry.typeAt us te.getAppArgs pe).fvarLeaves,
      (∃ x ∈ te.getAppArgs, l ∈ x.fvarLeaves) ∨ l ∈ pe.fvarLeaves := by
    intro l hl
    rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe] at hl
    rcases fvarLeaves_instSpine _ hl with hty | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (ConLeche.projEntry_body_hasFvar m.wf hent us)] at hty
      exact nomatch hty
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, hla⟩
      · rcases List.mem_singleton.mp ha with rfl
        exact Or.inr hla
  refine ⟨⟨ConLeche.projEntry_typeAt_WScoped m.wf hent us hlen
      (fun a ha => hwte'.getAppArgs a ha) hws,
    ConLeche.projEntry_typeAt_looseBVars m.wf hent us hlen
      (fun a ha => ConLeche.looseBVarsBounded_getAppArgs hbte a ha) hb,
    fun l hl => ?_⟩, fun l hl => ?_, restA, hrest, ?_⟩
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · exact hLte l (ConLeche.fvarLeaves_getAppArgs hx l hlx)
    · exact hLpe l hlx
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · rw [Expr.fvarLeaves]
      exact htpesub l (htesub l (ConLeche.fvarLeaves_getAppArgs hx l hlx))
    · rw [Expr.fvarLeaves]
      exact hlx
  intro σ hσ hL hgr
  have hLpe' : LeavesGr m φ d pe σ := hL.proj_arg
  -- the io grade's premise, hoisted through the projection spelling
  obtain ⟨hokPe, hokTpe, hmemPe⟩ :=
    hrowP σ hσ hLpe' (fun hg => ProjAV.hoistV (hgr hg))
  -- "not pt" source (1): the scrutinee's inferred type `tpea` is a type
  obtain ⟨hokTe, heqTe⟩ :=
    hredT σ hσ (hLpe'.of_subset htpesub) hokTpe.1 hokTpe.ne_pt
  -- the tower law's typing clause
  exact hA σ vs vp restA hlenVs hokTe (heqTe ▸ hokTpe.ne_pt) hokPe
    (heqTe ▸ hmemPe) hpeel (Or.inl hguard)

/-- **A projection at the io grade** (the io claim's projection
consumer): a projection of the point is the point (`projS_pt`); a
scrutinee that is a member of its type gets the tower law's typing
clause; and the scrutinee's claim is not hereditary, its type reducing
to the structure's application, which no ∀ does (`Red.rigid`). -/
theorem Infer.proj_soundIO (hin : RulesInputs V m φ) {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSemIO m φ d pe tpe) (hte : RedSem m φ d tpe te)
    (hter : Red env d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hg : ProjGuardSem m φ entry us) :
    InferSemIO m φ d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  intro hfr Δa ea hC hea
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded] at hb
  have hLpe : Expr.LeavesBounded pe := fun l hl =>
    hLb l (by simpa [Expr.fvarLeaves] using hl)
  have hCpe : CtxOkS m φ d Δa pe := hC.proj_arg
  obtain ⟨vp, -, hvp, -, rfl⟩ := denote_proj_inv hea
  -- the scrutinee's inferred type, and its reduct (readings)
  obtain ⟨htpef, htpesub, tpea, htpea, hrowP⟩ :=
    htpe ⟨hws, hb, hLpe⟩ hCpe hvp
  obtain ⟨htef, htesub, tea, htea, hredT⟩ :=
    hte htpef (hCpe.of_subset htpesub) htpea
  obtain ⟨hwte', hbte, hLte⟩ := htef
  -- the tower law's typing clause
  obtain ⟨-, -, -, ⟨cvT, capsT, hfT, hlpsT, -⟩, cvC, hfC, hlpsC, hlaw, -⟩ :=
    hin.tower_ok sn i entry hent
  have hguard : TowerGuardAt m φ entry us cvC := hg _ _ _ hfC (by rw [hlpsC]; exact hus)
    (fun cvT' caps' hT' => by
      obtain ⟨hsn₀, -⟩ := hin.tower_ok sn i entry hent
      rw [hsn₀, hfT] at hT'
      obtain rfl : cvT = cvT' := by
        injection hT' with h'; injection h' with a b
      rw [hlpsT]; exact hus)
  obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlaw us hus
  -- the reduced type's spine, at the former's leaf
  rw [show te = Expr.mkAppN te.getAppFn te.getAppArgs from
    (Expr.mkAppN_getApp te).symm, hhead] at htea
  obtain ⟨vT, vs, hvT, hspt, hteq⟩ := denote_mkAppN_inv htea
  have hlenT : us.length
      = (ConstantInfo.indInfo cvT capsT).toConstantVal.levelParams.length := by
    show us.length = cvT.levelParams.length
    rw [hlpsT]; exact hus
  rw [denote_const hfT hlenT] at hvT
  have hvT' : vT = m.acval sn (Level.substFn φ entry.levelParams us) := by
    rw [← hlpsT]; exact (Option.some.inj hvT).symm
  subst hvT'
  subst hteq
  -- the residual: the entry type's peel, read
  have hframes : ∀ x ∈ te.getAppArgs ++ [pe],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact ⟨hwte'.getAppArgs x hx',
        ConLeche.looseBVarsBounded_getAppArgs hbte x hx'⟩
    · rcases List.mem_singleton.mp hx' with rfl
      exact ⟨hws, hb⟩
  obtain ⟨restA, hrest, hpeel⟩ :=
    denote_typeAt_peel hent hTa hlen hframes (hspt.snoc hvp)
  have hlenVs : vs.length = entry.numParams := by
    rw [← hspt.length]; exact hlen
  -- the returned type's leaves: the spine's or the subject's
  have hleaves : ∀ l ∈ (entry.typeAt us te.getAppArgs pe).fvarLeaves,
      (∃ x ∈ te.getAppArgs, l ∈ x.fvarLeaves) ∨ l ∈ pe.fvarLeaves := by
    intro l hl
    rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe] at hl
    rcases fvarLeaves_instSpine _ hl with hty | ⟨a, ha, hla⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        (ConLeche.projEntry_body_hasFvar m.wf hent us)] at hty
      exact nomatch hty
    · rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, hla⟩
      · rcases List.mem_singleton.mp ha with rfl
        exact Or.inr hla
  refine ⟨⟨ConLeche.projEntry_typeAt_WScoped m.wf hent us hlen
      (fun a ha => hwte'.getAppArgs a ha) hws,
    ConLeche.projEntry_typeAt_looseBVars m.wf hent us hlen
      (fun a ha => ConLeche.looseBVarsBounded_getAppArgs hbte a ha) hb,
    fun l hl => ?_⟩, fun l hl => ?_, restA, hrest, ?_⟩
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · exact hLte l (ConLeche.fvarLeaves_getAppArgs hx l hlx)
    · exact hLpe l hlx
  · rcases hleaves l hl with ⟨x, hx, hlx⟩ | hlx
    · rw [Expr.fvarLeaves]
      exact htpesub l (htesub l (ConLeche.fvarLeaves_getAppArgs hx l hlx))
    · rw [Expr.fvarLeaves]
      exact hlx
  intro σ hσ hL hgr
  have hLpe' : LeavesGr m φ d pe σ := hL.proj_arg
  have hokPe : WellDenoted V σ vp := ProjAV.hoistV hgr
  rcases (hrowP σ hσ hLpe' hokPe).1 with h | h | h
  · -- the scrutinee is the point, and so is its projection
    rw [projNV_interp, h, ConLeche.SetTheory.Tower.projS_pt]
    exact IORelN.pt
  · obtain ⟨hokTpe, hmemPe⟩ := h.of_reading htpea
    -- "not pt" source (1): the scrutinee's inferred type `tpea` is a type
    obtain ⟨hokTe, heqTe⟩ :=
      hredT σ hσ (hLpe'.of_subset htpesub) hokTpe.1 hokTpe.ne_pt
    have hrow := hA σ vs vp restA hlenVs hokTe (heqTe ▸ hokTpe.ne_pt) hokPe
      (heqTe ▸ hmemPe) hpeel (Or.inl hguard)
    exact IORelN.of_mem hrest hrow.2.1 hrow.2.2
  · obtain ⟨_, _, rfl⟩ := h.forallE
    exact absurd (Red.rigid hter trivial ▸ hhead) (IsRigid.not_const (e := .forallE _ _) trivial)

/-- A projection, at either grade. -/
theorem Infer.proj_sound (hin : RulesInputs V m φ) {g : Grade} {d : Nat}
    {sn : Name} {i : Nat} {pe tpe te : Expr} {us : List Level}
    {entry : ProjEntry}
    (htpe : InferSem m φ g d pe tpe) (hte : RedSem m φ d tpe te)
    (hter : g = .io → Red env d tpe te)
    (hhead : te.getAppFn = .const sn us)
    (hent : env.findProj? sn i = some entry)
    (hlen : te.getAppArgs.length = entry.numParams)
    (hus : us.length = entry.levelParams.length)
    (hg : ProjGuardSem m φ entry us) :
    InferSem m φ g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe) := by
  cases g with
  | full => exact Infer.proj_soundFull hin htpe hte hhead hent hlen hus hg
  | io => exact Infer.proj_soundIO hin htpe hte (hter rfl) hhead hent hlen hus hg

end ConLeche.Model.Rules
