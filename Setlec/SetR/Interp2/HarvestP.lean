import Setlec.SetR.Interp2.CapstoneP
import Setlec.SetR.Install.ValueKinds

/-!
# The harvest, `defn` kind (task #161, P4 — the fold's species)

`harvestDefnP`: from a checked `def`'s harvest relation (`DeclDefnR`,
the H1-exposed runs included) and the P machinery at the prefix
environment, the P invariant extends — `declStepPM_of_cons`'s premises
assembled end to end:

* the v1 base and its agreement come **constructively** from
  `declDefnS` (`∃ m'`, not a `Nonempty`);
* the new leaf `A ψ` is the value's own `denoteP` reading (the
  `accepted_reads` totality leaf at the H1-exposed infer run); its
  laws are `denoteP_closed` / `denoteP_params_ext` / the claims'
  `AnnotOkP` conclusions at `Sat2_nil`;
* the leaf erases to the v1 leaf (`hAerase`) through `denoteP_erase`,
  `denote_install` (at `LitAgree.of_fresh` — freshness alone), and the
  new base's own `defn_eq` field;
* the membership (`hmemNew`) is the claims' membership at the value
  run carried across the H1-exposed defeq run by the defeq claim;
* `nat_heads` at the extension derives from the routed guard
  agreement + freshness — no bespoke premise.

Routed premises, both named tiers: `hsem : SemTierInputsP` (the
semantic bill) and `hlga : LitGuardsAgree` (the literal tier's
stability at this extension; free except at a support-completing
install, where the literal tier does bespoke work anyway).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint inferTypeCore isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-- **The `defn` harvest** (see the module docstring). -/
theorem harvestDefnP (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hdm : DivModPinS V)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    {env₂ : Env}
    (hR : DeclDefnR μ F env mp.base2.base.cval cv value hint env₂)
    (hlga : LitGuardsAgree env env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨m', hag⟩ := declDefnS hdm mp.base2.base hR
  obtain ⟨type', value', hcv, hvfr, rfl, hnatc, hdmc⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT, hfrontT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩,
    hfrontV⟩ := hvfr
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  obtain ⟨hvf', hbv'⟩ := annotate_syntax hannv hvhf hvlb
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the scoping packages of the primed forms
  have hwv : Expr.WScoped 0 value' := Expr.WScoped.of_not_hasFvar hvf'
  have hLv : Expr.LeavesBounded value' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlv : value'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf'
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlt : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hCv : CtxOkP mp.base2 (fun _ => 0) 0 ([] : List AVExpr) value' :=
    CtxOkP.nil hnlv
  -- the leaf: the value's reading, per assignment
  have hAex : ∀ ψ : Name → Nat,
      ∃ va, denoteP mp.base2.acval env ψ 0 value' = some va := by
    intro ψ
    exact hsem.accepted_reads mp.base2 ψ hvrun hwv hbv' hLv
  let A : (Name → Nat) → AVExpr :=
    fun ψ => (denoteP mp.base2.acval env ψ 0 value').getD default
  have hA : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 0 value' = some (A ψ) := by
    intro ψ
    obtain ⟨va, hva⟩ := hAex ψ
    show _ = some ((denoteP mp.base2.acval env ψ 0 value').getD default)
    simp [hva]
  -- the type's reading, per assignment
  obtain ⟨stype, u, hst, hens⟩ := hrunT
  have hTex : ∀ ψ : Name → Nat,
      ∃ ta, denoteP mp.base2.acval env ψ 0 type' = some ta := by
    intro ψ
    exact hsem.accepted_reads mp.base2 ψ hst hwt hbt' hLt
  let Ta : (Name → Nat) → AVExpr :=
    fun ψ => (denoteP mp.base2.acval env ψ 0 type').getD default
  have hTa : ∀ ψ : Name → Nat,
      denoteP mp.base2.acval env ψ 0 type' = some (Ta ψ) := by
    intro ψ
    obtain ⟨ta, hta⟩ := hTex ψ
    show _ = some ((denoteP mp.base2.acval env ψ 0 type').getD default)
    simp [hta]
  -- the claims and the reads, per assignment
  have hclaims := fun ψ =>
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem hsem mp ψ) F
  have hreads : ∀ ψ, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem hsem mp ψ).reads
  -- the value's rows: gradings and the membership at its own type
  have hrowsV : ∀ ψ : Name → Nat, ∃ vta,
      denoteP mp.base2.acval env ψ 0 vtype = some vta ∧
      ((∀ ρ : Nat → V, Sat2 V [] ρ → AnnotOkP V ρ (A ψ)) ∧
        (∀ ρ : Nat → V, Sat2 V [] ρ → AnnotOkP V ρ vta) ∧
        ∀ ρ : Nat → V, Sat2 V [] ρ →
          interp2 V ρ (A ψ) ∈ˢ interp2 V ρ vta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta⟩ :=
      hreads ψ hvrun hwv hbv' hLv (LeafReadsP.of_ctxOkP (CtxOkP.nil hnlv))
        (hA ψ)
    exact ⟨vta, hvta, ihi hvrun hwv hbv' hLv (CtxOkP.nil hnlv)
      (hA ψ) hvta⟩
  -- the type's rows: its own grading as a subject
  have hrowsT : ∀ ψ : Name → Nat, ∃ sta,
      denoteP mp.base2.acval env ψ 0 stype = some sta ∧
      ((∀ ρ : Nat → V, Sat2 V [] ρ → AnnotOkP V ρ (Ta ψ)) ∧
        (∀ ρ : Nat → V, Sat2 V [] ρ → AnnotOkP V ρ sta) ∧
        ∀ ρ : Nat → V, Sat2 V [] ρ →
          interp2 V ρ (Ta ψ) ∈ˢ interp2 V ρ sta) := by
    intro ψ
    obtain ⟨-, -, -, ihi⟩ := hclaims ψ
    obtain ⟨sta, hsta⟩ :=
      hreads ψ hst hwt hbt' hLt (LeafReadsP.of_ctxOkP (CtxOkP.nil hnlt))
        (hTa ψ)
    exact ⟨sta, hsta, ihi hst hwt hbt' hLt (CtxOkP.nil hnlt)
      (hTa ψ) hsta⟩
  -- the leaf laws
  have hAclosed : ∀ (ψ : Name → Nat) (k : Nat),
      (A ψ).liftN 1 k = A ψ := fun ψ k =>
    denoteP_closed mp.base2.acval_erase mp.base2.base.cval_closed
      hvf' hbv' (hA ψ) 1 k
  have hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hψ
    have := denoteP_params_ext mp.base2 hψ 0 value' hvp
    rw [hA ψ₁, hA ψ₂] at this
    exact Option.some.inj this
  have hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOk2 V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat2_nil V ρ)).1
  have hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ) := by
    intro ψ ρ
    obtain ⟨vta, hvta, hrE, -, -⟩ := hrowsV ψ
    exact (hrE ρ (Sat2_nil V ρ)).2
  -- the membership at the declared type, across the defeq run
  have hmemA : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (Ta ψ) := by
    intro ψ ρ
    obtain ⟨-, -, ihd, ihi⟩ := hclaims ψ
    obtain ⟨vta, hvta, hrE, hrT, hrM⟩ := hrowsV ψ
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    -- vtype's scoping package
    have hwvt : Expr.WScoped 0 vtype :=
      inferTypeCore_WScoped mp.base2.base.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.base.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.base.wf F hvrun hwv
      cases hh : vtype.fvarLeaves with
      | nil => rfl
      | cons l ls =>
        have := hsub l (by rw [hh]; exact List.mem_cons_self ..)
        rw [hnlv] at this
        exact absurd this (List.not_mem_nil)
    have hLvt : Expr.LeavesBounded vtype := fun l hl => by
      rw [hnlvt] at hl
      exact absurd hl (List.not_mem_nil)
    have heq := ihd hvde hwvt hbvt hLvt hwt hbt' hLt
      (CtxOkP.nil hnlvt) (CtxOkP.nil hnlt) hvta (hTa ψ)
      hrT htE ρ (Sat2_nil V ρ)
    rw [← heq]
    exact hrM ρ (Sat2_nil V ρ)
  -- the transfer to the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr
  have hcbV : ConstsBound env value' := constsBound_of_constsResolve _ hvr
  have hcomp : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
            env.consts⟩ ψ 0 e
        = denoteP mp.base2.acval env ψ 0 e :=
    fun ψ e hcb =>
      denoteP_cons_fresh
        (acval := mp.base2.acval)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh hlga ψ 0 e hcb
  -- the v1-side erasure link
  have hAerase : ∀ ψ,
      (A ψ).erase = m'.cval cv.name ψ := by
    intro ψ
    have hden : denote mp.base2.base.cval env ψ 0 value'
        = some (A ψ).erase :=
      denoteP_erase mp.base2.acval_erase 0 value' (hA ψ)
    have hden2 : denote m'.cval
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 value' = some (A ψ).erase := by
      refine denote_install hfresh hag
        (LitAgree.of_fresh (c₀ := .defnInfo
          ⟨cv.name, cv.levelParams, type'⟩ value' hint) hfresh hag)
        (natLitSupported_cons hfresh) (strLitSupported_cons hfresh)
        ?_ ?_ hden
      · intro hg
        refine levelParamsAt_cons_of_ne ?_
        intro hh
        have hh' : listNilName = cv.name := hh.symm
        simp only [Setlec.strLitSupported, Bool.and_eq_true] at hg
        obtain ⟨⟨⟨⟨-, h4⟩, -⟩, -⟩, -⟩ := hg
        rw [hh', hfresh] at h4
        simp [listNilTyOk] at h4
      · intro hg
        refine levelParamsAt_cons_of_ne ?_
        intro hh
        have hh' : listConsName = cv.name := hh.symm
        simp only [Setlec.strLitSupported, Bool.and_eq_true] at hg
        obtain ⟨⟨⟨-, h5⟩, -⟩, -⟩ := hg
        rw [hh', hfresh] at h5
        simp [listConsTyOk] at h5
    have hde := m'.defn_eq ⟨cv.name, cv.levelParams, type'⟩ value' hint
      (List.mem_cons_self ..) ψ
    rw [denoteClosed, hden2] at hde
    exact (Option.some.inj hde)
  -- assemble
  refine declStepPM_of_cons mp
    (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
    (A := A) hfresh m' (fun n hn => hag n hn) hlga hAerase hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteP (acvalWith mp.base2.acval cv.name A)
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, by rw [hcomp ψ type' hcbT]; exact hTa ψ⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 type' = some ta := hta
    rw [hcomp ψ type' hcbT, hTa ψ] at hta
    obtain rfl : ta = Ta ψ := (Option.some.inj hta).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat2_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 type' = some ta := hta
    rw [hcomp ψ type' hcbT, hTa ψ] at hta
    obtain rfl : ta = Ta ψ := (Option.some.inj hta).symm
    exact hmemA ψ ρ
  · -- `hvalReads`
    intro ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · injection hdt with h1 h2 h3
      show denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
            env.consts⟩ ψ 0 value2
        = some (A ψ)
      rw [h2, hcomp ψ value' hcbV]
      exact hA ψ
    · exact nomatch hdt
  · -- `nat_heads` at the extension, from the guard agreement
    intro φ hg ρ
    show interp2 V ρ (acvalWith mp.base2.acval cv.name A natZeroName
          (Level.substFn φ [] []))
        ∈ˢ interp2 V ρ (acvalWith mp.base2.acval cv.name A natName
          (Level.substFn φ [] [])) ∧
      interp2 V ρ (acvalWith mp.base2.acval cv.name A natSuccName
          (Level.substFn φ [] []))
        ∈ˢ piR 1 (interp2 V ρ (acvalWith mp.base2.acval cv.name A
            natName (Level.substFn φ [] [])))
          (fun _ => interp2 V ρ (acvalWith mp.base2.acval cv.name A
            natName (Level.substFn φ [] [])))
    have hgold : Setlec.natLitSupported env = true := by
      rw [hlga.1]; exact hg
    have hstored : ∀ n0, (env.find? n0).isSome = true →
        n0 ≠ cv.name := by
      intro n0 hs hh
      rw [hh, hfresh] at hs
      exact nomatch hs
    have hz : (env.find? natZeroName).isSome = true := by
      have hgg := hgold
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨⟨-, hz0⟩, -⟩ := hgg
      revert hz0; cases env.find? natZeroName <;> simp [natZeroOk]
    have hsc : (env.find? natSuccName).isSome = true := by
      have hgg := hgold
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨-, hs0⟩ := hgg
      revert hs0; cases env.find? natSuccName <;> simp [natSuccOk]
    have hn : (env.find? natName).isSome = true := by
      have hgg := hgold
      simp only [Setlec.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨⟨hn0, -⟩, -⟩ := hgg
      revert hn0; cases env.find? natName <;> simp [natIndOk]
    have e1 : acvalWith mp.base2.acval cv.name A natZeroName
        = mp.base2.acval natZeroName :=
      acvalWith_ne (hstored _ hz)
    have e2 : acvalWith mp.base2.acval cv.name A natSuccName
        = mp.base2.acval natSuccName :=
      acvalWith_ne (hstored _ hsc)
    have e3 : acvalWith mp.base2.acval cv.name A natName
        = mp.base2.acval natName :=
      acvalWith_ne (hstored _ hn)
    have := mp.nat_heads φ hgold ρ
    simpa only [e1, e2, e3] using this

end Setlec.SetR.Interp2
