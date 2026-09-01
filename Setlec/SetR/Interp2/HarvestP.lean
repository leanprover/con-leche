import Setlec.SetR.Interp2.CapstoneP
import Setlec.SetR.Install.ValueKinds

/-!
# The harvest, value kinds (task #161, P4 — the fold's species)

The `defn` species below, and then its `thm` mirror (batch H2, T1).
The `opaque` mirror is **not** here: see the SKIP record at the end of
this module for the one missing link and the upstream strengthening it
names.

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
semantic bill).  (`LitGuardsAgree` is GONE: the guard equality is
refutable at support-completing installs, and the monotone crossing
(`denoteP_cons_fresh_mono`) plus `natLitSupported_cons_back` replace
every use — the harvests carry no literal-tier premise at all.  The
next line's original text described the routed `hlga`; kept for the
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

/-- **The `Nat` guard reflects across a value-kind cons**: the three
components need `indInfo`/`ctorInfo` shapes, which no `defn`/`thm`/
`axiom` cons can supply — so a guard true at the extension was true
at the prefix.  (This kills the routed guard-equality premise: the
nat half is free, and the str half is never consulted backward.) -/
theorem natLitSupported_cons_back {env : Env} {c₀ : ConstantInfo}
    (hknd : (∀ cv mI, c₀ ≠ .indInfo cv mI) ∧
      ∀ cv a b, c₀ ≠ .ctorInfo cv a b)
    (hg : Setlec.natLitSupported ⟨c₀ :: env.consts⟩ = true) :
    Setlec.natLitSupported env = true := by
  have hfind : ∀ p : Name,
      (⟨c₀ :: env.consts⟩ : Env).find? p
        = if c₀.name = p then some c₀ else env.find? p := by
    intro p
    show List.find? _ (c₀ :: env.consts) = _
    by_cases hp : c₀.name = p
    · rw [List.find?_cons_of_pos (by simpa using hp), if_pos hp]
    · rw [List.find?_cons_of_neg (by simpa using hp), if_neg hp]
      rfl
  simp only [Setlec.natLitSupported, Bool.and_eq_true] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  rw [hfind] at h1 h2 h3
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · revert h1
    split
    · cases c₀ with
      | indInfo cv mI => exact absurd rfl (hknd.1 cv mI)
      | _ => intro h; simp [natIndOk] at h
    · exact id
  · revert h2
    split
    · cases c₀ with
      | ctorInfo cv a b => exact absurd rfl (hknd.2 cv a b)
      | _ => intro h; simp [natZeroOk] at h
    · exact id
  · revert h3
    split
    · cases c₀ with
      | ctorInfo cv a b => exact absurd rfl (hknd.2 cv a b)
      | _ => intro h; simp [natSuccOk] at h
    · exact id

/-- **`nat_heads` at a fresh cons, from the routed guard agreement.**
The three literal heads are *stored* wherever the guard holds, so
freshness makes each of them distinct from the new name and the fresh
leaf is invisible to all three — `mp.nat_heads` transports unchanged.
No bespoke premise: this is the lemma `InstallP.lean`'s docstring
calls `declStepPM_natHeads_fresh`, landed here because the harvest is
its only consumer and `InstallP.lean` is not this batch's to edit.

The species below predates it and still carries the block inline (its
statement is sealed; the proof adopts this when the seal next opens);
`harvestThmP` and `harvestAxiomP` call it. -/
theorem natHeadsP_cons_fresh (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hknd : (∀ cv mI, c₀ ≠ .indInfo cv mI) ∧
      ∀ cv a b, c₀ ≠ .ctorInfo cv a b)
    (m2 : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hacval : m2.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : NatHeadsP m2 φ := by
  intro hg ρ
  rw [hacval]
  have hgold : Setlec.natLitSupported env = true :=
    natLitSupported_cons_back hknd hg
  have hstored : ∀ n0, (env.find? n0).isSome = true → n0 ≠ c₀.name := by
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
  have e1 : acvalWith mp.base2.acval c₀.name A natZeroName
      = mp.base2.acval natZeroName :=
    acvalWith_ne (hstored _ hz)
  have e2 : acvalWith mp.base2.acval c₀.name A natSuccName
      = mp.base2.acval natSuccName :=
    acvalWith_ne (hstored _ hsc)
  have e3 : acvalWith mp.base2.acval c₀.name A natName
      = mp.base2.acval natName :=
    acvalWith_ne (hstored _ hn)
  have := mp.nat_heads φ hgold ρ
  simpa only [e1, e2, e3] using this

/-- **The `defn` harvest** (see the module docstring). -/
theorem harvestDefnP (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hdm : DivModPinS V)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    {env₂ : Env}
    (hR : DeclDefnR μ F env mp.base2.base.cval cv value hint env₂) :
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
      ∀ {ea : AVExpr}, denoteP mp.base2.acval env ψ 0 e = some ea →
      denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteP_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh ψ 0 e hcb h
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
    (A := A) hfresh m' (fun n hn => hag n hn) hAerase hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteP (acvalWith mp.base2.acval cv.name A)
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat2_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ ρ
  · -- `hvalReads`
    intro ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · injection hdt with h1 h2 h3
      show denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
            env.consts⟩ ψ 0 value2
        = some (A ψ)
      rw [h2]
      exact hcomp ψ value' hcbV (hA ψ)
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
    have hgold : Setlec.natLitSupported env = true :=
      natLitSupported_cons_back
        ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩ hg
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

/-! ## The `thm` mirror (batch H2, T1)

`harvestThmP` is `harvestDefnP` at `DeclThmR`/`declThmS`, and the
mirror is exact: the same two front doors (`ConstantValR`,
`ValueFrontR`) with the same H1-exposed runs, the same leaf (the
value's `denoteP` reading), the same claims, the same crossing.  The
three deltas are all shape:

* the stored kind is `.thmInfo cvA value'` — no `hint`, and the v1
  step is `declThmS`, which takes **no** `DivModPinS` (a theorem has
  neither the structural-`Nat` nor the div/mod pin clause, so the
  harvest sheds `hdm` too);
* the erasure link reads the new base's `thm_ok` field where the
  species reads `defn_eq` — the same equation, the other kind;
* `hvalReads`'s two arms swap: the `defnInfo` arm is `nomatch` and the
  `thmInfo` arm carries the reading.

`DeclThmR`'s two extra conjuncts (H1's prop-check run triple and the
semantic `.sort 0` front) are **not spent**: the type's P reading and
its grading come from `ConstantValR`'s own run, exactly as in the
species, and the P invariant stores no is-a-proposition field.  They
are destructured away with `-`. -/
theorem harvestThmP (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {env₂ : Env}
    (hR : DeclThmR μ F env mp.base2.base.cval cv value env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨m', hag⟩ := declThmS mp.base2.base hR
  obtain ⟨type', value', hcv, -, -, hvfr, rfl⟩ := hR
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
      ∀ {ea : AVExpr}, denoteP mp.base2.acval env ψ 0 e = some ea →
      denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteP_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
        (A := A) hfresh ψ 0 e hcb h
  -- the v1-side erasure link, at `thm_ok`
  have hAerase : ∀ ψ,
      (A ψ).erase = m'.cval cv.name ψ := by
    intro ψ
    have hden : denote mp.base2.base.cval env ψ 0 value'
        = some (A ψ).erase :=
      denoteP_erase mp.base2.acval_erase 0 value' (hA ψ)
    have hden2 : denote m'.cval
        ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
          env.consts⟩ ψ 0 value' = some (A ψ).erase := by
      refine denote_install hfresh hag
        (LitAgree.of_fresh (c₀ := .thmInfo
          ⟨cv.name, cv.levelParams, type'⟩ value') hfresh hag)
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
    have hde := m'.thm_ok ⟨cv.name, cv.levelParams, type'⟩ value'
      (List.mem_cons_self ..) ψ
    rw [denoteClosed, hden2] at hde
    exact (Option.some.inj hde)
  -- assemble
  refine declStepPM_of_cons mp
    (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
    (A := A) hfresh m' (fun n hn => hag n hn) hAerase hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteP (acvalWith mp.base2.acval cv.name A)
      ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat2_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ ρ
  · -- `hvalReads`: the `defn` arm is the impossible one here
    intro ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact nomatch hdt
    · injection hdt with h1 h2
      show denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
            env.consts⟩ ψ 0 value2
        = some (A ψ)
      rw [h2]
      exact hcomp ψ value' hcbV (hA ψ)
  · -- `nat_heads` at the extension, from the guard agreement
    exact fun φ => natHeadsP_cons_fresh mp
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value') (A := A)
      hfresh ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
      _ rfl φ

/-! ## The `opaque` kind: the H2 SKIP, since unlocked

(The record below is batch H2's original finding, kept for the trail;
the named strengthening has been LANDED — `extendValueS` now exposes
the leaf equation, `declOpaqueS` carries it with the annotate link —
and `harvestOpaqueP` at the end of this file is the species on it.)

There is **no `harvestOpaqueP` here**, and the wall is one equation.

Everything the species does transfers: `DeclOpaqueR` carries the same
two front doors, so the leaf `A` (the value's `denoteP` reading), its
laws, the type's reading and grading, the membership across the defeq
run, the crossing and `nat_heads` are all available verbatim, and
`hvalReads`'s two arms are *both* `nomatch` (an `opaque` is stored as
`.axiomInfo ⟨cv.name, cv.levelParams, type'⟩` — `Decl.lean`'s
`DeclOpaqueR`, third conjunct — so it is neither a `defnInfo` nor a
`thmInfo`).  What is missing is `declStepPM_of_cons`'s `hAerase`:

    ∀ ψ, (A ψ).erase = m'.cval cv.name ψ

At a `def` this is the new base's `defn_eq` field and at a `theorem`
its `thm_ok` field (`harvestDefnP` / `harvestThmP` above).  At an
`opaque` **neither field speaks**: v1 stores an axiom and keeps no
equation between the discarded body and the leaf.  The equation is
*true* — `extendValueS` values the constant by `cvalAt m.cval env
cv.name value'`, i.e. by the value's own denotation — but
`declOpaqueS`'s conclusion is `∃ m' : EnvS V env₂, ∀ n, n ≠ cv.name →
m.cval n = m'.cval n`, and the agreement says nothing *at* `cv.name`.
The witness that knows the leaf is thrown away at the `∃`-boundary.

This is the same wall the U tier already named: `declStep2_of_value`'s
`hleaf` premise, whose docstring (`Step2Cons.lean`, `leafEq_defn` /
`leafEq_thm`) records "a residue only at the `opaque` kind".  The P
tier hits it in the same place, for the same reason.

**The bill (upstream, `Setlec/SetR/Install/ValueKinds.lean` — not this
file's to edit).**  `declOpaqueS` should expose its leaf, the way
`extendValueS` already exposes its agreement:

    theorem declOpaqueS (hrp : ReducePinS V) … :
      ∃ m' : EnvS V env₂,
        (∀ n, n ≠ cv.name → m.cval n = m'.cval n) ∧
        ∀ value', annotateCore μ env F 0 value = .ok value' →
          ∀ ψ, denoteClosed m.cval env ψ value' = some (m'.cval cv.name ψ)

(the second conjunct quantified over the *annotate output*, which is
determined, since `value'` is bound inside `DeclOpaqueR`'s `∃`; the
proof is `cvalAt_self` at the `hkey` reading `extendValueS` already
has in hand, one `have` inside the existing call).  With that conjunct
`harvestOpaqueP` is the species with `defn_eq` replaced by it and both
`hvalReads` arms `nomatch` — no new semantic content, no new premise.
Landing it here instead as a premise would be a conditional form with
**no supplier at all** (unlike `harvestAxiomP` below, whose premises
the pin tier really does discharge), so it is not landed. -/

/-! ## The `axiom` kind (batch H2, T3)

`harvestAxiomP` is not a mirror of the species but of
`declStep2M_of_axiom` (`Step2Cons.lean`) at the P fields: **an axiom
has no value**, so the leaf is not a reading of anything the harvest
can see, and the constructive v1 step (`declAxiomExtS` /
`declAxiomLeafExtS`, `Install/Axiom.lean`) produces its leaf from the
pinned families' bespoke keys (`StdAxiomKeyS`, `trustCompilerKeyS`,
`ofReduceKeyS`).  So the leaf and its facts arrive as **premises** —
that is the pin tier's bill, and it is a real bill, not a conditional
form: `declAxiomLeafExtS` already yields `hbase`, `hag`, an `A`,
`hAerase` and `hAok` constructively; what P adds to that list is
`hAclosed`, `hAparams`, `hAvalid` and the interp2 membership `hmemA`.

What the harvest still does for free, and why the wrapper is worth
having: the *type* side is harvested exactly as in the species — the
type's P reading and its grading come from `ConstantValR`'s own
`inferType` run through `accepted_reads` and `checkSoundAtP` — the
crossing to the extension is `denoteP_cons_fresh`, `hvalReads`'s two
arms are both `nomatch` (an axiom is neither a `def` nor a `thm`), and
`nat_heads` comes from the routed guard agreement plus freshness.
`hmemA` is stated at the **prefix** reading, which is where the pin
tier works; the wrapper crosses it.

`DeclAxiomR`'s fourth branch — the tolerated skip — needs none of
this: it stores nothing (`env₂ = env`), so its P invariant is `mp`
itself. -/
theorem harvestAxiomP (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {type' : Expr} {A : (Name → Nat) → AVExpr}
    (hcv : ConstantValR μ F env mp.base2.base.cval cv type')
    (hbase : EnvS V ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩)
    (hag : ∀ n, n ≠ cv.name → mp.base2.base.cval n = hbase.cval n)
    (hAerase : ∀ ψ, (A ψ).erase = hbase.cval cv.name ψ)
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP mp.base2.acval env ψ 0 type' = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta) :
    Nonempty (EnvS2PM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT, hfrontT⟩ := hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  -- the type's scoping package
  have hwt : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type' := fun l hl => by
    rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'] at hl
    exact absurd hl (List.not_mem_nil)
  have hnlt : type'.fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
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
  -- the transfer to the extension
  have hcbT : ConstsBound env type' := constsBound_of_constsResolve _ htr
  have hcomp : ∀ (ψ : Name → Nat) (e : Expr), ConstsBound env e →
      ∀ {ea : AVExpr}, denoteP mp.base2.acval env ψ 0 e = some ea →
      denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteP_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
        (A := A) hfresh ψ 0 e hcb h
  -- assemble
  refine declStepPM_of_cons mp
    (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
    (A := A) hfresh hbase hag hAerase hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteP (acvalWith mp.base2.acval cv.name A)
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat2_nil V ρ)
  · -- `hmemNew`: the pin tier's membership, crossed
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ (Ta ψ) (hTa ψ) ρ
  · -- `hvalReads`: an axiom is neither a `def` nor a `thm`
    intro ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact nomatch hdt
    · exact nomatch hdt
  · -- `nat_heads` at the extension, from the guard agreement
    exact fun φ => natHeadsP_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
      _ rfl φ


/-! ## The `opaque` kind, unlocked (the exposed leaf equation)

The H2 SKIP record above named the one missing premise: the leaf
equation invisible at `declOpaqueS`'s `∃`-boundary.  `extendValueS`
now exposes it (an additive conjunct; `declOpaqueS` carries it with
the annotate link), and the harvest is the species with the erasure
link read **directly** off the exposed equation — no `denote_install`,
no `defn_eq`/`thm_ok` detour. -/

theorem harvestOpaqueP (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hrp : ReducePinS V)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {env₂ : Env}
    (hR : DeclOpaqueR μ F env mp.base2.base.cval cv value env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨m', hag, value'', hannv2, hleafEq⟩ :=
    declOpaqueS hrp mp.base2.base hR
  obtain ⟨type', value', hcv, hvfr, rfl, -⟩ := hR
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
      ∀ {ea : AVExpr}, denoteP mp.base2.acval env ψ 0 e = some ea →
      denoteP (acvalWith mp.base2.acval cv.name A)
          ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
            env.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteP_cons_fresh_mono
        (acval := mp.base2.acval)
        (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
        (A := A) hfresh ψ 0 e hcb h
  -- the v1-side erasure link: the exposed leaf equation, directly
  have hvv : value'' = value' :=
    Except.ok.inj (hannv2.symm.trans hannv)
  rw [hvv] at hleafEq
  have hAerase : ∀ ψ,
      (A ψ).erase = m'.cval cv.name ψ := by
    intro ψ
    have hden : denote mp.base2.base.cval env ψ 0 value'
        = some (A ψ).erase :=
      denoteP_erase mp.base2.acval_erase 0 value' (hA ψ)
    have hle := hleafEq ψ
    rw [denoteClosed, hden] at hle
    exact Option.some.inj hle
  -- assemble
  refine declStepPM_of_cons mp
    (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
    (A := A) hfresh m' (fun n hn => hag n hn) hAerase hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_
  · -- `htyReads`
    intro ψ
    show ∃ ta, denoteP (acvalWith mp.base2.acval cv.name A)
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
        env.consts⟩ ψ 0 type' = some ta
    exact ⟨Ta ψ, hcomp ψ type' hcbT (hTa ψ)⟩
  · -- `htyOk`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
    exact htE ρ (Sat2_nil V ρ)
  · -- `hmemNew`
    intro ψ ta hta ρ
    replace hta : denoteP (acvalWith mp.base2.acval cv.name A)
        ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
          env.consts⟩ ψ 0 type' = some ta := hta
    obtain rfl : ta = Ta ψ :=
      (Option.some.inj
        ((hcomp ψ type' hcbT (hTa ψ)).symm.trans hta)).symm
    exact hmemA ψ ρ
  · -- `hvalReads`: an opaque stores an axiom — both arms impossible
    intro ψ cv2 value2 hmem
    rcases hmem with ⟨hint2, hdt⟩ | hdt
    · exact nomatch hdt
    · exact nomatch hdt
  · -- `nat_heads` at the extension, from the guard agreement
    exact fun φ => natHeadsP_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh ⟨(fun _ _ h => ConstantInfo.noConfusion h),
          (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
      _ rfl φ

end Setlec.SetR.Interp2
