import ConLeche.SetP.CapstoneP
import ConLeche.SetP.NatEqsP
import ConLeche.SetP.DivModCertP
import ConLeche.SetP.CapsP
import ConLeche.SetP.RecRulesPCons
import ConLeche.SetP.ReduceOpsP
import ConLeche.Semantics.DeclRun

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
* `nat_heads` at the extension derives from guard reflection
  (`natLitSupported_cons_back`) + freshness — no bespoke premise.

No routed semantic premise any more: the subject-side totality leaf
is `acceptedReadsP_of` (`Step2/AcceptedP.lean`, task #161 ENDGAME A),
so the harvests take the environment invariant and the install-tier
pins alone.
`LitGuardsAgree` is GONE from every harvest: the guard equality is
refutable at a support-completing install, and the monotone crossing
(`denoteP_cons_fresh_mono`) plus guard reflection replace every use —
the harvests carry no literal-tier premise at all.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
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
    (hg : ConLeche.natLitSupported ⟨c₀ :: env.consts⟩ = true) :
    ConLeche.natLitSupported env = true := by
  have hfind : ∀ p : Name,
      (⟨c₀ :: env.consts⟩ : Env).find? p
        = if c₀.name = p then some c₀ else env.find? p := by
    intro p
    show List.find? _ (c₀ :: env.consts) = _
    by_cases hp : c₀.name = p
    · rw [List.find?_cons_of_pos (by simpa using hp), if_pos hp]
    · rw [List.find?_cons_of_neg (by simpa using hp), if_neg hp]
      rfl
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg ⊢
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
  have hgold : ConLeche.natLitSupported env = true :=
    natLitSupported_cons_back hknd hg
  have hstored : ∀ n0, (env.find? n0).isSome = true → n0 ≠ c₀.name := by
    intro n0 hs hh
    rw [hh, hfresh] at hs
    exact nomatch hs
  have hz : (env.find? natZeroName).isSome = true := by
    have hgg := hgold
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
    obtain ⟨⟨-, hz0⟩, -⟩ := hgg
    revert hz0; cases env.find? natZeroName <;> simp [natZeroOk]
  have hsc : (env.find? natSuccName).isSome = true := by
    have hgg := hgold
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
    obtain ⟨-, hs0⟩ := hgg
    revert hs0; cases env.find? natSuccName <;> simp [natSuccOk]
  have hn : (env.find? natName).isSome = true := by
    have hgg := hgold
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
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
theorem harvestDefnP (hμ : μ.verifiedChecks = true)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    {env₂ : Env}
    (hR : DeclDefnRun μ F env cv value hint env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨type', value', hcv, hvfr, rfl, hnatc, hdmc⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩⟩ := hvfr
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
    exact acceptedReadsP_of mp.base2 ψ hvrun hwv hbv' hLv
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
    exact acceptedReadsP_of mp.base2 ψ hst hwt hbt' hLt
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
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem mp ψ).reads
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
    denoteP_closed mp.base2.acval_erase mp.base2.cval_closed
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
      inferTypeCore_WScoped mp.base2.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
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
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStepPM_of_cons mp
    (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
    (A := A) hfresh
    (ConsHeadP.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => by
          obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
          exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq)⟩)
      (fun ψ => denote_closed mp.base2.cval_closed hvf' hbv'
        (denoteP_erase mp.base2.acval_erase 0 value' (hA ψ)))
      hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq)) hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
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
    have hgold : ConLeche.natLitSupported env = true :=
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
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨⟨-, hz0⟩, -⟩ := hgg
      revert hz0; cases env.find? natZeroName <;> simp [natZeroOk]
    have hsc : (env.find? natSuccName).isSome = true := by
      have hgg := hgold
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
      obtain ⟨-, hs0⟩ := hgg
      revert hs0; cases env.find? natSuccName <;> simp [natSuccOk]
    have hn : (env.find? natName).isSome = true := by
      have hgg := hgold
      simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hgg
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
  · -- `nat_ops` at the extension: the operation's own install goes
    -- through the run-certificate conversion; any other definition
    -- preserves the stored entries
    intro φ
    by_cases hno : ConLeche.natOpNames.contains cv.name = true
    · -- the install
      obtain ⟨hg2, hdeps₂, hruns⟩ := hnatc hno
      have hcmem : cv.name ∈ ConLeche.natOpNames :=
        List.contains_iff_mem.mp hno
      -- the self entry of the dependency check: level-mono + pinned
      have hself : cv.name ∈ ConLeche.natOpDeps cv.name := by
        have h7 := hcmem
        simp only [ConLeche.natOpNames, List.mem_cons,
          List.not_mem_nil, or_false] at h7
        rcases h7 with h | h | h | h | h | h | h <;> rw [h] <;> decide
      have hd := List.all_eq_true.mp hdeps₂ cv.name (by simpa using hself)
      unfold ConLeche.natOpStoredOk at hd
      rw [show (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
            value' hint :: env.consts⟩ : Env).find? cv.name
          = some (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value'
            hint) from by
        rw [ConLeche.Env.find?_cons]; exact if_pos rfl] at hd
      simp only [Bool.and_eq_true] at hd
      have hlpcv : cv.levelParams = [] := by
        simpa [List.isEmpty_iff] using hd.1
      have hpin : ConLeche.natOpTyPinned
          (⟨ConstantInfo.defnInfo ⟨cv.name, cv.levelParams, type'⟩
            value' hint :: env.consts⟩ : Env) cv.name type' = true :=
        hd.2
      have hsE : ConLeche.natLitSupported env = true :=
        natLitSupported_cons_back
          ⟨(fun _ _ h => ConstantInfo.noConfusion h),
            (fun _ _ _ h => ConstantInfo.noConfusion h)⟩
          (ConLeche.natOpGuard_deps hg2).1
      have hTok : ∀ (ψ : Name → Nat) (ρ : Nat → V),
          AnnotOkP V ρ (Ta ψ) := fun ψ ρ => by
        obtain ⟨sta, hsta, hT1, -, -⟩ := hrowsT ψ
        exact hT1 ρ (Sat2_nil V ρ)
      have hA2 : ∀ ψ, denoteP mp.base2.acval env ψ 2 value'
          = some (A ψ) := fun ψ =>
        denoteP_depth_of_closed mp.base2.acval_closed hvf'
          (hAclosed ψ) (hA ψ) 2
      obtain ⟨hSelfBin, hSelfUn⟩ := natSelfHeadP_install (φ := φ) mp
        hcmem hfresh hpin hsE hTa hTok hA2
        (fun ψ ρ => ⟨hAok ψ ρ, hAvalid ψ ρ⟩) hmemA
      exact natOpsP_install mp ((hclaims φ).2.2.1) (mp.nat_ops φ)
        hcmem hfresh hlpcv hsE hg2 hdeps₂ hruns hA hAclosed hvf' hbv'
        hSelfBin hSelfUn _ rfl
    · exact natOpsP_cons_fresh mp (mp.nat_ops φ)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
        (Or.inr (fun hm => hno (List.contains_iff_mem.mpr hm))) _ rfl
  · -- `div_mod` at the extension: a WF operation's own install goes
    -- through the certificate conversion; any other definition
    -- preserves the stored entries
    intro φ
    by_cases hno : ConLeche.natDivModNames.contains cv.name = true
    · obtain ⟨hgenv, -, -, pinA, -, hcerts⟩ := hdmc hno
      exact divModP_install mp (mp.div_mod φ) mp.eq_lawP
        (fun {d} {e} {t} hrun hw hb hL =>
          acceptedReadsP_of mp.base2 φ hrun hw hb hL)
        (hreads φ) ((hclaims φ).2.2.2) ((hclaims φ).2.2.1)
        (List.contains_iff_mem.mp hno) hfresh hgenv hcerts
        hA hAclosed hvf' hbv'
        hTa (fun ψ ρ => by
          obtain ⟨sta, hsta, hT1, -, -⟩ := hrowsT ψ
          exact hT1 ρ (Sat2_nil V ρ))
        (fun ψ ρ => ⟨hAok ψ ρ, hAvalid ψ ρ⟩) hmemA _ rfl
    · exact divModP_cons_fresh (mp.div_mod φ)
        (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (A := A) hfresh
        (Or.inr (fun hm => hno (List.contains_iff_mem.mpr hm))) _ rfl
  · -- `eq_lawP` at the extension: a definition is not an inductive
    exact eqLawP_cons_valueKind mp.eq_lawP
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOkP_cons_fresh mp mp.caps_ok
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRulesP_cons_fresh mp
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: a definition is not an
    -- `axiomInfo`, so no reduce operation can be this cons
    exact reduceOpsP_cons_fresh mp.reduce_ops
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh
      (Or.inl (fun _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOkP_cons_fresh mp
      (c₀ := .defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ

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
theorem harvestThmP (hμ : μ.verifiedChecks = true)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {env₂ : Env}
    (hR : DeclThmRun μ F env cv value env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨type', value', hcv, -, hvfr, rfl⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩⟩ := hvfr
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
    exact acceptedReadsP_of mp.base2 ψ hvrun hwv hbv' hLv
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
    exact acceptedReadsP_of mp.base2 ψ hst hwt hbt' hLt
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
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem mp ψ).reads
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
    denoteP_closed mp.base2.acval_erase mp.base2.cval_closed
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
      inferTypeCore_WScoped mp.base2.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
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
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStepPM_of_cons mp
    (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
    (A := A) hfresh
    (ConsHeadP.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => nomatch heq),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ _ heq => by
          obtain ⟨rfl, rfl⟩ := ConstantInfo.thmInfo.inj heq
          exact ⟨hvf', hvp, Expr.constsResolve_mono hvr, hbv'⟩),
        (fun _ heq => nomatch heq)⟩)
      (fun ψ => denote_closed mp.base2.cval_closed hvf' hbv'
        (denoteP_erase mp.base2.acval_erase 0 value' (hA ψ)))
      hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq)) hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
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
  · -- `nat_ops` at the extension: a theorem is not a definition
    exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ)
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value') (A := A)
      hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `div_mod`/`eq_lawP` at the extension: a theorem is neither a
    -- definition nor an inductive
    exact fun φ => divModP_cons_fresh (mp.div_mod φ)
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
      (A := A) hfresh
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · exact eqLawP_cons_valueKind mp.eq_lawP
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOkP_cons_fresh mp mp.caps_ok
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRulesP_cons_fresh mp
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: a theorem is not an `axiomInfo`
    exact reduceOpsP_cons_fresh mp.reduce_ops
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
      (A := A) hfresh
      (Or.inl (fun _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOkP_cons_fresh mp
      (c₀ := .thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ

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

**The bill (upstream, `ConLeche/SetR/Install/ValueKinds.lean` — not this
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
theorem harvestAxiomP (hμ : μ.verifiedChecks = true)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {type' : Expr} {A : (Name → Nat) → AVExpr}
    (hcv : ConstantValRun μ F env cv type')
    (hAvclosed : ∀ ψ : Name → Nat, VExpr.Closed ((A ψ).erase))
    (hAclosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ)
    (hAparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂)
    (hAok : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ))
    (hAvalid : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotValidV V ρ (A ψ))
    (hmemA : ∀ (ψ : Name → Nat) (ta : AVExpr),
      denoteP mp.base2.acval env ψ 0 type' = some ta →
      ∀ ρ : Nat → V, interp2 V ρ (A ψ) ∈ˢ interp2 V ρ ta)
    -- an axiom cons *is* an `axiomInfo`, so `reduce_ops`' preservation
    -- cannot go through the kind; it goes through the name.  Every
    -- `DeclAxiomR` branch pins `cv.name` (`matchesPin` compares it on
    -- the nose), and none of the pinned names is a reduce operation —
    -- the operations are installed as `opaque`s, never as axioms.
    (hnotreduce : cv.name ∉ ConLeche.reduceOpNames) :
    Nonempty (EnvS2PM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
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
    exact acceptedReadsP_of mp.base2 ψ hst hwt hbt' hLt
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
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem mp ψ).reads
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
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStepPM_of_cons mp
    (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
    (A := A) hfresh
    (ConsHeadP.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => nomatch heq),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq)⟩)
      hAvclosed hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq))
    hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
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
  · -- `nat_ops` at the extension: an axiom is not a definition
    exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `div_mod`/`eq_lawP` at the extension: an axiom is neither
    exact fun φ => divModP_cons_fresh (mp.div_mod φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · exact eqLawP_cons_valueKind mp.eq_lawP
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOkP_cons_fresh mp mp.caps_ok
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRulesP_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: the cons *is* an `axiomInfo`, so
    -- the preservation goes through the pinned name (the branch's
    -- hypothesis), not the kind
    exact reduceOpsP_cons_fresh mp.reduce_ops
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (Or.inr hnotreduce) _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOkP_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ


/-! ## The `opaque` kind, unlocked (the exposed leaf equation)

The H2 SKIP record above named the one missing premise: the leaf
equation invisible at `declOpaqueS`'s `∃`-boundary.  `extendValueS`
now exposes it (an additive conjunct; `declOpaqueS` carries it with
the annotate link), and the harvest is the species with the erasure
link read **directly** off the exposed equation — no `denote_install`,
no `defn_eq`/`thm_ok` detour. -/

theorem harvestOpaqueP (hμ : μ.verifiedChecks = true)
    (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {value : Expr} {env₂ : Env}
    (hR : DeclOpaqueRun μ F env cv value env₂) :
    Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨type', value', hcv, hvfr, rfl, hred⟩ := hR
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv
  obtain ⟨hvlb, hvhf, hannv, hvp, hvr, ⟨vtype, hvrun, hvde⟩⟩ := hvfr
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
    exact acceptedReadsP_of mp.base2 ψ hvrun hwv hbv' hLv
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
    exact acceptedReadsP_of mp.base2 ψ hst hwt hbt' hLt
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
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  have hreads : ∀ ψ, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem mp ψ).reads
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
    denoteP_closed mp.base2.acval_erase mp.base2.cval_closed
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
      inferTypeCore_WScoped mp.base2.wf F hvrun hwv
    have hbvt : vtype.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars mp.base2.wf F hvrun hwv hbv' hLv
    have hnlvt : vtype.fvarLeaves = [] := by
      have hsub := inferTypeCore_fvarLeaves mp.base2.wf F hvrun hwv
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
        (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
        ψ 0 e hcb h
  -- assemble
  refine ⟨(declStepPM_of_cons mp
    (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
    (A := A) hfresh
    (ConsHeadP.ofFresh
      (EnvWF.cons mp.base2.wf ⟨htf', htp,
        Expr.constsResolve_mono htr, hbt',
        (fun _ _ _ heq => nomatch heq),
        (fun _ _ _ _ heq => nomatch heq),
        (fun _ _ heq => nomatch heq),
        (fun _ heq => nomatch heq)⟩)
      (fun ψ => denote_closed mp.base2.cval_closed hvf' hbv'
        (denoteP_erase mp.base2.acval_erase 0 value' (hA ψ)))
      hnres (fun _ heq => nomatch heq)
      (fun _ _ _ _ heq => nomatch heq))
    hAclosed
    hAparams hAok hAvalid ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).choose⟩
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
  · -- `nat_ops` at the extension: an opaque stores an axiom entry
    exact fun φ => natOpsP_cons_fresh mp (mp.nat_ops φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩) (A := A)
      hfresh (hntc := fun _ h => ConstantInfo.noConfusion h)
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · -- `div_mod`/`eq_lawP` at the extension: an opaque stores an axiom
    -- entry, which is neither a definition nor an inductive
    exact fun φ => divModP_cons_fresh (mp.div_mod φ)
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh
      (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion h)) _ rfl
  · exact eqLawP_cons_valueKind mp.eq_lawP
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) (fun _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `caps_ok` at the extension: a value-kind cons is neither a
    -- former, nor a capability constructor, nor a projection function,
    -- so no stored family can be completed here
    exact capsOkP_cons_fresh mp mp.caps_ok
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl
  · -- `rec_rules` at the extension: a value-kind cons is neither a
    -- recursor nor a constructor, so no stored rule moves
    exact fun φ => recRulesP_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ _ _ _ h => ConstantInfo.noConfusion h) _ rfl φ
  · -- `reduce_ops` at the extension: **this is the establishment**.
    -- An `opaque` cons is the only place a compiler-trust operation is
    -- ever stored, and `ReducePinR`'s recorded identity-certificate run
    -- is what makes the law true of it (`Interp2/ReduceOpsP.lean`);
    -- every *other* stored operation crosses by the transport inside.
    exact reduceOpsP_install hμ mp hfresh hvf' hbv' hannv hA hAclosed
      hAok hAvalid hTa
      (fun ψ ρ => by
        obtain ⟨sta, hsta, htE, -, -⟩ := hrowsT ψ
        exact htE ρ (Sat2_nil V ρ))
      hmemA hred _ rfl
  · -- `tower_ok` (task #175 wiring W5): a value-kind cons is never a
    -- tower entry
    exact fun φ => towerOkP_cons_fresh mp
      (c₀ := .axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
      (A := A) hfresh (fun _ h => ConstantInfo.noConfusion h)
      (fun _ h => ConstantInfo.noConfusion h) _ rfl φ

end ConLeche.SetP
