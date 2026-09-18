module

public import ConLeche.Model.Inductives.StructRows
import ConLeche.Verify.Inductives.MutualNormPres
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Inductives.StructFrame
import ConLeche.Semantics.Frame

public section

/-!
# The constructors' positivity normalisation READS (task #315 L-B, DESIGN §U.30)

`normCtorValM`'s field-domain normalisation (`normPosDomM`,
`Kernel/Inductives/MutualInstall.lean`) is not the identity on the
expression — the λ-pin domain `(fun _ => PT α) k` is a redex the walk
reduces — so a copy's STORED field domain is the elimination's
rewritten one only up to it.  `CopyCtorInst.ordF`'s ordinary arm is
therefore stated at the READING (DESIGN §U.30), and this is the law
that discharges it: the walk preserves the interpretation.

Every step is one `whnf` (`WhnfClaim`: the reduct reads the same;
`WhnfReads`: it reads at all — both from `EnvModelM` at a verified
mode, `claimsAt_of`/`whnfReads_of`), and the Π step opens at
`.fvar d dom` and closes again — the `abstract1`/`instantiate1` round
trip the quarters' λ arms already run (`abstract1_instantiate1` at the
leaf condition the walk's frame preservation supplies,
`Verify/Inductives/MutualNormPres.lean`), with `CtxOk.open` extending
the context and `piR_congr` taking the two codomains apart.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The positivity normalisation preserves the reading**: at a
domain that reads, whose frame is the run's, the walk's output reads
the same at every satisfying valuation.  `hwc`/`hwr` are the P tier's
`whnf` claims at the run's fuel. -/
theorem normPosDomM_read {m : EnvModel V env} {F : Nat}
    (hwc : WhnfClaim μ m φ F) (hwr : WhnfReads m μ φ F) {memberNames : List Name} :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr} {Δa : List AnnotTerm} {ea ea' : AnnotTerm},
      ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env memberNames d fuel e
        = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea' := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro d e e' Δa ea ea' h hws hb hL hC hea hea' hok
    rcases ConLeche.normPosDomM_inv h with ⟨-, rfl⟩ | ⟨w, hw, hcase⟩
    · rw [hea] at hea'
      obtain rfl := Option.some.inj hea'
      exact fun _ _ => rfl
    obtain ⟨wa, hwa⟩ := hwr hw hws hb hL (LeafReads.of_ctxOk hC) hea
    obtain ⟨hokw, heqw⟩ := hwc hw hws hb hL hC hea hwa hok
    have hwws : Expr.WScoped d w := ConLeche.whnf_WScoped m.wf F hw hws
    have hwb : w.looseBVarsBounded 0 = true := ConLeche.whnf_looseBVars m.wf F hw hb
    have hwl : ∀ l ∈ w.fvarLeaves, l ∈ e.fvarLeaves := ConLeche.whnf_fvarLeaves m.wf F hw
    have hwL : Expr.LeavesBounded w := fun l hl => hL l (hwl l hl)
    have hCw : CtxOk m φ d Δa w := hC.of_subset hwl
    rcases hcase with rfl | ⟨dom, body, bm, body', fuel', rfl, rfl, -, hbody', rfl⟩
    · rw [hwa] at hea'
      obtain rfl := Option.some.inj hea'
      exact heqw
    -- the reduct's reading
    rw [denoteMeta] at hwa
    rcases hdoma : denoteMeta m.acval env φ d dom with _ | doma
    · rw [hdoma] at hwa; exact nomatch hwa
    rw [hdoma] at hwa
    rcases hboda : denoteMeta m.acval env φ (d + 1) (body.instantiate1 (.fvar d dom))
      with _ | boda
    · rw [hboda] at hwa; exact nomatch hwa
    rw [hboda] at hwa
    obtain rfl : wa = .pi 0 (pwBit φ bm.pw) doma boda := (Option.some.inj hwa).symm
    -- the output's reading
    rw [denoteMeta, hdoma] at hea'
    rcases hboda' : denoteMeta m.acval env φ (d + 1)
        ((body'.abstract1 d).instantiate1 (.fvar d dom)) with _ | boda'
    · rw [hboda'] at hea'; exact nomatch hea'
    rw [hboda'] at hea'
    obtain rfl : ea' = .pi 0 (pwBit φ bm.pw) doma boda' := (Option.some.inj hea').symm
    -- the opened frame, and the round trip that identifies the output's body
    simp only [Expr.WScoped] at hwws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwb
    have hLdom : Expr.LeavesBounded dom := fun l hl => hwL l (by simp [Expr.fvarLeaves, hl])
    have hLbody : Expr.LeavesBounded body := fun l hl => hwL l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwopen, hbopen, hLopen⟩ :=
      frame_open2 hwws.1 hwb.1 hwws.2 hwb.2 hLdom hLbody
    obtain ⟨-, hb2, hl2⟩ := ConLeche.normPosDomM_pres m.wf fuel' hbody' hwopen hbopen
    have hleaf : Expr.LeafCond d dom (body.instantiate1 (.fvar d dom)) := by
      intro l hl hd
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hwws.2 l h2
          omega)
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact rfl
        · exact absurd hd (by
            have := Expr.fvarLeaves_lt_of_wscoped hwws.1 l h3
            omega)
    have hcons : Expr.fvarConsistent d dom body' :=
      Expr.fvarConsistent_of_leafCond body' (fun l hl => hleaf l (hl2 l hl))
    have hround : (body'.abstract1 d).instantiate1 (.fvar d dom) = body' :=
      abstract1_instantiate1 body' 0 hcons hb2
    rw [hround] at hboda'
    -- the extended context and the graded readings under it
    have hokdoma : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ doma := by
      intro ρ hρ
      obtain ⟨hwd, hval⟩ := hokw ρ hρ
      rw [WellDenoted_pi] at hwd
      rw [AnnotValid_pi] at hval
      exact ⟨hwd.1, hval.1⟩
    have hCop : CtxOk m φ (d + 1) (doma :: Δa) (body.instantiate1 (.fvar d dom)) :=
      CtxOk.open hCw.forallE_body hCw.forallE_ty hdoma hokdoma
    have hokbody : ∀ ρ : Nat → V, Sat V (doma :: Δa) ρ → WellDenotedV V ρ boda := by
      intro ρ hρ
      have htail : Sat V Δa (fun j => ρ (j + 1)) := Sat_tail hρ
      have hx : ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) doma := by
        have := hρ 0 doma rfl
        simpa using this
      obtain ⟨hwd, hval⟩ := hokw _ htail
      rw [WellDenoted_pi] at hwd
      rw [AnnotValid_pi] at hval
      refine ⟨?_, ?_⟩
      · have := hwd.2 (ρ 0) hx
        rwa [cons_eta] at this
      · have := hval.2.1 (ρ 0) hx
        rwa [cons_eta] at this
    -- the codomains agree at every member of the domain
    intro ρ hρ
    refine heqw ρ hρ |>.trans ?_
    simp only [interp_pi]
    refine piR_congr fun x hx => ?_
    exact ih fuel' (by omega) hbody' hwopen hbopen hLopen hCop hboda hboda' hokbody _
      (Sat_cons V hρ hx)

/-- **The positivity normalisation's output READS, AND IS GRADED**: at
a domain that reads and is graded, whose frame is the run's, the
walk's output reads too and its reading is graded at the same context
— the existence half of `normPosDomM_read`, which takes the output's
reading as an input.  Same induction: every step's `whnf` output reads
by `WhnfReads` and is graded by `WhnfClaim`'s FIRST component (which
`normPosDomM_read` computes and discards), and at a `Π` both halves
are assembled from the domain's (unchanged) and the recursive call's,
through the `abstract1`/`instantiate1` round trip.

The grading is what an arm needs when the walk's output is the term it
must read a TARGET off — `WellDenoted` of an application is the fit of
its arguments, so the index expressions of a copy's recursive field fit
the target's index telescope only through this (task #315 L-B). -/
theorem normPosDomM_reads {m : EnvModel V env} {F : Nat}
    (hwc : WhnfClaim μ m φ F) (hwr : WhnfReads m μ φ F) {memberNames : List Name} :
    ∀ (fuel : Nat) {d : Nat} {e e' : Expr} {Δa : List AnnotTerm} {ea : AnnotTerm},
      ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env memberNames d fuel e
        = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      ∃ ea', denoteMeta m.acval env φ d e' = some ea' ∧
        ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea' := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro d e e' Δa ea h hws hb hL hC hea hok
    rcases ConLeche.normPosDomM_inv h with ⟨-, rfl⟩ | ⟨w, hw, hcase⟩
    · exact ⟨ea, hea, hok⟩
    obtain ⟨wa, hwa⟩ := hwr hw hws hb hL (LeafReads.of_ctxOk hC) hea
    obtain ⟨hokw, -⟩ := hwc hw hws hb hL hC hea hwa hok
    have hwws : Expr.WScoped d w := ConLeche.whnf_WScoped m.wf F hw hws
    have hwb : w.looseBVarsBounded 0 = true := ConLeche.whnf_looseBVars m.wf F hw hb
    have hwl : ∀ l ∈ w.fvarLeaves, l ∈ e.fvarLeaves := ConLeche.whnf_fvarLeaves m.wf F hw
    have hwL : Expr.LeavesBounded w := fun l hl => hL l (hwl l hl)
    have hCw : CtxOk m φ d Δa w := hC.of_subset hwl
    rcases hcase with rfl | ⟨dom, body, bm, body', fuel', rfl, rfl, -, hbody', rfl⟩
    · exact ⟨wa, hwa, hokw⟩
    -- the reduct's reading
    rw [denoteMeta] at hwa
    rcases hdoma : denoteMeta m.acval env φ d dom with _ | doma
    · rw [hdoma] at hwa; exact nomatch hwa
    rw [hdoma] at hwa
    rcases hboda : denoteMeta m.acval env φ (d + 1) (body.instantiate1 (.fvar d dom))
      with _ | boda
    · rw [hboda] at hwa; exact nomatch hwa
    rw [hboda] at hwa
    obtain rfl : wa = .pi 0 (pwBit φ bm.pw) doma boda := (Option.some.inj hwa).symm
    -- the opened frame, and the round trip that identifies the output's body
    simp only [Expr.WScoped] at hwws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwb
    have hLdom : Expr.LeavesBounded dom := fun l hl => hwL l (by simp [Expr.fvarLeaves, hl])
    have hLbody : Expr.LeavesBounded body := fun l hl => hwL l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hwopen, hbopen, hLopen⟩ :=
      frame_open2 hwws.1 hwb.1 hwws.2 hwb.2 hLdom hLbody
    obtain ⟨-, hb2, hl2⟩ := ConLeche.normPosDomM_pres m.wf fuel' hbody' hwopen hbopen
    have hleaf : Expr.LeafCond d dom (body.instantiate1 (.fvar d dom)) := by
      intro l hl hd
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · exact absurd hd (by
          have := Expr.fvarLeaves_lt_of_wscoped hwws.2 l h2
          omega)
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact rfl
        · exact absurd hd (by
            have := Expr.fvarLeaves_lt_of_wscoped hwws.1 l h3
            omega)
    have hcons : Expr.fvarConsistent d dom body' :=
      Expr.fvarConsistent_of_leafCond body' (fun l hl => hleaf l (hl2 l hl))
    have hround : (body'.abstract1 d).instantiate1 (.fvar d dom) = body' :=
      abstract1_instantiate1 body' 0 hcons hb2
    -- the extended context and the graded readings under it
    have hokdoma : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ doma := by
      intro ρ hρ
      obtain ⟨hwd, hval⟩ := hokw ρ hρ
      rw [WellDenoted_pi] at hwd
      rw [AnnotValid_pi] at hval
      exact ⟨hwd.1, hval.1⟩
    have hCop : CtxOk m φ (d + 1) (doma :: Δa) (body.instantiate1 (.fvar d dom)) :=
      CtxOk.open hCw.forallE_body hCw.forallE_ty hdoma hokdoma
    have hokbody : ∀ ρ : Nat → V, Sat V (doma :: Δa) ρ → WellDenotedV V ρ boda := by
      intro ρ hρ
      have htail : Sat V Δa (fun j => ρ (j + 1)) := Sat_tail hρ
      have hx : ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) doma := by
        have := hρ 0 doma rfl
        simpa using this
      obtain ⟨hwd, hval⟩ := hokw _ htail
      rw [WellDenoted_pi] at hwd
      rw [AnnotValid_pi] at hval
      refine ⟨?_, ?_⟩
      · have := hwd.2 (ρ 0) hx
        rwa [cons_eta] at this
      · have := hval.2.1 (ρ 0) hx
        rwa [cons_eta] at this
    -- the output's reading, assembled — and its grading with it
    obtain ⟨boda', hboda', hokboda'⟩ :=
      ih fuel' (by omega) hbody' hwopen hbopen hLopen hCop hboda hokbody
    -- the body's two readings agree, which is what the `Π`'s PROP-SORT
    -- clause of `AnnotValid` needs at the output
    have heqBody := normPosDomM_read hwc hwr fuel' hbody' hwopen hbopen hLopen hCop hboda hboda'
      hokbody
    have hokPi : ∀ ρ : Nat → V, Sat V Δa ρ →
        WellDenotedV V ρ (AnnotTerm.pi 0 (pwBit φ bm.pw) doma boda') := by
      intro ρ hρ
      obtain ⟨hwdD, hvalD⟩ := hokdoma ρ hρ
      have hsatX : ∀ x : V, x ∈ˢ interp V ρ doma → Sat V (doma :: Δa) (cons x ρ) :=
        fun x hx => Sat_cons V hρ hx
      refine ⟨?_, ?_⟩
      · rw [WellDenoted_pi]
        exact ⟨hwdD, fun x hx => (hokboda' _ (hsatX x hx)).1⟩
      · rw [AnnotValid_pi]
        refine ⟨hvalD, fun x hx => (hokboda' _ (hsatX x hx)).2, ?_⟩
        intro hz x hx
        obtain ⟨-, hvalW⟩ := hokw ρ hρ
        rw [AnnotValid_pi] at hvalW
        rw [← heqBody _ (hsatX x hx)]
        exact hvalW.2.2 hz x hx
    rw [← hround] at hboda'
    exact ⟨.pi 0 (pwBit φ bm.pw) doma boda', by rw [denoteMeta, hdoma, hboda']; rfl, hokPi⟩

/-- **The reading law at the run's own model package**: the `whnf`
claims a verified-mode `EnvModelM` answers (`claimsAt_of`,
`whnfReads_of`), so a consumer inside an inductive stage needs only
`μ.verifiedChecks` and its model. -/
theorem normPosDomM_read_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (φ : Name → Nat) (F : Nat) {memberNames : List Name}
    {fuel d : Nat} {e e' : Expr} {Δa : List AnnotTerm} {ea ea' : AnnotTerm}
    (h : ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env memberNames d
      fuel e = .ok e')
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true) (hL : Expr.LeavesBounded e)
    (hC : CtxOk mp.base2 φ d Δa e)
    (hea : denoteMeta mp.base2.acval env φ d e = some ea)
    (hea' : denoteMeta mp.base2.acval env φ d e' = some ea')
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea' :=
  normPosDomM_read (claimsAt_of hμ mp φ F).whnf
    (whnfReads_of (TierInputsAt.ofSem mp φ).reads) fuel h hws hb hL hC hea hea' hok

/-- **The consumer's form**: the walk's output reads, is GRADED, and
reads the same — `normPosDomM_reads` supplies the output's reading
that `normPosDomM_read_of` demands, so an arm inside an inductive
stage needs nothing about `e'` at all (task #315 L-B). -/
theorem normPosDomM_readEq_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    (φ : Name → Nat) (F : Nat) {memberNames : List Name}
    {fuel d : Nat} {e e' : Expr} {Δa : List AnnotTerm} {ea : AnnotTerm}
    (h : ConLeche.normPosDomM (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env memberNames d
      fuel e = .ok e')
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true) (hL : Expr.LeavesBounded e)
    (hC : CtxOk mp.base2 φ d Δa e)
    (hea : denoteMeta mp.base2.acval env φ d e = some ea)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    ∃ ea', denoteMeta mp.base2.acval env φ d e' = some ea' ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea' := by
  obtain ⟨ea', hea', hokOut⟩ :=
    normPosDomM_reads (claimsAt_of hμ mp φ F).whnf
      (whnfReads_of (TierInputsAt.ofSem mp φ).reads) fuel h hws hb hL hC hea hok
  exact ⟨ea', hea', hokOut, normPosDomM_read_of hμ mp φ F h hws hb hL hC hea hea' hok⟩

end ConLeche.Model
