module

import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Semantics.Inductives.FieldsEqOn
public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.CtxOkP
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
import ConLeche.Semantics.Frame
import ConLeche.Verify.Leaves
import ConLeche.Verify.Abstract
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Semantics.ConstsBound

public section

/-!
# The positivity walk's normal form READS like its input (lane ALPHA1)

The install stores a constructor type AS DECLARED; the positivity walk
(`nestPos`, `Kernel/Inductives/Positivity.lean`) reduces each field with
the kernel's `whnf` and returns the field's NORMAL FORM.  The model reads
the fields with holes off that normal form (where the flat shape, the
applied holes and U4 are syntactic facts the walk checked), and ties it
to the declared type SEMANTICALLY: `whnf`'s denotation lemma (`red_sound`,
`RedSem`) at every step, so the normal form reads, at every frame
satisfying the walk's context, as the declared term does.

* `FieldsEqOn V Δ As Bs`: two field lists read alike along every prefix
  satisfying `Δ` extended by the earlier fields;
* `nestPos_red`: one field — the output is framed, its leaves the
  input's, and it reads graded and equal to the input at every
  satisfying frame;
* `nestFields_red`, `nestMemberCtor_red`: the telescope — the input
  reads as a Π-tower over `abD`, the closed normal form as a Π-tower
  over `abN` with the same binder bits and the same body, and
  `FieldsEqOn Δ abD abN`.

Everything else about the two towers follows from `FieldsEqOn`: fitting
spines agree (`FieldsEqOn.spineFit_iff`), and so do field-wise
positivity (`FieldsEqOn.teleMonoOn`) and the relation under the fields
(`FieldsEqOn.underTele_eq`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckError CheckM NestCtx NestHole NestState NestFieldKind
  BinderMeta nestPos nestFields nestMemberCtor closeTelescope fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-- A Π-type is graded when its domain is, its codomain is under it, and
its bit is honest. -/
theorem graded_pi_intro {Δ : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (hA : Graded V Δ A) (hB : Graded V (A :: Δ) B)
    (hbit : v = 0 → ∀ ρ : Nat → V, Sat V Δ ρ → ∀ x, x ∈ˢ interp V ρ A →
      interp V (cons x ρ) B ∈ˢ (univZero : V)) :
    Graded V Δ (.pi u v A B) := by
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_pi]
    exact ⟨(hA ρ hρ).1, fun x hx => (hB _ (Sat_cons V hρ hx)).1⟩
  · rw [AnnotValid_pi]
    exact ⟨(hA ρ hρ).2, fun x hx => (hB _ (Sat_cons V hρ hx)).2,
      fun hv x hx => hbit hv ρ hρ x hx⟩

/-- A grading under a binder moves to a binder reading alike. -/
theorem graded_cons_congr {Δ : List AnnotTerm} {A B e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B)
    (hg : Graded V (A :: Δ) e) : Graded V (B :: Δ) e :=
  fun ρ hρ => hg ρ (sat_cons_congr (fun σ hσ => (h σ hσ).symm) hρ)

/-! ## A reading names only stored constants -/

omit [SetTheory V] in
/-- **A term that reads names only stored constants**, once its free
variables' annotations do (`denoteMeta` looks every constant up). -/
theorem constsBound_of_read {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm}, denoteMeta acval env φ d e = some ea →
      (∀ l ∈ e.fvarLeaves, ConstsBound env l.2) → ConstsBound env e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u => intro _ _ _; simp
  | case2 d idx ty => intro _ _ hl; simpa using hl (idx, ty) (by simp [Expr.fvarLeaves])
  | case3 d n us ci hf hlen => intro _ _ _; simp [hf]
  | case4 d n us ci hf hlen =>
    intro _ h _
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf => intro _ h _; rw [denoteMeta, hf] at h; exact nomatch h
  | case6 d ty body m ihty ihbody =>
    intro _ h hl
    obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_forallE_inv h
    have hty := ihty hta fun l h' => hl l (by simp [Expr.fvarLeaves, h'])
    refine constsBound_forallE.mpr ⟨hty, constsBound_of_instantiate1 _ 0 (ihbody hba fun l h' => ?_)⟩
    rcases Expr.fvarLeaves_instantiate1 body 0 h' with h3 | h3
    · exact hl l (by simp [Expr.fvarLeaves, h3])
    · simp only [Expr.fvarLeaves, List.mem_cons] at h3
      rcases h3 with rfl | h3
      · exact hty
      · exact hl l (by simp [Expr.fvarLeaves, h3])
  | case7 d ty body m ihty ihbody =>
    intro _ h hl
    obtain ⟨ta, ba, hta, hba, -⟩ := denoteMeta_lam_inv h
    have hty := ihty hta fun l h' => hl l (by simp [Expr.fvarLeaves, h'])
    refine constsBound_lam.mpr ⟨hty, constsBound_of_instantiate1 _ 0 (ihbody hba fun l h' => ?_)⟩
    rcases Expr.fvarLeaves_instantiate1 body 0 h' with h3 | h3
    · exact hl l (by simp [Expr.fvarLeaves, h3])
    · simp only [Expr.fvarLeaves, List.mem_cons] at h3
      rcases h3 with rfl | h3
      · exact hty
      · exact hl l (by simp [Expr.fvarLeaves, h3])
  | case8 d f a ihf iha =>
    intro _ h hl
    obtain ⟨fa, aa, hfa, haa, -⟩ := denoteMeta_app_inv h
    exact constsBound_app.mpr ⟨ihf hfa fun l h' => hl l (by simp [Expr.fvarLeaves, h']),
      iha haa fun l h' => hl l (by simp [Expr.fvarLeaves, h'])⟩
  | case9 d ty val body => intro _ h _; rw [denoteMeta] at h; exact nomatch h
  | case10 d sn j e ihe =>
    intro _ h hl
    obtain ⟨ea', hea', -⟩ := denoteMeta_proj_inv h
    exact constsBound_proj.mpr (ihe hea' fun l h' => hl l (by simpa [Expr.fvarLeaves] using h'))
  | case15 d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    intro _ _ _
    cases e with
    | bvar => simp
    | sort => exact (h1 _ rfl).elim
    | fvar => exact (h2 _ _ rfl).elim
    | const => exact (h3 _ _ rfl).elim
    | forallE => exact (h4 _ _ _ rfl).elim
    | lam => exact (h5 _ _ _ rfl).elim
    | app => exact (h6 _ _ rfl).elim
    | letE => exact (h7 _ _ _ rfl).elim
    | proj => exact (h8 _ _ _ rfl).elim
    | lit l => exact constsBound_lit
  | _ => intro _ _ _; exact constsBound_lit

/-! ## One field -/

variable {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **`nestPos`'s output reads like its input** (see the module
docstring): at every fuel, from the input's frame, context, reading and
grading. -/
theorem nestPos_red (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat) :
    ∀ (fuel : Nat) (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState)
      (k : NestFieldKind) (nd : Expr) (st' : NestState),
      nestPos (fueledOps .verified F) env ctx fuel prog dep kb e st = .ok (k, nd, st') →
      Frame dep e → ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
      CtxOkP m φ dep Δa e → denoteMeta m.acval env φ dep e = some ea → Graded V Δa ea →
      Frame dep nd ∧ LeavesSub nd e ∧ ∃ nda, denoteMeta m.acval env φ dep nd = some nda ∧
        Graded V Δa nda ∧ ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ nda := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog dep kb e st k nd st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro prog dep kb e st k nd st' hrun hfr Δa ea hC hea hgr
    rw [nestPos] at hrun
    cases hw : ConLeche.whnf .verified env F dep e with
    | error err =>
      have hw' : (fueledOps .verified F).whnf env dep e = .error err := hw
      simp [hw', bind, Except.bind] at hrun
    | ok w =>
      have hw' : (fueledOps .verified F).whnf env dep e = .ok w := hw
      simp only [hw', bind, Except.bind] at hrun
      obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
        red_sound hin (ConLeche.Rules.whnf_bridge hw) hfr hC.toCtxOk hea hgr
      -- the reduct as the output
      have hW : Frame dep w ∧ LeavesSub w e ∧ ∃ nda, denoteMeta m.acval env φ dep w = some nda ∧
          Graded V Δa nda ∧ ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ nda :=
        ⟨hfrw, hsub, wa, hwa, hgw, heq⟩
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨-, rfl, -⟩ := hrun
        split
        · exact hW
        · exact ⟨hfr, fun _ h => h, ea, hea, hgr, fun _ _ => rfl⟩
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b mb
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨-, rfl, -⟩ := hrun
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
        obtain ⟨hws, hb, hLb⟩ := hfrw
        simp only [Expr.WScoped] at hws
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
        have hCw : CtxOkP m φ dep Δa (.forallE a b mb) := hC.of_subset hsub
        have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
        obtain ⟨hfrn, hsubn, nba, hnba, hgn, heqn⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb st₁ hv
          (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hCop hba hgB
        obtain ⟨hwsn, hbn, hLn⟩ := hfrn
        have hbnd : nb.looseBVarsBounded 0 = true := hbn
        refine ⟨⟨?_, ?_, ?_⟩, ?_, .pi 0 (pwBit φ mb.pw) ta nba, ?_, ?_, ?_⟩
        · simp only [Expr.WScoped]
          exact ⟨hws.1, WScoped.abstract1 0 hwsn⟩
        · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hb.1, looseBVarsBounded_abstract1 nb 0 hbnd⟩
        · intro l hl
          simp only [Expr.fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hLa l hl
          · exact hLn l (Expr.fvarLeaves_abstract1_lt nb 0 hwsn l hl).1
        · -- the leaves: the domain's, and the body's below the binder
          intro l hl
          simp only [Expr.fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hsub l (by simp [Expr.fvarLeaves, hl])
          · obtain ⟨hl₁, hl₂⟩ := Expr.fvarLeaves_abstract1_lt nb 0 hwsn l hl
            rcases Expr.fvarLeaves_instantiate1 b 0 (hsubn l hl₁) with h3 | h3
            · exact hsub l (by simp [Expr.fvarLeaves, h3])
            · simp only [Expr.fvarLeaves, List.mem_cons] at h3
              rcases h3 with rfl | h3
              · exact absurd hl₂ (by simp)
              · exact hsub l (by simp [Expr.fvarLeaves, h3])
        · rw [denoteMeta_forallE, hta]
          simp only [bind, Option.bind]
          rw [denoteMeta_erasedEq (erasedEq_abstract1_instantiate1 nb 0 hbnd), hnba]
        · refine graded_pi_intro hgA hgn fun hv0 ρ hρ x hx => ?_
          rw [← heqn _ (Sat_cons V hρ hx)]
          have hgw' := hgw ρ hρ
          have hval := ((AnnotValid_pi V ρ 0 (pwBit φ mb.pw) ta ba) ▸ hgw'.2).2.2 hv0 x hx
          exact hval
        · intro ρ hρ
          rw [heq ρ hρ]
          simp only [interp_pi]
          exact piR_congr fun x hx => heqn _ (Sat_cons V hρ hx)
      · -- a head applied to arguments: the output is the reduct
        split at hrun
        · rename_i i ty hfn
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · rw [if_pos hmem] at hrun
            split at hrun
            · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              obtain ⟨-, rfl, -⟩ := hrun
              exact hW
            · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · rw [if_neg hmem] at hrun
            split at hrun
            · split at hrun
              · simp [throw, throwThe, MonadExceptOf.throw] at hrun
              · split at hrun
                · split at hrun
                  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨-, rfl, -⟩ := hrun
                    exact hW
                  · simp [throw, throwThe, MonadExceptOf.throw] at hrun
                · simp [throw, throwThe, MonadExceptOf.throw] at hrun
            · simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · rename_i n us hfn
          split at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨-, rfl, -⟩ := hrun
          exact hW
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

/-! ## The field telescope -/

/-- **The walked telescope and its closed normal form read alike** (see
the module docstring): the input reads as a Π-tower over `abD`, the
closing of the walk's outputs over `abN`, with the same binder data and
the same body, the fields reading alike along every satisfying prefix,
the normal form graded, framed and with the input's leaves. -/
theorem nestFields_red (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat) {base : Nat}
    {err : CheckError} :
    ∀ (n j : Nat) (cur : Expr) (st : NestState) (ks : List NestFieldKind)
      (nds : List (Expr × BinderMeta)) (res : Expr) (st' : NestState),
      nestFields (nestPos (fueledOps .verified F) env ctx 1024) [] base err n j cur st
        = .ok (ks, nds, res, st') → st'.restart = none →
      Frame (base + j) cur → ∀ {Δa : List AnnotTerm} {ca : AnnotTerm},
      CtxOkP m φ (base + j) Δa cur → denoteMeta m.acval env φ (base + j) cur = some ca →
      Graded V Δa ca →
      ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ca = mkPisAV abD B ∧
        denoteMeta m.acval env φ (base + j) (closeTelescope nds (base + j) res)
          = some (mkPisAV abN B) ∧
        abD.length = n ∧ abN.length = n ∧
        abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
        FieldsEqOn V Δa (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
        Graded V Δa (mkPisAV abN B) ∧
        Frame (base + j) (closeTelescope nds (base + j) res) ∧
        LeavesSub (closeTelescope nds (base + j) res) cur := by
  intro n
  induction n with
  | zero =>
    intro j cur st ks nds res st' h _ hfr Δa ca hC hca hgr
    simp only [nestFields, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl, -⟩ := h
    exact ⟨[], [], ca, rfl, by simpa [closeTelescope, mkPisAV] using hca, rfl, rfl, rfl, trivial,
      by simpa [mkPisAV] using hgr, by simpa [closeTelescope] using hfr,
      fun l hl => by simpa [closeTelescope] using hl⟩
  | succ n ih =>
    intro j cur st ks nds res st' h hr hfr Δa ca hC hca hgr
    cases cur with
    | forallE a b bm =>
      simp only [nestFields, bind, Except.bind] at h
      split at h
      · simp at h
      rename_i v hv
      obtain ⟨k, nd, st₁⟩ := v
      simp only at h
      split at h
      · rename_i hsome
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, rfl⟩ := h
        simp [hr] at hsome
      split at h
      · simp at h
      rename_i v' hv'
      obtain ⟨ks', nds', res', st₂⟩ := v'
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl⟩ := h
      obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
      obtain ⟨hws, hb, hLb⟩ := hfr
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
      -- the field
      obtain ⟨hfrn, hsubn, nda, hnda, hgn, heqn⟩ := nestPos_red hin ctx F 1024 [] (base + j) 0 a st
        k nd st₁ hv ⟨hws.1, hb.1, hLa⟩ hC.forallE_ty hta hgA
      -- the rest, one binder down
      have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
      have hfr' := frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd
      rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
      obtain ⟨abD, abN, B, hbaE, hrd, hlD, hlN, hbits, hEq, hgN, hfrc, hsubc⟩ :=
        ih (j + 1) _ st₁ ks' nds' res' _ hv' hr hfr' hCop hba hgB
      subst hbaE
      rw [show base + (j + 1) = base + j + 1 by omega] at hrd hfrc hsubc
      obtain ⟨hwsc, hbc, hLc⟩ := hfrc
      have hbnd : (closeTelescope nds' (base + j + 1) res').looseBVarsBounded 0 = true := hbc
      obtain ⟨hwsn, hbn, hLn⟩ := hfrn
      refine ⟨(0, pwBit φ bm.pw, ta) :: abD, (0, pwBit φ bm.pw, nda) :: abN, B, rfl, ?_,
        by simp [hlD], by simp [hlN], by simp [hbits], ⟨heqn, hEq⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · -- the reading
        simp only [closeTelescope]
        rw [denoteMeta_forallE, hnda]
        simp only [bind, Option.bind]
        rw [denoteMeta_erasedEq (erasedEq_abstract1_instantiate1 _ 0 hbnd), hrd]
        rfl
      · -- the grading
        refine graded_pi_intro hgn (graded_cons_congr heqn hgN) fun hv0 ρ hρ x hx => ?_
        have hx' : x ∈ˢ interp V ρ ta := (heqn ρ hρ).symm ▸ hx
        rw [← interp_mkPisAV_congr abD abN B hbits hEq _ (Sat_cons V hρ hx')]
        have hval := ((AnnotValid_pi V ρ 0 (pwBit φ bm.pw) ta (mkPisAV abD B)) ▸
          (hgr ρ hρ).2).2.2 hv0 x hx'
        exact hval
      · simp only [closeTelescope, Expr.WScoped]
        exact ⟨hwsn, WScoped.abstract1 0 hwsc⟩
      · simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hbn, looseBVarsBounded_abstract1 _ 0 hbnd⟩
      · intro l hl
        simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hLn l hl
        · exact hLc l (Expr.fvarLeaves_abstract1_lt _ 0 hwsc l hl).1
      · intro l hl
        simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact (by simp [Expr.fvarLeaves, hsubn l hl] : l ∈ (Expr.forallE a b bm).fvarLeaves)
        · obtain ⟨hl₁, hl₂⟩ := Expr.fvarLeaves_abstract1_lt _ 0 hwsc l hl
          rcases Expr.fvarLeaves_instantiate1 b 0 (hsubc l hl₁) with h3 | h3
          · simp [Expr.fvarLeaves, h3]
          · simp only [Expr.fvarLeaves, List.mem_cons] at h3
            rcases h3 with rfl | h3
            · exact absurd hl₂ (by simp)
            · simp [Expr.fvarLeaves, h3]
    | _ => simp [nestFields, throw, throwThe, MonadExceptOf.throw] at h

/-! ## One constructor -/

/-- **A member constructor's normal form reads like it** (the telescope,
`nestFields_red`, at the walk's depth; the normal form is the closing of
the walk's outputs, `nestMemberCtor_inv`). -/
theorem nestMemberCtor_red (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : nestMemberCtor (fueledOps .verified F) env ctx nF crest st = .ok (ks, tyN, st'))
    (hfr : Frame (ctx.hiAt 0) crest) {Δa : List AnnotTerm} {ca : AnnotTerm}
    (hC : CtxOkP m φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta m.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      ca = mkPisAV abD B ∧ denoteMeta m.acval env φ (ctx.hiAt 0) tyN = some (mkPisAV abN B) ∧
      abD.length = nF ∧ abN.length = nF ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      FieldsEqOn V Δa (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      Graded V Δa (mkPisAV abN B) ∧ Frame (ctx.hiAt 0) tyN ∧ LeavesSub tyN crest := by
  obtain ⟨err, nds, cur, hf, hr, htyN, -, -⟩ := nestMemberCtor_inv h
  subst htyN
  have := nestFields_red hin ctx F (base := ctx.hiAt 0) nF 0 crest st ks nds cur st' hf hr
    (by simpa using hfr) (by simpa using hC) (by simpa using hca) hgr
  simpa using this

end ConLeche.Model
