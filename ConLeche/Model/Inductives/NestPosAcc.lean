module

public import ConLeche.Model.Inductives.NestPosMono
public import ConLeche.Semantics.Inductives.HoleAcc
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Denote.Shift
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitShift
import ConLeche.Semantics.Frame
import ConLeche.Verify.InferLemmas
import ConLeche.Model.IndPointKit

public section

/-!
# `nestPos`'s run ⇒ ACCESSIBLE in the holes (lane ACCMODEL)

The twin of `NestPosMono.lean` for the closure witness (W) (maintainer
ruling "(W) by ACCESSIBILITY", 2026-09-24): joint accessibility at the
instantiation is an install-time lemma derived from the positivity
walk's run, like monotonicity.  The inversion is `nestPos_sem`'s, case
by case, over the reading-level lemmas of
`Semantics/Inductives/HoleAcc.lean`:

* the `whnf` step by `red_sound` (`AccOn.of_eqOn`);
* `const`: the reduct mentions no hole — the empty bound;
* `pi`: a hole-free domain, the body by induction under `underBoth`;
* `holeApp`: a member hole at hole-free arguments — the bound `{pt}`;
* a frame's hole: blind in its key's parameters (`FrameBlind`, a fact of
  the relation, `HoleRelA.frame`) — the bound `{pt}`;
* `contApp`: the premise `ContAcc` (the container case, its own lemma).

**The relation** (`HoleRelA`) relates COMPARABLE frames: they satisfy the
context and agree off the hole positions; no growth condition (supports
carry the elements).  Under a field the relation is `underBoth`.

**The bound's positions.**  Next to accessibility the theorem states
which positions the bound reads (`InvOn`): only the non-hole positions
the walk's OUTPUT mentions (`MentNH`).  A later field's bound then does
not read an earlier recursive, reflexive or nested field (U4 on the
normal-form telescope) — what makes a constructor's bound UNIFORM across
the tuples of the space.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckError CheckM NestCtx NestKey NestHole NestState NestFieldKind
  nestPos nestCont fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The positions an output mentions -/

/-- **The non-hole positions an output mentions** at depth `d`: position
`i` is the variable `d - 1 - i`, mentioned by `nf`, and not a hole. -/
@[expose] def MentNH (lo hi d : Nat) (nf : Expr) : Nat → Prop :=
  fun i => i < d ∧ nf.nestOcc [] (d - 1 - i) (d - i) = true ∧ ¬ holeP d lo hi i

omit [SetTheory V] in
theorem noBVar_exists' {α : Type} :
    ∀ {e : AnnotTerm} {P : α → Nat → Prop}, (∀ a, NoBVar (P a) e) →
      NoBVar (fun i => ∃ a, P a i) e := by
  intro e
  induction e with
  | bvar i => intro P h; exact fun ⟨a, ha⟩ => h a ha
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro P h; exact ⟨ihf fun a => (h a).1, iha fun a => (h a).2⟩
  | eqE a b iha ihb => intro P h; exact ⟨iha fun a => (h a).1, ihb fun a => (h a).2⟩
  | fst e ihe => intro P h; exact ihe fun a => h a
  | snd e ihe => intro P h; exact ihe fun a => h a
  | lam v A b ihA ihb =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihb (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi
  | pi u v A B ihA ihB =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihB (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi

/-- **A hole-free domain inside the output reads only mentioned non-hole
positions.** -/
theorem noBVar_not_mentNH {lo hi d : Nat} {a nf : Expr} {ta : AnnotTerm}
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hholes : NoBVar (holeP d lo hi) ta)
    (hsub : ∀ s, s < d → nf.nestOcc [] s (s + 1) = false → a.nestOcc [] s (s + 1) = false)
    (hta : denoteMeta m.acval env φ d a = some ta) :
    NoBVar (fun i => ¬ MentNH lo hi d nf i) ta := by
  have hbb := denote_bvarsBelow m.cval_closedL d a hws hb (denoteMeta_erase m.acval_erase d a hta)
  have hbelow : NoBVar (fun i => d ≤ i) ta := NoBVar_of_bvarsBelow hbb fun _ h => h
  have hnone : NoBVar (fun _ => False) ta := NoBVar_of_bvarsBelow hbb fun _ h => h.elim
  have hun : NoBVar (fun i => ∃ s, s < d ∧ nf.nestOcc [] s (s + 1) = false ∧ holeP d s (s + 1) i)
      ta := by
    refine noBVar_exists' (P := fun s i => s < d ∧ nf.nestOcc [] s (s + 1) = false ∧
      holeP d s (s + 1) i) fun s => ?_
    by_cases hs : s < d ∧ nf.nestOcc [] s (s + 1) = false
    · exact NoBVar.mono (fun i hn => hn.2.2)
        (denoteMeta_noBVar_of_nestOcc (m := m) (names := []) (lo := s) (hi := s + 1) d a hws
          (by omega) (hsub s hs.1 hs.2) hta)
    · exact NoBVar.mono (fun i hn => absurd ⟨hn.1, hn.2.1⟩ hs) hnone
  have hall := noBVar_exists' (α := Fin 3) (P := fun k i => match k with
    | 0 => d ≤ i
    | 1 => ∃ s, s < d ∧ nf.nestOcc [] s (s + 1) = false ∧ holeP d s (s + 1) i
    | 2 => holeP d lo hi i) (e := ta) fun k => by
      match k with
      | 0 => exact hbelow
      | 1 => exact hun
      | 2 => exact hholes
  refine NoBVar.mono (fun i hn => ?_) hall
  by_cases hid : i < d
  · by_cases hh : holeP d lo hi i
    · exact ⟨2, hh⟩
    · refine ⟨1, d - 1 - i, by omega, ?_, ⟨hid, by omega, by omega⟩⟩
      cases hm : nf.nestOcc [] (d - 1 - i) (d - 1 - i + 1)
      · rfl
      · exact absurd ⟨hid, by rw [show d - i = d - 1 - i + 1 by omega]; exact hm, hh⟩ hn
  · exact ⟨0, by omega⟩

/-- The body's output, one binder down, mentions no more than the Π's. -/
theorem mentNH_body {lo hi dep : Nat} {a nb : Expr} {bm : ConLeche.BinderMeta} :
    ∀ i, MentNH lo hi (dep + 1) nb i → liftM (MentNH lo hi dep (.forallE a (nb.abstract1 dep 0) bm)) i
  | 0, _ => trivial
  | i + 1, ⟨hlt, hm, hh⟩ => by
    refine ⟨by omega, ?_, fun h => hh (holeP_succ (i + 1) h)⟩
    simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true]
    refine Or.inr ?_
    rw [nestOcc_abstract1 (by omega) nb 0]
    rw [show dep + 1 - 1 - (i + 1) = dep - 1 - i by omega,
      show dep + 1 - (i + 1) = dep - i by omega] at hm
    exact hm

omit [SetTheory V] in
theorem InvOn.mono {M M' : Nat → Prop} {A : (Nat → V) → V} (h : InvOn M A) (hM : ∀ i, M i → M' i) :
    InvOn M' A :=
  fun ρ ρ' hag => h ρ ρ' fun i hi => hag i (hM i hi)

/-! ## The relation the run is proved along -/

/-- **The hole relation for accessibility** at depth `d` under the frames
`prog`: related frames satisfy the context and agree off the hole
positions; every frame's hole is blind in its key's parameters. -/
structure HoleRelA (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (prog : List NestHole)
    (d : Nat) (Δa : List AnnotTerm) (R : FrameRel V) : Prop where
  dom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ'
  agree : R.AgreesOff (holeP d ctx.nP (ctx.hiAt prog.length))
  frame : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ dsa,
    DenoteMetaSpine m.acval env φ d hk.key.ds dsa → FrameBlind R (d - 1 - (ctx.hiAt 0 + i)) dsa
  dsScoped : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
    Expr.WScoped (ctx.hiAt prog.length) x

theorem FrameBlind.underBoth {R : FrameRel V} {h : Nat} {ds : List AnnotTerm}
    (hb : FrameBlind R h ds) (A : AnnotTerm) :
    FrameBlind (R.underBoth A) (h + 1) (ds.map (AnnotTerm.liftN 1 · 0)) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩ is
  have hl : ∀ (σ : Nat → V), (ds.map (AnnotTerm.liftN 1 · 0)).map (interp V (cons x σ))
      = ds.map (interp V σ) := by
    intro σ
    rw [List.map_map]
    refine List.map_congr_left fun a _ => ?_
    show interp V (cons x σ) (a.liftN 1 0) = interp V σ a
    rw [interp_liftN]
    congr 1
  rw [hl, hl]
  exact hb ρ ρ' hR is

/-- **Under a binder** (a hole-free domain, or an earlier field): the
relation one level deeper, the bound value in the domain at both
frames. -/
theorem HoleRelA.underBoth {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List AnnotTerm}
    {R : FrameRel V} (h : HoleRelA m φ ctx prog d Δa R) (hd : ctx.hiAt prog.length ≤ d)
    (ta : AnnotTerm) :
    HoleRelA m φ ctx prog (d + 1) (ta :: Δa) (R.underBoth ta) where
  dom := by
    rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
    obtain ⟨h1, h2⟩ := h.dom ρ ρ' hR
    exact ⟨Sat_cons V h1 hx, Sat_cons V h2 hx'⟩
  agree := by
    intro σ σ' hr i hi
    exact (h.agree.underBoth ta) σ σ' hr i fun hs => hi (holeP_succ i hs)
  frame := by
    intro i key hk dsa' hsp
    have hlen : i < prog.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      simpa using this
    have hlt : ctx.hiAt 0 + i < d := by
      simp only [NestCtx.hiAt] at hd ⊢; omega
    obtain ⟨dsa, hdsa, rfl⟩ := DenoteMetaSpine.weaken_top
      (fun x hx => Expr.WScoped.mono hd (h.dsScoped i key hk x hx)) hsp
    rw [show d + 1 - 1 - (ctx.hiAt 0 + i) = d - 1 - (ctx.hiAt 0 + i) + 1 by omega]
    exact FrameBlind.underBoth (h.frame i key hk dsa hdsa) ta
  dsScoped := h.dsScoped

/-! ## The theorem -/

/-- A run of the positivity function (or of its recursive call one fuel
lower) which keeps the state invariant `I`, also when it ends in a
restart request, and whose reading is proved ACCESSIBLE when it does not
— with a bound reading only the non-hole positions the output mentions. -/
@[expose] def NestPosAcc (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (P : NestFieldKind → Prop) (I : NestState → Prop)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) (k : NestFieldKind)
    (nf : Expr) (st' : NestState),
    rec prog dep kb e st = .ok (k, nf, st') → P k →
    ctx.hiAt prog.length ≤ dep → Frame dep e → I st →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP m φ dep Δa e → denoteMeta m.acval env φ dep e = some ea → Graded V Δa ea →
      HoleRelA m φ ctx prog dep Δa R → I st' ∧ (st'.restart = none →
        ∃ A, AccOn R A ea ∧ InvOn (MentNH ctx.nP (ctx.hiAt prog.length) dep nf) A)

/-- **The container case**, as the premise the theorem takes: a
successful `nestCont` at a container reduct whose recursive call is
accessible makes the reduct's reading accessible, with a bound reading
only the reduct's non-hole positions (the output IS the reduct). -/
@[expose] def ContAcc (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (P : NestFieldKind → Prop) (I : NestState → Prop) (F : Nat)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)) :
    Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (w : Expr) (n : Name) (us : List Level)
    (st : NestState) (k : NestFieldKind) (st' : NestState),
    w.getAppFn = .const n us → ctx.names.contains n = false →
    nestCont ctx (fueledOps .verified F) env rec prog kb n us w.getAppArgs st = .ok (k, st') →
    P k →
    ctx.hiAt prog.length ≤ dep → Frame dep w → I st →
    ∀ {Δa : List AnnotTerm} {wa : AnnotTerm} {R : FrameRel V},
      CtxOkP m φ dep Δa w → denoteMeta m.acval env φ dep w = some wa → Graded V Δa wa →
      HoleRelA m φ ctx prog dep Δa R → I st' ∧ (st'.restart = none →
        ∃ A, AccOn R A wa ∧ InvOn (MentNH ctx.nP (ctx.hiAt prog.length) dep w) A)

/-- **THE THEOREM (non-container cases): a run of `nestPos` is
accessible.**  If the positivity function returns (at the pure verified
instantiation, at any fuel), leaving no restart request pending, then the
reading of its input is accessible along every accessibility hole
relation, with a bound reading only the non-hole positions of the
output.  By inversion of the run (`nestPos_sem`'s): the whnf step by
`red_sound`, then `const`, `pi` (by induction), `holeApp` and a frame's
hole; the container case is the premise `ContAcc`, given the theorem one
fuel lower. -/
theorem nestPos_acc (hin : RulesInputs V m φ) (ctx : NestCtx) (F : Nat)
    {P : NestFieldKind → Prop} {I : NestState → Prop}
    (hcont : ∀ rec, NestPosAcc m φ ctx P I rec → ContAcc m φ ctx P I F rec) :
    ∀ fuel, NestPosAcc m φ ctx P I (nestPos (fueledOps .verified F) env ctx fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog dep kb e st k nf st' hrun
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    intro prog dep kb e st k nf st' hrun hP hhi hfr hI Δa ea R hC hea hgr hR
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
      have hCw : CtxOkP m φ dep Δa w := hC.of_subset hsub
      suffices hw2 : I st' ∧ (st'.restart = none →
          ∃ A, AccOn R A wa ∧ InvOn (MentNH ctx.nP (ctx.hiAt prog.length) dep nf) A) from
        ⟨hw2.1, fun hc => by
          obtain ⟨A, hA, hinv⟩ := hw2.2 hc
          exact ⟨A, AccOn.of_eqOn (Q := Sat V Δa) hR.dom (fun ρ hρ => heq ρ hρ) hA, hinv⟩⟩
      by_cases hocc : w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false
      · refine ⟨?_, fun _ => ⟨_, (ConstOn.of_noBVar hR.agree
          (denoteMeta_noBVar_of_nestOcc dep w hfrw.1 hhi hocc hwa)).accOn, InvOn.const _ _⟩⟩
        rw [if_pos (by simpa using hocc)] at hrun
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        rw [← hrun.2.2]; exact hI
      rw [if_neg (by simpa using hocc)] at hrun
      split at hrun
      · -- `pi`
        rename_i a b mb
        by_cases ha : a.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = true
        · rw [if_pos ha] at hrun
          simp [throw, throwThe, MonadExceptOf.throw] at hrun
        rw [if_neg ha] at hrun
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
        obtain ⟨hws, hb, hLb⟩ := hfrw
        simp only [Expr.WScoped] at hws
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
        have hholes : NoBVar (holeP dep ctx.nP (ctx.hiAt prog.length)) ta :=
          denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi (by simpa using ha) hta
        have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree hholes
        obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
        have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
        split at hrun
        · simp at hrun
        rename_i v hv
        obtain ⟨k₁, nb, st₁⟩ := v
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl, rfl⟩ := hrun
        obtain ⟨hI', hB⟩ := ih prog (dep + 1) (kb + 1) _ st k₁ nb _ hv hP (by omega)
          (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hI hCop hba hgB (hR.underBoth hhi ta)
        refine ⟨hI', fun hc => ?_⟩
        obtain ⟨Ab, hAb, hinvb⟩ := hB hc
        refine ⟨_, AccOn.pi 0 _ hA hAb, InvOn.pi ?_ (InvOn.mono hinvb fun i hi => mentNH_body i hi)⟩
        refine noBVar_not_mentNH hws.1 hb.1 hholes (fun s _ hs => ?_) hta
        simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hs
        exact hs.1
      · -- a head applied to arguments
        rename_i hnotpi
        have hspine := Expr.mkAppN_getApp w
        split at hrun
        · rename_i i ty hfn
          rw [hfn] at hspine
          rw [← hspine] at hwa
          obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
          rw [denoteMeta_fvar] at hfa
          cases hfa
          have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
            have h0 := hfrw.1
            rw [← hspine] at h0
            exact (wScoped_mkAppN _ h0).2
          by_cases hmem : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
          · -- `holeApp`
            rw [if_pos hmem] at hrun
            by_cases hc : (w.getAppArgs.length == ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 &&
                List.take ctx.nP w.getAppArgs == ctx.params &&
                w.getAppArgs.all fun x => !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x)
                = true
            · rw [if_pos hc] at hrun
              simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
              refine ⟨by rw [← hrun.2.2]; exact hI, fun _ => ?_⟩
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              obtain ⟨-, hfree⟩ := hc
              have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
              exact ⟨_, AccOn.holeApp hvs, InvOn.const _ _⟩
            · rw [if_neg hc] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
          · rw [if_neg hmem] at hrun
            by_cases hfr' : (decide (ctx.hiAt 0 ≤ i) && decide (i < ctx.hiAt prog.length)) = true
            · -- a frame's hole
              rw [if_pos hfr'] at hrun
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hfr'
              split at hrun
              · simp [throw, throwThe, MonadExceptOf.throw] at hrun
              · rename_i key hk
                by_cases hpar : (decide (key.key.ds.length ≤ w.getAppArgs.length) &&
                    (List.take key.key.ds.length w.getAppArgs == key.key.ds)) = true
                · rw [if_pos hpar] at hrun
                  by_cases hidx : ((w.getAppArgs.drop key.key.ds.length).all fun x =>
                      !Expr.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) x) = true
                  · rw [if_pos hidx] at hrun
                    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
                    refine ⟨by rw [← hrun.2.2]; exact hI, fun _ => ?_⟩
                    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpar
                    simp only [List.all_eq_true, Bool.not_eq_true'] at hidx
                    rw [← List.take_append_drop key.key.ds.length w.getAppArgs] at hsp
                    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
                    have hvs₂ := constOn_spine hR.agree hhi hsp₂ fun a ha =>
                      ⟨hwsargs a (List.mem_of_mem_drop ha), by simpa using hidx a ha⟩
                    have hsp₁' : DenoteMetaSpine m.acval env φ dep key.key.ds vs₁ := by
                      rw [← hpar.2]; exact hsp₁
                    have hh := hR.frame (i - ctx.hiAt 0) key hk vs₁ hsp₁'
                    rw [show dep - 1 - (ctx.hiAt 0 + (i - ctx.hiAt 0)) = dep - 1 - i by omega] at hh
                    exact ⟨_, AccOn.holeAppArgs hh hvs₂, InvOn.const _ _⟩
                  · rw [if_neg hidx] at hrun
                    simp [throw, throwThe, MonadExceptOf.throw] at hrun
                · rw [if_neg hpar] at hrun
                  simp [throw, throwThe, MonadExceptOf.throw] at hrun
            · rw [if_neg hfr'] at hrun
              simp [throw, throwThe, MonadExceptOf.throw] at hrun
        · -- `contApp`
          rename_i n us hfn
          by_cases hnm : ctx.names.contains n = true
          · rw [if_pos hnm] at hrun
            simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rw [if_neg hnm] at hrun
          split at hrun
          · simp at hrun
          rename_i v hv
          obtain ⟨k₁, st₁⟩ := v
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl, rfl⟩ := hrun
          exact hcont _ ih prog dep kb w n us st k₁ _ hfn (by simpa using hnm) hv hP hhi
            hfrw hI hCw hwa hgw hR
        · simp [throw, throwThe, MonadExceptOf.throw] at hrun

end ConLeche.Model
