module

public import ConLeche.Model.Inductives.NestPosOut
public import ConLeche.Model.Inductives.NestPosMono
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

/-! ## Field lists that read alike -/

/-- **Two field lists read alike along every satisfying prefix**: the
first fields at every frame satisfying `Δ`, the rest under the first
field (either one: they read alike there). -/
@[expose] def FieldsEqOn (V : Type w) [SetTheory V] :
    List AnnotTerm → List AnnotTerm → List AnnotTerm → Prop
  | _, [], [] => True
  | Δ, A :: As, B :: Bs =>
    (∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B) ∧ FieldsEqOn V (A :: Δ) As Bs
  | _, _, _ => False

theorem FieldsEqOn.length_eq :
    ∀ {Δ As Bs : List AnnotTerm}, FieldsEqOn V Δ As Bs → As.length = Bs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => by simp [FieldsEqOn.length_eq h.2]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- A context whose head reads alike is satisfied alike. -/
theorem sat_cons_congr {Δ : List AnnotTerm} {A B : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B) {ρ : Nat → V}
    (hs : Sat V (A :: Δ) ρ) : Sat V (B :: Δ) ρ := by
  intro i Aa hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have := hs 0 A rfl
    rw [h _ (Sat_tail hs)] at this
    simpa using this
  | succ i => exact hs (i + 1) Aa (by simpa using hi)

/-- Fitting spines agree along field lists that read alike. -/
theorem FieldsEqOn.spineFit_iff :
    ∀ {Δ As Bs : List AnnotTerm}, FieldsEqOn V Δ As Bs → ∀ {ρ : Nat → V}, Sat V Δ ρ →
      ∀ fs : List V, SpineFit ρ As fs ↔ SpineFit ρ Bs fs
  | _, [], [], _, _, _, fs => Iff.rfl
  | _, A :: As, B :: Bs, h, ρ, hρ, [] => by simp [SpineFit]
  | Δ, A :: As, B :: Bs, h, ρ, hρ, x :: fs => by
    simp only [SpineFit]
    constructor
    · rintro ⟨hx, hfs⟩
      exact ⟨h.1 ρ hρ ▸ hx, (FieldsEqOn.spineFit_iff h.2 (Sat_cons V hρ hx) fs).mp hfs⟩
    · rintro ⟨hx, hfs⟩
      have hx' : x ∈ˢ interp V ρ A := (h.1 ρ hρ).symm ▸ hx
      exact ⟨hx', (FieldsEqOn.spineFit_iff h.2 (Sat_cons V hρ hx') fs).mpr hfs⟩
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim


/-- Spines fit two field lists alike when the fields read alike at every
prefix. -/
theorem spineFit_congr_all {σ ρ : Nat → V} :
    ∀ {Fs Gs : List AnnotTerm}, Fs.length = Gs.length →
      (∀ (i : Nat) (as : List V), i < Fs.length → as.length = i →
        interp V (consList as σ) (Fs.getD i default)
          = interp V (consList as ρ) (Gs.getD i default)) →
      ∀ fs : List V, SpineFit σ Fs fs ↔ SpineFit ρ Gs fs
  | [], [], _, _, fs => by cases fs <;> simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, [] => by simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, x :: fs => by
    simp only [SpineFit]
    have h0 : interp V σ F = interp V ρ G := h 0 [] (by simp) rfl
    rw [h0]
    refine and_congr_right fun _ => spineFit_congr_all (σ := cons x σ) (ρ := cons x ρ)
      (by simpa using hl) (fun i as hi has => ?_) fs
    have := h (i + 1) (x :: as) (by simp; omega) (by simp [has])
    simpa using this
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Spines fit two field lists alike when the fields read alike along
every prefix fitting the second list. -/
theorem spineFit_congr_fit {σ ρ : Nat → V} :
    ∀ {Fs Gs : List AnnotTerm}, Fs.length = Gs.length →
      (∀ (i : Nat) (as : List V), i < Fs.length → as.length = i → SpineFit ρ (Gs.take i) as →
        interp V (consList as σ) (Fs.getD i default)
          = interp V (consList as ρ) (Gs.getD i default)) →
      ∀ fs : List V, SpineFit σ Fs fs ↔ SpineFit ρ Gs fs
  | [], [], _, _, fs => by cases fs <;> simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, [] => by simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, x :: fs => by
    simp only [SpineFit]
    have h0 : interp V σ F = interp V ρ G := h 0 [] (by simp) rfl (by simp [SpineFit])
    rw [h0]
    refine and_congr_right fun hx => spineFit_congr_fit (σ := cons x σ) (ρ := cons x ρ)
      (by simpa using hl) (fun i as hi has hfit => ?_) fs
    have := h (i + 1) (x :: as) (by simp; omega) (by simp [has])
      (by simp only [List.take_succ_cons, SpineFit]; exact ⟨hx, hfit⟩)
    simpa using this
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Along a prefix fitting the first list, the next fields read alike. -/
theorem FieldsEqOn.getD_eq :
    ∀ {Δ As Bs : List AnnotTerm}, FieldsEqOn V Δ As Bs → ∀ {ρ : Nat → V}, Sat V Δ ρ →
      ∀ (l : Nat) (as : List V), l < As.length → SpineFit ρ (As.take l) as →
        interp V (consList as ρ) (As.getD l default) = interp V (consList as ρ) (Bs.getD l default)
  | _, A :: _, B :: _, h, ρ, hρ, 0, as, _, hfit => by
    cases as with
    | nil => exact h.1 ρ hρ
    | cons _ _ => simp [SpineFit] at hfit
  | _, A :: As, B :: Bs, h, ρ, hρ, l + 1, as, hl, hfit => by
    cases as with
    | nil => simp [SpineFit] at hfit
    | cons a as =>
      simp only [List.take_succ_cons, SpineFit] at hfit
      simp only [consList_cons, List.getD_cons_succ]
      exact FieldsEqOn.getD_eq h.2 (Sat_cons V hρ hfit.1) l as (by simpa using hl) hfit.2
  | _, [], _, _, _, _, _, _, hl, _ => by simp at hl
  | _, _ :: _, [], h, _, _, _, _, _, _ => h.elim

/-- Two Π-towers over field lists that read alike, with the same binder
data and the same body, read alike. -/
theorem interp_mkPisAV_congr :
    ∀ {Δ : List AnnotTerm} (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) →
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ (mkPisAV abD B) = interp V ρ (mkPisAV abN B)
  | _, [], [], _, _, _, _, _ => rfl
  | Δ, d :: abD, e :: abN, B, hb, h, ρ, hρ => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hb
    obtain ⟨⟨h1, h2⟩, hb⟩ := hb
    simp only [mkPisAV, interp_pi, h2]
    rw [h.1 ρ hρ]
    refine piR_congr fun x hx => ?_
    have hx' : x ∈ˢ interp V ρ d.2.2 := (h.1 ρ hρ).symm ▸ hx
    exact interp_mkPisAV_congr abD abN B hb h.2 _ (Sat_cons V hρ hx')
  | _, [], _ :: _, _, hb, _, _, _ => by simp at hb
  | _, _ :: _, [], _, hb, _, _, _ => by simp at hb

/-- The relation under a binder depends only on the binder's reading at
the relation's frames. -/
theorem under_eq_of_eqOn {Δ : List AnnotTerm} {A B : AnnotTerm} {R : FrameRel V}
    (h : ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B)
    (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') : R.under A = R.under B := by
  funext σ σ'
  apply propext
  constructor
  · rintro ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    exact ⟨x, ρ, ρ', rfl, rfl, hR, by rwa [← h ρ (hdom ρ ρ' hR).1]⟩
  · rintro ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    exact ⟨x, ρ, ρ', rfl, rfl, hR, by rwa [h ρ (hdom ρ ρ' hR).1]⟩

/-- Field-wise positivity moves along field lists that read alike, and
so does the relation under all the fields. -/
theorem FieldsEqOn.teleMonoOn :
    ∀ {Δ As Bs : List AnnotTerm} {R : FrameRel V}, FieldsEqOn V Δ As Bs →
      (∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') → TeleMonoOn R As →
      TeleMonoOn R Bs ∧ R.underTele As = R.underTele Bs
  | _, [], [], _, _, _, _ => ⟨trivial, rfl⟩
  | Δ, A :: As, B :: Bs, R, h, hdom, hm => by
    obtain ⟨hA, hAs⟩ := hm
    have hdom' : ∀ σ σ', R.under A σ σ' → Sat V (A :: Δ) σ ∧ Sat V (A :: Δ) σ' := by
      rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
      exact ⟨Sat_cons V (hdom ρ ρ' hR).1 hx, Sat_cons V (hdom ρ ρ' hR).2 (hA ρ ρ' hR x hx)⟩
    obtain ⟨hBs, hU⟩ := FieldsEqOn.teleMonoOn h.2 hdom' hAs
    have hUE := under_eq_of_eqOn h.1 hdom
    refine ⟨⟨MonoOn.of_eqOn (Q := Sat V Δ) hdom (fun ρ hρ => (h.1 ρ hρ).symm) hA, ?_⟩, ?_⟩
    · rw [← hUE]; exact hBs
    · show (R.under A).underTele As = (R.under B).underTele Bs
      rw [hU, hUE]
  | _, [], _ :: _, _, h, _, _ => h.elim
  | _, _ :: _, [], _, h, _, _ => h.elim

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
