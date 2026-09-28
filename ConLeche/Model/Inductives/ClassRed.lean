module

public import ConLeche.Verify.Inductives.ClassInv
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
public import ConLeche.Semantics.ConstsBound
import ConLeche.Model.Inductives.ErasureKit

public section

/-!
# The class check's normal form READS like its input (P2d, DESIGN CLASSCHECK / P2D4)

The class check's walk (`classPos`, check 3) reduces every field of an
abstracted crest with the kernel's `whnf` and returns the field's NORMAL
FORM.  By induction on the flat derivation (`FieldD`), the normal form
reads, at every frame satisfying the context, as the crest does
(`red_sound` at each whnf step): one field — framed, its leaves the
input's, reading graded and equal to the input; the telescope — the
crest a Π-tower over `abD`, the closed normal form a Π-tower over `abN`,
same binder bits and body, `FieldsEqOn Δ abD abN` (`fieldD_red`, the
port of the old walk's `posD_red`, whose generic pieces live here now).
The normal form is what a bound reading only the ordinary fields (U4)
is stated of — the accessibility of a crest's fit.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx BinderMeta closeTelescope fueledOps ClassInfo ClassJ
  FieldD)

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

variable {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **The whnf step reads like its input** (`red_sound`). -/
theorem red_whnf (hin : RulesInputs V m φ) {F dep : Nat} {e w : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok w) (hfr : Frame dep e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} (hC : CtxOkP m φ dep Δa e)
    (hea : denoteMeta m.acval env φ dep e = some ea) (hgr : Graded V Δa ea) :
    Frame dep w ∧ LeavesSub w e ∧ ∃ nda, denoteMeta m.acval env φ dep w = some nda ∧
      Graded V Δa nda ∧ ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ nda := by
  obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ := red_sound hin
    (ConLeche.Rules.whnf_bridge (show ConLeche.whnf .verified env F dep e = .ok w from hw)) hfr
    hC.toCtxOk hea hgr
  exact ⟨hfrw, hsub, wa, hwa, hgw, heq⟩

/-! ## The derivation's outputs read like its inputs -/

variable {env : Env} {m : EnvModel V env} {φ : Name → Nat}

section Motive

variable (m φ)

/-- **What a derivation proves of its outputs** (see the module
docstring): a field's output framed, with the input's leaves, reading
graded and equal to the input at every satisfying frame; a telescope's
closed normal form a Π-tower reading like the input's field by field. -/
@[expose] def ClassRedJ : ClassJ → Prop
  | .field dep _ e _ nd =>
    Frame dep e → ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
      CtxOkP m φ dep Δa e → denoteMeta m.acval env φ dep e = some ea → Graded V Δa ea →
      Frame dep nd ∧ LeavesSub nd e ∧ ∃ nda, denoteMeta m.acval env φ dep nd = some nda ∧
        Graded V Δa nda ∧ ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ nda
  | .tele base n j cur _ nds res =>
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
        LeavesSub (closeTelescope nds (base + j) res) cur

end Motive

/-- **The derivation's outputs read like its inputs** (see the module
docstring), by induction on the derivation. -/
theorem fieldD_red (hin : RulesInputs V m φ) {ctx : NestCtx} {cls : List ClassInfo} {hi F : Nat} :
    ∀ {J : ClassJ}, FieldD (fueledOps .verified F) env ctx cls hi J → ClassRedJ m φ J := by
  intro J h
  induction h with
  | @const dep kb e w hw hocc =>
    intro hfr Δa ea hC hea hgr
    split
    · exact red_whnf hin hw hfr hC hea hgr
    · exact ⟨hfr, fun _ h => h, ea, hea, hgr, fun _ _ => rfl⟩
  | @pi dep kb e a b mb k nb hw hocc ha hb ihb =>
    intro hfr Δa ea hC hea hgr
    obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ := red_whnf hin hw hfr hC hea hgr
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCw : CtxOkP m φ dep Δa (.forallE a b mb) := hC.of_subset hsub
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    obtain ⟨hfrn, hsubn, nba, hnba, hgn, heqn⟩ :=
      ihb (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hCop hba hgB
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
  | memberHole hw => intro hfr _ _ hC hea hgr; exact red_whnf hin hw hfr hC hea hgr
  | classHole hw => intro hfr _ _ hC hea hgr; exact red_whnf hin hw hfr hC hea hgr
  | teleNil =>
    intro hfr Δa ca hC hca hgr
    exact ⟨[], [], ca, rfl, by simpa [closeTelescope, mkPisAV] using hca, rfl, rfl, rfl, trivial,
      by simpa [mkPisAV] using hgr, by simpa [closeTelescope] using hfr,
      fun l hl => by simpa [closeTelescope] using hl⟩
  | @teleCons base n j a b bm k nd ks nds res _ _ iha ihb =>
    intro hfr Δa ca hC hca hgr
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    -- the field
    obtain ⟨hfrn, hsubn, nda, hnda, hgn, heqn⟩ := iha ⟨hws.1, hb.1, hLa⟩ hC.forallE_ty hta hgA
    -- the rest, one binder down
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd
    rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
    obtain ⟨abD, abN, B, hbaE, hrd, hlD, hlN, hbits, hEq, hgN, hfrc, hsubc⟩ :=
      ihb hfr' hCop hba hgB
    subst hbaE
    rw [show base + (j + 1) = base + j + 1 by omega] at hrd hfrc hsubc
    obtain ⟨hwsc, hbc, hLc⟩ := hfrc
    have hbnd : (closeTelescope nds (base + j + 1) res).looseBVarsBounded 0 = true := hbc
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

end ConLeche.Model
