module

public import ConLeche.Model.Inductives.ContCtor
public import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# A container frame's walk (lane CONTSEM, steps 3–4)

`nestCtors` inverted constructor by constructor (`nestCtors_sem`), the
state invariant threaded, and the frame lemma (`frame_sem`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

theorem nodup_of_nameNodup : ∀ {ns : List Name}, ConLeche.Name.nodup ns = true → ns.Nodup
  | [], _ => List.nodup_nil
  | n :: ns, h => by
    simp only [ConLeche.Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_of_nameNodup h.2⟩
    have := h.1
    simp [hm] at this

/-- What a successful frame walk leaves of one constructor: its level
parameters distinct, and its instantiated, abstracted type read, walked
positively along the frame relation, its result the hole applied with
hole-free indices. -/
@[expose] def CtorWalked (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (hi : Nat)
    (us : List Level) (ds : List Expr) (nPc : Nat) (sub : Name → List Level → Option Expr)
    (R : FrameRel V) (x : ConstantVal × Nat) : Prop :=
  x.1.levelParams.Nodup ∧ ∃ crest ca cur,
    instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
      = some crest ∧
    denoteMeta m.acval env φ hi crest = some ca ∧ ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop nPc).all (fun a => !a.nestOcc ctx.names ctx.nP hi) = true ∧
    PiPosThen (ResultAt m φ ctx.nP hi (hi + x.2) cur) x.2 R ca

/-- **A frame's constructors, walked** (see the module docstring): the
state invariant is kept, and when no restart is pending every
constructor was walked positively. -/
theorem nestCtors_sem {ctx : NestCtx} {F : Nat} {I : NestState → Prop}
    {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
    (hrec : NestPosSem m φ ctx (fun _ => True) I rec)
    {prog : List NestHole} {hi : Nat} {us : List Level} {ds : List Expr} {nPc : Nat}
    {sub : Name → List Level → Option Expr} (hhi : ctx.hiAt prog.length = hi)
    {Δ : List AnnotTerm} {R : FrameRel V} (hR : HoleRel m φ ctx prog hi Δ R)
    (hprem : ∀ (x : ConstantVal × Nat) (crest : Expr),
      instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
        = some crest →
      (∃ ty, ConLeche.inferTypeCore .verified env F hi crest = .ok ty) →
      ∃ ca, Frame hi crest ∧ CtxOkP m φ hi Δ crest ∧
        denoteMeta m.acval env φ hi crest = some ca ∧ Graded V Δ ca) :
    ∀ (ctors : List (ConstantVal × Nat)) (st st' : NestState),
      ConLeche.nestCtors ctx (fueledOps .verified F) env rec prog hi us ds nPc sub ctors st
        = .ok st' → I st →
      I st' ∧ (st'.restart = none → ∀ x ∈ ctors, CtorWalked m φ ctx hi us ds nPc sub R x) := by
  intro ctors
  induction ctors with
  | nil =>
    intro st st' h hI
    simp only [ConLeche.nestCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hI, fun _ x hx => nomatch hx⟩
  | cons x cs ih =>
    intro st st' h hI
    obtain ⟨cv, nF⟩ := x
    simp only [ConLeche.nestCtors, bind, Except.bind] at h
    have hnd : Name.nodup cv.levelParams = true := by
      rcases hb : Name.nodup cv.levelParams
      · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      · rfl
    rw [if_pos hnd] at h
    have hnd' : cv.levelParams.Nodup := nodup_of_nameNodup hnd
    split at h
    · simp at h
    rename_i crest hcrest
    have hcrest' := unwrapOr_ok hcrest
    split at h
    · simp at h
    rename_i ty hty
    split at h
    · simp at h
    rename_i sv hsv
    obtain ⟨ca, hfr, hC, hca, hgr⟩ := hprem (cv, nF) crest hcrest' ⟨ty, hty⟩
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨ks, nds, cur, st₁⟩ := r
    obtain ⟨hI₁, hpos⟩ := nestFields_sem (P := fun _ => True) hrec nF 0 crest st ks nds cur st₁
      (hi + nF) hr (fun _ _ => trivial) (by omega) (by rw [hhi]; omega) hfr hI hC hca hgr
      (by simpa using hR)
    dsimp only at h
    by_cases hrs : st₁.restart.isSome = true
    · rw [if_pos hrs] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨hI₁, fun hc => ?_⟩
      rw [hc] at hrs; exact nomatch hrs
    rw [if_neg hrs] at h
    have hc₁ : st₁.restart = none := by simpa using hrs
    split at h
    · rename_i hok
      obtain ⟨hI', hrest⟩ := ih st₁ st' h hI₁
      refine ⟨hI', fun hc x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Bool.and_eq_true] at hok
        refine ⟨hnd', crest, ca, cur, hcrest', hca, hok.1, hok.2, ?_⟩
        have := hpos hc₁
        rwa [hhi] at this
      · exact hrest hc x hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h

end ConLeche.Model
