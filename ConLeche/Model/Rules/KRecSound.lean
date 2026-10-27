module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of the relaxed K-like rule (tasks #367, #368)

See `Red.kRec` (`Rules/Rel.lean`); the boost translation's `Eq.rec`
steps use it.

The ι step's K branch (`Red.iota_sound`) without the major: at a K rule
the stored recursor's ι facts (`RecRuleExtra`) give the rule's law at the
recursor's own parameters for any major value in the major's domain, so
the major is never read, and nothing about it — not its reduction to the
constructor, not its type — is needed.  What remains is the recursor's
telescope fitting the redex's spine (the arity certificate, as at every
ι step).
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantVal RecRule)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem Red.kRec_sound (hin : RulesInputs V m φ) {d : Nat} {e : Expr} {c : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rl : RecRule}
    (hhead : e.getAppFn = .const c us)
    (hrec : env.find? c = some (.recInfo cv mI rP [rl]))
    (hk : rl.k = true) (_hnf : rl.nfields = 0)
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = cv.levelParams.length)
    (hcertR : TeleAritySem m φ d (cv.type.instantiateLevelParams cv.levelParams us)
      e.getAppArgs) :
    RedSem m φ d e
      (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us) (e.getAppArgs.take rP)) := by
  intro hf Δa ea hC hea
  have hrmem : rl ∈ [rl] := List.mem_cons_self
  obtain ⟨hrPle, hlaw0, hextra⟩ := hin.rec_rules c cv mI rP [rl] hrec rl hrmem
  obtain ⟨Ra, hRa0, -, -, -⟩ := hlaw0 us hus
  obtain ⟨hRaD, hRnf, hRbd⟩ := recRhs_depthK hrec hrmem hRa0
  have hfrE := frame_spine hf hC
  have hea' := hea
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp e).symm, hhead] at hea'
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denote_mkAppN_inv hea'
  rw [denote_const hrec (show us.length = _ from hus)] at hvc
  obtain rfl : vc = m.acval c (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hvc).symm
  have hxsLen : xs.length = mI + 1 := by rw [← hspx.length]; exact hlen
  obtain ⟨TVa, hTVaD, hokTVa, hmemR, hnfR, hbdR⟩ :=
    constTy_pkg hin.const_ty hrec (show us.length = _ from hus)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVaD hmemR hnfR hbdR
  obtain ⟨hfR, hCR⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfR hbdR hC.1
  obtain ⟨restR, hfitR⟩ :=
    hcertR (fa := m.acval c (Level.substFn φ cv.levelParams us))
      hfR hCR (hTVaD d) hfrE hspx
  obtain ⟨hK, -⟩ := hextra us hus TVa (hTVaD 0)
  have hspOut : DenoteSpine m.acval env φ d (e.getAppArgs.take rP) (xs.take rP) :=
    hspx.take rP
  refine ⟨frame_mkAppN ⟨ConLeche.Expr.WScoped.of_not_hasFvar hRnf, hRbd,
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hRnf⟩
      (fun y hy => (hfrE y (List.mem_of_mem_take hy)).1),
    leavesSub_mkAppN (leavesSub_of_not_hasFvar hRnf)
      (fun y hy l hl => ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_take hy) l hl),
    _, denote_mkAppN hspOut (hRaD d), fun ρ hρ hL hg hne => ?_⟩
  obtain ⟨-, hoX⟩ := hoist_spineV xs hg
  obtain ⟨hfitRVal0, -⟩ :=
    hfitR ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfR))
      (leavesGr_spine hL) (hokTVa ρ) hoX ⟨hg, hmemR ρ, hne⟩
  have hsplit := take_getD_splitAK hxsLen
  have hfitRVal : TeleFitPA V ρ TVa (xs.take mI ++ [xs.getD mI default]) restR := by
    rw [← hsplit]; exact hfitRVal0
  have hoX0 : ∀ x ∈ xs.take mI, WellDenoted V ρ x :=
    fun x hx => hoX x (List.mem_of_mem_take hx)
  have hxs0len : (xs.take mI).length = mI := by
    rw [List.length_take, hxsLen]; omega
  have hsubj0 : interp V ρ (Term.mkAppN
      (m.acval c (Level.substFn φ cv.levelParams us)) xs)
      = interp V ρ (Term.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [xs.getD mI default])) := by
    rw [← hsplit]
  obtain ⟨-, hKlaw⟩ := hK hk
  obtain ⟨heqK, htrK⟩ := hKlaw Ra hRa0 ρ (xs.take mI) _ restR hxs0len hfitRVal hoX0
  have hred : xs.take rP = (xs.take mI).take rP := by
    rw [List.take_take, Nat.min_eq_left hrPle]
  rw [hred]
  exact ⟨htrK hoX0, hsubj0.trans heqK⟩

end ConLeche.Model.Rules
