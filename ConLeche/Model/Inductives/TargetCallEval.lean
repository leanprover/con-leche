module

public import ConLeche.Model.Inductives.TargetNodeTie
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Semantics.Tower.TowerMk
import ConLeche.Verify.Shift
public import ConLeche.Model.Inductives.TargetCallTie
import ConLeche.Model.Inductives.TargetCallWalk

public section

/-!
# A field's call, read at a walk valuation (lane NESTIND, session 27)

At a walk valuation `σN` of a constructor's frames — the rule's prefix
parameters at the block's parameters, the rule's outer frame above the
holes — and a field lying in its walked normal form's reading:

* `fieldCall_core` — the call's target (the field applied along the call's
  telescope spine `bs`) lies in the walk leaf's head applied to its
  arguments, read at the walk valuation extended by the earlier fields and
  `bs`; the leaf's hole-free index arguments read as the call's indices
  (`callWalkSem` at the substitution `callSubst`, its agreement
  `wStar_agree`);
* `argsA_split` — such an argument reading is the key parameters' readings
  at the walk valuation, then the call's indices;
* `headRead_fvar` — a head variable reads as the walk valuation's entry.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole BinderMeta nestHoleConst)

universe w

variable {V : Type w} [SetTheory V]

/-- **The one substitution's readings at the rule's depth**: every entry
below the field is scoped, bvar-closed and read. -/
theorem callSubst_reads {env : Env} (m : EnvModel V env) (ψ : Name → Nat) {ctx : NestCtx}
    {prog : List NestHole} {rP : Nat} {fvsF : List Expr} (hnP : ctx.nP ≤ rP)
    (hfvF : ∀ l, l < fvsF.length → ∃ ty, fvsF[l]? = some (.fvar (rP + l) ty))
    (hfvW : ∀ x ∈ fvsF, Expr.WScoped (rP + fvsF.length) x)
    (hread : NodeHolesRead env ctx prog) {i : Nat} (hi : i ≤ fvsF.length) :
    ∀ v, v < ctx.hiAt prog.length + i →
      Expr.WScoped (rP + fvsF.length) (callSubst ctx prog fvsF v) ∧
      (callSubst ctx prog fvsF v).looseBVarsBounded 0 = true ∧
      denoteMeta m.acval env ψ (rP + fvsF.length) (callSubst ctx prog fvsF v)
        = some ((denoteMeta m.acval env ψ (rP + fvsF.length) (callSubst ctx prog fvsF v)).getD
          default) := by
  intro v hv
  by_cases h1 : v < ctx.nP
  · simp only [callSubst, if_pos h1]
    refine ⟨by simp [Expr.WScoped]; omega, rfl, ?_⟩
    rw [denoteMeta_fvar]; rfl
  by_cases h2 : v < ctx.hiAt prog.length
  · obtain ⟨n, us, hc⟩ := nestHoleConst_hole (prog := prog) (Nat.le_of_not_lt h1) h2
    simp only [callSubst, if_neg h1, if_pos h2, hc, Option.getD_some]
    have hmem : Expr.const n us ∈ nodeHoleConsts ctx prog := by
      rw [nestHoleConst_eq_holeMap] at hc
      unfold holeMap at hc
      rw [if_pos (Nat.le_of_not_lt h1)] at hc
      exact List.mem_of_getElem? hc
    obtain ⟨n', us', ci, he, hf, hl⟩ := hread _ hmem
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by simpa using he
    refine ⟨by simp [Expr.WScoped], rfl, ?_⟩
    rw [denoteMeta_const hf hl]; rfl
  · have hl : v - ctx.hiAt prog.length < fvsF.length := by omega
    obtain ⟨ty, hty⟩ := hfvF _ hl
    simp only [callSubst, if_neg h1, if_neg h2, hty, Option.getD_some]
    refine ⟨hfvW _ (List.mem_of_getElem? hty), rfl, ?_⟩
    rw [denoteMeta_fvar]; rfl

set_option maxHeartbeats 1600000 in
/-- **A field's call, read** (see the module docstring). -/
theorem fieldCall_core {env : Env} (m : EnvModel V env) (ψ : Name → Nat)
    {ctx : NestCtx} {prog : List NestHole} {i rP : Nat} {fvsF : List Expr}
    {teleW tele : List (Expr × BinderMeta)} {leafC w : Expr}
    (htl : tele.length = teleW.length)
    (htel : ∀ (l : Nat) (p p' : Expr × BinderMeta), tele[l]? = some p → teleW[l]? = some p' →
      p.2 = p'.2 ∧ Expr.ErasedEq p.1 (Expr.substFvars (ctx.hiAt prog.length + i)
        (rP + fvsF.length) (callSubst ctx prog fvsF) p'.1))
    (hteleHF : ∀ p ∈ teleW, p.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false ∧
      Expr.fvarsBelow (ctx.hiAt prog.length + i) p.1)
    (hopen : ∀ os, LocList (ctx.hiAt prog.length + i) teleW.length os →
      Expr.ErasedEq (leafC.instantiateList os 0) w)
    (hwF : Expr.fvarsBelow (ctx.hiAt prog.length + i + teleW.length) w)
    {P idxR : List Expr}
    (hargs : ∀ (q : Nat) (xM xW : Expr), (P ++ idxR)[q]? = some xM → w.getAppArgs[q]? = some xW →
      Expr.ErasedEq xM (Expr.substFvars (ctx.hiAt prog.length + i) (rP + fvsF.length)
        (callSubst ctx prog fvsF) xW))
    (hnP : ctx.nP ≤ rP)
    (hfvF : ∀ l, l < fvsF.length → ∃ ty, fvsF[l]? = some (.fvar (rP + l) ty))
    (hfvW : ∀ x ∈ fvsF, Expr.WScoped (rP + fvsF.length) x)
    (hread : NodeHolesRead env ctx prog) (hi : i < fvsF.length)
    {nda : AnnotTerm}
    (hnda : denoteMeta m.acval env ψ (ctx.hiAt prog.length + i) (Expr.mkPisOf teleW leafC)
      = some nda)
    {xs fs : List V} {ρ σN : Nat → V} (hxl : xs.length = rP) (hfl : fs.length = fvsF.length)
    (hpar : ∀ v, v < ctx.nP → σN (ctx.hiAt prog.length - 1 - v) = xs.getD v pt)
    (htail : ∀ q, σN (q + ctx.hiAt prog.length) = ρ q)
    (hf : fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda)
    (hval : AnnotValid V (consList (fs.take i) σN) nda)
    {bs : List V}
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms m.acval env ψ (rP + fvsF.length) [] (tele.map (·.1))).getD []) bs) :
    bs.length = tele.length ∧
    ∃ (ha : AnnotTerm) (argsA : List AnnotTerm),
      denoteMeta m.acval env ψ (ctx.hiAt prog.length + i + bs.length) w.getAppFn = some ha ∧
      DenoteMetaSpine m.acval env ψ (ctx.hiAt prog.length + i + bs.length) w.getAppArgs argsA ∧
      bs.foldl app (fs.getD i pt) ∈ˢ
        (argsA.map (interp V (consList bs (consList (fs.take i) σN)))).foldl app
          (interp V (consList bs (consList (fs.take i) σN)) ha) ∧
      (∀ (l : Nat) (xR xW : Expr) (xa : AnnotTerm), idxR[l]? = some xR →
        w.getAppArgs[P.length + l]? = some xW → argsA[P.length + l]? = some xa →
        xW.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false →
        interp V (consList bs (consList (xs ++ fs) ρ))
            ((denoteMeta m.acval env ψ (rP + fvsF.length + bs.length) xR).getD default)
          = interp V (consList bs (consList (fs.take i) σN)) xa) := by
  have hs := callSubst_reads m ψ (prog := prog) hnP hfvF hfvW hread (Nat.le_of_lt hi)
  have hnh : ctx.nP ≤ ctx.hiAt prog.length := by simp [ConLeche.NestCtx.hiAt]; omega
  have hag := wStar_agree (nP := ctx.nP) (hiP := ctx.hiAt prog.length) (i := i) (rP := rP)
    (B := rP + fvsF.length)
    (x := fun v => (denoteMeta m.acval env ψ (rP + fvsF.length) (callSubst ctx prog fvsF v)).getD
      default)
    (xs := xs) (fs := fs) (by rw [hfl]) hxl hnP (by omega) hnh
    (fun v hv => by
      simp only [callSubst, if_pos hv]
      rw [denoteMeta_fvar]; rfl)
    (fun l hl => by
      have h1 : ¬ ctx.hiAt prog.length + l < ctx.nP := by omega
      have h2 : ¬ ctx.hiAt prog.length + l < ctx.hiAt prog.length := by omega
      obtain ⟨ty, hty⟩ := hfvF l (by omega)
      simp only [callSubst, if_neg h1, if_neg h2, Nat.add_sub_cancel_left, hty, Option.getD_some]
      rw [denoteMeta_fvar]; rfl)
    (ρ := ρ) (σW := σN) hpar htail
  exact callWalkSem m ψ htl htel hteleHF hopen hwF hargs hs hnda hf hval hag hbs

/-- **An argument spine's reading, split**: the first `n` arguments,
scoped at `D0`, read at the valuation below the extension `L`; the rest
as given. -/
theorem argsA_split {env : Env} (m : EnvModel V env) (ψ : Name → Nat) {D0 D' : Nat}
    {args : List Expr} {argsA : List AnnotTerm}
    (hsp : DenoteMetaSpine m.acval env ψ D' args argsA) {n : Nat} (hn : n ≤ args.length)
    (hpre : ∀ x ∈ args.take n, Expr.WScoped D0 x)
    {L : List V} (hL : D' = D0 + L.length) (σ : Nat → V)
    {isR : List V} (hlen : isR.length = args.length - n)
    (htail : ∀ (l : Nat) (xa : AnnotTerm), argsA[n + l]? = some xa →
      isR[l]? = some (interp V (consList L σ) xa)) :
    argsA.map (interp V (consList L σ))
      = (args.take n).map (fun x => interp V σ ((denoteMeta m.acval env ψ D0 x).getD default))
        ++ isR := by
  have hl := hsp.length
  have hmap := denoteMetaSpine_eq_map hsp
  apply List.ext_getElem?
  intro q
  by_cases hq : q < n
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_map,
      List.getElem?_take_of_lt hq]
    obtain ⟨x, hx⟩ : ∃ x, args[q]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨v, hv, hdv⟩ := denoteMetaSpine_getElem?' hsp q x hx
    rw [hv, hx, Option.map_some, Option.map_some]
    have hw : Expr.WScoped D0 x :=
      hpre x (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hq]; exact hx))
    have hlift := denoteMeta_lift (env := env) (φ := ψ) m.acval_closed hw D' (by omega)
    rw [hdv] at hlift
    cases h0 : denoteMeta m.acval env ψ D0 x with
    | none => rw [h0] at hlift; exact nomatch hlift
    | some a =>
      rw [h0, Option.map_some, Option.some.injEq] at hlift
      subst hlift
      rw [Option.getD_some, show D' - D0 = L.length by omega, interp_liftN_consList]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map]
    simp only [List.length_map, List.length_take, Nat.min_eq_left hn]
    by_cases hq2 : q < argsA.length
    · rw [List.getElem?_eq_getElem hq2, Option.map_some]
      have hq3 : argsA[n + (q - n)]? = some argsA[q] := by
        rw [show n + (q - n) = q by omega]; exact List.getElem?_eq_getElem hq2
      rw [htail (q - n) (argsA[q]) hq3]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      rfl

/-- **A head variable reads as the walk valuation's entry.** -/
theorem headRead_fvar {env : Env} {acval : Name → (Name → Nat) → AnnotTerm} {ψ : Name → Nat}
    {D0 D' v : Nat} {ty : Expr} {ha : AnnotTerm}
    (h : denoteMeta acval env ψ D' (.fvar v ty) = some ha) (hv : v < D0)
    {L : List V} (hL : D' = D0 + L.length) (σ : Nat → V) :
    interp V (consList L σ) ha = σ (D0 - 1 - v) := by
  rw [denoteMeta_fvar, Option.some.injEq] at h
  subst h
  rw [interp_bvar, show D' - 1 - v = (D0 - 1 - v) + L.length by omega, consList_apply_add]

end ConLeche.Model
