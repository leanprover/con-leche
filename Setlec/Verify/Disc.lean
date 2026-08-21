import Setlec.Verify.Scoped

/-!
# The call-discipline walks

Per core body and record-parameterized helper: a successful run at the
(real, unguarded) cached record on well-scoped inputs is reproduced by
the guarded record `gFns` — i.e. every record call the body makes is on
well-scoped arguments at the ambient depth.  One `DiscV` walk per
function, mirroring the body structure; the scoping of intermediate
values flows out of the site lemmas (`ScopedSim.site_*`), the scoping
of syntactically constructed arguments out of the `WScoped` toolkit
(`Setlec/Verify/Shift.lean`, `Setlec/Verify/InferLemmas.lean`) — the
same per-site facts the depth-invariance bisimulation
(`Setlec/Verify/Deep.lean`) established, with a one-sided conclusion.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

/-- Scoping of an optional result. -/
def WScopedO (d : Nat) (o : Option Expr) : Prop :=
  ∀ x, o = some x → WScoped d x

theorem WScopedO.none {d : Nat} : WScopedO d none := fun _ h => nomatch h

theorem WScopedO.some {d : Nat} {x : Expr} (h : WScoped d x) :
    WScopedO d (some x) := fun _ hx => by cases hx; exact h

section Walks

variable {env : Env} {f : Nat}

/-- Shorthand for the two records every walk relates. -/
local notation "C" => cachedFns env f
local notation "G" => gFns env f

theorem ensureSort_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (fun _ => True) (ensureSort C env d e)
      (ensureSort G env d e) := by
  show DiscV env _
    ((C : CoreFns CheckSM).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
    ((G : CoreFns CheckSM).whnf d e >>= fun w =>
      match w with
      | .sort u => pure u
      | _ => throw (.invalid "expected a sort"))
  refine DiscV.bind (ih.site_whnf henv hw) (fun w _ => ?_)
  cases w <;> first
    | exact DiscV.pure trivial
    | exact DiscV.throw _

theorem reduceNat_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    DiscV env (WScopedO d) (reduceNat C env d e)
      (reduceNat G env d e) := by
  match e with
  | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    exact DiscV.pure WScopedO.none
  | .app g' a =>
    have hwfa : WScoped d g' ∧ WScoped d a := by
      simpa only [WScoped] using hw
    match g' with
    | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
    | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      exact DiscV.pure WScopedO.none
    | .const c us =>
      match us with
      | _ :: _ => exact DiscV.pure WScopedO.none
      | [] =>
        simp only [reduceNat]
        split
        · cases rawNatLit? a with
          | some n => exact DiscV.pure (WScopedO.some (by simp [WScoped]))
          | none => exact DiscV.pure WScopedO.none
        · split
          · refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w _ => ?_)
            cases rawNatLit? w with
            | none => exact DiscV.pure WScopedO.none
            | some n =>
              dsimp only
              cases hres : natOpResult c n 0 with
              | none => exact DiscV.pure WScopedO.none
              | some r =>
                rcases natOpResult_shape hres with ⟨n', rfl⟩ | ⟨bn, rfl⟩ <;>
                  exact DiscV.pure (WScopedO.some (by simp [WScoped]))
          · split
            · refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w _ => ?_)
              cases rawNatLit? w with
              | none => exact DiscV.pure WScopedO.none
              | some _ => exact DiscV.throw _
            · exact DiscV.pure WScopedO.none
    | .app g b =>
      have hwgb : WScoped d g ∧ WScoped d b := by
        simpa only [WScoped] using hwfa.1
      match g with
      | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
      | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .app _ _ =>
        exact DiscV.pure WScopedO.none
      | .const c us =>
        match us with
        | _ :: _ => exact DiscV.pure WScopedO.none
        | [] =>
          simp only [reduceNat]
          split
          · refine DiscV.bind (ih.site_whnf henv hwgb.2) (fun w₁ _ => ?_)
            refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w₂ _ => ?_)
            cases rawNatLit? w₁ with
            | none =>
              cases rawNatLit? w₂ <;> exact DiscV.pure WScopedO.none
            | some n₁ =>
              cases rawNatLit? w₂ with
              | none => exact DiscV.pure WScopedO.none
              | some n₂ =>
                dsimp only
                cases hres : natOpResult c n₁ n₂ with
                | none => exact DiscV.pure WScopedO.none
                | some r =>
                  rcases natOpResult_shape hres with ⟨n', rfl⟩ |
                    ⟨bn, rfl⟩ <;>
                    exact DiscV.pure (WScopedO.some (by simp [WScoped]))
          · split
            · refine DiscV.bind (ih.site_whnf henv hwgb.2) (fun w₁ _ => ?_)
              refine DiscV.bind (ih.site_whnf henv hwfa.2) (fun w₂ _ => ?_)
              cases rawNatLit? w₁ with
              | none =>
                cases rawNatLit? w₂ <;> exact DiscV.pure WScopedO.none
              | some _ =>
                cases rawNatLit? w₂ with
                | none => exact DiscV.pure WScopedO.none
                | some _ => exact DiscV.throw _
            · exact DiscV.pure WScopedO.none

theorem iotaCerts_disc (ih : ScopedSim env f) (henv : EnvWF env)
    {d : Nat} :
    ∀ {args : List Expr} {ty : Expr}, WScoped d ty →
      (∀ x ∈ args, WScoped d x) →
      DiscV env (fun _ => True) (iotaCerts C env d ty args)
        (iotaCerts G env d ty args) := by
  intro args
  induction args with
  | nil => intro ty _ _; exact DiscV.pure trivial
  | cons arg rest ihrest =>
    intro ty hwty hwargs
    have hwarg : WScoped d arg := hwargs arg (List.mem_cons_self ..)
    have hwrest : ∀ x ∈ rest, WScoped d x :=
      fun x hx => hwargs x (List.mem_cons_of_mem _ hx)
    cases ty with
    | forallE n ty body mb =>
      have hwtb : WScoped d ty ∧ WScoped d body := by
        simpa only [WScoped] using hwty
      show DiscV env _
        ((C : CoreFns CheckSM).infer d arg >>= fun ta =>
          (C : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then iotaCerts C env d (body.instantiate1 arg) rest
          else pure false)
        ((G : CoreFns CheckSM).infer d arg >>= fun ta =>
          (G : CoreFns CheckSM).defeq d ta ty >>= fun b =>
          if b then iotaCerts G env d (body.instantiate1 arg) rest
          else pure false)
      refine DiscV.bind (ih.site_infer henv hwarg) (fun ta hta => ?_)
      refine DiscV.bind (ih.site_defeq hta hwtb.1) (fun b _ => ?_)
      cases b with
      | true =>
        simp only [↓reduceIte]
        exact ihrest (WScoped.instantiate1_gen hwarg 0 hwtb.2) hwrest
      | false => exact DiscV.pure trivial
    | bvar _ | fvar _ _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ => exact DiscV.pure trivial

theorem defEqList_disc (ih : ScopedSim env f) {d : Nat} :
    ∀ {as bs : List Expr}, (∀ x ∈ as, WScoped d x) →
      (∀ x ∈ bs, WScoped d x) →
      DiscV env (fun _ => True) (defEqList C env d as bs)
        (defEqList G env d as bs) := by
  intro as
  induction as with
  | nil =>
    intro bs _ _
    cases bs with
    | nil => exact DiscV.pure trivial
    | cons b bs => exact DiscV.pure trivial
  | cons a as ihas =>
    intro bs hwas hwbs
    cases bs with
    | nil => exact DiscV.pure trivial
    | cons b bs =>
      show DiscV env _
        ((C : CoreFns CheckSM).defeq d a b >>= fun r =>
          if r then defEqList C env d as bs else pure false)
        ((G : CoreFns CheckSM).defeq d a b >>= fun r =>
          if r then defEqList G env d as bs else pure false)
      refine DiscV.bind (ih.site_defeq (hwas a (List.mem_cons_self ..))
        (hwbs b (List.mem_cons_self ..))) (fun r _ => ?_)
      cases r with
      | true =>
        simp only [↓reduceIte]
        exact ihas (fun x hx => hwas x (List.mem_cons_of_mem _ hx))
          (fun x hx => hwbs x (List.mem_cons_of_mem _ hx))
      | false => exact DiscV.pure trivial

theorem defeqSpine_disc (ih : ScopedSim env f) {d : Nat} {a b : Expr}
    (hwa : WScoped d a) (hwb : WScoped d b) :
    DiscV env (fun _ => True) (defeqSpine C env d a b)
      (defeqSpine G env d a b) := by
  unfold defeqSpine
  split
  · split
    · split
      · split
        · exact defEqList_disc ih hwa.getAppArgs hwb.getAppArgs
        · exact DiscV.pure trivial
      · exact DiscV.pure trivial
    · exact DiscV.pure trivial
  · exact DiscV.pure trivial

end Walks

end Setlec
