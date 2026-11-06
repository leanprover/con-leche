module

public import InLeanProof.StateOpsI
import ConLeche.Verify.Cached.DiscC1

/-!
# InLean's body walks, part 1: list helpers and small twins (task #451, lane P2-whnf)

The twins of `Verify/Cached/DiscC1.lean`'s walks: each InLean body
(`InLean/CoreC.lean`) simulates con-leche's pure fueled original at the
translation, under `KnotSpecI` of its callback record, proved by the cached
twin's `sym … => vcgen … <;> finish` script with the translation's vocabulary
(`InLeanProof/GrindI.lean`) in the `grind` set.  This module adds the
vocabulary its walks need beyond `GrindI` (the spine's length, the
`eagerReduce` head).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Vocabulary -/

section Vocab
variable (s : InLean.CState)

theorem appArgs_go_length : ∀ (e : Expr) (acc : List Expr),
    (appArgs.go e acc).length = Expr.getAppNumArgsT e + acc.length := by
  intro e
  induction e with
  | app f a ihf _ => intro acc; simp only [appArgs.go, ihf, Expr.getAppNumArgsT, List.length_cons]; omega
  | mdata _ x ih => intro acc; simp only [appArgs.go, ih, Expr.getAppNumArgsT]
  | _ => intro acc; simp [appArgs.go, Expr.getAppNumArgsT]

/-- The spine's length, read through `mdata`, is the translation's. -/
@[conleche_grind =] theorem TrS_getAppArgs_length (e : Expr) :
    (TrS s e).getAppArgs.length = Expr.getAppNumArgsT e := by
  rw [← TrSL_appArgs s e, TrSL, List.length_map, appArgs, appArgs_go_length]; rfl

/-- The spine's head, read through `mdata`, is never `mdata`. -/
theorem getAppFnT_ne_mdata : ∀ {e : Expr} {m : MData} {x : Expr}, Expr.getAppFnT e = .mdata m x → False
  | .app f _, m, x, h => by rw [Expr.getAppFnT] at h; exact getAppFnT_ne_mdata h
  | .mdata _ y, m, x, h => by rw [Expr.getAppFnT] at h; exact getAppFnT_ne_mdata h
  | .bvar _, _, _, h | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h
  | .const .., _, _, h | .lam .., _, _, h | .forallE .., _, _, h | .letE .., _, _, h
  | .lit _, _, _, h | .proj .., _, _, h => by simp [Expr.getAppFnT] at h

/-- con-leche's `eagerReduce` test as a head and an argument count. -/
theorem cl_isEagerReduce_eq (x : ConLeche.Expr) :
    x.isEagerReduce = (x.getAppArgs.length == 2 &&
      match x.getAppFn with
      | .const c _ => c == ConLeche.eagerReduceName
      | _ => false) := by
  rcases x with _ | _ | _ | _ | ⟨_ | _ | _ | _ | ⟨_ | _ | _ | _ | ⟨g, _⟩ | _ | _ | _ | _, _⟩ |
    _ | _ | _ | _ | _, _⟩ | _ | _ | _ | _ | _ <;>
    simp [ConLeche.Expr.isEagerReduce, ConLeche.Expr.getAppArgs, ConLeche.Expr.getAppFn]

theorem toName_eagerReduceName : toName InLean.eagerReduceName = ConLeche.eagerReduceName := rfl

/-- The `eagerReduce` head, read through the translation. -/
@[conleche_grind =] theorem TrS_isEagerReduce (e : Expr) :
    (TrS s e).isEagerReduce = Expr.isEagerReduce e := by
  unfold Expr.isEagerReduce
  rw [← TrS_getAppArgs_length s e, cl_isEagerReduce_eq, ← TrS_getAppFnT s e]
  congr 1
  generalize hh : Expr.getAppFnT e = h
  cases h with
  | const c us =>
    simp only [TrS_const, ← toName_eagerReduceName]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun h => toName_inj h, fun h => h ▸ rfl⟩
  | fvar id =>
    simp only [TrS, trE]
    cases h : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c h
      rfl
  | mdata _ x => exact (getAppFnT_ne_mdata hh).elim
  | _ => rfl

/-- A list's reading and translation are stable along the run. -/
theorem okSL_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {l : List Expr}, OkSL s₀ l = true → OkSL s₁ l = true
  | [], _ => rfl
  | a :: l, hl => by
    simp only [OkSL_cons, Bool.and_eq_true] at hl ⊢
    exact ⟨okS_of_tabLe h hl.1, okSL_of_tabLe h hl.2⟩
grind_pattern [conleche_grind] okSL_of_tabLe => TabLe s₀ s₁, OkSL s₁ l

theorem TrSL_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {l : List Expr}, OkSL s₀ l = true → TrSL s₁ l = TrSL s₀ l
  | [], _ => rfl
  | a :: l, hl => by
    simp only [OkSL_cons, Bool.and_eq_true] at hl
    simp only [TrSL_cons, TrS_of_tabLe h hl.1, TrSL_of_tabLe h hl.2]
grind_pattern [conleche_grind] TrSL_of_tabLe => TabLe s₀ s₁, TrSL s₁ l

@[conleche_grind =] theorem AllClosed_nil : AllClosed [] = true := rfl
@[conleche_grind =] theorem AllClosed_cons (a : ConLeche.Expr) (l : List ConLeche.Expr) :
    AllClosed (a :: l) = (a.looseBVarsBounded 0 && AllClosed l) := rfl

end Vocab

/-! ## The walks -/

section Walks

variable {r : InLean.CoreFnsI}

/-- **The full-grade argument check** (`defeqArgC_spec`'s twin): the same
argument, so the same tower. -/
theorem defeqArgI_spec (ih : KnotSpecI mode eager env r) {s₀ : InLean.CState} {d : Nat}
    {a ta ty : Expr} (hs : CSOKI mode eager env s₀) (hta : OkS s₀ ta = true)
    (hty : OkS s₀ ty = true) (hwta : ConLeche.Expr.WScoped d (TrS s₀ ta))
    (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty)) (hcta : (TrS s₀ ta).looseBVarsBounded 0 = true)
    (hcty : (TrS s₀ ty).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ defeqArgI r d a ta ty
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqArg (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ ta)
        (TrS s₀ ty)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqArg] =>
    vcgen [InLean.defeqArgI, ih.defeq hs hta hty hwta hwty hcta hcty,
      ih.defeqE hs hta hty hwta hwty hcta hcty] <;> finish

/-- **The pairwise definitional-equality helper** (`defEqListC_spec`'s twin). -/
theorem defEqListI_spec (ih : KnotSpecI mode eager env r) {d : Nat} :
    ∀ {args brgs : List Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ →
      OkSL s₀ args = true → OkSL s₀ brgs = true →
      AllWS d (TrSL s₀ args) → AllWS d (TrSL s₀ brgs) →
      AllClosed (TrSL s₀ args) = true → AllClosed (TrSL s₀ brgs) = true →
      ⦃fun s => s = s₀⦄ defEqListI r d args brgs
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
          Runs (ConLeche.defEqList (ConLeche.fueledFns mode eager env) env d (TrSL s₀ args)
            (TrSL s₀ brgs)) v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro brgs
    cases brgs with
    | nil =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList.eq_1] =>
        vcgen [InLean.defEqListI] <;> finish
    | cons _ _ =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList] =>
        vcgen [InLean.defEqListI.eq_def] <;> finish
  | cons a as ihA =>
    intro brgs
    cases brgs with
    | nil =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList] =>
        vcgen [InLean.defEqListI.eq_def] <;> finish
    | cons b bs =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList.eq_2] =>
        vcgen [InLean.defEqListI, ih.defeq, ihA] <;> finish

end Walks

end InLeanProof
