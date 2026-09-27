module

public import ConLeche.Verify.Inductives.PosDerivK
public import ConLeche.Verify.Shift
public import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Leaves
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.PosDerivKInv
import ConLeche.Verify.Inductives.LayoutKSpec

public section

/-!
# The key-named construction's syntax (PRIMREC / NESTKN-M3B)

Syntactic facts about the kernel's own constructions in the key-named
positivity check (`Kernel/Inductives/PositivityK.lean`), the (P) half of the
use hook `UseOkK`:

* `Expr.replaceTopSpec`: the pure `replaceTop` (the memoised top-down
  replacement `absKeysK` is built on), `replaceTop_eq`; its leaves, scope and
  loose bound variables;
* `SubT`: "a subterm, as far as leaves and scope go" — the relation every
  construction here respects: `containedK`'s keys, `matchGoK`'s bindings;
* the layout's syntax.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-! ## The pure top-down replacement -/

/-- **The pure `replaceTop`**: at every node but a leaf, `f` answers first (a
hit is not descended into). -/
@[expose] def Expr.replaceTopSpec (f : Expr → Option Expr) : Expr → Expr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .lit l => .lit l
  | .fvar i ty => .fvar i ty
  | .const n us => (f (.const n us)).getD (.const n us)
  | .app a b => (f (.app a b)).getD (.app (replaceTopSpec f a) (replaceTopSpec f b))
  | .lam t b bm => (f (.lam t b bm)).getD (.lam (replaceTopSpec f t) (replaceTopSpec f b) bm)
  | .forallE t b bm =>
    (f (.forallE t b bm)).getD (.forallE (replaceTopSpec f t) (replaceTopSpec f b) bm)
  | .letE t v b =>
    (f (.letE t v b)).getD (.letE (replaceTopSpec f t) (replaceTopSpec f v) (replaceTopSpec f b))
  | .proj s i x => (f (.proj s i x)).getD (.proj s i (replaceTopSpec f x))

/-- The memo invariant of `replaceTopGo`: every stored answer is the spec's. -/
@[expose] def MemoRTInv (f : Expr → Option Expr) (memo : Std.HashMap Expr Expr) : Prop :=
  ∀ e r, memo[e]? = some r → r = Expr.replaceTopSpec f e

theorem MemoRTInv.empty (f : Expr → Option Expr) : MemoRTInv f {} := by
  intro e r h; simp at h

theorem MemoRTInv.insert {f : Expr → Option Expr} {memo : Std.HashMap Expr Expr}
    (hm : MemoRTInv f memo) {e r : Expr} (heq : r = Expr.replaceTopSpec f e) :
    MemoRTInv f (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← (beq_iff_eq ..).mp hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The memoised walk is the pure one.** -/
theorem replaceTopGo_spec (f : Expr → Option Expr) : ∀ (e : Expr) {memo : Std.HashMap Expr Expr},
    MemoRTInv f memo →
      (Expr.replaceTopGo f memo e).1 = Expr.replaceTopSpec f e ∧
        MemoRTInv f (Expr.replaceTopGo f memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | const n us =>
    intro memo hm
    rw [Expr.replaceTopGo.eq_def]
    simp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · cases hf : f (.const n us) with
      | some r =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
      | none =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
  | app a b iha ihb =>
    intro memo hm
    rw [Expr.replaceTopGo.eq_def]
    simp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · cases hf : f (.app a b) with
      | some r =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
      | none =>
        simp only [hf]
        obtain ⟨h1, hm1⟩ := iha hm
        obtain ⟨h2, hm2⟩ := ihb hm1
        refine ⟨by simp [Expr.replaceTopSpec, hf, h1, h2], hm2.insert ?_⟩
        simp [Expr.replaceTopSpec, hf, h1, h2]
  | lam t b bm iht ihb =>
    intro memo hm
    rw [Expr.replaceTopGo.eq_def]
    simp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · cases hf : f (.lam t b bm) with
      | some r =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
      | none =>
        simp only [hf]
        obtain ⟨h1, hm1⟩ := iht hm
        obtain ⟨h2, hm2⟩ := ihb hm1
        refine ⟨by simp [Expr.replaceTopSpec, hf, h1, h2], hm2.insert ?_⟩
        simp [Expr.replaceTopSpec, hf, h1, h2]
  | forallE t b bm iht ihb =>
    intro memo hm
    rw [Expr.replaceTopGo.eq_def]
    simp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · cases hf : f (.forallE t b bm) with
      | some r =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
      | none =>
        simp only [hf]
        obtain ⟨h1, hm1⟩ := iht hm
        obtain ⟨h2, hm2⟩ := ihb hm1
        refine ⟨by simp [Expr.replaceTopSpec, hf, h1, h2], hm2.insert ?_⟩
        simp [Expr.replaceTopSpec, hf, h1, h2]
  | letE t v b iht ihv ihb =>
    intro memo hm
    rw [Expr.replaceTopGo.eq_def]
    simp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · cases hf : f (.letE t v b) with
      | some r =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
      | none =>
        simp only [hf]
        obtain ⟨h1, hm1⟩ := iht hm
        obtain ⟨h2, hm2⟩ := ihv hm1
        obtain ⟨h3, hm3⟩ := ihb hm2
        refine ⟨by simp [Expr.replaceTopSpec, hf, h1, h2, h3], hm3.insert ?_⟩
        simp [Expr.replaceTopSpec, hf, h1, h2, h3]
  | proj s i x ih =>
    intro memo hm
    rw [Expr.replaceTopGo.eq_def]
    simp only
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · cases hf : f (.proj s i x) with
      | some r =>
        simp only [hf]
        exact ⟨by simp [Expr.replaceTopSpec, hf], hm.insert (by simp [Expr.replaceTopSpec, hf])⟩
      | none =>
        simp only [hf]
        obtain ⟨h1, hm1⟩ := ih hm
        refine ⟨by simp [Expr.replaceTopSpec, hf, h1], hm1.insert ?_⟩
        simp [Expr.replaceTopSpec, hf, h1]

/-- **`replaceTop` is the pure replacement.** -/
theorem replaceTop_eq (f : Expr → Option Expr) (e : Expr) :
    e.replaceTop f = Expr.replaceTopSpec f e :=
  (replaceTopGo_spec f e (MemoRTInv.empty f)).1

/-! ## The pure replacement's syntax -/

section Spec

variable {f : Expr → Option Expr}

/-- The replacement's leaves: the term's, or a replacement's. -/
theorem replaceTopSpec_leaves : ∀ (e : Expr) (l : Nat × Expr),
    l ∈ (Expr.replaceTopSpec f e).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ x r, f x = some r ∧ l ∈ r.fvarLeaves
  | .bvar _, l, h => Or.inl h
  | .sort _, l, h => Or.inl h
  | .lit _, l, h => Or.inl h
  | .fvar .., l, h => Or.inl h
  | .const n us, l, h => by
    cases hf : f (.const n us) with
    | some r => simp only [Expr.replaceTopSpec, hf, Option.getD_some] at h; exact Or.inr ⟨_, r, hf, h⟩
    | none => simp only [Expr.replaceTopSpec, hf, Option.getD_none] at h; exact Or.inl h
  | .app a b, l, h => by
    cases hf : f (.app a b) with
    | some r => simp only [Expr.replaceTopSpec, hf, Option.getD_some] at h; exact Or.inr ⟨_, r, hf, h⟩
    | none =>
      simp only [Expr.replaceTopSpec, hf, Option.getD_none, fvarLeaves, List.mem_append] at h
      rcases h with h | h
      · rcases replaceTopSpec_leaves a l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
      · rcases replaceTopSpec_leaves b l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
  | .lam t b bm, l, h => by
    cases hf : f (.lam t b bm) with
    | some r => simp only [Expr.replaceTopSpec, hf, Option.getD_some] at h; exact Or.inr ⟨_, r, hf, h⟩
    | none =>
      simp only [Expr.replaceTopSpec, hf, Option.getD_none, fvarLeaves, List.mem_append] at h
      rcases h with h | h
      · rcases replaceTopSpec_leaves t l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
      · rcases replaceTopSpec_leaves b l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
  | .forallE t b bm, l, h => by
    cases hf : f (.forallE t b bm) with
    | some r => simp only [Expr.replaceTopSpec, hf, Option.getD_some] at h; exact Or.inr ⟨_, r, hf, h⟩
    | none =>
      simp only [Expr.replaceTopSpec, hf, Option.getD_none, fvarLeaves, List.mem_append] at h
      rcases h with h | h
      · rcases replaceTopSpec_leaves t l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
      · rcases replaceTopSpec_leaves b l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
  | .letE t v b, l, h => by
    cases hf : f (.letE t v b) with
    | some r => simp only [Expr.replaceTopSpec, hf, Option.getD_some] at h; exact Or.inr ⟨_, r, hf, h⟩
    | none =>
      simp only [Expr.replaceTopSpec, hf, Option.getD_none, fvarLeaves, List.mem_append] at h
      rcases h with (h | h) | h
      · rcases replaceTopSpec_leaves t l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
      · rcases replaceTopSpec_leaves v l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
      · rcases replaceTopSpec_leaves b l h with h | h
        · exact Or.inl (by simp [fvarLeaves, h])
        · exact Or.inr h
  | .proj s i x, l, h => by
    cases hf : f (.proj s i x) with
    | some r => simp only [Expr.replaceTopSpec, hf, Option.getD_some] at h; exact Or.inr ⟨_, r, hf, h⟩
    | none =>
      simp only [Expr.replaceTopSpec, hf, Option.getD_none, fvarLeaves] at h
      rcases replaceTopSpec_leaves x l h with h | h
      · exact Or.inl (by simp [fvarLeaves, h])
      · exact Or.inr h

/-- The replacement is scoped where the term and the replacements are. -/
theorem replaceTopSpec_WScoped {d : Nat} (hf : ∀ x r, f x = some r → WScoped d r) :
    ∀ (e : Expr), WScoped d e → WScoped d (Expr.replaceTopSpec f e)
  | .bvar _, h => h
  | .sort _, h => h
  | .lit _, h => h
  | .fvar .., h => h
  | .const n us, h => by
    cases hx : f (.const n us) with
    | some r => simp only [Expr.replaceTopSpec, hx, Option.getD_some]; exact hf _ _ hx
    | none => simp only [Expr.replaceTopSpec, hx, Option.getD_none]; exact h
  | .app a b, h => by
    cases hx : f (.app a b) with
    | some r => simp only [Expr.replaceTopSpec, hx, Option.getD_some]; exact hf _ _ hx
    | none =>
      simp only [WScoped] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, WScoped]
      exact ⟨replaceTopSpec_WScoped hf a h.1, replaceTopSpec_WScoped hf b h.2⟩
  | .lam t b bm, h => by
    cases hx : f (.lam t b bm) with
    | some r => simp only [Expr.replaceTopSpec, hx, Option.getD_some]; exact hf _ _ hx
    | none =>
      simp only [WScoped] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, WScoped]
      exact ⟨replaceTopSpec_WScoped hf t h.1, replaceTopSpec_WScoped hf b h.2⟩
  | .forallE t b bm, h => by
    cases hx : f (.forallE t b bm) with
    | some r => simp only [Expr.replaceTopSpec, hx, Option.getD_some]; exact hf _ _ hx
    | none =>
      simp only [WScoped] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, WScoped]
      exact ⟨replaceTopSpec_WScoped hf t h.1, replaceTopSpec_WScoped hf b h.2⟩
  | .letE t v b, h => by
    cases hx : f (.letE t v b) with
    | some r => simp only [Expr.replaceTopSpec, hx, Option.getD_some]; exact hf _ _ hx
    | none =>
      simp only [WScoped] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, WScoped]
      exact ⟨replaceTopSpec_WScoped hf t h.1, replaceTopSpec_WScoped hf v h.2.1,
        replaceTopSpec_WScoped hf b h.2.2⟩
  | .proj s i x, h => by
    cases hx : f (.proj s i x) with
    | some r => simp only [Expr.replaceTopSpec, hx, Option.getD_some]; exact hf _ _ hx
    | none =>
      simp only [WScoped] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, WScoped]
      exact replaceTopSpec_WScoped hf x h

/-- The replacement keeps loose-bvar bounds, at bvar-closed replacements. -/
theorem replaceTopSpec_lbb (hf : ∀ x r, f x = some r → r.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (Expr.replaceTopSpec f e).looseBVarsBounded k = true
  | .bvar _, _, h => h
  | .sort _, _, h => h
  | .lit _, _, h => h
  | .fvar .., _, h => h
  | .const n us, k, h => by
    cases hx : f (.const n us) with
    | some r =>
      simp only [Expr.replaceTopSpec, hx, Option.getD_some]
      exact Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ hx)
    | none => simp only [Expr.replaceTopSpec, hx, Option.getD_none]; exact h
  | .app a b, k, h => by
    cases hx : f (.app a b) with
    | some r =>
      simp only [Expr.replaceTopSpec, hx, Option.getD_some]
      exact Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ hx)
    | none =>
      simp only [looseBVarsBounded, Bool.and_eq_true] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, looseBVarsBounded, Bool.and_eq_true]
      exact ⟨replaceTopSpec_lbb hf a k h.1, replaceTopSpec_lbb hf b k h.2⟩
  | .lam t b bm, k, h => by
    cases hx : f (.lam t b bm) with
    | some r =>
      simp only [Expr.replaceTopSpec, hx, Option.getD_some]
      exact Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ hx)
    | none =>
      simp only [looseBVarsBounded, Bool.and_eq_true] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, looseBVarsBounded, Bool.and_eq_true]
      exact ⟨replaceTopSpec_lbb hf t k h.1, replaceTopSpec_lbb hf b (k + 1) h.2⟩
  | .forallE t b bm, k, h => by
    cases hx : f (.forallE t b bm) with
    | some r =>
      simp only [Expr.replaceTopSpec, hx, Option.getD_some]
      exact Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ hx)
    | none =>
      simp only [looseBVarsBounded, Bool.and_eq_true] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, looseBVarsBounded, Bool.and_eq_true]
      exact ⟨replaceTopSpec_lbb hf t k h.1, replaceTopSpec_lbb hf b (k + 1) h.2⟩
  | .letE t v b, k, h => by
    cases hx : f (.letE t v b) with
    | some r =>
      simp only [Expr.replaceTopSpec, hx, Option.getD_some]
      exact Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ hx)
    | none =>
      simp only [looseBVarsBounded, Bool.and_eq_true] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, looseBVarsBounded, Bool.and_eq_true]
      exact ⟨⟨replaceTopSpec_lbb hf t k h.1.1, replaceTopSpec_lbb hf v k h.1.2⟩,
        replaceTopSpec_lbb hf b (k + 1) h.2⟩
  | .proj s i x, k, h => by
    cases hx : f (.proj s i x) with
    | some r =>
      simp only [Expr.replaceTopSpec, hx, Option.getD_some]
      exact Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf _ _ hx)
    | none =>
      simp only [looseBVarsBounded] at h
      simp only [Expr.replaceTopSpec, hx, Option.getD_none, looseBVarsBounded]
      exact replaceTopSpec_lbb hf x k h

end Spec

/-! ## The abstraction -/

/-- `absKeysK` replaces only by the substitution's terms. -/
theorem absKeysK_repl {S : List (NestKey × Expr)} {x r : Expr}
    (h : ((S.find? fun (k, _) => spineIsK k x).map (·.2)) = some r) : ∃ p ∈ S, r = p.2 := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨p, List.mem_of_find?_eq_some hp, rfl⟩

/-- The abstraction's leaves: the term's, or a substitution term's. -/
theorem absKeysK_leaves {S : List (NestKey × Expr)} {e : Expr} {l : Nat × Expr}
    (h : l ∈ (absKeysK S e).fvarLeaves) : l ∈ e.fvarLeaves ∨ ∃ p ∈ S, l ∈ p.2.fvarLeaves := by
  unfold absKeysK at h
  rw [replaceTop_eq] at h
  rcases replaceTopSpec_leaves e l h with h | ⟨x, r, hr, hl⟩
  · exact Or.inl h
  · obtain ⟨p, hp, rfl⟩ := absKeysK_repl hr
    exact Or.inr ⟨p, hp, hl⟩

theorem absKeysK_WScoped {S : List (NestKey × Expr)} {d : Nat} (hS : ∀ p ∈ S, WScoped d p.2)
    {e : Expr} (h : WScoped d e) : WScoped d (absKeysK S e) := by
  unfold absKeysK
  rw [replaceTop_eq]
  exact replaceTopSpec_WScoped (fun x r hr => by
    obtain ⟨p, hp, rfl⟩ := absKeysK_repl hr; exact hS p hp) e h

theorem absKeysK_lbb {S : List (NestKey × Expr)} (hS : ∀ p ∈ S, p.2.looseBVarsBounded 0 = true)
    {e : Expr} {k : Nat} (h : e.looseBVarsBounded k = true) :
    (absKeysK S e).looseBVarsBounded k = true := by
  unfold absKeysK
  rw [replaceTop_eq]
  exact replaceTopSpec_lbb (fun x r hr => by
    obtain ⟨p, hp, rfl⟩ := absKeysK_repl hr; exact hS p hp) e k h

/-! ## Subterms, as far as leaves and scope go -/

/-- `x` sits inside `e` as far as leaves and scope go. -/
@[expose] def SubT (x e : Expr) : Prop :=
  (∀ l ∈ x.fvarLeaves, l ∈ e.fvarLeaves) ∧ ∀ d, WScoped d e → WScoped d x

theorem SubT.refl (e : Expr) : SubT e e := ⟨fun _ h => h, fun _ h => h⟩

theorem SubT.trans {x y z : Expr} (h₁ : SubT x y) (h₂ : SubT y z) : SubT x z :=
  ⟨fun l hl => h₂.1 l (h₁.1 l hl), fun d hd => h₁.2 d (h₂.2 d hd)⟩

theorem SubT.app_fn (f a : Expr) : SubT f (.app f a) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.1⟩

theorem SubT.app_arg (f a : Expr) : SubT a (.app f a) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.2⟩

theorem SubT.lam_ty (t b : Expr) (bm : BinderMeta) : SubT t (.lam t b bm) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.1⟩

theorem SubT.lam_body (t b : Expr) (bm : BinderMeta) : SubT b (.lam t b bm) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.2⟩

theorem SubT.pi_ty (t b : Expr) (bm : BinderMeta) : SubT t (.forallE t b bm) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.1⟩

theorem SubT.pi_body (t b : Expr) (bm : BinderMeta) : SubT b (.forallE t b bm) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.2⟩

theorem SubT.let_ty (t v b : Expr) : SubT t (.letE t v b) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.1⟩

theorem SubT.let_val (t v b : Expr) : SubT v (.letE t v b) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.2.1⟩

theorem SubT.let_body (t v b : Expr) : SubT b (.letE t v b) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h.2.2⟩

theorem SubT.proj_sub (s : Name) (i : Nat) (x : Expr) : SubT x (.proj s i x) :=
  ⟨fun l hl => by simp [fvarLeaves, hl], fun d h => by simp only [WScoped] at h; exact h⟩

theorem SubT.getAppFn : ∀ e : Expr, SubT e.getAppFn e
  | .app f a => (SubT.getAppFn f).trans (SubT.app_fn f a)
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => SubT.refl _

theorem SubT.of_mem_getAppArgs : ∀ {e x : Expr}, x ∈ e.getAppArgs → SubT x e
  | .app f a, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact (SubT.of_mem_getAppArgs hx).trans (SubT.app_fn f a)
    · rw [hx]; exact SubT.app_arg f a
  | .bvar _, _, hx | .fvar .., _, hx | .sort _, _, hx | .const .., _, hx | .lam .., _, hx
  | .forallE .., _, hx | .letE .., _, hx | .lit _, _, hx | .proj .., _, hx => by
    simp [Expr.getAppArgs] at hx

theorem WScoped_mkAppN {d : Nat} : ∀ {xs : List Expr} {f : Expr}, WScoped d f →
    (∀ x ∈ xs, WScoped d x) → WScoped d (Expr.mkAppN f xs)
  | [], _, hf, _ => hf
  | x :: xs, f, hf, hxs => by
    simp only [Expr.mkAppN]
    refine WScoped_mkAppN ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [WScoped]
    exact ⟨hf, hxs x List.mem_cons_self⟩

/-- An application of pieces of `e` sits inside `e`. -/
theorem SubT.mkAppN {e f : Expr} {xs : List Expr} (hf : SubT f e) (hxs : ∀ x ∈ xs, SubT x e) :
    SubT (Expr.mkAppN f xs) e := by
  refine ⟨fun l hl => ?_, fun d hd => WScoped_mkAppN (hf.2 d hd) fun x hx => (hxs x hx).2 d hd⟩
  rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, h⟩
  · exact hf.1 l h
  · exact (hxs x hx).1 l h

/-- A spine prefix of `e` sits inside `e`. -/
theorem SubT.spinePrefix (e : Expr) (n : Nat) :
    SubT (Expr.mkAppN e.getAppFn (e.getAppArgs.take n)) e :=
  SubT.mkAppN (SubT.getAppFn e) fun _ hx => SubT.of_mem_getAppArgs (List.mem_of_mem_take hx)

/-! ## `mapM` in `Except` -/

/-- An output of a successful `mapM` is the function's output at an input. -/
theorem except_mapM_memK {α β ε : Type} {g : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM g = .ok r → ∀ b ∈ r, ∃ a ∈ l, g a = .ok b
  | [], r, h, b, hb => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact nomatch hb
  | x :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    cases hx : g x with
    | error e => rw [hx] at h; exact nomatch h
    | ok b₀ =>
      rw [hx] at h
      cases hl : l.mapM g with
      | error e => simp only [hl] at h; exact nomatch h
      | ok rs =>
        simp only [hl] at h
        change Except.ok (b₀ :: rs) = Except.ok r at h
        cases h
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨a, ha, hga⟩ := except_mapM_memK hl b hb
          exact ⟨a, List.mem_cons_of_mem _ ha, hga⟩

/-- Leaf `l` is a leaf of one of `xs`. -/
@[expose] def LeafIn (xs : List Expr) (l : Nat × Expr) : Prop := ∃ x ∈ xs, l ∈ x.fvarLeaves

/-! ## `replaceFVars`, syntactically -/

/-- The leaves of a replaced term: the term's own or a replacement's. -/
theorem Expr.fvarLeaves_replaceFVars {f : Nat → Option Expr} :
    ∀ (e : Expr) (l : Nat × Expr), l ∈ (e.replaceFVars f).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ i b, f i = some b ∧ l ∈ b.fvarLeaves
  | .bvar _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .fvar i ty, l, h => by
    simp only [Expr.replaceFVars] at h
    cases hi : f i with
    | none => rw [hi] at h; exact Or.inl h
    | some b => rw [hi] at h; exact Or.inr ⟨i, b, hi, h⟩
  | .sort _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .const .., l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .lit _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .app g a, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars g l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars a l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .lam t b _, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars t l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars b l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .forallE t b _, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars t l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars b l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .letE t v b, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with (h | h) | h
    · rcases fvarLeaves_replaceFVars t l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars v l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars b l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .proj _ _ x, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves] at h
    rcases fvarLeaves_replaceFVars x l h with h | h
    · exact Or.inl (by simp [Expr.fvarLeaves, h])
    · exact Or.inr h

/-- A replaced term is as bvar-closed as the term, at bvar-closed replacements. -/
theorem Expr.looseBVarsBounded_replaceFVars {f : Nat → Option Expr}
    (hf : ∀ i b, f i = some b → b.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceFVars f).looseBVarsBounded k = true
  | .bvar _, _, h => h
  | .fvar i ty, k, _ => by
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => rfl
    | some b => exact ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf i b hi)
  | .sort _, _, h => h
  | .const .., _, h => h
  | .lit _, _, h => h
  | .app g a, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨looseBVarsBounded_replaceFVars hf g k h.1, looseBVarsBounded_replaceFVars hf a k h.2⟩
  | .lam t b _, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨looseBVarsBounded_replaceFVars hf t k h.1,
      looseBVarsBounded_replaceFVars hf b (k + 1) h.2⟩
  | .forallE t b _, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨looseBVarsBounded_replaceFVars hf t k h.1,
      looseBVarsBounded_replaceFVars hf b (k + 1) h.2⟩
  | .letE t v b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨looseBVarsBounded_replaceFVars hf t k h.1.1, looseBVarsBounded_replaceFVars hf v k h.1.2⟩,
      looseBVarsBounded_replaceFVars hf b (k + 1) h.2⟩
  | .proj _ _ x, k, h => by
    simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded]
    exact looseBVarsBounded_replaceFVars hf x k h

/-- A replaced term is scoped where its kept variables and the replacements are. -/
theorem Expr.WScoped_replaceFVars {f : Nat → Option Expr} {d : Nat}
    (hf : ∀ i b, f i = some b → Expr.WScoped d b) :
    ∀ (e : Expr) {D : Nat}, Expr.WScoped D e → (∀ l ∈ e.fvarLeaves, f l.1 = none → l.1 < d) →
      Expr.WScoped d (e.replaceFVars f)
  | .bvar _, _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .fvar i ty, D, h, hk => by
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none =>
      simp only [Option.getD_none, Expr.WScoped]
      simp only [Expr.WScoped] at h
      exact ⟨hk (i, ty) (by simp [Expr.fvarLeaves]) hi, h.2⟩
    | some b => exact hf i b hi
  | .sort _, _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .const .., _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .lit _, _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .app g a, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf g h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf a h.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .lam t b _, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf t h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf b h.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .forallE t b _, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf t h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf b h.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .letE t v b, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf t h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf v h.2.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf b h.2.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .proj _ _ x, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact WScoped_replaceFVars hf x h fun l hl => hk l (by simp [Expr.fvarLeaves, hl])

/-- **The leaves of a replaced term, sharply**: a replacement's, or a leaf of
the term at or below a KEPT variable of the term (a kept variable's
annotation reads only variables below it). -/
theorem Expr.fvarLeaves_replaceFVars_kept {f : Nat → Option Expr} :
    ∀ (e : Expr) {D : Nat}, Expr.WScoped D e → ∀ l ∈ (e.replaceFVars f).fvarLeaves,
      (∃ i b, f i = some b ∧ l ∈ b.fvarLeaves) ∨
      (l ∈ e.fvarLeaves ∧ ∃ i ty, f i = none ∧ (i, ty) ∈ e.fvarLeaves ∧ l.1 ≤ i)
  | .bvar _, _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .fvar i ty, D, hw, l, h => by
    simp only [Expr.replaceFVars] at h
    cases hi : f i with
    | none =>
      rw [hi] at h
      simp only [Option.getD_none] at h
      refine Or.inr ⟨h, i, ty, hi, by simp [Expr.fvarLeaves], ?_⟩
      simp only [Expr.fvarLeaves, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · simp only [Expr.WScoped] at hw
        exact Nat.le_of_lt (ConLeche.Expr.fvarLeaves_lt_of_wscoped hw.2 l h)
    | some b => rw [hi] at h; exact Or.inl ⟨i, b, hi, h⟩
  | .sort _, _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .const .., _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .lit _, _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .app g a, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars_kept g hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept a hw.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .lam t b _, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars_kept t hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept b hw.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .forallE t b _, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars_kept t hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept b hw.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .letE t v b, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with (h | h) | h
    · rcases fvarLeaves_replaceFVars_kept t hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept v hw.2.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept b hw.2.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .proj _ _ x, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves] at h
    rcases fvarLeaves_replaceFVars_kept x hw l h with h | ⟨h1, i, ty, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩

/-! ## Telescope instantiation, syntactically -/

theorem instPisWith_leavesK :
    ∀ (as : List Expr) (e r : Expr), instPisWith as e = some r →
      ∀ l ∈ r.fvarLeaves, l ∈ e.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves
  | [], e, r, h, l, hl => by
    simp only [instPisWith, Option.some.injEq] at h; subst h; exact Or.inl hl
  | a :: as, e, r, h, l, hl => by
    cases e with
    | forallE dom body bm =>
      simp only [instPisWith] at h
      rcases instPisWith_leavesK as _ r h l hl with h1 | ⟨x, hx, h1⟩
      · rcases Expr.fvarLeaves_instantiate1 body 0 h1 with h2 | h2
        · exact Or.inl (by simp [Expr.fvarLeaves, h2])
        · exact Or.inr ⟨a, List.mem_cons_self, h2⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h1⟩
    | _ => simp [instPisWith] at h

theorem instPisWith_WScopedK {d : Nat} :
    ∀ {as : List Expr} {t r : Expr}, instPisWith as t = some r → WScoped d t →
      (∀ a ∈ as, WScoped d a) → WScoped d r
  | [], t, r, h, ht, _ => by
    simp only [instPisWith, Option.some.injEq] at h
    exact h ▸ ht
  | a :: as, t, r, h, ht, ha => by
    cases t with
    | forallE dom body bi =>
      simp only [instPisWith] at h
      simp only [WScoped] at ht
      exact instPisWith_WScopedK h (WScoped.instantiate1_gen (ha a List.mem_cons_self) 0 ht.2)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    | _ => simp [instPisWith] at h

theorem instPisWith_lbbK :
    ∀ {as : List Expr} {t r : Expr}, instPisWith as t = some r → t.looseBVarsBounded 0 = true →
      (∀ a ∈ as, a.looseBVarsBounded 0 = true) → r.looseBVarsBounded 0 = true
  | [], t, r, h, ht, _ => by
    simp only [instPisWith, Option.some.injEq] at h
    exact h ▸ ht
  | a :: as, t, r, h, ht, ha => by
    cases t with
    | forallE dom body bi =>
      simp only [instPisWith] at h
      simp only [looseBVarsBounded, Bool.and_eq_true] at ht
      exact instPisWith_lbbK h
        (Expr.looseBVarsBounded_instantiate1_gen (ha a List.mem_cons_self) ht.2)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
    | _ => simp [instPisWith] at h

/-! ## The layout's syntax -/

/-- The context's stored types are closed (`EnvWF`'s `ConstWF`, at the
context's lookup). -/
@[expose] def CtxTysClosed (ctx : NestCtx) : Prop :=
  ∀ n ci, ctx.find? n = some ci →
    ci.toConstantVal.type.hasFvar = false ∧ ci.toConstantVal.type.looseBVarsBounded 0 = true

/-- A key read off `e`: every parameter sits inside `e`, bvar-closed. -/
@[expose] def KeyIn (e : Expr) (k : NestKey) : Prop :=
  ∀ x ∈ k.ds, SubT x e ∧ x.looseBVarsBounded 0 = true

theorem KeyIn.trans {e e' : Expr} {k : NestKey} (h : KeyIn e k) (he : SubT e e') : KeyIn e' k :=
  fun x hx => ⟨(h x hx).1.trans he, (h x hx).2⟩

/-- Concrete parameters: scoped at the members, bvar-closed, leaves bounded. -/
@[expose] def KeyGoodK (ctx : NestCtx) (ds : List Expr) : Prop :=
  ∀ x ∈ ds, WScoped (ctx.hiAt 0) x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x

/-! ## The hook's syntactic clauses -/

/-- **A layout's material, syntactically**: one type and one key per flexible
family, each type scoped below its family, bvar-closed, its leaves' annotations
closed; the families' keys concrete. -/
@[expose] def LayGoodK (ctx : NestCtx) (L : LayoutK) : Prop :=
  L.famTys.length = L.nF ∧ L.fams.length = L.nF ∧
  (∀ j (hj : j < L.famTys.length), WScoped (ctx.hiAt 0 + j) L.famTys[j] ∧
    L.famTys[j].looseBVarsBounded 0 = true ∧ Expr.LeavesBounded L.famTys[j]) ∧
  (∀ p ∈ L.fams, KeyGoodK ctx p.1.ds)

/-- **The leaves of a layout's material**: its `DsF`'s, its families' keys',
and its families' own (the family variable with its type). -/
@[expose] def LayLeafK (ctx : NestCtx) (L : LayoutK) (l : Nat × Expr) : Prop :=
  LeafIn L.dsF l ∨ (∃ p ∈ L.fams, LeafIn p.1.ds l) ∨
    ∃ x, ∃ hx : x < L.famTys.length, l ∈ (Expr.fvar (ctx.hiAt 0 + x) L.famTys[x]).fvarLeaves

/-- **A use site, syntactically** (what the model knows at every use): the
user's layout's depth, its material, its spelling scoped at the layout,
bvar-closed, leaves bounded. -/
@[expose] def SiteSynK (ctx : NestCtx) (L : LayoutK) (ps : List Expr) : Prop :=
  L.hi = ctx.hiAt 0 + L.nF + L.grp.length ∧ LayGoodK ctx L ∧
  ∀ x ∈ ps, WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x

/-- **A node's material, syntactically** (U2–U5): the layout's material good;
each family type's leaves the key's (below the members) or an earlier
family's; `DsF` scoped at the node's base, bvar-closed, leaves bounded, its
leaves the key's or a family's; the families' keys' leaves the key's. -/
@[expose] def NodeSynK (ctx : NestCtx) (kn : NestKey) (lo : LayoutOutK) : Prop :=
  LayGoodK ctx lo.L ∧
  (∀ j (hj : j < lo.L.famTys.length), ∀ l ∈ lo.L.famTys[j].fvarLeaves,
    (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
      ∃ i, ∃ hi : i < j, l = (ctx.hiAt 0 + i, lo.L.famTys[i]'(by omega))) ∧
  (∀ x ∈ lo.L.dsF, WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded x ∧ ∀ l ∈ x.fvarLeaves, (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
      ∃ i, ∃ hi : i < lo.L.famTys.length, l = (ctx.hiAt 0 + i, lo.L.famTys[i])) ∧
  (∀ p ∈ lo.L.fams, ∀ x ∈ p.1.ds, ∀ l ∈ x.fvarLeaves, LeafIn kn.ds l)


/-- **A binding good at a use site**: scoped at the user, its leaves'
annotations closed, its leaves the spelling's or the user's layout material's. -/
@[expose] def BindGoodK (ctx : NestCtx) (L : LayoutK) (ps : List Expr) (b : Expr) : Prop :=
  WScoped L.hi b ∧ Expr.LeavesBounded b ∧ ∀ l ∈ b.fvarLeaves, LeafIn ps l ∨ LayLeafK ctx L l

/-- **A use's syntax** (U2–U7's (P) half): the node's material (`NodeSynK`);
the node's key's leaves the user's spelling's or the user's families' keys'
(U6); every binding of the match scoped at the user, its leaves' annotations
closed, its leaves the spelling's or the user's layout material's (U7). -/
@[expose] def UseSynK (ctx : NestCtx) (L : LayoutK) (kn : NestKey) (ps : List Expr)
    (lo : LayoutOutK) (bs : List (Nat × Expr)) : Prop :=
  NodeSynK ctx kn lo ∧
  (∀ l, LeafIn kn.ds l → LeafIn ps l ∨ ∃ p ∈ L.fams, LeafIn p.1.ds l) ∧
  ∀ b ∈ bs, BindGoodK ctx L ps b.2

section Layout

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

theorem keyOccK?_ds {lo hi : Nat} {e : Expr} {k : NestKey} (h : keyOccK? ctx lo hi e = some k) :
    ∀ x ∈ k.ds, x ∈ e.getAppArgs := by
  unfold keyOccK? at h
  split at h
  · dsimp only at h
    split at h
    · simp at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          intro x hx
          exact List.mem_of_mem_take hx
        · simp at h
      · simp at h
  · simp at h

/-- The contained-key scan's keys are read off the scanned term. -/
theorem containedGoK_keys : ∀ (e : Expr) (acc : NestSynAcc) (k : NestKey),
    k ∈ (containedGoK ctx e acc).keys.toList → k ∈ acc.keys.toList ∨ KeyIn e k := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · dsimp only at hk
      have lift : ∀ acc', (k ∈ acc'.keys.toList → k ∈ acc.keys.toList) →
          k ∈ (containedGoK ctx a (containedGoK ctx f acc')).keys.toList →
          k ∈ acc.keys.toList ∨ KeyIn (.app f a) k := by
        intro acc' h0 hk
        rcases iha _ k hk with hk | hk
        · rcases ihf _ k hk with hk | hk
          · exact .inl (h0 hk)
          · exact .inr (hk.trans (SubT.app_fn f a))
        · exact .inr (hk.trans (SubT.app_arg f a))
      split at hk
      · rename_i k' hk'
        split at hk
        · rename_i hcl
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk
          rcases hk with hk | rfl
          · exact lift { acc with seen := acc.seen.insert (.app f a) } (fun h => h) hk
          · refine .inr fun x hx => ⟨SubT.of_mem_getAppArgs (keyOccK?_ds hk' x hx), ?_⟩
            simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hcl
            exact Expr.bvarB_le (by rw [hcl.1 x hx]; exact Nat.le_refl 0)
        · exact lift { acc with seen := acc.seen.insert (.app f a) } (fun h => h) hk
      · exact lift { acc with seen := acc.seen.insert (.app f a) } (fun h => h) hk
  | lam t b bm iht ihb =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · rcases ihb _ k hk with hk | hk
      · rcases iht _ k hk with hk | hk
        · exact .inl hk
        · exact .inr (hk.trans (SubT.lam_ty t b bm))
      · exact .inr (hk.trans (SubT.lam_body t b bm))
  | forallE t b bm iht ihb =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · rcases ihb _ k hk with hk | hk
      · rcases iht _ k hk with hk | hk
        · exact .inl hk
        · exact .inr (hk.trans (SubT.pi_ty t b bm))
      · exact .inr (hk.trans (SubT.pi_body t b bm))
  | letE t v b iht ihv ihb =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · rcases ihb _ k hk with hk | hk
      · rcases ihv _ k hk with hk | hk
        · rcases iht _ k hk with hk | hk
          · exact .inl hk
          · exact .inr (hk.trans (SubT.let_ty t v b))
        · exact .inr (hk.trans (SubT.let_val t v b))
      · exact .inr (hk.trans (SubT.let_body t v b))
  | proj s i x ih =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · rcases ih _ k hk with hk | hk
      · exact .inl hk
      · exact .inr (hk.trans (SubT.proj_sub s i x))
  | bvar _ =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · exact .inl hk
  | fvar _ _ _ =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · exact .inl hk
  | sort _ =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · exact .inl hk
  | const _ _ =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · exact .inl hk
  | lit _ =>
    intro acc k hk
    rw [containedGoK] at hk
    split at hk
    · exact .inl hk
    · exact .inl hk

theorem containedK_keys_go : ∀ (ds : List Expr) (acc : NestSynAcc) (k : NestKey),
    k ∈ (ds.foldl (fun acc d => containedGoK ctx d acc) acc).keys.toList →
      k ∈ acc.keys.toList ∨ ∃ d ∈ ds, KeyIn d k
  | [], acc, k, hk => .inl hk
  | d :: ds, acc, k, hk => by
    rcases containedK_keys_go ds _ k hk with hk | ⟨d', hd', hk⟩
    · rcases containedGoK_keys d acc k hk with hk | hk
      · exact .inl hk
      · exact .inr ⟨d, List.mem_cons_self, hk⟩
    · exact .inr ⟨d', List.mem_cons_of_mem _ hd', hk⟩

/-- **A contained key is read off the key's parameters.** -/
theorem containedK_keyIn {ds : List Expr} {k : NestKey} (hk : k ∈ containedK ctx ds) :
    ∃ d ∈ ds, KeyIn d k := by
  rcases containedK_keys_go (ctx := ctx) ds {} k hk with hk | h
  · simp at hk
  · exact h

/-- KN5's representatives are contained keys. -/
theorem mergeK_reps : ∀ (ks reps : List NestKey) (als : List (NestKey × Nat))
    (r : List NestKey × List (NestKey × Nat)),
    mergeK (m := CheckM) ops env ctx ks reps als = .ok r → ∀ k ∈ r.1, k ∈ reps ∨ k ∈ ks
  | [], reps, als, r, h, k, hk => by
    simp only [mergeK, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .inl hk
  | k₀ :: ks, reps, als, r, h, k, hk => by
    simp only [mergeK, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i o ho
    split at h
    · rcases mergeK_reps ks reps _ r h k hk with h1 | h1
      · exact .inl h1
      · exact .inr (List.mem_cons_of_mem _ h1)
    · rcases mergeK_reps ks _ als r h k hk with h1 | h1
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact .inl h1
        · rw [List.mem_singleton.mp h1]; exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ h1)

/-- The flexible substitution: family `i` at `hiAt0 + i`, typed by `fl[i]`'s type. -/
theorem flexSubstK_mem {reps : List NestKey} {als : List (NestKey × Nat)}
    {fl : List (Nat × Expr × Nat)} :
    ∀ p ∈ flexSubstK ctx reps als fl,
      ∃ i, ∃ hi : i < fl.length, p.2 = .fvar (ctx.hiAt 0 + i) fl[i].2.1 := by
  intro p hp
  unfold flexSubstK at hp
  obtain ⟨rz, hrz, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hrz
  rw [List.getElem_mapIdx] at he
  have hi' : i < fl.length := by simpa using hi
  refine ⟨i, hi', ?_⟩
  subst he
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
    rfl
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
    rfl

/-- **The flexibility trials' invariant**: each flexible family's
representative and type, the type its container's former at the key's
parameters with the EARLIER families abstracted. -/
@[expose] def FlexInvK (ctx : NestCtx) (reps : List NestKey) (als : List (NestKey × Nat))
    (fl : List (Nat × Expr × Nat)) : Prop :=
  ∀ j (hj : j < fl.length), ∃ k, reps[fl[j].1]? = some k ∧
    famTypeK ctx (flexSubstK ctx reps als (fl.take j)) k = some (fl[j].2.1, fl[j].2.2)

theorem flexK_inv {kc : NestKey} {gnames : List Name} {ctors : List (ConstantVal × Nat)}
    {reps : List NestKey} {als : List (NestKey × Nat)} :
    ∀ (rs : List Nat) (fl fl' : List (Nat × Expr × Nat)),
      flexK (m := CheckM) ops env ctx kc gnames ctors reps als rs fl = .ok fl' →
      FlexInvK ctx reps als fl → FlexInvK ctx reps als fl'
  | [], fl, fl', h, hI => by
    simp only [flexK, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | r :: rs, fl, fl', h, hI => by
    simp only [flexK] at h
    split at h
    · rename_i k ty nI hk hft
      simp only [bind, Except.bind] at h
      split at h
      · simp at h
      rename_i ok hok
      refine flexK_inv rs _ fl' h ?_
      split
      · intro j hj
        rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < fl.length
        · obtain ⟨k', hk', hf'⟩ := hI j hjl
          rw [List.getElem_append_left hjl, List.take_append_of_le_length (by omega)]
          exact ⟨k', hk', hf'⟩
        · have hjeq : j = fl.length := by omega
          subst hjeq
          rw [List.getElem_append_right (by omega), List.take_append_of_le_length (by omega),
            List.take_length]
          simp only [Nat.sub_self, List.getElem_cons_zero]
          refine ⟨k, hk, ?_⟩
          rw [hk] at hft
          simpa using hft
      · exact hI
    · exact flexK_inv rs fl fl' h hI

/-- **The layout's syntax, inverted**: the representatives (contained keys),
the flexibility trials' invariant, the families and `DsF` built from them. -/
theorem nestLayoutK_syn {kc : NestKey} {lo : LayoutOutK}
    (h : nestLayoutK (m := CheckM) ops env ctx (nestContainer ctx) kc = .ok lo) :
    ∃ reps als fl, (∀ k ∈ reps, ∃ d ∈ kc.ds, KeyIn d k) ∧ FlexInvK ctx reps als fl ∧
      lo.L.nF = fl.length ∧ lo.L.famTys = fl.map (·.2.1) ∧
      lo.L.fams = fl.filterMap (fun (r, _, nI) => (reps[r]?).map fun k => (k, nI)) ∧
      lo.L.dsF = kc.ds.map (absKeysK (flexSubstK ctx reps als fl)) := by
  simp only [nestLayoutK, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i q hq
  split at h
  · simp at h
  rename_i ctors hctors
  split at h
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hnd
  split at h
  · simp at h
  rename_i ra hra
  obtain ⟨reps, als⟩ := ra
  split at h
  · simp at h
  rename_i fl hfl
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨dsF, ginfo, crests⟩ := r
  split at h
  · simp at h
  rename_i u3 hu3
  split at h
  · simp at h
  rename_i u5 hu5
  simp only [Except.ok.injEq] at h
  subst h
  have hlt : layoutTypeK (m := CheckM) ops env ctx
      { kc with cname := (groupOfK ctx kc.cname).headD kc.cname } (groupOfK ctx kc.cname)
      ctors (flexSubstK ctx reps als fl) fl.length = .ok (dsF, ginfo, crests) := by
    rcases tryCatchVerdictK_ok hr with hr | ⟨err, _, _, hr⟩
    · exact hr
    · exfalso
      revert hr
      split
      · split <;> exact throwK_ne_ok
      · exact throwK_ne_ok
  obtain ⟨hds, -⟩ := layoutTypeK_ok hlt
  refine ⟨reps, als, fl, fun k hk => ?_, flexK_inv _ [] fl hfl (fun j hj => by simp at hj),
    rfl, rfl, rfl, hds⟩
  rcases mergeK_reps _ [] [] _ hra k hk with h1 | h1
  · simp at h1
  · exact containedK_keyIn h1

/-- A leaf of a key's parameters' reading, its leaves' annotations closed. -/
theorem KeyGoodK.leaf {ds : List Expr} (h : KeyGoodK ctx ds) {l : Nat × Expr} (hl : LeafIn ds l) :
    l.1 < ctx.hiAt 0 ∧ l.2.looseBVarsBounded 0 = true := by
  obtain ⟨x, hx, hl⟩ := hl
  exact ⟨Expr.fvarLeaves_lt_of_wscoped (h x hx).1 l hl, (h x hx).2.2 l hl⟩

/-- **The flexible families' types** (U3's syntax): each scoped below its
family, bvar-closed, its leaves the key's (below the members) or an earlier
family's. -/
theorem flexTys_syn (hcl : CtxTysClosed ctx) {kn : NestKey} (hkn : KeyGoodK ctx kn.ds)
    {reps : List NestKey} {als : List (NestKey × Nat)} {fl : List (Nat × Expr × Nat)}
    (hreps : ∀ k ∈ reps, ∃ d ∈ kn.ds, KeyIn d k) (hfl : FlexInvK ctx reps als fl) :
    ∀ j (hj : j < fl.length), WScoped (ctx.hiAt 0 + j) fl[j].2.1 ∧
      fl[j].2.1.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded fl[j].2.1 ∧
      ∀ l ∈ fl[j].2.1.fvarLeaves, (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
        ∃ i, ∃ hi : i < j, l = (ctx.hiAt 0 + i, (fl[i]'(by omega)).2.1) := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro hj
  obtain ⟨k, hk, hft⟩ := hfl j hj
  obtain ⟨d0, hd0, hkin⟩ := hreps k (List.mem_of_getElem? hk)
  -- the substitution: the earlier families
  have hS : ∀ p ∈ flexSubstK ctx reps als (fl.take j),
      ∃ i, ∃ hi : i < j, p.2 = .fvar (ctx.hiAt 0 + i) (fl[i]'(by omega)).2.1 := by
    intro p hp
    obtain ⟨i, hi, he⟩ := flexSubstK_mem p hp
    have hi' : i < j := by simp at hi; omega
    refine ⟨i, hi', ?_⟩
    rw [he, List.getElem_take]
  have hSW : ∀ p ∈ flexSubstK ctx reps als (fl.take j), WScoped (ctx.hiAt 0 + j) p.2 := by
    intro p hp
    obtain ⟨i, hi, he⟩ := hS p hp
    rw [he]
    simp only [WScoped]
    exact ⟨by omega, (ih i hi (by omega)).1⟩
  have hSB : ∀ p ∈ flexSubstK ctx reps als (fl.take j), p.2.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi, he⟩ := hS p hp
    rw [he]; rfl
  -- the parameters
  have hkx : ∀ x ∈ k.ds, WScoped (ctx.hiAt 0) x ∧ x.looseBVarsBounded 0 = true ∧
      ∀ l ∈ x.fvarLeaves, l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l := by
    intro x hx
    obtain ⟨hsub, hxb⟩ := hkin x hx
    refine ⟨hsub.2 _ (hkn d0 hd0).1, hxb, fun l hl => ?_⟩
    have hl' := hsub.1 l hl
    exact ⟨Expr.fvarLeaves_lt_of_wscoped (hkn d0 hd0).1 l hl', d0, hd0, hl'⟩
  have hargs : ∀ a ∈ k.ds.map (absKeysK (flexSubstK ctx reps als (fl.take j))),
      WScoped (ctx.hiAt 0 + j) a ∧ a.looseBVarsBounded 0 = true ∧
      ∀ l ∈ a.fvarLeaves, (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
        ∃ i, ∃ hi : i < j, l = (ctx.hiAt 0 + i, (fl[i]'(by omega)).2.1) := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨hxw, hxb, hxl⟩ := hkx x hx
    refine ⟨absKeysK_WScoped hSW (WScoped.mono (by omega) hxw), absKeysK_lbb hSB hxb,
      fun l hl => ?_⟩
    rcases absKeysK_leaves hl with hl | ⟨p, hp, hl⟩
    · exact .inl (hxl l hl)
    · obtain ⟨i, hi, he⟩ := hS p hp
      rw [he] at hl
      simp only [Expr.fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact .inr ⟨i, hi, rfl⟩
      · rcases (ih i hi (by omega)).2.2.2 l hl with h | ⟨i', hi', rfl⟩
        · exact .inl h
        · exact .inr ⟨i', by omega, rfl⟩
  unfold famTypeK at hft
  split at hft
  · rename_i cv caps hf
    obtain ⟨t, ht, htn⟩ := Option.map_eq_some_iff.mp hft
    simp only [Prod.mk.injEq] at htn
    obtain ⟨hte, -⟩ := htn
    rw [← hte]
    obtain ⟨hcf, hcb⟩ := hcl _ _ hf
    have hTf : (cv.type.instantiateLevelParams cv.levelParams k.lvls).hasFvar = false := by
      rw [Expr.hasFvar_instantiateLevelParams]; exact hcf
    have hTb : (cv.type.instantiateLevelParams cv.levelParams k.lvls).looseBVarsBounded 0 = true := by
      rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hcb
    have hleaves : ∀ l ∈ t.fvarLeaves, (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
        ∃ i, ∃ hi : i < j, l = (ctx.hiAt 0 + i, (fl[i]'(by omega)).2.1) := by
      intro l hl
      rcases instPisWith_leavesK _ _ _ ht l hl with hl | ⟨a, ha, hl⟩
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hTf] at hl; exact nomatch hl
      · exact (hargs a ha).2.2 l hl
    refine ⟨instPisWith_WScopedK ht (WScoped.of_not_hasFvar hTf) fun a ha => (hargs a ha).1,
      instPisWith_lbbK ht hTb fun a ha => (hargs a ha).2.1, fun l hl => ?_, hleaves⟩
    rcases hleaves l hl with ⟨-, hkl⟩ | ⟨i, hi, rfl⟩
    · exact (hkn.leaf hkl).2
    · exact (ih i hi (by omega)).2.1
  · simp at hft

theorem length_filterMap_of_isSomeK {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    rw [hb]
    simp only [List.length_cons]
    rw [length_filterMap_of_isSomeK fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **A node's material, from its layout's run** (U2–U5's syntax). -/
theorem nodeSynK_of_layout (hcl : CtxTysClosed ctx) {kn : NestKey} {lo : LayoutOutK}
    (hkn : KeyGoodK ctx kn.ds)
    (h : nestLayoutK (m := CheckM) ops env ctx (nestContainer ctx) kn = .ok lo) :
    NodeSynK ctx kn lo := by
  obtain ⟨reps, als, fl, hreps, hfl, hnF, hTys, hfams, hdsF⟩ := nestLayoutK_syn h
  have hty := flexTys_syn hcl hkn hreps hfl
  have htl : lo.L.famTys.length = fl.length := by rw [hTys, List.length_map]
  have hget : ∀ j (hj : j < lo.L.famTys.length), lo.L.famTys[j] = (fl[j]'(by omega)).2.1 := by
    intro j hj
    simp only [hTys, List.getElem_map]
  have hsome : ∀ x ∈ fl, ((reps[x.1]?).map fun k => (k, x.2.2)).isSome = true := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨k, hk, -⟩ := hfl j hj
    simp [hk]
  have hfl' : lo.L.fams.length = fl.length := by
    rw [hfams]
    exact length_filterMap_of_isSomeK fun x hx => hsome x hx
  have hfamk : ∀ p ∈ lo.L.fams, ∃ d ∈ kn.ds, KeyIn d p.1 := by
    intro p hp
    rw [hfams] at hp
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.mp hp
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact hreps k (List.mem_of_getElem? hk)
  refine ⟨⟨htl.trans hnF.symm, hfl'.trans hnF.symm, fun j hj => ?_, fun p hp x hx => ?_⟩,
    fun j hj l hl => ?_, fun x hx => ?_, fun p hp x hx l hl => ?_⟩
  · rw [hget j hj]
    obtain ⟨h1, h2, h3, -⟩ := hty j (by omega)
    exact ⟨h1, h2, h3⟩
  · obtain ⟨d, hd, hkin⟩ := hfamk p hp
    obtain ⟨hsub, hxb⟩ := hkin x hx
    exact ⟨hsub.2 _ (hkn d hd).1, hxb, fun l hl => (hkn d hd).2.2 l (hsub.1 l hl)⟩
  · rw [hget j hj] at hl
    rcases (hty j (by omega)).2.2.2 l hl with h1 | ⟨i, hi, rfl⟩
    · exact .inl h1
    · exact .inr ⟨i, hi, by rw [hget i (by omega)]⟩
  · rw [hdsF] at hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    have hS : ∀ p ∈ flexSubstK ctx reps als fl, WScoped (ctx.hiAt 0 + lo.L.nF) p.2 ∧
        p.2.looseBVarsBounded 0 = true := by
      intro p hp
      obtain ⟨i, hi, he⟩ := flexSubstK_mem p hp
      rw [he]
      simp only [WScoped]
      exact ⟨⟨by omega, (hty i hi).1⟩, rfl⟩
    have hleaves : ∀ l ∈ (absKeysK (flexSubstK ctx reps als fl) d).fvarLeaves,
        (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
          ∃ i, ∃ hi : i < lo.L.famTys.length, l = (ctx.hiAt 0 + i, lo.L.famTys[i]) := by
      intro l hl
      rcases absKeysK_leaves hl with hl | ⟨p, hp, hl⟩
      · exact .inl ⟨Expr.fvarLeaves_lt_of_wscoped (hkn d hd).1 l hl, d, hd, hl⟩
      · obtain ⟨i, hi, he⟩ := flexSubstK_mem p hp
        rw [he] at hl
        simp only [Expr.fvarLeaves, List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact .inr ⟨i, by omega, by rw [hget i (by omega)]⟩
        · rcases (hty i hi).2.2.2 l hl with h1 | ⟨i', hi', rfl⟩
          · exact .inl h1
          · exact .inr ⟨i', by omega, by rw [hget i' (by omega)]⟩
    refine ⟨absKeysK_WScoped (fun p hp => (hS p hp).1) (WScoped.mono (by omega) (hkn d hd).1),
      absKeysK_lbb (fun p hp => (hS p hp).2) (hkn d hd).2.1, fun l hl => ?_, hleaves⟩
    rcases hleaves l hl with ⟨-, hkl⟩ | ⟨i, hi, rfl⟩
    · exact (hkn.leaf hkl).2
    · rw [hget i hi]; exact (hty i (by omega)).2.1
  · obtain ⟨d, hd, hkin⟩ := hfamk p hp
    exact ⟨d, hd, (hkin x hx).1.1 l hl⟩

/-! ## The readback -/

/-- **The readback at a use site**: the spelling read back is concrete, its
leaves the spelling's or the user's families' keys'. -/
theorem rbK_syn {L : LayoutK} {ps : List Expr} (hs : SiteSynK ctx L ps) :
    KeyGoodK ctx (ps.map (rbK ctx L)) ∧
      ∀ l, LeafIn (ps.map (rbK ctx L)) l → LeafIn ps l ∨ ∃ p ∈ L.fams, LeafIn p.1.ds l := by
  obtain ⟨hhi, ⟨htl, hfl, hty, hkeys⟩, hps⟩ := hs
  -- the replacements
  have hrep : ∀ i b, (if ctx.hiAt 0 ≤ i && i < ctx.hiAt 0 + L.nF then
        (L.fams[i - ctx.hiAt 0]?).map (·.1.expr)
      else if ctx.hiAt 0 + L.nF ≤ i && i < L.hi then
        (L.grp[i - ctx.hiAt 0 - L.nF]?).map fun g => Expr.const g L.lvls
      else none) = some b →
      (∃ p ∈ L.fams, b = p.1.expr) ∨ ∃ g, b = .const g L.lvls := by
    intro i b h
    split at h
    · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .inl ⟨p, List.mem_of_getElem? hp, rfl⟩
    · split at h
      · obtain ⟨g, -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .inr ⟨g, rfl⟩
      · simp at h
  have hkeyL : ∀ p ∈ L.fams, ∀ l ∈ p.1.expr.fvarLeaves, LeafIn p.1.ds l := by
    intro p hp l hl
    rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, h⟩
    · simp [Expr.fvarLeaves] at h
    · exact ⟨x, hx, h⟩
  have hleaf : ∀ x ∈ ps, ∀ l ∈ (rbK ctx L x).fvarLeaves,
      l ∈ x.fvarLeaves ∨ ∃ p ∈ L.fams, LeafIn p.1.ds l := by
    intro x hx l hl
    unfold rbK at hl
    rcases Expr.fvarLeaves_replaceFVars x l hl with h | ⟨i, b, hb, h⟩
    · exact .inl h
    · rcases hrep i b hb with ⟨p, hp, rfl⟩ | ⟨g, rfl⟩
      · exact .inr ⟨p, hp, hkeyL p hp l h⟩
      · simp [Expr.fvarLeaves] at h
  refine ⟨fun y hy => ?_, fun l ⟨y, hy, hl⟩ => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hxw, hxb, hxL⟩ := hps x hx
    refine ⟨?_, ?_, fun l hl => ?_⟩
    · unfold rbK
      refine Expr.WScoped_replaceFVars (fun i b hb => ?_) x hxw fun l hl hn => ?_
      · rcases hrep i b hb with ⟨p, hp, rfl⟩ | ⟨g, rfl⟩
        · exact WScoped_mkAppN (by simp [WScoped]) fun y hy => (hkeys p hp y hy).1
        · simp [WScoped]
      · have hlt := Expr.fvarLeaves_lt_of_wscoped hxw l hl
        refine Nat.lt_of_not_le fun hge => ?_
        split at hn
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          rw [List.getElem?_eq_getElem (by omega)] at hn
          simp at hn
        · split at hn
          · rename_i hc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            rw [List.getElem?_eq_getElem (by omega)] at hn
            simp at hn
          · rename_i hc1 hc2
            simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at hc1 hc2
            have := hc2 (by omega)
            omega
    · unfold rbK
      refine Expr.looseBVarsBounded_replaceFVars (fun i b hb => ?_) x 0 hxb
      rcases hrep i b hb with ⟨p, hp, rfl⟩ | ⟨g, rfl⟩
      · exact looseBVarsBounded_mkAppN rfl fun y hy => (hkeys p hp y hy).2.1
      · rfl
    · rcases hleaf x hx l hl with h | ⟨p, hp, y, hy, h⟩
      · exact hxL l h
      · exact (hkeys p hp y hy).2.2 l h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    rcases hleaf x hx l hl with h | h
    · exact .inl ⟨x, hx, h⟩
    · exact .inr h

/-! ## The match's bindings -/

/-- A successful bind in `Except`. -/
theorem except_bind_okK {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {r : β}
    (h : (m >>= f) = .ok r) : ∃ a, m = .ok a ∧ f a = .ok r := by
  cases m with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- **A binding of the match sits inside the user's target** (a spine prefix
of a subterm). -/
theorem matchGoK_sub {L : LayoutK} {lo nF : Nat} :
    ∀ (fuel : Nat) (p t : Expr) (rs : List (Nat × Expr)),
      matchGoK ctx L lo nF fuel p t = .ok rs → ∀ b ∈ rs, SubT b.2 t
  | 0, p, t, rs, h, b, hb => by simp [matchGoK] at h
  | fuel + 1, p, t, rs, h, b, hb => by
    unfold matchGoK at h
    split at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h; exact nomatch hb
    · split at h
      · dsimp only at h
        split at h
        · -- a pattern variable: the spine prefix, and the indices matched
          try dsimp only at h
          split at h
          · simp at h
          · split at h
            · rename_i rs' hrs'
              simp only [Except.ok.injEq] at h
              subst h
              rcases List.mem_cons.mp hb with rfl | hb
              · exact SubT.spinePrefix t _
              · obtain ⟨r, hr, hbr⟩ := List.mem_flatten.mp hb
                obtain ⟨⟨x, y⟩, hxy, hg⟩ := except_mapM_memK hrs' r hr
                have hy : y ∈ t.getAppArgs := List.mem_of_mem_drop (List.of_mem_zip hxy).2
                exact (matchGoK_sub fuel x y r hg b hbr).trans (SubT.of_mem_getAppArgs hy)
            · simp at h
        · try dsimp only at h
          cases p <;> cases t <;> first
          | (simp at h; done)
          | (exact (matchGoK_sub fuel _ _ rs h b hb).trans (SubT.proj_sub _ _ _))
          | (obtain ⟨x, hx, h⟩ := except_bind_okK h
             obtain ⟨y, hy, h⟩ := except_bind_okK h
             first
             | (simp only [pure, Except.pure, Except.ok.injEq] at h
                subst h
                rcases List.mem_append.mp hb with hb | hb
                · first
                  | exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.app_fn _ _)
                  | exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.lam_ty _ _ _)
                  | exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.pi_ty _ _ _)
                · first
                  | exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.app_arg _ _)
                  | exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.lam_body _ _ _)
                  | exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.pi_body _ _ _))
             | (obtain ⟨z, hz, h⟩ := except_bind_okK h
                simp only [pure, Except.pure, Except.ok.injEq] at h
                subst h
                rcases List.mem_append.mp hb with hb | hb
                · rcases List.mem_append.mp hb with hb | hb
                  · exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.let_ty _ _ _)
                  · exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.let_val _ _ _)
                · exact (matchGoK_sub fuel _ _ z hz b hb).trans (SubT.let_body _ _ _)))
      · dsimp only at h
        cases p <;> cases t <;> first
        | (simp at h; done)
        | (exact (matchGoK_sub fuel _ _ rs h b hb).trans (SubT.proj_sub _ _ _))
        | (obtain ⟨x, hx, h⟩ := except_bind_okK h
           obtain ⟨y, hy, h⟩ := except_bind_okK h
           first
           | (simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              rcases List.mem_append.mp hb with hb | hb
              · first
                | exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.app_fn _ _)
                | exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.lam_ty _ _ _)
                | exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.pi_ty _ _ _)
              · first
                | exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.app_arg _ _)
                | exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.lam_body _ _ _)
                | exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.pi_body _ _ _))
           | (obtain ⟨z, hz, h⟩ := except_bind_okK h
              simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              rcases List.mem_append.mp hb with hb | hb
              · rcases List.mem_append.mp hb with hb | hb
                · exact (matchGoK_sub fuel _ _ x hx b hb).trans (SubT.let_ty _ _ _)
                · exact (matchGoK_sub fuel _ _ y hy b hb).trans (SubT.let_val _ _ _)
              · exact (matchGoK_sub fuel _ _ z hz b hb).trans (SubT.let_body _ _ _)))

theorem BindGoodK.sub {L : LayoutK} {ps : List Expr} {b x : Expr} (h : BindGoodK ctx L ps b)
    (hx : SubT x b) : BindGoodK ctx L ps x :=
  ⟨hx.2 _ h.1, fun l hl => h.2.1 l (hx.1 l hl), fun l hl => h.2.2 l (hx.1 l hl)⟩

theorem viaArgsK_sub {L : LayoutK} {lo nF : Nat} {qs : List Expr} {b : Expr}
    {new : List (Nat × Expr)}
    (h : (do
      let rs ← List.mapM (fun x => matchGoK ctx L lo nF (whnfWalkFuel x.fst + whnfWalkFuel x.snd)
        x.fst x.snd) (qs.zip b.getAppArgs)
      pure rs.flatten : Except String (List (Nat × Expr))) = .ok new) :
    ∀ x ∈ new, SubT x.2 b := by
  obtain ⟨rs, hrs, h⟩ := except_bind_okK h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro x hx
  obtain ⟨r, hr, hxr⟩ := List.mem_flatten.mp hx
  obtain ⟨⟨p, t⟩, hpt, hg⟩ := except_mapM_memK hrs r hr
  exact (matchGoK_sub _ p t r hg x hxr).trans (SubT.of_mem_getAppArgs (List.of_mem_zip hpt).2)

theorem viaArgsK_sub' {L : LayoutK} {lo nF : Nat} {qs : List Expr} {b : Expr}
    {new : List (Nat × Expr)}
    (h : (if (b.getAppArgs.length != qs.length) = true then do
        Except.error "bind: an outer family's binding has another parameter count"
        let rs ← List.mapM (fun x => matchGoK ctx L lo nF (whnfWalkFuel x.fst + whnfWalkFuel x.snd)
          x.fst x.snd) (qs.zip b.getAppArgs)
        pure rs.flatten
      else do
        let rs ← List.mapM (fun x => matchGoK ctx L lo nF (whnfWalkFuel x.fst + whnfWalkFuel x.snd)
          x.fst x.snd) (qs.zip b.getAppArgs)
        pure rs.flatten : Except String (List (Nat × Expr))) = .ok new) :
    ∀ x ∈ new, SubT x.2 b := by
  split at h
  · obtain ⟨_, h', _⟩ := except_bind_okK h; exact nomatch h'
  · exact viaArgsK_sub h

theorem famVar_bindGood {L : LayoutK} {ps : List Expr} (hs : SiteSynK ctx L ps) {x : Nat}
    (hx : x < L.fams.length) :
    BindGoodK ctx L ps (.fvar (ctx.hiAt 0 + x) (L.famTys.getD x (.sort .zero))) := by
  obtain ⟨hhi, ⟨htl, hfl, hty, -⟩, -⟩ := hs
  have hx' : x < L.famTys.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx', Option.getD_some]
  obtain ⟨hw, hb, hL⟩ := hty x hx'
  refine ⟨by simp only [WScoped]; exact ⟨by omega, hw⟩, fun l hl => ?_, fun l hl => .inr (.inr (.inr ⟨x, hx', hl⟩))⟩
  simp only [Expr.fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact hb
  · exact hL l hl

theorem bindInnerK_good {L : LayoutK} {nd : NodeK} {ps : List Expr} (hs : SiteSynK ctx L ps)
    (hkeys : ∀ k ∈ nd.famKeys, BindGoodK ctx L ps k.expr) :
    ∀ (js : List Nat) (bs bs' : List (Nat × Expr)), bindInnerK ctx L nd js bs = .ok bs' →
      (∀ b ∈ bs, BindGoodK ctx L ps b.2) → ∀ b ∈ bs', BindGoodK ctx L ps b.2
  | [], bs, bs', h, hbs => by
    simp only [bindInnerK, Except.ok.injEq] at h
    subst h; exact hbs
  | j :: js, bs, bs', h, hbs => by
    have finish : ∀ new : List (Nat × Expr), (∀ x ∈ new, BindGoodK ctx L ps x.2) →
        bindInnerK ctx L nd js (bs ++ List.filter (fun x => !bs.any fun x_1 => x_1.fst == x.fst) new)
          = .ok bs' → ∀ b ∈ bs', BindGoodK ctx L ps b.2 := by
      intro new hnew h
      refine bindInnerK_good hs hkeys js _ bs' h fun x hx => ?_
      rcases List.mem_append.mp hx with hx | hx
      · exact hbs x hx
      · exact hnew x (List.mem_filter.mp hx).1
    unfold bindInnerK at h
    split at h
    · exact bindInnerK_good hs hkeys js bs bs' h hbs
    rename_i fst b hfind
    have hb : BindGoodK ctx L ps b := hbs _ (List.mem_of_find?_eq_some hfind)
    split at h
    · -- a key application
      dsimp only at h
      split at h
      · exact bindInnerK_good hs hkeys js bs bs' h hbs
      split at h
      · rename_i new hnew
        exact finish new (fun x hx => hb.sub (viaArgsK_sub' hnew x hx)) h
      · simp at h
    · -- a variable
      dsimp only at h
      split at h
      · exact bindInnerK_good hs hkeys js bs bs' h hbs
      split at h
      · rename_i new hnew
        refine finish new ?_ h
        split at hnew
        · exact fun x hx => hb.sub (viaArgsK_sub' hnew x hx)
        · split at hnew
          · simp only [Except.ok.injEq] at hnew
            subst hnew
            intro x hx
            obtain ⟨i', -, hx⟩ := List.mem_filterMap.mp hx
            split at hx
            · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hx
              split
              · rename_i xi hxi
                exact famVar_bindGood hs (List.findIdx?_eq_some_iff_getElem.mp hxi).1
              · exact hkeys k (List.mem_of_getElem? hk)
            · simp at hx
          · simp at hnew
      · simp at h
    · dsimp only at h
      split at h
      · exact bindInnerK_good hs hkeys js bs bs' h hbs
      · simp at h

/-- **A use's syntax, from the run** (U2–U7's (P) half): at a use site whose
spelling is scoped (`SiteSynK`), the node's key the spelling read back, the
node's layout the run's, the match and its inner bindings the run's. -/
theorem useSynK_of_run (hcl : CtxTysClosed ctx) {L : LayoutK} {kn : NestKey} {ps : List Expr}
    {lo : LayoutOutK} {rs : List (List (Nat × Expr))} {bs : List (Nat × Expr)}
    (hs : SiteSynK ctx L ps) (hkn : kn.ds = ps.map (rbK ctx L))
    (hlay : nestLayoutK (m := CheckM) ops env ctx (nestContainer ctx) kn = .ok lo)
    (hbs : (lo.L.dsF.zip ps).mapM (matchStepK ctx L lo.L.nF) = .ok rs)
    (hinner : bindInnerK ctx L (nodeOfK lo) (List.range lo.L.nF).reverse rs.flatten = .ok bs) :
    UseSynK ctx L kn ps lo bs := by
  obtain ⟨hkg, hU6⟩ := rbK_syn hs
  rw [← hkn] at hkg hU6
  have hnode := nodeSynK_of_layout hcl hkg hlay
  refine ⟨hnode, hU6, fun b hb => ?_⟩
  refine bindInnerK_good hs (fun k hk => ?_) _ _ _ hinner (fun b hb => ?_) b hb
  · -- a node family's key
    simp only [nodeOfK, List.mem_map] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    have hkd := hnode.1.2.2.2 p hp
    refine ⟨WScoped_mkAppN (by simp [WScoped]) fun x hx =>
        WScoped.mono (by rw [hs.1]; omega) (hkd x hx).1, fun l hl => ?_, fun l hl => ?_⟩
    · rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, h⟩
      · simp [Expr.fvarLeaves] at h
      · exact (hkd x hx).2.2 l h
    · rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, h⟩
      · simp [Expr.fvarLeaves] at h
      · rcases hU6 l (hnode.2.2.2 p hp x hx l h) with h1 | h1
        · exact .inl h1
        · exact .inr (.inr (.inl h1))
  · -- a binding of the match
    obtain ⟨r, hr, hbr⟩ := List.mem_flatten.mp hb
    obtain ⟨⟨p, t⟩, hpt, hg⟩ := except_mapM_memK hbs r hr
    have ht := (List.of_mem_zip hpt).2
    obtain ⟨htw, -, htL⟩ := hs.2.2 t ht
    exact BindGoodK.sub ⟨htw, htL, fun l hl => .inl ⟨t, ht, hl⟩⟩ (matchGoK_sub _ p t r hg b hbr)

end Layout

end ConLeche
