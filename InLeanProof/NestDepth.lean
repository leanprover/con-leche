module

public import InLeanProof.GrindI
public import InLean.Inductives.Positivity
public import ConLeche.Kernel.Inductives.Positivity

/-!
# The walk's fuel against master's (task #451, lane O7-positivity)

`whnfWalkFuel` is a term's depth plus the slack on both sides.  Both depths
are memoised walks; each computes its plain structural depth (the memo
invariant: every entry is the plain depth of its key), and InLean's, which
reads through `mdata`, is master's on the reading: `depth_TrS`, so
`whnfWalkFuel_TrS`.
-/

public section

namespace InLeanProof

open Lean InLean

/-! ## Master's depth -/

/-- Master's `Expr.depth`, unmemoised. -/
@[expose] def cdepth : ConLeche.Expr → Nat
  | .app f a => max (cdepth f) (cdepth a) + 1
  | .lam t b | .forallE t b => max (cdepth t) (cdepth b) + 1
  | .letE t v b => max (max (cdepth t) (cdepth v)) (cdepth b) + 1
  | .proj _ _ x => cdepth x + 1
  | _ => 1

/-- The memo invariant of master's walk. -/
@[expose] def CDepthMemoInv (memo : Std.HashMap ConLeche.Expr Nat) : Prop :=
  ∀ k r, memo[k]? = some r → r = cdepth k

theorem CDepthMemoInv.insert {memo : Std.HashMap ConLeche.Expr Nat} (hm : CDepthMemoInv memo)
    {e : ConLeche.Expr} {r : Nat} (hr : r = cdepth e) : CDepthMemoInv (memo.insert e r) := by
  intro k r' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    have : e = k := eq_of_beq heq
    subst this
    simp only [Option.some.injEq] at h
    exact h ▸ hr
  · exact hm k r' h

/-- **Master's memoised depth is the plain one** (and keeps the invariant). -/
theorem cdepthGo_spec : ∀ (e : ConLeche.Expr) (memo : Std.HashMap ConLeche.Expr Nat),
    CDepthMemoInv memo →
      (e.depthGo memo).1 = cdepth e ∧ CDepthMemoInv (e.depthGo memo).2 := by
  intro e
  induction e with
  | bvar | fvar | sort | const | lit => intro memo hm; exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro memo hm
    rw [ConLeche.Expr.depthGo]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ihf memo hm
      obtain ⟨h3, h4⟩ := iha _ h2
      have hv : max (f.depthGo memo).1 (a.depthGo (f.depthGo memo).2).1 + 1 = cdepth (.app f a) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | lam t b iht ihb =>
    intro memo hm
    rw [ConLeche.Expr.depthGo]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : max (t.depthGo memo).1 (b.depthGo (t.depthGo memo).2).1 + 1 = cdepth (.lam t b) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | forallE t b iht ihb =>
    intro memo hm
    rw [ConLeche.Expr.depthGo]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : max (t.depthGo memo).1 (b.depthGo (t.depthGo memo).2).1 + 1 =
          cdepth (.forallE t b) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | letE t v b iht ihv ihb =>
    intro memo hm
    rw [ConLeche.Expr.depthGo]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      have hv : max (max (t.depthGo memo).1 (v.depthGo (t.depthGo memo).2).1)
          (b.depthGo (v.depthGo (t.depthGo memo).2).2).1 + 1 = cdepth (.letE t v b) := by
        rw [h1, h3, h5]; rfl
      exact ⟨hv, h6.insert hv⟩
  | proj n i x ih =>
    intro memo hm
    rw [ConLeche.Expr.depthGo]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      have hv : (x.depthGo memo).1 + 1 = cdepth (.proj n i x) := by rw [h1]; rfl
      exact ⟨hv, h2.insert hv⟩

theorem cdepth_eq (e : ConLeche.Expr) : e.depth = cdepth e :=
  (cdepthGo_spec e {} (by intro k r h; simp at h)).1

/-! ## InLean's depth -/

/- The walk's memo compares nodes exactly (`instBEqExprExact`, as
`InLean/ExprOps.lean` elaborates it). -/
attribute [local instance 2000] instBEqExprExact
local instance : LawfulBEq Expr := instBEqExprExact_lawful
local instance : LawfulHashable Expr := ⟨fun _ _ h => by rw [eq_of_beq h]⟩

/-- InLean's `EO.depth`, unmemoised: through `mdata`. -/
@[expose] def ldepth : Expr → Nat
  | .app f a => max (ldepth f) (ldepth a) + 1
  | .lam _ t b _ | .forallE _ t b _ => max (ldepth t) (ldepth b) + 1
  | .letE _ t v b _ => max (max (ldepth t) (ldepth v)) (ldepth b) + 1
  | .mdata _ x => ldepth x
  | .proj _ _ x => ldepth x + 1
  | _ => 1

/-- The memo invariant of InLean's walk. -/
@[expose] def LDepthMemoInv (memo : Std.HashMap Expr Nat) : Prop :=
  ∀ k r, memo[k]? = some r → r = ldepth k

theorem LDepthMemoInv.insert {memo : Std.HashMap Expr Nat} (hm : LDepthMemoInv memo)
    {e : Expr} {r : Nat} (hr : r = ldepth e) : LDepthMemoInv (memo.insert e r) := by
  intro k r' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    have : e = k := eq_of_beq heq
    subst this
    simp only [Option.some.injEq] at h
    exact h ▸ hr
  · exact hm k r' h

/-- **InLean's memoised depth is the plain one** (and keeps the invariant). -/
theorem ldepthGo_spec : ∀ (e : Expr) (memo : Std.HashMap Expr Nat), LDepthMemoInv memo →
    (EO.depthGo e memo).1 = ldepth e ∧ LDepthMemoInv (EO.depthGo e memo).2 := by
  intro e
  induction e with
  | bvar | fvar | mvar | sort | const | lit =>
    intro memo hm
    unfold EO.depthGo
    exact ⟨rfl, hm⟩
  | app f a ihf iha =>
    intro memo hm
    rw [EO.depthGo]
    simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ihf memo hm
      obtain ⟨h3, h4⟩ := iha _ h2
      have hv : max (EO.depthGo f memo).1 (EO.depthGo a (EO.depthGo f memo).2).1 + 1 =
          ldepth (.app f a) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | lam n t b bi iht ihb =>
    intro memo hm
    rw [EO.depthGo]
    simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : max (EO.depthGo t memo).1 (EO.depthGo b (EO.depthGo t memo).2).1 + 1 =
          ldepth (.lam n t b bi) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | forallE n t b bi iht ihb =>
    intro memo hm
    rw [EO.depthGo]
    simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : max (EO.depthGo t memo).1 (EO.depthGo b (EO.depthGo t memo).2).1 + 1 =
          ldepth (.forallE n t b bi) := by
        rw [h1, h3]; rfl
      exact ⟨hv, h4.insert hv⟩
  | letE n t v b nd iht ihv ihb =>
    intro memo hm
    rw [EO.depthGo]
    simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      have hv : max (max (EO.depthGo t memo).1 (EO.depthGo v (EO.depthGo t memo).2).1)
          (EO.depthGo b (EO.depthGo v (EO.depthGo t memo).2).2).1 + 1 =
          ldepth (.letE n t v b nd) := by
        rw [h1, h3, h5]; rfl
      exact ⟨hv, h6.insert hv⟩
  | mdata m x ih =>
    intro memo hm
    rw [EO.depthGo]
    simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      have hv : (EO.depthGo x memo).1 = ldepth (.mdata m x) := h1
      exact ⟨hv, h2.insert hv⟩
  | proj n i x ih =>
    intro memo hm
    rw [EO.depthGo]
    simp only [EO.isCompound, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r hhit; exact ⟨hm _ _ hhit, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      have hv : (EO.depthGo x memo).1 + 1 = ldepth (.proj n i x) := by rw [h1]; rfl
      exact ⟨hv, h2.insert hv⟩

theorem ldepth_eq (e : Expr) : EO.depth e = ldepth e :=
  (ldepthGo_spec e _ (by intro k r h; simp [EO.freshFor] at h)).1

/-! ## The reading -/

theorem ldepth_trE {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) :
    ∀ e : Expr, ldepth e = cdepth (trE fv e) := by
  intro e
  induction e with
  | fvar id =>
    simp only [ldepth, trE]
    cases h : fv id with
    | none => rfl
    | some c => obtain ⟨i, ty, rfl⟩ := hfv id c h; rfl
  | bvar | mvar | sort | const | lit => rfl
  | app f a ihf iha => simp only [ldepth, trE, cdepth, ihf, iha]
  | lam n t b bi iht ihb => simp only [ldepth, trE, cdepth, iht, ihb]
  | forallE n t b bi iht ihb => simp only [ldepth, trE, cdepth, iht, ihb]
  | letE n t v b nd iht ihv ihb => simp only [ldepth, trE, cdepth, iht, ihv, ihb]
  | mdata m x ih => simp only [ldepth, trE, ih]
  | proj n i x ih => simp only [ldepth, trE, cdepth, ih]

/-- **InLean's depth is master's on the reading.** -/
theorem depth_TrS (s : InLean.CState) (e : Expr) : EO.depth e = (TrS s e).depth := by
  rw [ldepth_eq, cdepth_eq, TrS, ldepth_trE (FVarTable.trans_fvarsOnly _)]

/-- **The walk's fuel is master's on the reading.** -/
theorem whnfWalkFuel_TrS (s : InLean.CState) (e : Expr) :
    InLean.whnfWalkFuel e = ConLeche.whnfWalkFuel (TrS s e) := by
  rw [InLean.whnfWalkFuel, ConLeche.whnfWalkFuel, depth_TrS s e]; rfl

end InLeanProof
