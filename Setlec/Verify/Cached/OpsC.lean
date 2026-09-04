import Setlec.Cached.ExprOpsC
import Setlec.Verify.Cached.Erase
import Setlec.Verify.Subst
import Setlec.Verify.InstList
import Setlec.Verify.AbstractRange

/-!
# The cached representation's syntactic operations commute with erasure

Task #163, batch 3.  Every operation of `Setlec/Cached/ExprOpsC.lean`
is proved, on the field invariant `WFc`, to

* return a `WFc` result (so the invariant is closed under the whole
  operation set — nothing downstream re-establishes it), and
* **commute with the erasure**: the erasure of the cached result is the
  `Expr`-side counterpart applied to the erasure of the input.

These are the transpositions of the arena twins' `*I_spec` theorems in
`Setlec/Verify/IExprOps.lean` — same case structure, with the
denotation facts replaced by erasure equalities and no store, no `Ext`,
no `TWF` anywhere.

The memoized walks carry their memo invariant in the
**erasure-function-of-key** form (`… memo[k]? = some r → WFc r ∧
eraseC r = f (eraseC k) …`): the key is never assumed `WFc`, because a
memo hit's key is only `BEq`-equal to the query and `beq_sound`
transports the *erasure*, not the fields.  Insert-preservation goes
through `Std.HashMap.getElem?_insert` plus `beq_sound` on the
colliding key.
-/

namespace Setlec.Cached

open Setlec

namespace ExprC

/-! ## Pair keys

The memo tables are keyed by `ExprC` paired with cursors.  The
`Std.HashMap` lemmas want `EquivBEq` and `LawfulHashable` of the whole
key type; `Erase.lean` supplies them for `ExprC` itself, and products
inherit them componentwise. -/

section PairKey

variable {β : Type} [BEq β] [Hashable β] [EquivBEq β] [LawfulHashable β]

instance : EquivBEq (ExprC × β) where
  symm := by
    intro a b h
    simp only [BEq.beq, Bool.and_eq_true] at *
    exact ⟨by rw [beq_eq h.1]; exact beq_self _, BEq.symm h.2⟩
  trans := by
    intro a b c h₁ h₂
    simp only [BEq.beq, Bool.and_eq_true] at *
    exact ⟨by rw [beq_eq h₁.1]; exact h₂.1, BEq.trans h₁.2 h₂.2⟩
  rfl := by
    intro a
    simp only [BEq.beq, Bool.and_eq_true]
    exact ⟨beq_self _, BEq.refl _⟩

instance : LawfulHashable (ExprC × β) where
  hash_eq := by
    intro a b h
    simp only [BEq.beq, Bool.and_eq_true] at h
    have h₂ := LawfulHashable.hash_eq _ _ h.2
    simp only [Hashable.hash]
    rw [show Prod.fst a = Prod.fst b from beq_eq h.1]
    exact congrArg _ h₂

omit [Hashable β] [EquivBEq β] [LawfulHashable β] in
/-- The key components of a `BEq`-equal pair key: the `ExprC` halves
have equal erasures, the rest is honest equality. -/
theorem pairKey_inv {a c : ExprC} {b d : β} (h : ((a, b) == (c, d)) = true) :
    eraseC a = eraseC c ∧ (b == d) = true := by
  simp only [BEq.beq, Bool.and_eq_true] at h
  exact ⟨beq_sound h.1, h.2⟩

end PairKey

/-! ## List-level erasure

The arena's `DenL` (a list of indices denotes a list of expressions)
transposes to a plain `List.map eraseC` equation plus the invariant on
the elements. -/

/-- Every element of the list satisfies the field invariant. -/
def WFcL (xs : List ExprC) : Prop := ∀ x ∈ xs, WFc x

theorem WFcL.nil : WFcL [] := by intro x hx; cases hx

theorem WFcL.cons {x : ExprC} {xs : List ExprC} (hx : WFc x)
    (hxs : WFcL xs) : WFcL (x :: xs) := by
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · exact h ▸ hx
  · exact hxs y h

theorem WFcL.head {x : ExprC} {xs : List ExprC} (h : WFcL (x :: xs)) :
    WFc x := h x (by simp)

theorem WFcL.tail {x : ExprC} {xs : List ExprC} (h : WFcL (x :: xs)) :
    WFcL xs := fun y hy => h y (by simp [hy])

theorem WFcL.append {xs ys : List ExprC} (hx : WFcL xs) (hy : WFcL ys) :
    WFcL (xs ++ ys) := by
  intro z hz
  rcases List.mem_append.mp hz with h | h
  · exact hx z h
  · exact hy z h

theorem WFcL.reverse {xs : List ExprC} (h : WFcL xs) : WFcL xs.reverse :=
  fun y hy => h y (List.mem_reverse.mp hy)

/-! ## Optional results

The arena's `OptDen` (an optional index relates to an optional
expression) transposes to this. -/

/-- An optional cached result carries the invariant and erases to the
optional `Expr`-side result. -/
def OptEr : Option ExprC → Option Expr → Prop
  | none, none => True
  | some e, some x => WFc e ∧ eraseC e = x
  | _, _ => False

/-! ## The one-level view -/

/-- The `Expr`-side view builder — the counterpart of `ExprC.ofView`
(the core's `internI` at this representation).  `Expr.view` is its
inverse (`ofViewE_view`). -/
def ofViewE : ExprView Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n ty
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app f a
  | .lam n ty b m => .lam n ty b m
  | .forallE n ty b m => .forallE n ty b m
  | .letE n ty v b => .letE n ty v b
  | .lit l => .lit l
  | .proj s i e => .proj s i e

@[simp] theorem ofViewE_view (a : Expr) : ofViewE a.view = a := by
  cases a <;> rfl

/-- Erasure at the view level. -/
def eraseCV : ExprView ExprC → ExprView Expr
  | .bvar i => .bvar i
  | .fvar idx n ty => .fvar idx n (eraseC ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (eraseC f) (eraseC a)
  | .lam n ty b m => .lam n (eraseC ty) (eraseC b) m
  | .forallE n ty b m => .forallE n (eraseC ty) (eraseC b) m
  | .letE n ty v b => .letE n (eraseC ty) (eraseC v) (eraseC b)
  | .lit l => .lit l
  | .proj s i e => .proj s i (eraseC e)

/-- The field invariant on a view's children. -/
def WFcV : ExprView ExprC → Prop
  | .bvar _ | .sort _ | .const _ _ | .lit _ => True
  | .fvar _ _ ty => WFc ty
  | .app f a => WFc f ∧ WFc a
  | .lam _ ty b _ | .forallE _ ty b _ => WFc ty ∧ WFc b
  | .letE _ ty v b => WFc ty ∧ WFc v ∧ WFc b
  | .proj _ _ e => WFc e

/-- Reading a node one level down preserves the invariant and commutes
with the erasure. -/
theorem view_spec {e : ExprC} (hw : WFc e) :
    WFcV (view e) ∧ eraseCV (view e) = (eraseC e).view := by
  cases e with
  | fvar idx n ty => exact ⟨hw.fvar_inv.1, rfl⟩
  | app f a => exact ⟨⟨hw.app_inv.1, hw.app_inv.2.1⟩, rfl⟩
  | lam n ty b m => exact ⟨⟨hw.lam_inv.1, hw.lam_inv.2.1⟩, rfl⟩
  | forallE n ty b m =>
    exact ⟨⟨hw.forallE_inv.1, hw.forallE_inv.2.1⟩, rfl⟩
  | letE n ty v b =>
    exact ⟨⟨hw.letE_inv.1, hw.letE_inv.2.1, hw.letE_inv.2.2.1⟩, rfl⟩
  | proj s i sub => exact ⟨hw.proj_inv.1, rfl⟩
  | _ => exact ⟨trivial, rfl⟩

/-- Building a node from a one-level view preserves the invariant and
commutes with the erasure — the transposition of the arena's
`intern_spec`. -/
theorem ofView_spec {v : ExprView ExprC} (hv : WFcV v) :
    WFc (ofView v) ∧ eraseC (ofView v) = ofViewE (eraseCV v) := by
  cases v with
  | bvar i => exact ⟨WFc.mkBVar i, rfl⟩
  | fvar idx n ty => exact ⟨WFc.mkFVar idx n hv, rfl⟩
  | sort u => exact ⟨WFc.mkSort u, rfl⟩
  | const n us => exact ⟨WFc.mkConst n us, rfl⟩
  | app f a => exact ⟨WFc.mkApp hv.1 hv.2, rfl⟩
  | lam n ty b m => exact ⟨WFc.mkLam n m hv.1 hv.2, rfl⟩
  | forallE n ty b m => exact ⟨WFc.mkForallE n m hv.1 hv.2, rfl⟩
  | letE n ty v b => exact ⟨WFc.mkLetE n hv.1 hv.2.1 hv.2.2, rfl⟩
  | lit l => exact ⟨WFc.mkLit l, rfl⟩
  | proj s i e => exact ⟨WFc.mkProj s i hv, rfl⟩

/-! ## Spines -/

theorem getAppFn_spec : ∀ {e : ExprC}, WFc e →
    WFc (getAppFn e) ∧ eraseC (getAppFn e) = (eraseC e).getAppFn := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hw
    exact ihf hw.app_inv.1
  | _ => intro hw; exact ⟨hw, rfl⟩

theorem getAppArgsAcc_spec : ∀ {e : ExprC}, WFc e →
    ∀ {acc : List ExprC}, WFcL acc →
      WFcL (getAppArgsAcc e acc) ∧
        (getAppArgsAcc e acc).map eraseC
          = (eraseC e).getAppArgs ++ acc.map eraseC := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hw acc hacc
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    obtain ⟨h₁, h₂⟩ := ihf hf (acc := a :: acc) (WFcL.cons ha hacc)
    refine ⟨h₁, ?_⟩
    rw [show getAppArgsAcc (.app f a) acc
        = getAppArgsAcc f (a :: acc) from rfl, h₂,
      show eraseC (.app f a)
        = .app (eraseC f) (eraseC a) from rfl,
      show ((.app (eraseC f) (eraseC a) : Expr)).getAppArgs
        = (eraseC f).getAppArgs ++ [eraseC a] from rfl,
      List.append_assoc]
    rfl
  | _ => intro hw acc hacc; exact ⟨hacc, rfl⟩

theorem getAppArgs_spec {e : ExprC} (hw : WFc e) :
    WFcL (getAppArgs e) ∧
      (getAppArgs e).map eraseC = (eraseC e).getAppArgs := by
  obtain ⟨h₁, h₂⟩ := getAppArgsAcc_spec hw (acc := []) WFcL.nil
  exact ⟨h₁, by simpa [getAppArgs] using h₂⟩

theorem mkAppN_spec : ∀ {args : List ExprC}, WFcL args →
    ∀ {f : ExprC}, WFc f →
      WFc (mkAppN f args) ∧
        eraseC (mkAppN f args) = Expr.mkAppN (eraseC f) (args.map eraseC)
  | [], _, f, hf => ⟨hf, rfl⟩
  | a :: as, hargs, f, hf => by
    have := mkAppN_spec (args := as) hargs.tail
      (f := mkApp f a) (WFc.mkApp hf hargs.head)
    rw [show mkAppN f (a :: as) = mkAppN (mkApp f a) as from rfl]
    refine ⟨this.1, ?_⟩
    rw [this.2]
    rfl

/-! ## Telescope queries -/

theorem stripPisBody_spec : ∀ {k : Nat} {e : ExprC}, WFc e →
    OptEr (stripPisBody k e) (((eraseC e).stripPis k).map (·.2)) := by
  intro k
  induction k with
  | zero => intro e hw; exact ⟨hw, rfl⟩
  | succ k ih =>
    intro e hw
    cases e with
    | forallE n ty b m =>
      obtain ⟨-, hb, -⟩ := hw.forallE_inv
      have := ih (e := b) hb
      rw [show stripPisBody (k + 1) (.forallE n ty b m)
          = stripPisBody k b from rfl]
      rw [show ((eraseC (.forallE n ty b m)).stripPis (k + 1)).map
            (·.2)
          = ((eraseC b).stripPis k).map (·.2) by
        cases hs : (eraseC b).stripPis k <;>
          simp [eraseC, Expr.stripPis, hs]]
      exact this
    | _ => exact trivial

theorem pisToLams_spec : ∀ {k : Nat} {e body : ExprC}, WFc e → WFc body →
    OptEr (pisToLams k e body)
      (Expr.pisToLams k (eraseC e) (eraseC body)) := by
  intro k
  induction k with
  | zero => intro e body hw hb; exact ⟨hb, rfl⟩
  | succ k ih =>
    intro e body hw hb
    cases e with
    | forallE n ty rest mb =>
      obtain ⟨hty, hrest, -⟩ := hw.forallE_inv
      have hrec := ih (e := rest) (body := body) hrest hb
      rw [show pisToLams (k + 1) (.forallE n ty rest mb) body
          = (match pisToLams k rest body with
             | some b => some (mkLam n ty b ⟨mb.bi, .never⟩)
             | none => none) from rfl]
      rw [show Expr.pisToLams (k + 1)
            (eraseC (.forallE n ty rest mb)) (eraseC body)
          = (Expr.pisToLams k (eraseC rest) (eraseC body)).map
              (fun bx => .lam n (eraseC ty) bx ⟨mb.bi, .never⟩) from rfl]
      cases hgo : pisToLams k rest body with
      | none =>
        rw [hgo] at hrec
        cases hox : Expr.pisToLams k (eraseC rest) (eraseC body) with
        | none => exact trivial
        | some bx => rw [hox] at hrec; exact absurd hrec not_false
      | some bc =>
        rw [hgo] at hrec
        cases hox : Expr.pisToLams k (eraseC rest) (eraseC body) with
        | none => rw [hox] at hrec; exact absurd hrec not_false
        | some bx =>
          rw [hox] at hrec
          obtain ⟨hbc, hbe⟩ := hrec
          refine ⟨WFc.mkLam n _ hty hbc, ?_⟩
          rw [eraseC_mkLam, hbe]
    | _ => exact trivial

/-! ## Scope queries -/

theorem looseBVarsBounded_spec {k : Nat} {e : ExprC} (hw : WFc e) :
    looseBVarsBounded k e = (eraseC e).looseBVarsBounded k := by
  rw [show looseBVarsBounded k e = decide (e.bvarB ≤ k) from rfl,
    bvarB_exact hw]
  cases hb : (eraseC e).looseBVarsBounded k with
  | true =>
    simp only [decide_eq_true_eq]
    exact EStore.looseBVarsBounded_iff.mp hb
  | false =>
    simp only [decide_eq_false_iff_not]
    intro hle
    rw [EStore.looseBVarsBounded_iff.mpr hle] at hb
    exact Bool.noConfusion hb

/-! ## Instantiation of one bound variable

The memo invariant is stated in the **erasure-function-of-key** form:
nothing is claimed about the key's *fields*, only that the stored value
is well formed and erases to the substitution applied to the key's
erasure.  That is exactly what survives a memo hit, whose key is only
`BEq`-equal to the query. -/

/-- The `instantiate1` memo invariant at the ambient replacement `v`. -/
def Memo1Inv (v : ExprC) (memo : MemoN) : Prop :=
  ∀ (k : ExprC) (c : Nat) (r : ExprC), memo[(k, c)]? = some r →
    WFc r ∧ eraseC r = (eraseC k).instantiate1 (eraseC v) c

theorem Memo1Inv.empty {v : ExprC} : Memo1Inv v {} := by
  intro k c r h
  simp at h

theorem Memo1Inv.insert {v : ExprC} {memo : MemoN} (hm : Memo1Inv v memo)
    {e r : ExprC} {d : Nat} (hr : WFc r)
    (heq : eraseC r = (eraseC e).instantiate1 (eraseC v) d) :
    Memo1Inv v (memo.insert (e, d) r) := by
  intro k c r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hd⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hd]
    exact ⟨hr, heq⟩

  · exact hm k c r' hk

/-- **The `instantiate1` core commutes with erasure.**  The
transposition of `instantiate1I_spec`: the walk's `bvarB` cutoff is the
`Expr` side's `instantiate1_eq_self`, and every rebuilt node's erasure
is the corresponding `Expr` constructor. -/
theorem instantiate1Go_spec {v : ExprC} (hv : WFc v) : ∀ {e : ExprC}, WFc e →
    ∀ {memo : MemoN} {d : Nat}, Memo1Inv v memo →
      WFc (instantiate1Go v memo e d).1 ∧
        Memo1Inv v (instantiate1Go v memo e d).2 ∧
        eraseC (instantiate1Go v memo e d).1
          = (eraseC e).instantiate1 (eraseC v) d := by
  intro e
  induction e with
  | bvar i =>
    intro hw memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · dsimp only
        split
        · rename_i hid
          refine ⟨hv, hm.insert hv ?_, ?_⟩ <;>
            simp [eraseC, hid]
        · split
          · rename_i hid hid'
            refine ⟨WFc.mkBVar _, hm.insert (WFc.mkBVar _) ?_, ?_⟩ <;>
              simp [eraseC, hid, hid']
          · rename_i hid hid'
            refine ⟨hw, hm.insert hw ?_, ?_⟩ <;>
              simp [eraseC, hid, hid']
  | fvar idx n ty iht =>
    intro hw memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | sort u =>
    intro hw memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | const n us =>
    intro hw memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | lit l =>
    intro hw memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | app f a ihf iha =>
    intro hw memo d hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨hf1, hf2, hf3⟩ := ihf hf (d := d) hm
        rcases hpf : instantiate1Go v memo f d with ⟨f', mf⟩
        rw [hpf] at hf1 hf2 hf3
        obtain ⟨ha1, ha2, ha3⟩ := iha ha (d := d) hf2
        rcases hpa : instantiate1Go v mf a d with ⟨a', ma⟩
        rw [hpa] at ha1 ha2 ha3
        simp only [hpf, hpa]
        have hres : eraseC (mkApp f' a')
            = (eraseC (.app f a)).instantiate1 (eraseC v) d := by
          rw [eraseC_mkApp, hf3, ha3]; rfl
        exact ⟨WFc.mkApp hf1 ha1, ha2.insert (WFc.mkApp hf1 ha1) hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro hw memo d hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (d := d) hm
        rcases hp : instantiate1Go v memo ty d with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd (d := d + 1) h2
        rcases hq : instantiate1Go v mt bd (d + 1) with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkLam n ty' b' m)
            = (eraseC (.lam n ty bd m)).instantiate1
                (eraseC v) d := by
          rw [eraseC_mkLam, h3, h6]; rfl
        exact ⟨WFc.mkLam n m h1 h4, h5.insert (WFc.mkLam n m h1 h4) hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro hw memo d hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (d := d) hm
        rcases hp : instantiate1Go v memo ty d with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd (d := d + 1) h2
        rcases hq : instantiate1Go v mt bd (d + 1) with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkForallE n ty' b' m)
            = (eraseC (.forallE n ty bd m)).instantiate1
                (eraseC v) d := by
          rw [eraseC_mkForallE, h3, h6]; rfl
        exact ⟨WFc.mkForallE n m h1 h4,
          h5.insert (WFc.mkForallE n m h1 h4) hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro hw memo d hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (d := d) hm
        rcases hp : instantiate1Go v memo ty d with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihv hval (d := d) h2
        rcases hq : instantiate1Go v mt val d with ⟨v', mv⟩
        rw [hq] at h4 h5 h6
        obtain ⟨h7, h8, h9⟩ := ihb hbd (d := d + 1) h5
        rcases hr : instantiate1Go v mv bd (d + 1) with ⟨b', mb⟩
        rw [hr] at h7 h8 h9
        simp only [hp, hq, hr]
        have hres : eraseC (mkLetE n ty' v' b')
            = (eraseC (.letE n ty val bd)).instantiate1
                (eraseC v) d := by
          rw [eraseC_mkLetE, h3, h6, h9]; rfl
        exact ⟨WFc.mkLetE n h1 h4 h7,
          h8.insert (WFc.mkLetE n h1 h4 h7) hres, hres⟩
  | proj s i sub ihe =>
    intro hw memo d hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihe he (d := d) hm
        rcases hp : instantiate1Go v memo sub d with ⟨s', ms⟩
        rw [hp] at h1 h2 h3
        simp only [hp]
        have hres : eraseC (mkProj s i s')
            = (eraseC (.proj s i sub)).instantiate1
                (eraseC v) d := by
          rw [eraseC_mkProj, h3]; rfl
        exact ⟨WFc.mkProj s i h1, h2.insert (WFc.mkProj s i h1) hres, hres⟩

theorem instantiate1_spec {e v : ExprC} {d : Nat} (hw : WFc e) (hv : WFc v) :
    WFc (instantiate1 e v d) ∧
      eraseC (instantiate1 e v d) = (eraseC e).instantiate1 (eraseC v) d := by
  rw [instantiate1]
  split
  · rename_i hcut
    exact ⟨hw, (Expr.instantiate1_eq_self (bvarB_le hw hcut)).symm⟩
  · obtain ⟨h1, -, h3⟩ :=
      instantiate1Go_spec (v := v) hv hw (d := d) Memo1Inv.empty
    exact ⟨h1, h3⟩

/-! ## Bulk instantiation -/

/-- The bulk-instantiation memo invariant: every stored value is well
formed and erases to the substitution of the *live prefix* named by the
key at the key's own erasure. -/
def MemoLInv (ws : List Expr) (memo : MemoNL) : Prop :=
  ∀ (e : ExprC) (k c : Nat) (r : ExprC), memo[(e, k, c)]? = some r →
    WFc r ∧ eraseC r = (eraseC e).instantiateList (ws.take k) c

theorem MemoLInv.empty {ws : List Expr} : MemoLInv ws {} := by
  intro e k c r h
  simp at h

theorem MemoLInv.insert {ws : List Expr} {memo : MemoNL}
    (hm : MemoLInv ws memo) {e r : ExprC} {k c : Nat} (hr : WFc r)
    (heq : eraseC r = (eraseC e).instantiateList (ws.take k) c) :
    MemoLInv ws (memo.insert (e, k, c) r) := by
  intro e' k' c' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hkc⟩ := pairKey_inv hbeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (eq_of_beq hkc)
    rw [← he]
    exact ⟨hr, heq⟩
  · exact hm e' k' c' r' hk

/-! `Expr.instantiateList` is well founded, so it does not reduce
definitionally: the per-constructor equations have to be named. -/

private theorem instList_app (f a : Expr) (ws : List Expr) (d : Nat) :
    (Expr.app f a).instantiateList ws d
      = .app (f.instantiateList ws d) (a.instantiateList ws d) := by
  rw [Expr.instantiateList]

private theorem instList_lam (n : Name) (ty b : Expr) (m : BinderMeta)
    (ws : List Expr) (d : Nat) :
    (Expr.lam n ty b m).instantiateList ws d
      = .lam n (ty.instantiateList ws d) (b.instantiateList ws (d + 1)) m := by
  rw [Expr.instantiateList]

private theorem instList_forallE (n : Name) (ty b : Expr) (m : BinderMeta)
    (ws : List Expr) (d : Nat) :
    (Expr.forallE n ty b m).instantiateList ws d
      = .forallE n (ty.instantiateList ws d)
          (b.instantiateList ws (d + 1)) m := by
  rw [Expr.instantiateList]

private theorem instList_letE (n : Name) (ty v b : Expr) (ws : List Expr)
    (d : Nat) :
    (Expr.letE n ty v b).instantiateList ws d
      = .letE n (ty.instantiateList ws d) (v.instantiateList ws d)
          (b.instantiateList ws (d + 1)) := by
  rw [Expr.instantiateList]

private theorem instList_proj (s : Name) (i : Nat) (e : Expr)
    (ws : List Expr) (d : Nat) :
    (Expr.proj s i e).instantiateList ws d
      = .proj s i (e.instantiateList ws d) := by
  rw [Expr.instantiateList]

/-- The leaf arms: `fvar`/`sort`/`const`/`lit` erasures are
`looseBVarsBounded` at every cursor, so bulk instantiation is the
identity on them (`Expr.instantiateList` is well-founded, hence does
not reduce definitionally — the equation has to be supplied). -/
private theorem instList_leaf {e : ExprC} {ws : List Expr} {d : Nat}
    (h : (eraseC e).looseBVarsBounded d = true) :
    eraseC e = (eraseC e).instantiateList ws d :=
  (Expr.instantiateList_eq_self h).symm

/-- **The bulk-instantiation core commutes with erasure.**  The
transposition of `instantiateListIGo_spec`: the induction is the
function's own — strong on the live prefix `k` (the `bvar` arm re-enters
at the replacement with a shorter prefix), structural on the node
inside it. -/
theorem instantiateListGo_spec {vs : Array ExprC} (hvs : WFcL vs.toList) :
    ∀ (k : Nat) (e : ExprC), WFc e → ∀ {memo : MemoNL} {d : Nat},
      k ≤ vs.size → MemoLInv (vs.toList.map eraseC) memo →
      WFc (instantiateListGo vs memo e k d).1 ∧
        MemoLInv (vs.toList.map eraseC) (instantiateListGo vs memo e k d).2 ∧
        eraseC (instantiateListGo vs memo e k d).1
          = (eraseC e).instantiateList
              ((vs.toList.map eraseC).take k) d := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro e
  induction e with
  | bvar i =>
    intro hw memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · rename_i hk0 hcut _
          have hlen : ((vs.toList.map eraseC).take k).length = k := by
            simp; omega
          dsimp only
          split
          · rename_i hid
            have hres : eraseC (Expr.bvar i)
                = (eraseC (Expr.bvar i)).instantiateList
                    ((vs.toList.map eraseC).take k) d := by
              simp [eraseC, Expr.instantiateList, hid]
            exact ⟨hw, hm.insert hw hres, hres⟩
          · rename_i hid
            split
            · rename_i hidk
              split
              · rename_i hidv
                have hmem : WFc vs[i - d] := hvs vs[i - d] (by simp)
                obtain ⟨h1, h2, h3⟩ :=
                  ihk (i - d) hidk vs[i - d] hmem (d := d)
                    (Nat.le_of_lt hidv) hm
                rcases hp : instantiateListGo vs memo vs[i - d] (i - d) d
                  with ⟨r₁, m₁⟩
                rw [hp] at h1 h2 h3
                have hget : ((vs.toList.map eraseC).take k)[i - d]'(by
                    rw [hlen]; exact hidk) = eraseC vs[i - d] := by
                  rw [List.getElem_take]
                  simp
                have htk : ((vs.toList.map eraseC).take k).take (i - d)
                    = (vs.toList.map eraseC).take (i - d) := by
                  rw [List.take_take]
                  congr 1
                  omega
                have hres : eraseC r₁
                    = (eraseC (Expr.bvar i)).instantiateList
                        ((vs.toList.map eraseC).take k) d := by
                  rw [h3, show eraseC (Expr.bvar i)
                      = Expr.bvar i from rfl, Expr.instantiateList,
                    if_neg hid, dif_pos (by rw [hlen]; exact hidk), hget,
                    htk]
                exact ⟨h1, h2.insert h1 hres, hres⟩
              · rename_i hidv
                exact absurd (by omega : i - d < vs.size) hidv
            · rename_i hidk
              have hres : eraseC (mkBVar (i - k))
                  = (eraseC (Expr.bvar i)).instantiateList
                      ((vs.toList.map eraseC).take k) d := by
                rw [eraseC_mkBVar, show eraseC (Expr.bvar i)
                    = Expr.bvar i from rfl, Expr.instantiateList,
                  if_neg hid, dif_neg (by rw [hlen]; exact hidk), hlen]
              exact ⟨WFc.mkBVar _, hm.insert (WFc.mkBVar _) hres, hres⟩
  | fvar idx n ty iht =>
    intro hw memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · exact ⟨hw, hm.insert hw (instList_leaf rfl), instList_leaf rfl⟩
  | sort u =>
    intro hw memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · exact ⟨hw, hm.insert hw (instList_leaf rfl), instList_leaf rfl⟩
  | const n us =>
    intro hw memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · exact ⟨hw, hm.insert hw (instList_leaf rfl), instList_leaf rfl⟩
  | lit l =>
    intro hw memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · exact ⟨hw, hm.insert hw (instList_leaf rfl), instList_leaf rfl⟩
  | app f a ihf iha =>
    intro hw memo d hk hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · obtain ⟨h1, h2, h3⟩ := ihf hf (d := d) hk hm
          rcases hp : instantiateListGo vs memo f k d with ⟨f', mf⟩
          rw [hp] at h1 h2 h3
          obtain ⟨h4, h5, h6⟩ := iha ha (d := d) hk h2
          rcases hq : instantiateListGo vs mf a k d with ⟨a', ma⟩
          rw [hq] at h4 h5 h6
          simp only [hp, hq]
          have hres : eraseC (mkApp f' a')
              = (eraseC (.app f a)).instantiateList
                  ((vs.toList.map eraseC).take k) d := by
            rw [show eraseC (Expr.app f a)
                = Expr.app (eraseC f) (eraseC a) from rfl,
              instList_app, eraseC_mkApp, h3, h6]
          exact ⟨WFc.mkApp h1 h4, h5.insert (WFc.mkApp h1 h4) hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro hw memo d hk hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · obtain ⟨h1, h2, h3⟩ := iht hty (d := d) hk hm
          rcases hp : instantiateListGo vs memo ty k d with ⟨ty', mt⟩
          rw [hp] at h1 h2 h3
          obtain ⟨h4, h5, h6⟩ := ihb hbd (d := d + 1) hk h2
          rcases hq : instantiateListGo vs mt bd k (d + 1) with ⟨b', mb⟩
          rw [hq] at h4 h5 h6
          simp only [hp, hq]
          have hres : eraseC (mkLam n ty' b' m)
              = (eraseC (.lam n ty bd m)).instantiateList
                  ((vs.toList.map eraseC).take k) d := by
            rw [show eraseC (Expr.lam n ty bd m)
                = Expr.lam n (eraseC ty) (eraseC bd) m from rfl,
              instList_lam, eraseC_mkLam, h3, h6]
          exact ⟨WFc.mkLam n m h1 h4, h5.insert (WFc.mkLam n m h1 h4) hres,
            hres⟩
  | forallE n ty bd m iht ihb =>
    intro hw memo d hk hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · obtain ⟨h1, h2, h3⟩ := iht hty (d := d) hk hm
          rcases hp : instantiateListGo vs memo ty k d with ⟨ty', mt⟩
          rw [hp] at h1 h2 h3
          obtain ⟨h4, h5, h6⟩ := ihb hbd (d := d + 1) hk h2
          rcases hq : instantiateListGo vs mt bd k (d + 1) with ⟨b', mb⟩
          rw [hq] at h4 h5 h6
          simp only [hp, hq]
          have hres : eraseC (mkForallE n ty' b' m)
              = (eraseC (.forallE n ty bd m)).instantiateList
                  ((vs.toList.map eraseC).take k) d := by
            rw [show eraseC (Expr.forallE n ty bd m)
                = Expr.forallE n (eraseC ty) (eraseC bd) m from rfl,
              instList_forallE, eraseC_mkForallE, h3, h6]
          exact ⟨WFc.mkForallE n m h1 h4,
            h5.insert (WFc.mkForallE n m h1 h4) hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro hw memo d hk hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · obtain ⟨h1, h2, h3⟩ := iht hty (d := d) hk hm
          rcases hp : instantiateListGo vs memo ty k d with ⟨ty', mt⟩
          rw [hp] at h1 h2 h3
          obtain ⟨h4, h5, h6⟩ := ihv hval (d := d) hk h2
          rcases hq : instantiateListGo vs mt val k d with ⟨v', mv⟩
          rw [hq] at h4 h5 h6
          obtain ⟨h7, h8, h9⟩ := ihb hbd (d := d + 1) hk h5
          rcases hr : instantiateListGo vs mv bd k (d + 1) with ⟨b', mb⟩
          rw [hr] at h7 h8 h9
          simp only [hp, hq, hr]
          have hres : eraseC (mkLetE n ty' v' b')
              = (eraseC (.letE n ty val bd)).instantiateList
                  ((vs.toList.map eraseC).take k) d := by
            rw [show eraseC (Expr.letE n ty val bd)
                = Expr.letE n (eraseC ty) (eraseC val) (eraseC bd) from rfl,
              instList_letE, eraseC_mkLetE, h3, h6, h9]
          exact ⟨WFc.mkLetE n h1 h4 h7,
            h8.insert (WFc.mkLetE n h1 h4 h7) hres, hres⟩
  | proj s i sub ihe =>
    intro hw memo d hk hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hw, hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hw, hm,
          (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨(hm _ _ _ _ hhit).1, hm, (hm _ _ _ _ hhit).2⟩
        · obtain ⟨h1, h2, h3⟩ := ihe he (d := d) hk hm
          rcases hp : instantiateListGo vs memo sub k d with ⟨s', ms⟩
          rw [hp] at h1 h2 h3
          simp only [hp]
          have hres : eraseC (mkProj s i s')
              = (eraseC (.proj s i sub)).instantiateList
                  ((vs.toList.map eraseC).take k) d := by
            rw [show eraseC (Expr.proj s i sub)
                = Expr.proj s i (eraseC sub) from rfl,
              instList_proj, eraseC_mkProj, h3]
          exact ⟨WFc.mkProj s i h1, h2.insert (WFc.mkProj s i h1) hres, hres⟩

theorem instantiateList_spec {e : ExprC} {vs : List ExprC} {d : Nat}
    (hw : WFc e) (hvs : WFcL vs) :
    WFc (instantiateList e vs d) ∧
      eraseC (instantiateList e vs d)
        = (eraseC e).instantiateList (vs.map eraseC) d := by
  cases vs with
  | nil => exact ⟨hw, by rw [instantiateList]; simp [Expr.instantiateList_nil]⟩
  | cons v vs' =>
    have harr : (v :: vs').toArray.toList = v :: vs' := rfl
    obtain ⟨h1, -, h3⟩ :=
      instantiateListGo_spec (vs := (v :: vs').toArray)
        (harr ▸ hvs) (v :: vs').toArray.size e hw (d := d)
        (Nat.le_refl _) MemoLInv.empty
    refine ⟨h1, ?_⟩
    rw [instantiateList]
    rw [h3, harr]
    congr 1
    rw [show (v :: vs').toArray.size = ((v :: vs').map eraseC).length from
        by simp, List.take_length]

/-! ## Telescope-context spine instantiation -/

theorem instSpineChain_spec : ∀ {args : List ExprC}, WFcL args →
    ∀ {t : Nat} {e : ExprC}, WFc e →
      WFc (instSpineChain args t e) ∧
        eraseC (instSpineChain args t e)
          = Expr.instSpine (args.map eraseC) t (eraseC e)
  | [], _, _, _, he => ⟨he, rfl⟩
  | a :: as, hargs, t, e, he => by
    obtain ⟨h1, h2⟩ := instantiate1_spec (e := e) (v := a) (d := t) he
      hargs.head
    obtain ⟨h3, h4⟩ := instSpineChain_spec (args := as) hargs.tail
      (t := t - 1) h1
    rw [show instSpineChain (a :: as) t e
        = instSpineChain as (t - 1) (instantiate1 e a t) from rfl]
    refine ⟨h3, ?_⟩
    rw [h4, h2]
    rfl

theorem instSpine_spec {args : List ExprC} {t : Nat} {e : ExprC}
    (hargs : WFcL args) (he : WFc e) :
    WFc (instSpine args t e) ∧
      eraseC (instSpine args t e)
        = Expr.instSpine (args.map eraseC) t (eraseC e) := by
  rw [instSpine]
  split
  · rename_i hlen
    have hxlen : (args.map eraseC).length = t + 1 := by simpa using hlen
    obtain ⟨h1, h2⟩ :=
      instantiateList_spec (e := e) (vs := args.reverse) (d := 0) he
        hargs.reverse
    refine ⟨h1, ?_⟩
    rw [h2, Expr.instSpine_eq_instantiateList _ t _ hxlen, List.map_reverse]
  · exact instSpineChain_spec hargs he

/-! ## Bulk instantiation on a reversed accumulator

As in the arena (`instantiateRevIGo_eq`), the reversed walk is the
forward walk on the reversed array — proved pointwise, so every
`instantiateList` fact transfers. -/

theorem instantiateRevGo_eq {vs : Array ExprC} :
    ∀ (k : Nat) (e : ExprC) (memo : MemoNL) (d : Nat),
      instantiateRevGo vs memo e k d
        = instantiateListGo vs.reverse memo e k d := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro e
  induction e with
  | bvar i =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.bvar i).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    cases hmemo : memo[(Expr.bvar i, k, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      by_cases hid : i < d
      · rw [if_pos hid, if_pos hid]
      rw [if_neg hid, if_neg hid]
      by_cases hidk : i - d < k
      · rw [dif_pos hidk, dif_pos hidk]
        have hsz : vs.reverse.size = vs.size := by simp
        by_cases hidv : i - d < vs.size
        · rw [dif_pos hidv, dif_pos (hsz ▸ hidv)]
          have hget : vs.reverse[i - d]'(hsz ▸ hidv)
              = vs[vs.size - 1 - (i - d)]'(by omega) := by
            simp [Array.getElem_reverse]
          rw [ihk (i - d) hidk, hget]
        · rw [dif_neg hidv, dif_neg (fun h => hidv (hsz ▸ h))]
      · rw [dif_neg hidk, dif_neg hidk]
  | fvar idx n ty iht =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
  | sort u =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
  | const n us =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
  | lit l =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
  | app f a ihf iha =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.app f a).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    cases hmemo : memo[(Expr.app f a, k, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      rw [ihf memo d]
      rcases h1 : instantiateListGo vs.reverse memo f k d with ⟨f', m₁⟩
      rw [iha m₁ d]
  | lam n ty bd m iht ihb =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.lam n ty bd m).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    cases hmemo : memo[(Expr.lam n ty bd m, k, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      rw [iht memo d]
      rcases h1 : instantiateListGo vs.reverse memo ty k d with ⟨ty', m₁⟩
      rw [ihb m₁ (d + 1)]
  | forallE n ty bd m iht ihb =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.forallE n ty bd m).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    cases hmemo : memo[(Expr.forallE n ty bd m, k, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      rw [iht memo d]
      rcases h1 : instantiateListGo vs.reverse memo ty k d with ⟨ty', m₁⟩
      rw [ihb m₁ (d + 1)]
  | letE n ty val bd iht ihv ihb =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.letE n ty val bd).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    cases hmemo : memo[(Expr.letE n ty val bd, k, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      rw [iht memo d]
      rcases h1 : instantiateListGo vs.reverse memo ty k d with ⟨ty', m₁⟩
      rw [ihv m₁ d]
      rcases h2 : instantiateListGo vs.reverse m₁ val k d with ⟨v', m₂⟩
      rw [ihb m₂ (d + 1)]
  | proj s i sub ihe =>
    intro memo d
    rw [instantiateRevGo.eq_def, instantiateListGo.eq_def]
    by_cases hk0 : k = 0
    · simp only [if_pos hk0]
    rw [if_neg hk0, if_neg hk0]
    by_cases hcut : (Expr.proj s i sub).bvarB ≤ d
    · rw [if_pos hcut, if_pos hcut]
    rw [if_neg hcut, if_neg hcut]
    cases hmemo : memo[(Expr.proj s i sub, k, d)]? with
    | some r => rfl
    | none =>
      dsimp only
      rw [ihe memo d]

theorem instantiateRev_spec {e : ExprC} {vs : Array ExprC} {d : Nat}
    (hw : WFc e) (hvs : WFcL vs.toList) :
    WFc (instantiateRev e vs d) ∧
      eraseC (instantiateRev e vs d)
        = (eraseC e).instantiateList (vs.toList.reverse.map eraseC) d := by
  have hrevwf : WFcL vs.reverse.toList := by
    intro x hx
    exact hvs x (by simpa using hx)
  have hws : vs.reverse.toList.map eraseC = vs.toList.reverse.map eraseC := by
    simp
  rw [instantiateRev]
  split
  · rename_i h0
    have hnil : vs.toList.reverse.map eraseC = [] := by
      have he : vs.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using h0
      simp [he]
    rw [hnil]
    exact ⟨hw, (Expr.instantiateList_nil _ _).symm⟩
  · split
    · rename_i hcut
      exact ⟨hw, (Expr.instantiateList_eq_self (bvarB_le hw hcut)).symm⟩
    · rw [instantiateRevGo_eq]
      obtain ⟨h1, -, h3⟩ :=
        instantiateListGo_spec (vs := vs.reverse) hrevwf vs.size e hw (d := d)
          (by simp) MemoLInv.empty
      refine ⟨h1, ?_⟩
      rw [h3, hws]
      congr 1
      rw [show vs.size = (vs.toList.reverse.map eraseC).length from by simp,
        List.take_length]

/-! ## Abstraction

The clone's abstraction walks carry a **documented deviation** from the
arena twins: a node whose cached fvar range is at or below the
abstracted level is returned unchanged (the arena does not need the
cutoff — its rebuild re-interns to the same index).  The identity is
exactly `abstractRange_eq_self` / its `abstract1` twin below, so the
value is the same either way. -/

/-- `Expr.abstract1` at or above a term's fvar range is the identity —
the `abstract1` twin of `abstractRange_eq_self`, which `Setlec/Verify`
has only for the bulk form. -/
private theorem abstract1_eq_self : ∀ {e : Expr} {d k : Nat},
    Expr.fvarsBelow d e → e.abstract1 d k = e := by
  intro e
  induction e <;> intro d k hb <;>
    simp_all only [Expr.fvarsBelow, Expr.abstract1]
  rw [if_neg (by omega)]

/-- The `abstract1` memo invariant at the ambient level `d`. -/
def MemoAInv (d : Nat) (memo : MemoN) : Prop :=
  ∀ (e : ExprC) (k : Nat) (r : ExprC), memo[(e, k)]? = some r →
    WFc r ∧ eraseC r = (eraseC e).abstract1 d k

theorem MemoAInv.empty {d : Nat} : MemoAInv d {} := by
  intro e k r h
  simp at h

theorem MemoAInv.insert {d : Nat} {memo : MemoN} (hm : MemoAInv d memo)
    {e r : ExprC} {k : Nat} (hr : WFc r)
    (heq : eraseC r = (eraseC e).abstract1 d k) :
    MemoAInv d (memo.insert (e, k) r) := by
  intro e' k' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hkk⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hkk]
    exact ⟨hr, heq⟩
  · exact hm e' k' r' hk

/-- **The `abstract1` core commutes with erasure** (deviation cutoff
included: `fvarB_le` certifies `Expr.fvarsBelow`, whence
`abstract1_eq_self`). -/
theorem abstract1Go_spec {d : Nat} : ∀ {e : ExprC}, WFc e →
    ∀ {memo : MemoN} {k : Nat}, MemoAInv d memo →
      WFc (abstract1Go d memo e k).1 ∧
        MemoAInv d (abstract1Go d memo e k).2 ∧
        eraseC (abstract1Go d memo e k).1 = (eraseC e).abstract1 d k := by
  intro e
  induction e with
  | fvar idx n ty iht =>
    intro hw memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · dsimp only
        split
        · rename_i hidx
          refine ⟨WFc.mkBVar _, hm.insert (WFc.mkBVar _) ?_, ?_⟩ <;>
            simp [eraseC, Expr.abstract1, hidx]
        · rename_i hidx
          refine ⟨hw, hm.insert hw ?_, ?_⟩ <;>
            simp [eraseC, Expr.abstract1, hidx]
  | bvar i =>
    intro hw memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | sort u =>
    intro hw memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | const n us =>
    intro hw memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | lit l =>
    intro hw memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | app f a ihf iha =>
    intro hw memo k hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihf hf (k := k) hm
        rcases hp : abstract1Go d memo f k with ⟨f', mf⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := iha ha (k := k) h2
        rcases hq : abstract1Go d mf a k with ⟨a', ma⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkApp f' a')
            = (eraseC (.app f a)).abstract1 d k := by
          rw [eraseC_mkApp, h3, h6]; rfl
        exact ⟨WFc.mkApp h1 h4, h5.insert (WFc.mkApp h1 h4) hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro hw memo k hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (k := k) hm
        rcases hp : abstract1Go d memo ty k with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd (k := k + 1) h2
        rcases hq : abstract1Go d mt bd (k + 1) with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkLam n ty' b' m)
            = (eraseC (.lam n ty bd m)).abstract1 d k := by
          rw [eraseC_mkLam, h3, h6]; rfl
        exact ⟨WFc.mkLam n m h1 h4, h5.insert (WFc.mkLam n m h1 h4) hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro hw memo k hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (k := k) hm
        rcases hp : abstract1Go d memo ty k with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd (k := k + 1) h2
        rcases hq : abstract1Go d mt bd (k + 1) with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkForallE n ty' b' m)
            = (eraseC (.forallE n ty bd m)).abstract1 d k := by
          rw [eraseC_mkForallE, h3, h6]; rfl
        exact ⟨WFc.mkForallE n m h1 h4,
          h5.insert (WFc.mkForallE n m h1 h4) hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro hw memo k hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (k := k) hm
        rcases hp : abstract1Go d memo ty k with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihv hval (k := k) h2
        rcases hq : abstract1Go d mt val k with ⟨v', mv⟩
        rw [hq] at h4 h5 h6
        obtain ⟨h7, h8, h9⟩ := ihb hbd (k := k + 1) h5
        rcases hr : abstract1Go d mv bd (k + 1) with ⟨b', mb⟩
        rw [hr] at h7 h8 h9
        simp only [hp, hq, hr]
        have hres : eraseC (mkLetE n ty' v' b')
            = (eraseC (.letE n ty val bd)).abstract1 d k := by
          rw [eraseC_mkLetE, h3, h6, h9]; rfl
        exact ⟨WFc.mkLetE n h1 h4 h7,
          h8.insert (WFc.mkLetE n h1 h4 h7) hres, hres⟩
  | proj s i sub ihe =>
    intro hw memo k hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihe he (k := k) hm
        rcases hp : abstract1Go d memo sub k with ⟨s', ms⟩
        rw [hp] at h1 h2 h3
        simp only [hp]
        have hres : eraseC (mkProj s i s')
            = (eraseC (.proj s i sub)).abstract1 d k := by
          rw [eraseC_mkProj, h3]; rfl
        exact ⟨WFc.mkProj s i h1, h2.insert (WFc.mkProj s i h1) hres, hres⟩

theorem abstract1_spec {e : ExprC} {d k : Nat} (hw : WFc e) :
    WFc (abstract1 e d k) ∧
      eraseC (abstract1 e d k) = (eraseC e).abstract1 d k := by
  rw [abstract1]
  split
  · rename_i hcut
    exact ⟨hw, (abstract1_eq_self (fvarB_le hw hcut)).symm⟩
  · obtain ⟨h1, -, h3⟩ := abstract1Go_spec (d := d) hw (k := k) MemoAInv.empty
    exact ⟨h1, h3⟩

/-! ### Bulk abstraction -/

/-- Abstracting an empty range is the identity. -/
private theorem abstractRange_zero : ∀ (e : Expr) (d c : Nat),
    e.abstractRange d 0 c = e := by
  intro e
  induction e <;> intro d c <;> simp_all [Expr.abstractRange]

/-- The `abstractRange` memo invariant at the ambient window `d`, `k`. -/
def MemoARInv (d k : Nat) (memo : MemoN) : Prop :=
  ∀ (e : ExprC) (c : Nat) (r : ExprC), memo[(e, c)]? = some r →
    WFc r ∧ eraseC r = (eraseC e).abstractRange d k c

theorem MemoARInv.empty {d k : Nat} : MemoARInv d k {} := by
  intro e c r h
  simp at h

theorem MemoARInv.insert {d k : Nat} {memo : MemoN} (hm : MemoARInv d k memo)
    {e r : ExprC} {c : Nat} (hr : WFc r)
    (heq : eraseC r = (eraseC e).abstractRange d k c) :
    MemoARInv d k (memo.insert (e, c) r) := by
  intro e' c' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hcc⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hcc]
    exact ⟨hr, heq⟩
  · exact hm e' c' r' hk

/-- **The bulk-abstraction core commutes with erasure.** -/
theorem abstractRangeGo_spec {d k : Nat} : ∀ {e : ExprC}, WFc e →
    ∀ {memo : MemoN} {c : Nat}, MemoARInv d k memo →
      WFc (abstractRangeGo d k memo e c).1 ∧
        MemoARInv d k (abstractRangeGo d k memo e c).2 ∧
        eraseC (abstractRangeGo d k memo e c).1
          = (eraseC e).abstractRange d k c := by
  intro e
  induction e with
  | fvar idx n ty iht =>
    intro hw memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · dsimp only
        split
        · rename_i hidx
          refine ⟨WFc.mkBVar _, hm.insert (WFc.mkBVar _) ?_, ?_⟩ <;>
            simp [eraseC, Expr.abstractRange, hidx]
        · rename_i hidx
          refine ⟨hw, hm.insert hw ?_, ?_⟩ <;>
            simp [eraseC, Expr.abstractRange, hidx]
  | bvar i =>
    intro hw memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | sort u =>
    intro hw memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | const n us =>
    intro hw memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | lit l =>
    intro hw memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | app f a ihf iha =>
    intro hw memo c hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihf hf (c := c) hm
        rcases hp : abstractRangeGo d k memo f c with ⟨f', mf⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := iha ha (c := c) h2
        rcases hq : abstractRangeGo d k mf a c with ⟨a', ma⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkApp f' a')
            = (eraseC (.app f a)).abstractRange d k c := by
          rw [eraseC_mkApp, h3, h6]; rfl
        exact ⟨WFc.mkApp h1 h4, h5.insert (WFc.mkApp h1 h4) hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro hw memo c hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (c := c) hm
        rcases hp : abstractRangeGo d k memo ty c with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd (c := c + 1) h2
        rcases hq : abstractRangeGo d k mt bd (c + 1) with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkLam n ty' b' m)
            = (eraseC (.lam n ty bd m)).abstractRange d k c := by
          rw [eraseC_mkLam, h3, h6]; rfl
        exact ⟨WFc.mkLam n m h1 h4, h5.insert (WFc.mkLam n m h1 h4) hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro hw memo c hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (c := c) hm
        rcases hp : abstractRangeGo d k memo ty c with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd (c := c + 1) h2
        rcases hq : abstractRangeGo d k mt bd (c + 1) with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkForallE n ty' b' m)
            = (eraseC (.forallE n ty bd m)).abstractRange
                d k c := by
          rw [eraseC_mkForallE, h3, h6]; rfl
        exact ⟨WFc.mkForallE n m h1 h4,
          h5.insert (WFc.mkForallE n m h1 h4) hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro hw memo c hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty (c := c) hm
        rcases hp : abstractRangeGo d k memo ty c with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihv hval (c := c) h2
        rcases hq : abstractRangeGo d k mt val c with ⟨v', mv⟩
        rw [hq] at h4 h5 h6
        obtain ⟨h7, h8, h9⟩ := ihb hbd (c := c + 1) h5
        rcases hr : abstractRangeGo d k mv bd (c + 1) with ⟨b', mb⟩
        rw [hr] at h7 h8 h9
        simp only [hp, hq, hr]
        have hres : eraseC (mkLetE n ty' v' b')
            = (eraseC (.letE n ty val bd)).abstractRange
                d k c := by
          rw [eraseC_mkLetE, h3, h6, h9]; rfl
        exact ⟨WFc.mkLetE n h1 h4 h7,
          h8.insert (WFc.mkLetE n h1 h4 h7) hres, hres⟩
  | proj s i sub ihe =>
    intro hw memo c hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ _ hhit).1, hm, (hm _ _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihe he (c := c) hm
        rcases hp : abstractRangeGo d k memo sub c with ⟨s', ms⟩
        rw [hp] at h1 h2 h3
        simp only [hp]
        have hres : eraseC (mkProj s i s')
            = (eraseC (.proj s i sub)).abstractRange d k c := by
          rw [eraseC_mkProj, h3]; rfl
        exact ⟨WFc.mkProj s i h1, h2.insert (WFc.mkProj s i h1) hres, hres⟩

theorem abstractRange_spec {e : ExprC} {d k c : Nat} (hw : WFc e) :
    WFc (abstractRange e d k c) ∧
      eraseC (abstractRange e d k c) = (eraseC e).abstractRange d k c := by
  cases k with
  | zero => exact ⟨hw, (abstractRange_zero _ _ _).symm⟩
  | succ k' =>
    rw [abstractRange]
    split
    · rename_i hcut
      exact ⟨hw, (abstractRange_eq_self (fvarB_le hw hcut)).symm⟩
    · obtain ⟨h1, -, h3⟩ :=
        abstractRangeGo_spec (d := d) (k := k' + 1) hw (c := c) MemoARInv.empty
      exact ⟨h1, h3⟩

/-! ## Level instantiation -/

/-- The `instLevelParams` memo invariant (the key carries no cursor). -/
def MemoLPInv (ks : List Name) (us : List Level) (memo : Memo0) : Prop :=
  ∀ (e r : ExprC), memo[e]? = some r →
    WFc r ∧ eraseC r = (eraseC e).instantiateLevelParams ks us

theorem MemoLPInv.empty {ks : List Name} {us : List Level} :
    MemoLPInv ks us {} := by
  intro e r h
  simp at h

theorem MemoLPInv.insert {ks : List Name} {us : List Level} {memo : Memo0}
    (hm : MemoLPInv ks us memo) {e r : ExprC} (hr : WFc r)
    (heq : eraseC r = (eraseC e).instantiateLevelParams ks us) :
    MemoLPInv ks us (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← beq_sound hbeq]
    exact ⟨hr, heq⟩
  · exact hm e' r' hk

/-- **The level-instantiation core commutes with erasure** (the
`hasLP` cutoff is `hasLP_false`; the binder arms substitute the
prop-ness datum exactly as `Expr.instantiateLevelParams` does). -/
theorem instLevelParamsGo_spec {ks : List Name} {us : List Level} :
    ∀ {e : ExprC}, WFc e → ∀ {memo : Memo0}, MemoLPInv ks us memo →
      WFc (instLevelParamsGo ks us memo e).1 ∧
        MemoLPInv ks us (instLevelParamsGo ks us memo e).2 ∧
        eraseC (instLevelParamsGo ks us memo e).1
          = (eraseC e).instantiateLevelParams ks us := by
  intro e
  induction e with
  | bvar i =>
    intro hw memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | lit l =>
    intro hw memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · exact ⟨hw, hm.insert hw rfl, rfl⟩
  | sort u =>
    intro hw memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · exact ⟨WFc.mkSort _, (hm.insert (WFc.mkSort _) rfl), rfl⟩
  | const n vs =>
    intro hw memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · exact ⟨WFc.mkConst .., (hm.insert (WFc.mkConst ..) rfl), rfl⟩
  | fvar idx n ty iht =>
    intro hw memo hm
    obtain ⟨hty, -⟩ := hw.fvar_inv
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨t, mt⟩
        rw [hp] at h1 h2 h3
        simp only [hp]
        have hres : eraseC (mkFVar idx n t)
            = (eraseC (.fvar idx n ty)).instantiateLevelParams
                ks us := by
          rw [eraseC_mkFVar, h3]; rfl
        exact ⟨WFc.mkFVar idx n h1, h2.insert (WFc.mkFVar idx n h1) hres,
          hres⟩
  | app f a ihf iha =>
    intro hw memo hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihf hf hm
        rcases hp : instLevelParamsGo ks us memo f with ⟨f', mf⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := iha ha h2
        rcases hq : instLevelParamsGo ks us mf a with ⟨a', ma⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkApp f' a')
            = (eraseC (.app f a)).instantiateLevelParams
                ks us := by
          rw [eraseC_mkApp, h3, h6]; rfl
        exact ⟨WFc.mkApp h1 h4, h5.insert (WFc.mkApp h1 h4) hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd h2
        rcases hq : instLevelParamsGo ks us mt bd with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC (mkLam n ty' b' ⟨m.bi, Level.substPW ks us m.pw⟩)
            = (eraseC (.lam n ty bd m)).instantiateLevelParams
                ks us := by
          rw [eraseC_mkLam, h3, h6]; rfl
        exact ⟨WFc.mkLam n _ h1 h4, h5.insert (WFc.mkLam n _ h1 h4) hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro hw memo hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihb hbd h2
        rcases hq : instLevelParamsGo ks us mt bd with ⟨b', mb⟩
        rw [hq] at h4 h5 h6
        simp only [hp, hq]
        have hres : eraseC
              (mkForallE n ty' b' ⟨m.bi, Level.substPW ks us m.pw⟩)
            = (eraseC (.forallE n ty bd m)).instantiateLevelParams
                ks us := by
          rw [eraseC_mkForallE, h3, h6]; rfl
        exact ⟨WFc.mkForallE n _ h1 h4,
          h5.insert (WFc.mkForallE n _ h1 h4) hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro hw memo hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := iht hty hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨ty', mt⟩
        rw [hp] at h1 h2 h3
        obtain ⟨h4, h5, h6⟩ := ihv hval h2
        rcases hq : instLevelParamsGo ks us mt val with ⟨v', mv⟩
        rw [hq] at h4 h5 h6
        obtain ⟨h7, h8, h9⟩ := ihb hbd h5
        rcases hr : instLevelParamsGo ks us mv bd with ⟨b', mb⟩
        rw [hr] at h7 h8 h9
        simp only [hp, hq, hr]
        have hres : eraseC (mkLetE n ty' v' b')
            = (eraseC (.letE n ty val bd)).instantiateLevelParams
                ks us := by
          rw [eraseC_mkLetE, h3, h6, h9]; rfl
        exact ⟨WFc.mkLetE n h1 h4 h7,
          h8.insert (WFc.mkLetE n h1 h4 h7) hres, hres⟩
  | proj s i sub ihe =>
    intro hw memo hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hw, hm, (hasLP_false hw (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨(hm _ _ hhit).1, hm, (hm _ _ hhit).2⟩
      · obtain ⟨h1, h2, h3⟩ := ihe he hm
        rcases hp : instLevelParamsGo ks us memo sub with ⟨s', ms⟩
        rw [hp] at h1 h2 h3
        simp only [hp]
        have hres : eraseC (mkProj s i s')
            = (eraseC (.proj s i sub)).instantiateLevelParams
                ks us := by
          rw [eraseC_mkProj, h3]; rfl
        exact ⟨WFc.mkProj s i h1, h2.insert (WFc.mkProj s i h1) hres, hres⟩

theorem instLevelParams_spec {ks : List Name} {us : List Level} {e : ExprC}
    (hw : WFc e) :
    WFc (instLevelParams ks us e) ∧
      eraseC (instLevelParams ks us e)
        = (eraseC e).instantiateLevelParams ks us := by
  rw [instLevelParams]
  split
  · rename_i hcut
    exact ⟨hw, (hasLP_false hw (by simpa using hcut)).symm⟩
  · obtain ⟨h1, -, h3⟩ := instLevelParamsGo_spec (ks := ks) (us := us) hw
      MemoLPInv.empty
    exact ⟨h1, h3⟩

/-! ## The scope walk

`Expr.wscopedB` is well founded (on `sizeF`, since it descends into
`fvar` annotations), so its per-constructor equations are named here
too. -/

private theorem wscopedB_bvar (i d : Nat) :
    (Expr.bvar i).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_sort (u : Level) (d : Nat) :
    (Expr.sort u).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_const (n : Name) (us : List Level) (d : Nat) :
    (Expr.const n us).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_lit (l : Literal) (d : Nat) :
    (Expr.lit l).wscopedB d = true := by rw [Expr.wscopedB]

private theorem wscopedB_fvar (idx : Nat) (n : Name) (ty : Expr) (d : Nat) :
    (Expr.fvar idx n ty).wscopedB d
      = (decide (idx < d) && ty.wscopedB idx) := by rw [Expr.wscopedB]

private theorem wscopedB_app (f a : Expr) (d : Nat) :
    (Expr.app f a).wscopedB d = (f.wscopedB d && a.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_lam (n : Name) (ty b : Expr) (m : BinderMeta)
    (d : Nat) :
    (Expr.lam n ty b m).wscopedB d = (ty.wscopedB d && b.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_forallE (n : Name) (ty b : Expr) (m : BinderMeta)
    (d : Nat) :
    (Expr.forallE n ty b m).wscopedB d = (ty.wscopedB d && b.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_letE (n : Name) (ty v b : Expr) (d : Nat) :
    (Expr.letE n ty v b).wscopedB d
      = (ty.wscopedB d && v.wscopedB d && b.wscopedB d) := by
  rw [Expr.wscopedB]

private theorem wscopedB_proj (s : Name) (i : Nat) (e : Expr) (d : Nat) :
    (Expr.proj s i e).wscopedB d = e.wscopedB d := by rw [Expr.wscopedB]

/-- The clone's `fvarB == 0` shortcut: a node whose cached fvar range is
zero has no `fvar` leaf at all (annotations only exist under `fvar`
nodes), so it is well scoped at every cursor.  The arena twin has no
such cutoff. -/
private theorem wscopedB_of_fvarsBelow_zero : ∀ (e : Expr),
    Expr.fvarsBelow 0 e → ∀ d, e.wscopedB d = true := by
  intro e
  induction e <;> intro hb d <;> simp_all [Expr.fvarsBelow, Expr.wscopedB]

/-- The scope walk's memo invariant. -/
def MemoWInv (memo : Std.HashMap (ExprC × Nat) Bool) : Prop :=
  ∀ (e : ExprC) (d : Nat) (r : Bool), memo[(e, d)]? = some r →
    r = (eraseC e).wscopedB d

theorem MemoWInv.empty : MemoWInv {} := by
  intro e d r h
  simp at h

theorem MemoWInv.insert {memo : Std.HashMap (ExprC × Nat) Bool}
    (hm : MemoWInv memo) {e : ExprC} {d : Nat} {r : Bool}
    (heq : r = (eraseC e).wscopedB d) : MemoWInv (memo.insert (e, d) r) := by
  intro e' d' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hd⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hd]
    exact heq
  · exact hm e' d' r' hk

/-- **The scope walk agrees with `Expr.wscopedB` on the erasure.** -/
theorem wscopedBGo_spec : ∀ {e : ExprC}, WFc e →
    ∀ {memo : Std.HashMap (ExprC × Nat) Bool} {d : Nat}, MemoWInv memo →
      (wscopedBGo memo d e).1 = (eraseC e).wscopedB d ∧
        MemoWInv (wscopedBGo memo d e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro hw memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_bvar i d).symm,
          hm.insert (wscopedB_bvar i d).symm⟩
  | sort u =>
    intro hw memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_sort u d).symm,
          hm.insert (wscopedB_sort u d).symm⟩
  | const n us =>
    intro hw memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_const n us d).symm,
          hm.insert (wscopedB_const n us d).symm⟩
  | lit l =>
    intro hw memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_lit l d).symm, hm.insert (wscopedB_lit l d).symm⟩
  | fvar idx n ty iht =>
    intro hw memo d hm
    obtain ⟨hty, -⟩ := hw.fvar_inv
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · dsimp only
        split
        · rename_i hidx
          obtain ⟨h1, h2⟩ := iht hty (d := idx) hm
          rcases hp : wscopedBGo memo idx ty with ⟨rt, mt⟩
          rw [hp] at h1 h2
          have hres : rt = (eraseC (.fvar idx n ty)).wscopedB d := by
            rw [show eraseC (Expr.fvar idx n ty)
                = Expr.fvar idx n (eraseC ty) from rfl, wscopedB_fvar,
              ← h1, decide_eq_true hidx, Bool.true_and]
          exact ⟨hres, h2.insert hres⟩
        · rename_i hidx
          have hres : false
              = (eraseC (.fvar idx n ty)).wscopedB d := by
            rw [show eraseC (Expr.fvar idx n ty)
                = Expr.fvar idx n (eraseC ty) from rfl, wscopedB_fvar,
              decide_eq_false hidx, Bool.false_and]
          exact ⟨hres, hm.insert hres⟩
  | app f a ihf iha =>
    intro hw memo d hm
    obtain ⟨hf, ha, -⟩ := hw.app_inv
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihf hf (d := d) hm
        rcases hp : wscopedBGo memo d f with ⟨rf, mf⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rf with
        | true =>
          obtain ⟨h3, h4⟩ := iha ha (d := d) h2
          rcases hq : wscopedBGo mf d a with ⟨ra, ma⟩
          rw [hq] at h3 h4
          have hres : ra = (eraseC (.app f a)).wscopedB d := by
            rw [show eraseC (Expr.app f a)
                = Expr.app (eraseC f) (eraseC a) from rfl, wscopedB_app,
              ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false = (eraseC (.app f a)).wscopedB d := by
            rw [show eraseC (Expr.app f a)
                = Expr.app (eraseC f) (eraseC a) from rfl, wscopedB_app,
              ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m iht ihb =>
    intro hw memo d hm
    obtain ⟨hty, hbd, -⟩ := hw.lam_inv
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty (d := d) hm
        rcases hp : wscopedBGo memo d ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb hbd (d := d) h2
          rcases hq : wscopedBGo mt d bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : rb
              = (eraseC (.lam n ty bd m)).wscopedB d := by
            rw [show eraseC (Expr.lam n ty bd m)
                = Expr.lam n (eraseC ty) (eraseC bd) m from rfl,
              wscopedB_lam, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (eraseC (.lam n ty bd m)).wscopedB d := by
            rw [show eraseC (Expr.lam n ty bd m)
                = Expr.lam n (eraseC ty) (eraseC bd) m from rfl,
              wscopedB_lam, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m iht ihb =>
    intro hw memo d hm
    obtain ⟨hty, hbd, -⟩ := hw.forallE_inv
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht hty (d := d) hm
        rcases hp : wscopedBGo memo d ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb hbd (d := d) h2
          rcases hq : wscopedBGo mt d bd with ⟨rb, mb⟩
          rw [hq] at h3 h4
          have hres : rb
              = (eraseC (.forallE n ty bd m)).wscopedB d := by
            rw [show eraseC (Expr.forallE n ty bd m)
                = Expr.forallE n (eraseC ty) (eraseC bd) m from rfl,
              wscopedB_forallE, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (eraseC (.forallE n ty bd m)).wscopedB d := by
            rw [show eraseC (Expr.forallE n ty bd m)
                = Expr.forallE n (eraseC ty) (eraseC bd) m from rfl,
              wscopedB_forallE, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro hw memo d hm
    obtain ⟨hty, hval, hbd, -⟩ := hw.letE_inv
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · have herase : eraseC (Expr.letE n ty val bd)
            = Expr.letE n (eraseC ty) (eraseC val) (eraseC bd) := rfl
        obtain ⟨h1, h2⟩ := iht hty (d := d) hm
        rcases hp : wscopedBGo memo d ty with ⟨rt, mt⟩
        rw [hp] at h1 h2
        simp only [hp]
        cases rt with
        | false =>
          have hres : false
              = (eraseC (.letE n ty val bd)).wscopedB d := by
            rw [herase, wscopedB_letE, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
        | true =>
          obtain ⟨h3, h4⟩ := ihv hval (d := d) h2
          rcases hq : wscopedBGo mt d val with ⟨rv, mv⟩
          rw [hq] at h3 h4
          cases rv with
          | false =>
            have hres : false
                = (eraseC (.letE n ty val bd)).wscopedB d := by
              rw [herase, wscopedB_letE, ← h1, ← h3]
              simp
            exact ⟨hres, h4.insert hres⟩
          | true =>
            obtain ⟨h5, h6⟩ := ihb hbd (d := d) h4
            rcases hr : wscopedBGo mv d bd with ⟨rb, mb⟩
            rw [hr] at h5 h6
            have hres : rb
                = (eraseC (.letE n ty val bd)).wscopedB d := by
              rw [herase, wscopedB_letE, ← h1, ← h3, ← h5]
              simp
            exact ⟨hres, h6.insert hres⟩
  | proj s i sub ihe =>
    intro hw memo d hm
    obtain ⟨he, -⟩ := hw.proj_inv
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le hw (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihe he (d := d) hm
        rcases hp : wscopedBGo memo d sub with ⟨rs, ms⟩
        rw [hp] at h1 h2
        simp only [hp]
        have hres : rs
            = (eraseC (.proj s i sub)).wscopedB d := by
          rw [show eraseC (Expr.proj s i sub)
              = Expr.proj s i (eraseC sub) from rfl, wscopedB_proj, ← h1]
        exact ⟨hres, h2.insert hres⟩

theorem wscopedB_spec {d : Nat} {e : ExprC} (hw : WFc e) :
    wscopedB d e = (eraseC e).wscopedB d :=
  (wscopedBGo_spec hw (d := d) MemoWInv.empty).1

/-! ## The `∀`-telescope residual

`piResidualAcc` follows the arena twin's accumulator discipline: the
`forallE` arm consumes an argument into the accumulator, the `bvar` arm
flushes a nonempty accumulator by one bulk instantiation and re-enters.
The induction is the function's own measure `(as.length, acc.length)`. -/

theorem piResidualAcc_spec :
    ∀ (as acc : List ExprC) (e : ExprC), WFc e → WFcL acc → WFcL as →
      OptEr (piResidualAcc acc e as)
        (_root_.Setlec.piResidual
          ((eraseC e).instantiateList (acc.map eraseC)) (as.map eraseC))
  | [], acc, e, he, hacc, _ => by
    rw [piResidualAcc.eq_def]
    obtain ⟨h1, h2⟩ := instantiateList_spec (d := 0) he hacc
    exact ⟨h1, h2⟩
  | a :: as, acc, e, he, hacc, has => by
    cases e with
    | forallE n ty b m =>
      obtain ⟨-, hb, -⟩ := he.forallE_inv
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [show eraseC (Expr.forallE n ty b m)
          = Expr.forallE n (eraseC ty) (eraseC b) m from rfl,
        instList_forallE, List.map_cons,
        show _root_.Setlec.piResidual
            (Expr.forallE n ((eraseC ty).instantiateList (acc.map eraseC) 0)
              ((eraseC b).instantiateList (acc.map eraseC) 1) m)
            (eraseC a :: as.map eraseC)
          = _root_.Setlec.piResidual
              (((eraseC b).instantiateList (acc.map eraseC) 1).instantiate1
                (eraseC a)) (as.map eraseC) from rfl,
        ← Expr.instantiateList_cons]
      exact piResidualAcc_spec as (a :: acc) b hb (WFcL.cons has.head hacc)
        has.tail
    | bvar i =>
      rw [piResidualAcc.eq_def]
      dsimp only
      cases acc with
      | nil =>
        rw [List.map_nil, Expr.instantiateList_nil]
        exact trivial
      | cons a' acc' =>
        obtain ⟨h1, h2⟩ :=
          instantiateList_spec (e := Expr.bvar i)
            (vs := a' :: acc') (d := 0) he hacc
        have hrec := piResidualAcc_spec (a :: as) []
          (instantiateList (Expr.bvar i) (a' :: acc') 0) h1
          WFcL.nil has
        rw [List.map_nil, Expr.instantiateList_nil, h2] at hrec
        exact hrec
    | fvar idx n ty =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.fvar idx n ty)
        (ws := acc.map eraseC) (d := 0) rfl]
      exact trivial
    | sort u =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.sort u)
        (ws := acc.map eraseC) (d := 0) rfl]
      exact trivial
    | const n us =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.const n us)
        (ws := acc.map eraseC) (d := 0) rfl]
      exact trivial
    | lit l =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.lit l)
        (ws := acc.map eraseC) (d := 0) rfl]
      exact trivial
    | app f a' =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [show eraseC (Expr.app f a')
          = Expr.app (eraseC f) (eraseC a') from rfl, instList_app]
      exact trivial
    | lam n ty b m =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [show eraseC (Expr.lam n ty b m)
          = Expr.lam n (eraseC ty) (eraseC b) m from rfl, instList_lam]
      exact trivial
    | letE n ty v b =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [show eraseC (Expr.letE n ty v b)
          = Expr.letE n (eraseC ty) (eraseC v) (eraseC b) from rfl,
        instList_letE]
      exact trivial
    | proj s i sub =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [show eraseC (Expr.proj s i sub)
          = Expr.proj s i (eraseC sub) from rfl, instList_proj]
      exact trivial
termination_by as acc => (as.length, acc.length)
decreasing_by
  · apply Prod.Lex.right' <;> simp_all
  · apply Prod.Lex.left; simp

theorem piResidual_spec {e : ExprC} {args : List ExprC} (hw : WFc e)
    (hargs : WFcL args) :
    OptEr (piResidual e args)
      (_root_.Setlec.piResidual (eraseC e) (args.map eraseC)) := by
  have h := piResidualAcc_spec args [] e hw WFcL.nil hargs
  rw [List.map_nil, Expr.instantiateList_nil] at h
  exact h

end ExprC

end Setlec.Cached
