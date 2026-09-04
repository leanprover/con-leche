import Setlec.Cached.ExprOpsC
import Setlec.Verify.Cached.Erase
import Setlec.Verify.Subst
import Setlec.Verify.InstList
import Setlec.Verify.AbstractRange

/-!
# The cached representation's syntactic operations are the pure ones

Task #163, batch 3; rewritten at #172 B3a/B3b.  Every operation of
`Setlec/Cached/ExprOpsC.lean` — memoized, `Std.HashMap`-backed — is
proved **equal to its `Setlec.Expr` counterpart**.  These are the
transpositions of the arena twins' `*I_spec` theorems in
`Setlec/Verify/IExprOps.lean`: same case structure, no store, no
`Ext`, no `TWF`.

Two conjuncts each of these statements used to carry are gone: the
erasure (B3a — one type, so the equation is between the cached and the
pure function at the *same* argument) and the field invariant `WFc` of
the result (B3b — the fields are the compiler's, so there is nothing
for an operation to preserve).  What is left is the memo invariant,
which is real: a clause says every stored value is the pure function at
its key, and insert-preservation goes through
`Std.HashMap.getElem?_insert` plus `beq_sound` on the colliding key —
a memo hit's key is only `BEq`-equal to the query.
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
    a = c ∧ (b == d) = true := by
  simp only [BEq.beq, Bool.and_eq_true] at h
  exact ⟨beq_sound h.1, h.2⟩

end PairKey

/-! ## Optional results

The arena's `OptDen` (an optional index relates to an optional
expression) transposes to this. -/

/-- An optional cached result agrees with the optional `Expr`-side
result.  (Before task #172 B3b this also carried the field invariant
of the value; the invariant is the compiler's now.) -/
def OptEr : Option ExprC → Option Expr → Prop
  | none, none => True
  | some e, some x => e = x
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

/-- Reading a node one level down is the pure view. -/
theorem view_spec (e : ExprC) : (view e) = (Expr.view e) := by
  cases e <;> rfl

/-- Building a node from a one-level view is the pure builder — the
transposition of the arena's `intern_spec`. -/
theorem ofView_spec (v : ExprView ExprC) : (ofView v) = ofViewE v := by
  cases v <;> rfl

/-! ## Spines -/

theorem getAppFn_spec : ∀ e : ExprC, (getAppFn e) = (Expr.getAppFn e) := by
  intro e
  induction e with
  | app f a ihf iha => exact ihf
  | _ => rfl

theorem getAppArgsAcc_spec : ∀ (e : ExprC) (acc : List ExprC),
    (getAppArgsAcc e acc) = (Expr.getAppArgs e) ++ acc := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro acc
    rw [show getAppArgsAcc (.app f a) acc
        = getAppArgsAcc f (a :: acc) from rfl, ihf,
      show ((.app f a : Expr)).getAppArgs
        = (Expr.getAppArgs f) ++ [a] from rfl,
      List.append_assoc]
    rfl
  | _ => intro acc; rfl

theorem getAppArgs_spec (e : ExprC) :
    (getAppArgs e) = (Expr.getAppArgs e) := by
  simpa [getAppArgs] using getAppArgsAcc_spec e []

theorem mkAppN_spec : ∀ (args : List ExprC) (f : ExprC),
    (mkAppN f args) = Expr.mkAppN f args
  | [], _ => rfl
  | a :: as, f => by
    have := mkAppN_spec as (mkApp f a)
    rw [show mkAppN f (a :: as) = mkAppN (mkApp f a) as from rfl, this]
    rfl

/-! ## Telescope queries -/

theorem stripPisBody_spec : ∀ (k : Nat) (e : ExprC),
    OptEr (stripPisBody k e) (((Expr.stripPis k e)).map (·.2)) := by
  intro k
  induction k with
  | zero => intro e; exact rfl
  | succ k ih =>
    intro e
    cases e with
    | forallE n ty b m =>
      have := ih b
      rw [show stripPisBody (k + 1) (.forallE n ty b m)
          = stripPisBody k b from rfl]
      rw [show ((Expr.stripPis (k + 1) (.forallE n ty b m))).map
            (·.2)
          = ((Expr.stripPis k b)).map (·.2) by
        cases hs : (Expr.stripPis k b) <;>
          simp [Expr.stripPis, hs]]
      exact this
    | _ => exact trivial

theorem pisToLams_spec : ∀ (k : Nat) (e body : ExprC),
    OptEr (pisToLams k e body)
      (Expr.pisToLams k e body) := by
  intro k
  induction k with
  | zero => intro e body; exact rfl
  | succ k ih =>
    intro e body
    cases e with
    | forallE n ty rest mb =>
      have hrec := ih rest body
      rw [show pisToLams (k + 1) (.forallE n ty rest mb) body
          = (match pisToLams k rest body with
             | some b => some (mkLam n ty b ⟨mb.bi, .never⟩)
             | none => none) from rfl]
      rw [show Expr.pisToLams (k + 1)
            ((.forallE n ty rest mb)) body
          = (Expr.pisToLams k rest body).map
              (fun bx => .lam n ty bx ⟨mb.bi, .never⟩) from rfl]
      cases hgo : pisToLams k rest body with
      | none =>
        rw [hgo] at hrec
        cases hox : Expr.pisToLams k rest body with
        | none => exact trivial
        | some bx => rw [hox] at hrec; exact absurd hrec not_false
      | some bc =>
        rw [hgo] at hrec
        cases hox : Expr.pisToLams k rest body with
        | none => rw [hox] at hrec; exact absurd hrec not_false
        | some bx =>
          rw [hox] at hrec
          show mkLam n ty bc ⟨mb.bi, .never⟩ = _
          rw [mkLam_eq, (hrec : bc = bx)]
    | _ => exact trivial

/-! ## Scope queries -/

theorem looseBVarsBounded_spec {k : Nat} (e : ExprC) :
    looseBVarsBounded k e = (Expr.looseBVarsBounded k e) := by
  rw [show looseBVarsBounded k e = decide (e.bvarB ≤ k) from rfl,
    bvarB_eq e]
  cases hb : (Expr.looseBVarsBounded k e) with
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
    r = (Expr.instantiate1 k v c)

theorem Memo1Inv.empty {v : ExprC} : Memo1Inv v {} := by
  intro k c r h
  simp at h

theorem Memo1Inv.insert {v : ExprC} {memo : MemoN} (hm : Memo1Inv v memo)
    {e r : ExprC} {d : Nat}
    (heq : r = (Expr.instantiate1 e v d)) :
    Memo1Inv v (memo.insert (e, d) r) := by
  intro k c r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hd⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hd]
    exact heq

  · exact hm k c r' hk

/-- **The `instantiate1` core commutes with erasure.**  The
transposition of `instantiate1I_spec`: the walk's `bvarB` cutoff is the
`Expr` side's `instantiate1_eq_self`, and every rebuilt node's erasure
is the corresponding `Expr` constructor. -/
theorem instantiate1Go_spec {v : ExprC} : ∀ {e : ExprC},
    ∀ {memo : MemoN} {d : Nat}, Memo1Inv v memo →
        Memo1Inv v (instantiate1Go v memo e d).2 ∧
        (instantiate1Go v memo e d).1
          = (Expr.instantiate1 e v d) := by
  intro e
  induction e with
  | bvar i =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · dsimp only
        split
        · rename_i hid
          refine ⟨hm.insert ?_, ?_⟩ <;>
            simp [hid]
        · split
          · rename_i hid hid'
            refine ⟨hm.insert ?_, ?_⟩ <;>
              simp [hid, hid']
          · rename_i hid hid'
            refine ⟨hm.insert ?_, ?_⟩ <;>
              simp [hid, hid']
  | fvar idx n ty iht =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | sort u =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | const n us =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | lit l =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | app f a ihf iha =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨hf2, hf3⟩ := ihf (d := d) hm
        rcases hpf : instantiate1Go v memo f d with ⟨f', mf⟩
        simp only [hpf] at hf2 hf3
        obtain ⟨ha2, ha3⟩ := iha (d := d) hf2
        rcases hpa : instantiate1Go v mf a d with ⟨a', ma⟩
        simp only [hpa] at ha2 ha3
        simp only [hpf, hpa]
        have hres : (mkApp f' a')
            = (Expr.instantiate1 (.app f a) v d) := by
          rw [mkApp_eq, hf3, ha3]; rfl
        exact ⟨ha2.insert hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (d := d) hm
        rcases hp : instantiate1Go v memo ty d with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb (d := d + 1) h2
        rcases hq : instantiate1Go v mt bd (d + 1) with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkLam n ty' b' m)
            = (Expr.instantiate1 (.lam n ty bd m)
                v d) := by
          rw [mkLam_eq, h3, h6]; rfl
        exact ⟨h5.insert hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (d := d) hm
        rcases hp : instantiate1Go v memo ty d with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb (d := d + 1) h2
        rcases hq : instantiate1Go v mt bd (d + 1) with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkForallE n ty' b' m)
            = (Expr.instantiate1 (.forallE n ty bd m)
                v d) := by
          rw [mkForallE_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (d := d) hm
        rcases hp : instantiate1Go v memo ty d with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihv (d := d) h2
        rcases hq : instantiate1Go v mt val d with ⟨v', mv⟩
        simp only [hq] at h5 h6
        obtain ⟨h8, h9⟩ := ihb (d := d + 1) h5
        rcases hr : instantiate1Go v mv bd (d + 1) with ⟨b', mb⟩
        simp only [hr] at h8 h9
        simp only [hp, hq, hr]
        have hres : (mkLetE n ty' v' b')
            = (Expr.instantiate1 (.letE n ty val bd)
                v d) := by
          rw [mkLetE_eq, h3, h6, h9]; rfl
        exact ⟨h8.insert hres, hres⟩
  | proj s i sub ihe =>
    intro memo d hm
    rw [instantiate1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (Expr.instantiate1_eq_self (bvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihe (d := d) hm
        rcases hp : instantiate1Go v memo sub d with ⟨s', ms⟩
        simp only [hp] at h2 h3
        simp only [hp]
        have hres : (mkProj s i s')
            = (Expr.instantiate1 (.proj s i sub)
                v d) := by
          rw [mkProj_eq, h3]; rfl
        exact ⟨h2.insert hres, hres⟩

theorem instantiate1_spec {e v : ExprC} {d : Nat} :
      (instantiate1 e v d) = (Expr.instantiate1 e v d) := by
  rw [instantiate1]
  split
  · rename_i hcut
    exact (Expr.instantiate1_eq_self (bvarB_le hcut)).symm
  · exact (instantiate1Go_spec (v := v) (d := d) Memo1Inv.empty).2

/-! ## Bulk instantiation -/

/-- The bulk-instantiation memo invariant: every stored value is well
formed and erases to the substitution of the *live prefix* named by the
key at the key's own erasure. -/
def MemoLInv (ws : List Expr) (memo : MemoNL) : Prop :=
  ∀ (e : ExprC) (k c : Nat) (r : ExprC), memo[(e, k, c)]? = some r →
    r = (Expr.instantiateList e (ws.take k) c)

theorem MemoLInv.empty {ws : List Expr} : MemoLInv ws {} := by
  intro e k c r h
  simp at h

theorem MemoLInv.insert {ws : List Expr} {memo : MemoNL}
    (hm : MemoLInv ws memo) {e r : ExprC} {k c : Nat}
    (heq : r = (Expr.instantiateList e (ws.take k) c)) :
    MemoLInv ws (memo.insert (e, k, c) r) := by
  intro e' k' c' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hkc⟩ := pairKey_inv hbeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (eq_of_beq hkc)
    rw [← he]
    exact heq
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
    (h : (Expr.looseBVarsBounded d e) = true) :
    e = (Expr.instantiateList e ws d) :=
  (Expr.instantiateList_eq_self h).symm

/-- **The bulk-instantiation core commutes with erasure.**  The
transposition of `instantiateListIGo_spec`: the induction is the
function's own — strong on the live prefix `k` (the `bvar` arm re-enters
at the replacement with a shorter prefix), structural on the node
inside it. -/
theorem instantiateListGo_spec {vs : Array ExprC} :
    ∀ (k : Nat) (e : ExprC), ∀ {memo : MemoNL} {d : Nat},
      k ≤ vs.size → MemoLInv (vs.toList) memo →
        MemoLInv (vs.toList) (instantiateListGo vs memo e k d).2 ∧
        (instantiateListGo vs memo e k d).1
          = (Expr.instantiateList e
              ((vs.toList).take k) d) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro e
  induction e with
  | bvar i =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · rename_i hk0 hcut _
          have hlen : ((vs.toList).take k).length = k := by
            simp; omega
          dsimp only
          split
          · rename_i hid
            have hres : (Expr.bvar i)
                = (Expr.instantiateList (Expr.bvar i)
                    ((vs.toList).take k) d) := by
              simp [Expr.instantiateList, hid]
            exact ⟨hm.insert hres, hres⟩
          · rename_i hid
            split
            · rename_i hidk
              split
              · rename_i hidv
                obtain ⟨h2, h3⟩ :=
                  ihk (i - d) hidk vs[i - d] (d := d)
                    (Nat.le_of_lt hidv) hm
                rcases hp : instantiateListGo vs memo vs[i - d] (i - d) d
                  with ⟨r₁, m₁⟩
                simp only [hp] at h2 h3
                have hget : ((vs.toList).take k)[i - d]'(by
                    rw [hlen]; exact hidk) = vs[i - d] := by
                  rw [List.getElem_take]
                  simp
                have htk : ((vs.toList).take k).take (i - d)
                    = (vs.toList).take (i - d) := by
                  rw [List.take_take]
                  congr 1
                  omega
                have hres : r₁
                    = (Expr.instantiateList (Expr.bvar i)
                        ((vs.toList).take k) d) := by
                  rw [h3, Expr.instantiateList,
                    if_neg hid, dif_pos (by rw [hlen]; exact hidk), hget,
                    htk]
                exact ⟨h2.insert hres, hres⟩
              · rename_i hidv
                exact absurd (by omega : i - d < vs.size) hidv
            · rename_i hidk
              have hres : (mkBVar (i - k))
                  = (Expr.instantiateList (Expr.bvar i)
                      ((vs.toList).take k) d) := by
                rw [mkBVar_eq, Expr.instantiateList,
                  if_neg hid, dif_neg (by rw [hlen]; exact hidk), hlen]
              exact ⟨hm.insert hres, hres⟩
  | fvar idx n ty iht =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · exact ⟨hm.insert (instList_leaf rfl), instList_leaf rfl⟩
  | sort u =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · exact ⟨hm.insert (instList_leaf rfl), instList_leaf rfl⟩
  | const n us =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · exact ⟨hm.insert (instList_leaf rfl), instList_leaf rfl⟩
  | lit l =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · exact ⟨hm.insert (instList_leaf rfl), instList_leaf rfl⟩
  | app f a ihf iha =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · obtain ⟨h2, h3⟩ := ihf (d := d) hk hm
          rcases hp : instantiateListGo vs memo f k d with ⟨f', mf⟩
          simp only [hp] at h2 h3
          obtain ⟨h5, h6⟩ := iha (d := d) hk h2
          rcases hq : instantiateListGo vs mf a k d with ⟨a', ma⟩
          simp only [hq] at h5 h6
          simp only [hp, hq]
          have hres : (mkApp f' a')
              = (Expr.instantiateList (.app f a)
                  ((vs.toList).take k) d) := by
            rw [instList_app, mkApp_eq, h3, h6]
          exact ⟨h5.insert hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · obtain ⟨h2, h3⟩ := iht (d := d) hk hm
          rcases hp : instantiateListGo vs memo ty k d with ⟨ty', mt⟩
          simp only [hp] at h2 h3
          obtain ⟨h5, h6⟩ := ihb (d := d + 1) hk h2
          rcases hq : instantiateListGo vs mt bd k (d + 1) with ⟨b', mb⟩
          simp only [hq] at h5 h6
          simp only [hp, hq]
          have hres : (mkLam n ty' b' m)
              = (Expr.instantiateList (.lam n ty bd m)
                  ((vs.toList).take k) d) := by
            rw [instList_lam, mkLam_eq, h3, h6]
          exact ⟨h5.insert hres,
            hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · obtain ⟨h2, h3⟩ := iht (d := d) hk hm
          rcases hp : instantiateListGo vs memo ty k d with ⟨ty', mt⟩
          simp only [hp] at h2 h3
          obtain ⟨h5, h6⟩ := ihb (d := d + 1) hk h2
          rcases hq : instantiateListGo vs mt bd k (d + 1) with ⟨b', mb⟩
          simp only [hq] at h5 h6
          simp only [hp, hq]
          have hres : (mkForallE n ty' b' m)
              = (Expr.instantiateList (.forallE n ty bd m)
                  ((vs.toList).take k) d) := by
            rw [instList_forallE, mkForallE_eq, h3, h6]
          exact ⟨h5.insert hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · obtain ⟨h2, h3⟩ := iht (d := d) hk hm
          rcases hp : instantiateListGo vs memo ty k d with ⟨ty', mt⟩
          simp only [hp] at h2 h3
          obtain ⟨h5, h6⟩ := ihv (d := d) hk h2
          rcases hq : instantiateListGo vs mt val k d with ⟨v', mv⟩
          simp only [hq] at h5 h6
          obtain ⟨h8, h9⟩ := ihb (d := d + 1) hk h5
          rcases hr : instantiateListGo vs mv bd k (d + 1) with ⟨b', mb⟩
          simp only [hr] at h8 h9
          simp only [hp, hq, hr]
          have hres : (mkLetE n ty' v' b')
              = (Expr.instantiateList (.letE n ty val bd)
                  ((vs.toList).take k) d) := by
            rw [instList_letE, mkLetE_eq, h3, h6, h9]
          exact ⟨h8.insert hres, hres⟩
  | proj s i sub ihe =>
    intro memo d hk hm
    rw [instantiateListGo.eq_def]
    split
    · rename_i hk0
      subst hk0
      exact ⟨hm, by simp [Expr.instantiateList_nil]⟩
    · split
      · rename_i hcut
        exact ⟨hm,
          (Expr.instantiateList_eq_self (bvarB_le hcut)).symm⟩
      · split
        · rename_i r hhit
          exact ⟨hm, (hm _ _ _ _ hhit)⟩
        · obtain ⟨h2, h3⟩ := ihe (d := d) hk hm
          rcases hp : instantiateListGo vs memo sub k d with ⟨s', ms⟩
          simp only [hp] at h2 h3
          simp only [hp]
          have hres : (mkProj s i s')
              = (Expr.instantiateList (.proj s i sub)
                  ((vs.toList).take k) d) := by
            rw [instList_proj, mkProj_eq, h3]
          exact ⟨h2.insert hres, hres⟩

theorem instantiateList_spec {e : ExprC} {vs : List ExprC} {d : Nat} :
    (instantiateList e vs d)
      = (Expr.instantiateList e vs d) := by
  cases vs with
  | nil => rw [instantiateList]; simp [Expr.instantiateList_nil]
  | cons v vs' =>
    have harr : (v :: vs').toArray.toList = v :: vs' := rfl
    obtain ⟨-, h3⟩ :=
      instantiateListGo_spec (vs := (v :: vs').toArray)
        (v :: vs').toArray.size e (d := d)
        (Nat.le_refl _) MemoLInv.empty
    rw [instantiateList]
    rw [h3, harr]
    congr 1
    rw [show (v :: vs').toArray.size = ((v :: vs')).length from
        by simp, List.take_length]

/-! ## Telescope-context spine instantiation -/

theorem instSpineChain_spec : ∀ (args : List ExprC) (t : Nat) (e : ExprC),
    (instSpineChain args t e) = Expr.instSpine args t e
  | [], _, _ => rfl
  | a :: as, t, e => by
    have h2 := instantiate1_spec (e := e) (v := a) (d := t)
    have h4 := instSpineChain_spec as (t - 1) (instantiate1 e a t)
    rw [show instSpineChain (a :: as) t e
        = instSpineChain as (t - 1) (instantiate1 e a t) from rfl, h4, h2]
    rfl

theorem instSpine_spec {args : List ExprC} {t : Nat} {e : ExprC} :
    (instSpine args t e) = Expr.instSpine args t e := by
  rw [instSpine]
  split
  · rename_i hlen
    have hxlen : args.length = t + 1 := by simpa using hlen
    have h2 := instantiateList_spec (e := e) (vs := args.reverse) (d := 0)
    rw [h2, Expr.instSpine_eq_instantiateList _ t _ hxlen]
  · exact instSpineChain_spec args t e

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
    :
      (instantiateRev e vs d)
        = (Expr.instantiateList e (vs.toList.reverse) d) := by
  have hws : vs.reverse.toList = vs.toList.reverse := by
    simp
  rw [instantiateRev]
  split
  · rename_i h0
    have hnil : vs.toList.reverse = [] := by
      have he : vs.toList = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using h0
      simp [he]
    rw [hnil]
    exact (Expr.instantiateList_nil _ _).symm
  · split
    · rename_i hcut
      exact (Expr.instantiateList_eq_self (bvarB_le hcut)).symm
    · rw [instantiateRevGo_eq]
      obtain ⟨-, h3⟩ :=
        instantiateListGo_spec (vs := vs.reverse) vs.size e (d := d)
          (by simp) MemoLInv.empty
      rw [h3, hws]
      congr 1
      rw [show vs.size = (vs.toList.reverse).length from by simp,
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
    r = (Expr.abstract1 e d k)

theorem MemoAInv.empty {d : Nat} : MemoAInv d {} := by
  intro e k r h
  simp at h

theorem MemoAInv.insert {d : Nat} {memo : MemoN} (hm : MemoAInv d memo)
    {e r : ExprC} {k : Nat}
    (heq : r = (Expr.abstract1 e d k)) :
    MemoAInv d (memo.insert (e, k) r) := by
  intro e' k' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hkk⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hkk]
    exact heq
  · exact hm e' k' r' hk

/-- **The `abstract1` core commutes with erasure** (deviation cutoff
included: `fvarB_le` certifies `Expr.fvarsBelow`, whence
`abstract1_eq_self`). -/
theorem abstract1Go_spec {d : Nat} : ∀ {e : ExprC},
    ∀ {memo : MemoN} {k : Nat}, MemoAInv d memo →
        MemoAInv d (abstract1Go d memo e k).2 ∧
        (abstract1Go d memo e k).1 = (Expr.abstract1 e d k) := by
  intro e
  induction e with
  | fvar idx n ty iht =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · dsimp only
        split
        · rename_i hidx
          refine ⟨hm.insert ?_, ?_⟩ <;>
            simp [Expr.abstract1, hidx]
        · rename_i hidx
          refine ⟨hm.insert ?_, ?_⟩ <;>
            simp [Expr.abstract1, hidx]
  | bvar i =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | sort u =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | const n us =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | lit l =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | app f a ihf iha =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihf (k := k) hm
        rcases hp : abstract1Go d memo f k with ⟨f', mf⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := iha (k := k) h2
        rcases hq : abstract1Go d mf a k with ⟨a', ma⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkApp f' a')
            = (Expr.abstract1 (.app f a) d k) := by
          rw [mkApp_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (k := k) hm
        rcases hp : abstract1Go d memo ty k with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb (k := k + 1) h2
        rcases hq : abstract1Go d mt bd (k + 1) with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkLam n ty' b' m)
            = (Expr.abstract1 (.lam n ty bd m) d k) := by
          rw [mkLam_eq, h3, h6]; rfl
        exact ⟨h5.insert hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (k := k) hm
        rcases hp : abstract1Go d memo ty k with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb (k := k + 1) h2
        rcases hq : abstract1Go d mt bd (k + 1) with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkForallE n ty' b' m)
            = (Expr.abstract1 (.forallE n ty bd m) d k) := by
          rw [mkForallE_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (k := k) hm
        rcases hp : abstract1Go d memo ty k with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihv (k := k) h2
        rcases hq : abstract1Go d mt val k with ⟨v', mv⟩
        simp only [hq] at h5 h6
        obtain ⟨h8, h9⟩ := ihb (k := k + 1) h5
        rcases hr : abstract1Go d mv bd (k + 1) with ⟨b', mb⟩
        simp only [hr] at h8 h9
        simp only [hp, hq, hr]
        have hres : (mkLetE n ty' v' b')
            = (Expr.abstract1 (.letE n ty val bd) d k) := by
          rw [mkLetE_eq, h3, h6, h9]; rfl
        exact ⟨h8.insert hres, hres⟩
  | proj s i sub ihe =>
    intro memo k hm
    rw [abstract1Go.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstract1_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihe (k := k) hm
        rcases hp : abstract1Go d memo sub k with ⟨s', ms⟩
        simp only [hp] at h2 h3
        simp only [hp]
        have hres : (mkProj s i s')
            = (Expr.abstract1 (.proj s i sub) d k) := by
          rw [mkProj_eq, h3]; rfl
        exact ⟨h2.insert hres, hres⟩

theorem abstract1_spec {e : ExprC} {d k : Nat} :
      (abstract1 e d k) = (Expr.abstract1 e d k) := by
  rw [abstract1]
  split
  · rename_i hcut
    exact (abstract1_eq_self (fvarB_le hcut)).symm
  · exact (abstract1Go_spec (d := d) (k := k) MemoAInv.empty).2

/-! ### Bulk abstraction -/

/-- Abstracting an empty range is the identity. -/
private theorem abstractRange_zero : ∀ (e : Expr) (d c : Nat),
    e.abstractRange d 0 c = e := by
  intro e
  induction e <;> intro d c <;> simp_all [Expr.abstractRange]

/-- The `abstractRange` memo invariant at the ambient window `d`, `k`. -/
def MemoARInv (d k : Nat) (memo : MemoN) : Prop :=
  ∀ (e : ExprC) (c : Nat) (r : ExprC), memo[(e, c)]? = some r →
    r = (Expr.abstractRange e d k c)

theorem MemoARInv.empty {d k : Nat} : MemoARInv d k {} := by
  intro e c r h
  simp at h

theorem MemoARInv.insert {d k : Nat} {memo : MemoN} (hm : MemoARInv d k memo)
    {e r : ExprC} {c : Nat}
    (heq : r = (Expr.abstractRange e d k c)) :
    MemoARInv d k (memo.insert (e, c) r) := by
  intro e' c' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    obtain ⟨he, hcc⟩ := pairKey_inv hbeq
    rw [← he, ← (beq_iff_eq ..).mp hcc]
    exact heq
  · exact hm e' c' r' hk

/-- **The bulk-abstraction core commutes with erasure.** -/
theorem abstractRangeGo_spec {d k : Nat} : ∀ {e : ExprC},
    ∀ {memo : MemoN} {c : Nat}, MemoARInv d k memo →
        MemoARInv d k (abstractRangeGo d k memo e c).2 ∧
        (abstractRangeGo d k memo e c).1
          = (Expr.abstractRange e d k c) := by
  intro e
  induction e with
  | fvar idx n ty iht =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · dsimp only
        split
        · rename_i hidx
          refine ⟨hm.insert ?_, ?_⟩ <;>
            simp [Expr.abstractRange, hidx]
        · rename_i hidx
          refine ⟨hm.insert ?_, ?_⟩ <;>
            simp [Expr.abstractRange, hidx]
  | bvar i =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | sort u =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | const n us =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | lit l =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | app f a ihf iha =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihf (c := c) hm
        rcases hp : abstractRangeGo d k memo f c with ⟨f', mf⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := iha (c := c) h2
        rcases hq : abstractRangeGo d k mf a c with ⟨a', ma⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkApp f' a')
            = (Expr.abstractRange (.app f a) d k c) := by
          rw [mkApp_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (c := c) hm
        rcases hp : abstractRangeGo d k memo ty c with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb (c := c + 1) h2
        rcases hq : abstractRangeGo d k mt bd (c + 1) with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkLam n ty' b' m)
            = (Expr.abstractRange (.lam n ty bd m) d k c) := by
          rw [mkLam_eq, h3, h6]; rfl
        exact ⟨h5.insert hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (c := c) hm
        rcases hp : abstractRangeGo d k memo ty c with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb (c := c + 1) h2
        rcases hq : abstractRangeGo d k mt bd (c + 1) with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkForallE n ty' b' m)
            = (Expr.abstractRange (.forallE n ty bd m)
                d k c) := by
          rw [mkForallE_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht (c := c) hm
        rcases hp : abstractRangeGo d k memo ty c with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihv (c := c) h2
        rcases hq : abstractRangeGo d k mt val c with ⟨v', mv⟩
        simp only [hq] at h5 h6
        obtain ⟨h8, h9⟩ := ihb (c := c + 1) h5
        rcases hr : abstractRangeGo d k mv bd (c + 1) with ⟨b', mb⟩
        simp only [hr] at h8 h9
        simp only [hp, hq, hr]
        have hres : (mkLetE n ty' v' b')
            = (Expr.abstractRange (.letE n ty val bd)
                d k c) := by
          rw [mkLetE_eq, h3, h6, h9]; rfl
        exact ⟨h8.insert hres, hres⟩
  | proj s i sub ihe =>
    intro memo c hm
    rw [abstractRangeGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (abstractRange_eq_self (fvarB_le hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihe (c := c) hm
        rcases hp : abstractRangeGo d k memo sub c with ⟨s', ms⟩
        simp only [hp] at h2 h3
        simp only [hp]
        have hres : (mkProj s i s')
            = (Expr.abstractRange (.proj s i sub) d k c) := by
          rw [mkProj_eq, h3]; rfl
        exact ⟨h2.insert hres, hres⟩

theorem abstractRange_spec {e : ExprC} {d k c : Nat} :
      (abstractRange e d k c) = (Expr.abstractRange e d k c) := by
  cases k with
  | zero => exact (abstractRange_zero _ _ _).symm
  | succ k' =>
    rw [abstractRange]
    split
    · rename_i hcut
      exact (abstractRange_eq_self (fvarB_le hcut)).symm
    · exact (abstractRangeGo_spec (d := d) (k := k' + 1) (c := c)
        MemoARInv.empty).2

/-! ## Level instantiation -/

/-- The `instLevelParams` memo invariant (the key carries no cursor). -/
def MemoLPInv (ks : List Name) (us : List Level) (memo : Memo0) : Prop :=
  ∀ (e r : ExprC), memo[e]? = some r →
    r = e.instantiateLevelParams ks us

theorem MemoLPInv.empty {ks : List Name} {us : List Level} :
    MemoLPInv ks us {} := by
  intro e r h
  simp at h

theorem MemoLPInv.insert {ks : List Name} {us : List Level} {memo : Memo0}
    (hm : MemoLPInv ks us memo) {e r : ExprC}
    (heq : r = e.instantiateLevelParams ks us) :
    MemoLPInv ks us (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← beq_sound hbeq]
    exact heq
  · exact hm e' r' hk

/-- **The level-instantiation core commutes with erasure** (the
`hasLP` cutoff is `hasLP_false`; the binder arms substitute the
prop-ness datum exactly as `Expr.instantiateLevelParams` does). -/
theorem instLevelParamsGo_spec {ks : List Name} {us : List Level} :
    ∀ {e : ExprC}, ∀ {memo : Memo0}, MemoLPInv ks us memo →
        MemoLPInv ks us (instLevelParamsGo ks us memo e).2 ∧
        (instLevelParamsGo ks us memo e).1
          = e.instantiateLevelParams ks us := by
  intro e
  induction e with
  | bvar i =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | lit l =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · exact ⟨hm.insert rfl, rfl⟩
  | sort u =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · exact ⟨(hm.insert rfl), rfl⟩
  | const n vs =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · exact ⟨(hm.insert rfl), rfl⟩
  | fvar idx n ty iht =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨t, mt⟩
        simp only [hp] at h2 h3
        simp only [hp]
        have hres : (mkFVar idx n t)
            = (Expr.fvar idx n ty).instantiateLevelParams
                ks us := by
          rw [mkFVar_eq, h3]; rfl
        exact ⟨h2.insert hres,
          hres⟩
  | app f a ihf iha =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihf hm
        rcases hp : instLevelParamsGo ks us memo f with ⟨f', mf⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := iha h2
        rcases hq : instLevelParamsGo ks us mf a with ⟨a', ma⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkApp f' a')
            = (Expr.app f a).instantiateLevelParams
                ks us := by
          rw [mkApp_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | lam n ty bd m iht ihb =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb h2
        rcases hq : instLevelParamsGo ks us mt bd with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres : (mkLam n ty' b' ⟨m.bi, Level.substPW ks us m.pw⟩)
            = (Expr.lam n ty bd m).instantiateLevelParams
                ks us := by
          rw [mkLam_eq, h3, h6]; rfl
        exact ⟨h5.insert hres,
          hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihb h2
        rcases hq : instLevelParamsGo ks us mt bd with ⟨b', mb⟩
        simp only [hq] at h5 h6
        simp only [hp, hq]
        have hres :               (mkForallE n ty' b' ⟨m.bi, Level.substPW ks us m.pw⟩)
            = (Expr.forallE n ty bd m).instantiateLevelParams
                ks us := by
          rw [mkForallE_eq, h3, h6]; rfl
        exact ⟨h5.insert hres, hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := iht hm
        rcases hp : instLevelParamsGo ks us memo ty with ⟨ty', mt⟩
        simp only [hp] at h2 h3
        obtain ⟨h5, h6⟩ := ihv h2
        rcases hq : instLevelParamsGo ks us mt val with ⟨v', mv⟩
        simp only [hq] at h5 h6
        obtain ⟨h8, h9⟩ := ihb h5
        rcases hr : instLevelParamsGo ks us mv bd with ⟨b', mb⟩
        simp only [hr] at h8 h9
        simp only [hp, hq, hr]
        have hres : (mkLetE n ty' v' b')
            = (Expr.letE n ty val bd).instantiateLevelParams
                ks us := by
          rw [mkLetE_eq, h3, h6, h9]; rfl
        exact ⟨h8.insert hres, hres⟩
  | proj s i sub ihe =>
    intro memo hm
    rw [instLevelParamsGo.eq_def]
    split
    · rename_i hcut
      exact ⟨hm, (hasLP_false (by simpa using hcut)).symm⟩
    · split
      · rename_i r hhit
        exact ⟨hm, (hm _ _ hhit)⟩
      · obtain ⟨h2, h3⟩ := ihe hm
        rcases hp : instLevelParamsGo ks us memo sub with ⟨s', ms⟩
        simp only [hp] at h2 h3
        simp only [hp]
        have hres : (mkProj s i s')
            = (Expr.proj s i sub).instantiateLevelParams
                ks us := by
          rw [mkProj_eq, h3]; rfl
        exact ⟨h2.insert hres, hres⟩

theorem instLevelParams_spec {ks : List Name} {us : List Level} {e : ExprC} :
    (instLevelParams ks us e) = e.instantiateLevelParams ks us := by
  rw [instLevelParams]
  split
  · rename_i hcut
    exact (hasLP_false (by simpa using hcut)).symm
  · exact (instLevelParamsGo_spec (ks := ks) (us := us) MemoLPInv.empty).2

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
    r = (Expr.wscopedB d e)

theorem MemoWInv.empty : MemoWInv {} := by
  intro e d r h
  simp at h

theorem MemoWInv.insert {memo : Std.HashMap (ExprC × Nat) Bool}
    (hm : MemoWInv memo) {e : ExprC} {d : Nat} {r : Bool}
    (heq : r = (Expr.wscopedB d e)) : MemoWInv (memo.insert (e, d) r) := by
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
theorem wscopedBGo_spec : ∀ {e : ExprC},
    ∀ {memo : Std.HashMap (ExprC × Nat) Bool} {d : Nat}, MemoWInv memo →
      (wscopedBGo memo d e).1 = (Expr.wscopedB d e) ∧
        MemoWInv (wscopedBGo memo d e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_bvar i d).symm,
          hm.insert (wscopedB_bvar i d).symm⟩
  | sort u =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_sort u d).symm,
          hm.insert (wscopedB_sort u d).symm⟩
  | const n us =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_const n us d).symm,
          hm.insert (wscopedB_const n us d).symm⟩
  | lit l =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · exact ⟨(wscopedB_lit l d).symm, hm.insert (wscopedB_lit l d).symm⟩
  | fvar idx n ty iht =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · dsimp only
        split
        · rename_i hidx
          obtain ⟨h1, h2⟩ := iht (d := idx) hm
          rcases hp : wscopedBGo memo idx ty with ⟨rt, mt⟩
          simp only [hp] at h1 h2
          have hres : rt = (Expr.wscopedB d (.fvar idx n ty)) := by
            rw [show (Expr.fvar idx n ty)
                = Expr.fvar idx n ty from rfl, wscopedB_fvar,
              ← h1, decide_eq_true hidx, Bool.true_and]
          exact ⟨hres, h2.insert hres⟩
        · rename_i hidx
          have hres : false
              = (Expr.wscopedB d (.fvar idx n ty)) := by
            rw [wscopedB_fvar,
              decide_eq_false hidx, Bool.false_and]
          exact ⟨hres, hm.insert hres⟩
  | app f a ihf iha =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihf (d := d) hm
        rcases hp : wscopedBGo memo d f with ⟨rf, mf⟩
        simp only [hp] at h1 h2
        simp only [hp]
        cases rf with
        | true =>
          obtain ⟨h3, h4⟩ := iha (d := d) h2
          rcases hq : wscopedBGo mf d a with ⟨ra, ma⟩
          simp only [hq] at h3 h4
          have hres : ra = (Expr.wscopedB d (.app f a)) := by
            rw [wscopedB_app,
              ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false = (Expr.wscopedB d (.app f a)) := by
            rw [wscopedB_app,
              ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | lam n ty bd m iht ihb =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht (d := d) hm
        rcases hp : wscopedBGo memo d ty with ⟨rt, mt⟩
        simp only [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb (d := d) h2
          rcases hq : wscopedBGo mt d bd with ⟨rb, mb⟩
          simp only [hq] at h3 h4
          have hres : rb
              = (Expr.wscopedB d (.lam n ty bd m)) := by
            rw [wscopedB_lam, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (Expr.wscopedB d (.lam n ty bd m)) := by
            rw [wscopedB_lam, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | forallE n ty bd m iht ihb =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := iht (d := d) hm
        rcases hp : wscopedBGo memo d ty with ⟨rt, mt⟩
        simp only [hp] at h1 h2
        simp only [hp]
        cases rt with
        | true =>
          obtain ⟨h3, h4⟩ := ihb (d := d) h2
          rcases hq : wscopedBGo mt d bd with ⟨rb, mb⟩
          simp only [hq] at h3 h4
          have hres : rb
              = (Expr.wscopedB d (.forallE n ty bd m)) := by
            rw [wscopedB_forallE, ← h1, ← h3, Bool.true_and]
          exact ⟨hres, h4.insert hres⟩
        | false =>
          have hres : false
              = (Expr.wscopedB d (.forallE n ty bd m)) := by
            rw [wscopedB_forallE, ← h1, Bool.false_and]
          exact ⟨hres, h2.insert hres⟩
  | letE n ty val bd iht ihv ihb =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · have herase : (Expr.letE n ty val bd)
            = Expr.letE n ty val bd := rfl
        obtain ⟨h1, h2⟩ := iht (d := d) hm
        rcases hp : wscopedBGo memo d ty with ⟨rt, mt⟩
        simp only [hp] at h1 h2
        simp only [hp]
        cases rt with
        | false =>
          have hres : false
              = (Expr.wscopedB d (.letE n ty val bd)) := by
            rw [herase, wscopedB_letE, ← h1]
            simp
          exact ⟨hres, h2.insert hres⟩
        | true =>
          obtain ⟨h3, h4⟩ := ihv (d := d) h2
          rcases hq : wscopedBGo mt d val with ⟨rv, mv⟩
          simp only [hq] at h3 h4
          cases rv with
          | false =>
            have hres : false
                = (Expr.wscopedB d (.letE n ty val bd)) := by
              rw [herase, wscopedB_letE, ← h1, ← h3]
              simp
            exact ⟨hres, h4.insert hres⟩
          | true =>
            obtain ⟨h5, h6⟩ := ihb (d := d) h4
            rcases hr : wscopedBGo mv d bd with ⟨rb, mb⟩
            simp only [hr] at h5 h6
            have hres : rb
                = (Expr.wscopedB d (.letE n ty val bd)) := by
              rw [herase, wscopedB_letE, ← h1, ← h3, ← h5]
              simp
            exact ⟨hres, h6.insert hres⟩
  | proj s i sub ihe =>
    intro memo d hm
    rw [wscopedBGo.eq_def]
    split
    · rename_i hcut
      exact ⟨(wscopedB_of_fvarsBelow_zero _
        (fvarB_le (Nat.le_of_eq (by simpa using hcut))) d).symm, hm⟩
    · split
      · rename_i r hhit
        exact ⟨hm _ _ _ hhit, hm⟩
      · obtain ⟨h1, h2⟩ := ihe (d := d) hm
        rcases hp : wscopedBGo memo d sub with ⟨rs, ms⟩
        simp only [hp] at h1 h2
        simp only [hp]
        have hres : rs
            = (Expr.wscopedB d (.proj s i sub)) := by
          rw [wscopedB_proj, ← h1]
        exact ⟨hres, h2.insert hres⟩

theorem wscopedB_spec {d : Nat} {e : ExprC} :
    wscopedB d e = (Expr.wscopedB d e) :=
  (wscopedBGo_spec (d := d) MemoWInv.empty).1

/-! ## The `∀`-telescope residual

`piResidualAcc` follows the arena twin's accumulator discipline: the
`forallE` arm consumes an argument into the accumulator, the `bvar` arm
flushes a nonempty accumulator by one bulk instantiation and re-enters.
The induction is the function's own measure `(as.length, acc.length)`. -/

theorem piResidualAcc_spec :
    ∀ (as acc : List ExprC) (e : ExprC),
      OptEr (piResidualAcc acc e as)
        (_root_.Setlec.piResidual
          ((Expr.instantiateList e acc)) as)
  | [], acc, e => by
    rw [piResidualAcc.eq_def]
    exact instantiateList_spec (d := 0)
  | a :: as, acc, e => by
    cases e with
    | forallE n ty b m =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_forallE,
        show _root_.Setlec.piResidual
            (Expr.forallE n ((Expr.instantiateList ty acc 0))
              ((Expr.instantiateList b acc 1)) m)
            (a :: as)
          = _root_.Setlec.piResidual
              (((Expr.instantiateList b acc 1)).instantiate1
                a) as from rfl,
        ← Expr.instantiateList_cons]
      exact piResidualAcc_spec as (a :: acc) b
    | bvar i =>
      rw [piResidualAcc.eq_def]
      dsimp only
      cases acc with
      | nil =>
        rw [Expr.instantiateList_nil]
        exact trivial
      | cons a' acc' =>
        have h2 :=
          instantiateList_spec (e := Expr.bvar i)
            (vs := a' :: acc') (d := 0)
        have hrec := piResidualAcc_spec (a :: as) []
          (instantiateList (Expr.bvar i) (a' :: acc') 0)
        rw [Expr.instantiateList_nil] at hrec
        rw [← h2]
        exact hrec
    | fvar idx n ty =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.fvar idx n ty)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | sort u =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.sort u)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | const n us =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.const n us)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | lit l =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [← instList_leaf (e := Expr.lit l)
        (ws := acc) (d := 0) rfl]
      exact trivial
    | app f a' =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_app]
      exact trivial
    | lam n ty b m =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_lam]
      exact trivial
    | letE n ty v b =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_letE]
      exact trivial
    | proj s i sub =>
      rw [piResidualAcc.eq_def]
      dsimp only
      rw [instList_proj]
      exact trivial
termination_by as acc => (as.length, acc.length)
decreasing_by
  · apply Prod.Lex.right' <;> simp_all
  · apply Prod.Lex.left; simp

theorem piResidual_spec {e : ExprC} {args : List ExprC} :
    OptEr (piResidual e args)
      (_root_.Setlec.piResidual e args) := by
  have h := piResidualAcc_spec args [] e
  rw [Expr.instantiateList_nil] at h
  exact h

end ExprC

end Setlec.Cached
