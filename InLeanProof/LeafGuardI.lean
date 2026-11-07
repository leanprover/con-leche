module

public import InLeanProof.WalksIota
public import ConLeche.Verify.Cached.DiscC3
/- `FVarId`'s derived `BEq` is not exposed by `Lean.Expr`; the id sets'
lawfulness reads it. -/
import all Lean.Expr

/-!
# The rescues' free-variable guards (task #451, lane P2-whnf)

InLean's guards on a fabricated major (`InLean/CoreC.lean`'s `majorToCtorI`)
against con-leche's: the scope guard `Expr.wscopedBC` (ids' depths) holds on a
scoped translation (`wscopedBC_of_WScoped`), the closedness guard
`Expr.closedBV` (the cached range) on a closed one (`closedBV_of_lbb`), and the
leaf guard `leafGuardM` (a worklist closure of ids through the interned types)
answers `leafGuardP` at the translations (`leafGuardSpecI`).

The free variables `EO.fvarIds` collects are exactly the term's
(`mem_fvarIds`: its `seen` skip and `hasFVar` cut, under `Expr.RangeOk`);
the leaves of a translation are the translations of the ids its variables
reach through the interned types (`term_leaves`, `idLeaves`).

**The leaf guard** (`leafGuardSpecI`): the closure spends fuel only on
expanding a table number not expanded before, so its fuel `tys.size` never
runs out (`ClosureInv`, a counting argument, `hashSetNat_size_le`); the
cached `hasFVar` cut of `EO.fvarIds` on the interned types reads
`FVTableOK.range`.
-/

public section

namespace InLeanProof
open Lean InLean Std.WP
open scoped Lean.Order

/-! ## Free-variable occurrences and their collection -/

instance instLawfulBEqFVarIdI : LawfulBEq FVarId where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, instBEqFVarId.beq] at h
    exact congrArg FVarId.mk (eq_of_beq (show (_ == _) = true from h))
  rfl {a} := by cases a with | mk n => exact (beq_self_eq_true n : (n == n) = true)

/-- `x` occurs as a free variable of `e`. -/
@[expose] def OccF (x : FVarId) : Expr → Prop
  | .fvar id => id = x
  | .app f a | .lam _ f a _ | .forallE _ f a _ => OccF x f ∨ OccF x a
  | .letE _ t v b _ => OccF x t ∨ OccF x v ∨ OccF x b
  | .mdata _ e | .proj _ _ e => OccF x e
  | _ => False

theorem not_occF_of_fvarS {x : FVarId} : ∀ {e : Expr}, fvarS e = false → ¬ OccF x e := by
  intro e
  induction e <;> simp_all [fvarS, OccF]

section Collect
attribute [local instance 3000] instBEqExprExact
attribute [local instance] instBEqExprExact_lawful

/-- Every node of `seen` up to size `sz` has its free variables in `acc`. -/
@[expose] def CPre (seen : Std.HashSet Expr) (acc : Array FVarId) (sz : Nat) : Prop :=
  ∀ x, seen.contains x = true → sizeOf x ≤ sz → ∀ a, OccF a x → a ∈ acc

/-- What one call of the collecting walk does, for the occurrences `P` of what it
walks, at size bound `sz`. -/
@[expose] def GoSpecP (P : FVarId → Prop) (sz : Nat) (seen : Std.HashSet Expr)
    (acc : Array FVarId) (r : Std.HashSet Expr × Array FVarId) : Prop :=
  (∀ a, a ∈ acc → a ∈ r.2) ∧ (∀ a, a ∈ r.2 → a ∈ acc ∨ P a) ∧
  (∀ x, seen.contains x = true → r.1.contains x = true) ∧
  (∀ x, r.1.contains x = true → seen.contains x = true ∨ sizeOf x ≤ sz) ∧
  (CPre seen acc sz → CPre r.1 r.2 sz ∧ ∀ a, P a → a ∈ r.2)

theorem GoSpecP.seq {P Q : FVarId → Prop} {sz₁ sz₂ : Nat} {seen : Std.HashSet Expr}
    {acc : Array FVarId} {r₁ r₂ : Std.HashSet Expr × Array FVarId}
    (h₁ : GoSpecP P sz₁ seen acc r₁) (h₂ : GoSpecP Q sz₂ r₁.1 r₁.2 r₂) :
    GoSpecP (fun a => P a ∨ Q a) (max sz₁ sz₂) seen acc r₂ := by
  obtain ⟨m₁, s₁, c₁, n₁, k₁⟩ := h₁
  obtain ⟨m₂, s₂, c₂, n₂, k₂⟩ := h₂
  refine ⟨fun a ha => m₂ a (m₁ a ha), fun a ha => ?_, fun x hx => c₂ x (c₁ x hx),
    fun x hx => ?_, fun hpre => ?_⟩
  · rcases s₂ a ha with h | h
    · rcases s₁ a h with h' | h'
      · exact .inl h'
      · exact .inr (.inl h')
    · exact .inr (.inr h)
  · rcases n₂ x hx with h | h
    · rcases n₁ x h with h' | h'
      · exact .inl h'
      · exact .inr (by omega)
    · exact .inr (by omega)
  · have hpre₁ : CPre seen acc sz₁ := fun x hx hs a ha => hpre x hx (by omega) a ha
    obtain ⟨post₁, comp₁⟩ := k₁ hpre₁
    have hpre₂ : CPre r₁.1 r₁.2 sz₂ := by
      intro x hx hs a ha
      by_cases hle : sizeOf x ≤ sz₁
      · exact post₁ x hx hle a ha
      · rcases n₁ x hx with h | h
        · exact m₁ a (hpre x h (by omega) a ha)
        · exact absurd h hle
    obtain ⟨post₂, comp₂⟩ := k₂ hpre₂
    refine ⟨fun x hx hs a ha => ?_, fun a ha => ?_⟩
    · by_cases hle₂ : sizeOf x ≤ sz₂
      · exact post₂ x hx hle₂ a ha
      · rcases n₂ x hx with h | h
        · by_cases hle₁ : sizeOf x ≤ sz₁
          · exact m₂ a (post₁ x h hle₁ a ha)
          · rcases n₁ x h with h' | h'
            · exact m₂ a (m₁ a (hpre x h' hs a ha))
            · exact absurd h' hle₁
        · exact absurd h hle₂
    · rcases ha with ha | ha
      · exact m₂ a (comp₁ a ha)
      · exact comp₂ a ha

theorem GoSpecP.wrap {P : FVarId → Prop} {sz : Nat} {e : Expr} {seen : Std.HashSet Expr}
    {acc : Array FVarId} {r : Std.HashSet Expr × Array FVarId}
    (hsz : sz < sizeOf e) (hP : ∀ a, OccF a e ↔ P a)
    (h : GoSpecP P sz (seen.insert e) acc r) :
    GoSpecP (fun a => OccF a e) (sizeOf e) seen acc r := by
  obtain ⟨m, so, c, n, k⟩ := h
  refine ⟨m, fun a ha => ?_, fun x hx => c x ?_, fun x hx => ?_, fun hpre => ?_⟩
  · rcases so a ha with h | h
    · exact .inl h
    · exact .inr ((hP a).2 h)
  · rw [Std.HashSet.contains_insert, hx, Bool.or_true]
  · rcases n x hx with h | h
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; exact .inr (Nat.le_refl _)
      · exact .inl h
    · exact .inr (by omega)
  · have hpre' : CPre (seen.insert e) acc sz := by
      intro x hx hs a ha
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with hx | hx
      · subst hx; omega
      · exact hpre x hx (by omega) a ha
    obtain ⟨post, comp⟩ := k hpre'
    have compE : ∀ a, OccF a e → a ∈ r.2 := fun a ha => comp a ((hP a).1 ha)
    refine ⟨fun x hx hs a ha => ?_, compE⟩
    by_cases hle : sizeOf x ≤ sz
    · exact post x hx hle a ha
    · rcases n x hx with h | h
      · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · subst h; exact compE a ha
        · exact m a (hpre x h hs a ha)
      · exact absurd h hle

/-- A call that returns its inputs on a node already seen. -/
theorem GoSpecP.seen {e : Expr} {seen : Std.HashSet Expr} {acc : Array FVarId}
    (h : seen.contains e = true) : GoSpecP (fun a => OccF a e) (sizeOf e) seen acc (seen, acc) :=
  ⟨fun _ h => h, fun _ h => .inl h, fun _ h => h, fun _ h => .inl h,
    fun hpre => ⟨hpre, fun a ha => hpre e h (Nat.le_refl _) a ha⟩⟩

/-- A call on a node without occurrences that returns its inputs. -/
theorem GoSpecP.none {e : Expr} {seen : Std.HashSet Expr} {acc : Array FVarId}
    (h : ∀ a, ¬ OccF a e) : GoSpecP (fun a => OccF a e) (sizeOf e) seen acc (seen, acc) :=
  ⟨fun _ h => h, fun _ h => .inl h, fun _ h => h, fun _ h => .inl h,
    fun hpre => ⟨hpre, fun a ha => absurd ha (h a)⟩⟩

variable (stop : Expr → Bool) (pick : Expr → Option FVarId)
  (hstop : ∀ x, Expr.RangeOk x → stop x = true → ∀ a, ¬ OccF a x)
  (hpick : ∀ x a, pick x = some a ↔ x = .fvar a)

include hstop hpick in
theorem collect_go_spec : ∀ (e : Expr), Expr.RangeOk e → ∀ (seen : Std.HashSet Expr) (acc : Array FVarId),
    GoSpecP (fun a => OccF a e) (sizeOf e) seen acc (EO.collect.go stop pick e seen acc) := by
  have hnp : ∀ x, (∀ a, x ≠ .fvar a) → pick x = none := by
    intro x hx
    cases h : pick x with
    | none => rfl
    | some b => exact absurd ((hpick _ b).1 h) (hx b)
  intro e
  induction e with
  | app f a iht ihb =>
    intro hr seen acc
    have hp := hnp (.app f a) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    by_cases hs : stop (.app f a) = true
    · simp only [hs, ↓reduceIte]; exact GoSpecP.none (hstop _ hr hs)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, EO.isCompound, Bool.not_true]
      cases hc : seen.contains (.app f a)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine GoSpecP.wrap ?_ (fun _ => Iff.rfl) ((iht hr.1 _ acc).seq (ihb hr.2 _ _))
        simp only [Expr.app.sizeOf_spec]; omega
      · simp only [↓reduceIte]; exact GoSpecP.seen hc
  | lam n t b bi iht ihb =>
    intro hr seen acc
    have hp := hnp (.lam n t b bi) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    by_cases hs : stop (.lam n t b bi) = true
    · simp only [hs, ↓reduceIte]; exact GoSpecP.none (hstop _ hr hs)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, EO.isCompound, Bool.not_true]
      cases hc : seen.contains (.lam n t b bi)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine GoSpecP.wrap ?_ (fun _ => Iff.rfl) ((iht hr.1 _ acc).seq (ihb hr.2 _ _))
        simp only [Expr.lam.sizeOf_spec]; omega
      · simp only [↓reduceIte]; exact GoSpecP.seen hc
  | forallE n t b bi iht ihb =>
    intro hr seen acc
    have hp := hnp (.forallE n t b bi) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    by_cases hs : stop (.forallE n t b bi) = true
    · simp only [hs, ↓reduceIte]; exact GoSpecP.none (hstop _ hr hs)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, EO.isCompound, Bool.not_true]
      cases hc : seen.contains (.forallE n t b bi)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine GoSpecP.wrap ?_ (fun _ => Iff.rfl) ((iht hr.1 _ acc).seq (ihb hr.2 _ _))
        simp only [Expr.forallE.sizeOf_spec]; omega
      · simp only [↓reduceIte]; exact GoSpecP.seen hc
  | letE n t v b nd iht ihv ihb =>
    intro hr seen acc
    have hp := hnp (.letE n t v b nd) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    by_cases hs : stop (.letE n t v b nd) = true
    · simp only [hs, ↓reduceIte]; exact GoSpecP.none (hstop _ hr hs)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, EO.isCompound, Bool.not_true]
      cases hc : seen.contains (.letE n t v b nd)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine GoSpecP.wrap ?_ (fun _ => by simp only [OccF, or_assoc])
          (((iht hr.1 _ acc).seq (ihv hr.2.1 _ _)).seq (ihb hr.2.2 _ _))
        simp only [Expr.letE.sizeOf_spec]; omega
      · simp only [↓reduceIte]; exact GoSpecP.seen hc
  | mdata m x ihx =>
    intro hr seen acc
    have hp := hnp (.mdata m x) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    by_cases hs : stop (.mdata m x) = true
    · simp only [hs, ↓reduceIte]; exact GoSpecP.none (hstop _ hr hs)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, EO.isCompound, Bool.not_true]
      cases hc : seen.contains (.mdata m x)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine GoSpecP.wrap ?_ (fun _ => Iff.rfl) (ihx hr _ acc)
        simp only [Expr.mdata.sizeOf_spec]; omega
      · simp only [↓reduceIte]; exact GoSpecP.seen hc
  | proj sn i x ihx =>
    intro hr seen acc
    have hp := hnp (.proj sn i x) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    by_cases hs : stop (.proj sn i x) = true
    · simp only [hs, ↓reduceIte]; exact GoSpecP.none (hstop _ hr hs)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, EO.isCompound, Bool.not_true]
      cases hc : seen.contains (.proj sn i x)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine GoSpecP.wrap ?_ (fun _ => Iff.rfl) (ihx hr _ acc)
        simp only [Expr.proj.sizeOf_spec]; omega
      · simp only [↓reduceIte]; exact GoSpecP.seen hc
  | bvar i =>
    intro hr seen acc
    have hp := hnp (.bvar i) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    have hno : ∀ a, ¬ OccF a (.bvar i) := fun a h => by simp only [OccF] at h
    split <;> (try simp only [EO.isCompound, Bool.not_false, ↓reduceIte]) <;> exact GoSpecP.none hno
  | mvar m =>
    intro hr seen acc
    have hp := hnp (.mvar m) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    have hno : ∀ a, ¬ OccF a (.mvar m) := fun a h => by simp only [OccF] at h
    split <;> (try simp only [EO.isCompound, Bool.not_false, ↓reduceIte]) <;> exact GoSpecP.none hno
  | sort u =>
    intro hr seen acc
    have hp := hnp (.sort u) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    have hno : ∀ a, ¬ OccF a (.sort u) := fun a h => by simp only [OccF] at h
    split <;> (try simp only [EO.isCompound, Bool.not_false, ↓reduceIte]) <;> exact GoSpecP.none hno
  | const n us =>
    intro hr seen acc
    have hp := hnp (.const n us) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    have hno : ∀ a, ¬ OccF a (.const n us) := fun a h => by simp only [OccF] at h
    split <;> (try simp only [EO.isCompound, Bool.not_false, ↓reduceIte]) <;> exact GoSpecP.none hno
  | lit l =>
    intro hr seen acc
    have hp := hnp (.lit l) (by intro b h; cases h)
    unfold EO.collect.go
    simp only [hp]
    have hno : ∀ a, ¬ OccF a (.lit l) := fun a h => by simp only [OccF] at h
    split <;> (try simp only [EO.isCompound, Bool.not_false, ↓reduceIte]) <;> exact GoSpecP.none hno
  | fvar id =>
    intro hr seen acc
    have hp : pick (.fvar id) = some id := (hpick _ _).2 rfl
    unfold EO.collect.go
    simp only [hp]
    split
    · rename_i hs; exact GoSpecP.none (hstop _ hr hs)
    · simp only [EO.isCompound, Bool.not_false, ↓reduceIte]
      refine ⟨fun a h => Array.mem_push_of_mem _ h, fun a h => ?_, fun _ h => h, fun _ h => .inl h,
        fun hpre => ⟨fun x hx hs a ha => Array.mem_push_of_mem _ (hpre x hx hs a ha),
          fun a ha => ?_⟩⟩
      · rcases Array.mem_push.1 h with h | h
        · exact .inl h
        · exact .inr (by simp [OccF, h])
      · simp only [OccF] at ha; subst ha; exact Array.mem_push_self
end Collect

/-- The dedup fold of `EO.fvarIds` keeps exactly the list's members. -/
theorem fvarIds_fold_mem : ∀ (l : List FVarId) (st : Std.HashSet FVarId) (acc : Array FVarId),
    (∀ a, st.contains a = true ↔ a ∈ acc) → ∀ a,
    a ∈ (l.foldl (fun (x : Std.HashSet FVarId × Array FVarId) id =>
        match x with
        | (s, acc) => if s.contains id = true then (s, acc) else (s.insert id, acc.push id))
      (st, acc)).2 ↔ a ∈ acc ∨ a ∈ l := by
  intro l
  induction l with
  | nil => intro st acc _ a; simp
  | cons b l ih =>
    intro st acc hinv a
    simp only [List.foldl_cons]
    split
    · rename_i hb
      rw [ih st acc hinv a]
      have := (hinv b).1 hb
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inl h
        · subst h; exact .inl this
        · exact .inr h
    · rw [ih (st.insert b) (acc.push b) ?_ a]
      · simp only [Array.mem_push, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · rintro (h | h | h)
          · exact .inl (.inl h)
          · exact .inl (.inr h)
          · exact .inr h
      · intro x
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hinv x, Array.mem_push,
          @eq_comm _ b x]
        exact Or.comm

section FvarIds
attribute [local instance 3000] instBEqExprExact
attribute [local instance] instBEqExprExact_lawful

/-- **The free variables `EO.fvarIds` collects are exactly the term's** (in
range: its cut reads the cached `hasFVar`). -/
theorem mem_fvarIds {e : Expr} (hr : Expr.RangeOk e) (a : FVarId) :
    a ∈ EO.fvarIds e ↔ OccF a e := by
  have hstop : ∀ x, Expr.RangeOk x → (!x.hasFVar) = true → ∀ a, ¬ OccF a x := by
    intro x hx hs a
    rw [Expr.hasFVar_eq hx, Bool.not_eq_true'] at hs
    exact not_occF_of_fvarS hs
  have hpick : ∀ (x : Expr) (a : FVarId),
      (match x with | .fvar id => some id | _ => none) = some a ↔ x = .fvar a := by
    intro x a; cases x <;> simp
  have hg := collect_go_spec _ _ hstop hpick e hr
    (Std.HashSet.emptyWithCapacity (e.approxDepth.toNat + 8)) #[]
  obtain ⟨-, hsound, -, -, hcomp⟩ := hg
  have hpre : CPre (Std.HashSet.emptyWithCapacity (e.approxDepth.toNat + 8)) #[] (sizeOf e) := by
    intro x hx; simp at hx
  have hall : ∀ a, a ∈ EO.collect (fun x => !x.hasFVar)
      (fun x => match x with | .fvar id => some id | _ => none) e ↔ OccF a e := by
    intro a
    refine ⟨fun h => ?_, fun h => (hcomp hpre).2 a h⟩
    rcases hsound a h with h | h
    · simp at h
    · exact h
  unfold EO.fvarIds
  simp only
  rw [← Array.foldl_toList, fvarIds_fold_mem _ _ _ (by simp), ← hall a]
  simp only [Array.mem_toList_iff, false_or, Array.not_mem_empty]
  exact Iff.rfl

end FvarIds

/-! ## The scope and closedness guards -/

/-- A free variable of a term with a reading is an interned id, and its
depth is below every depth the translation is scoped at. -/
theorem occF_depth {s : InLean.CState} {d : Nat} {a : FVarId} :
    ∀ {e : Expr}, OkS s e = true → ConLeche.Expr.WScoped d (TrS s e) → OccF a e →
      ∃ i n, a = fvId i n ∧ i < d := by
  intro e
  induction e generalizing d with
  | fvar id =>
    intro he hw ho
    simp only [OccF] at ho; subst ho
    simp only [OkS, okE, Option.isSome_iff_exists] at he
    obtain ⟨c, hc⟩ := he
    obtain ⟨i, n, rfl, hn⟩ := FVarTable.trans_some hc
    obtain ⟨-, -, cty, -, -, rfl⟩ := FVarTable.transNum_some hn
    have : TrS s (.fvar (fvId i n)) = .fvar i cty := by simp [TrS, trE, hc]
    rw [this] at hw
    simp only [ConLeche.Expr.WScoped] at hw
    exact ⟨i, n, rfl, hw.1⟩
  | app f x ihf ihx =>
    intro he hw ho
    rw [OkS_app, Bool.and_eq_true] at he
    rw [TrS_app] at hw; simp only [ConLeche.Expr.WScoped] at hw
    rcases ho with ho | ho
    · exact ihf he.1 hw.1 ho
    · exact ihx he.2 hw.2 ho
  | lam _ t b _ iht ihb =>
    intro he hw ho
    rw [OkS_lam, Bool.and_eq_true] at he
    rw [TrS_lam] at hw; simp only [ConLeche.Expr.WScoped] at hw
    rcases ho with ho | ho
    · exact iht he.1 hw.1 ho
    · exact ihb he.2 hw.2 ho
  | forallE _ t b _ iht ihb =>
    intro he hw ho
    rw [OkS_forallE, Bool.and_eq_true] at he
    rw [TrS_forallE] at hw; simp only [ConLeche.Expr.WScoped] at hw
    rcases ho with ho | ho
    · exact iht he.1 hw.1 ho
    · exact ihb he.2 hw.2 ho
  | letE _ t v b _ iht ihv ihb =>
    intro he hw ho
    simp only [OkS, okE, Bool.and_eq_true] at he
    rw [TrS_letE] at hw; simp only [ConLeche.Expr.WScoped] at hw
    rcases ho with ho | ho | ho
    · exact iht he.1.1 hw.1 ho
    · exact ihv he.1.2 hw.2.1 ho
    · exact ihb he.2 hw.2.2 ho
  | mdata _ x ih => intro he hw ho; exact ih he hw ho
  | proj _ _ x ih =>
    intro he hw ho
    rw [TrS_proj] at hw; simp only [ConLeche.Expr.WScoped] at hw
    exact ih he hw ho
  | bvar _ | mvar _ | sort _ | const _ _ | lit _ => intro _ _ ho; simp only [OccF] at ho

/-- **The scope guard holds on a scoped term** (`Expr.wscopedBC`, read off the
ids). -/
theorem wscopedBC_of_WScoped {s : InLean.CState} {e : Expr} {d : Nat} (he : OkS s e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s e)) : InLean.Expr.wscopedBC d e = true := by
  unfold InLean.Expr.wscopedBC
  rw [Bool.or_eq_true]; right
  rw [Array.all_eq_true_iff_forall_mem]
  intro a ha
  obtain ⟨i, n, rfl, hi⟩ := occF_depth he hw ((mem_fvarIds (RangeOk_of_OkS he) a).1 ha)
  rw [fvDepth_fvId]; exact decide_eq_true hi

/-- A translation bounded at `k` comes from a term whose range is at most `k`. -/
theorem rangeS_le_of_lbb {s : InLean.CState} : ∀ {e : Expr} {k : Nat},
    (TrS s e).looseBVarsBounded k = true → rangeS e ≤ k := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simp only [TrS_bvar, ConLeche.Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [rangeS]; omega
  | app f x ihf ihx =>
    intro k h
    rw [TrS_app, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have := ihf h.1; have := ihx h.2; simp only [rangeS]; omega
  | lam _ t b _ iht ihb =>
    intro k h
    rw [TrS_lam, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have := iht h.1; have := ihb h.2; simp only [rangeS]; omega
  | forallE _ t b _ iht ihb =>
    intro k h
    rw [TrS_forallE, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have := iht h.1; have := ihb h.2; simp only [rangeS]; omega
  | letE _ t v b _ iht ihv ihb =>
    intro k h
    rw [TrS_letE, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true, Bool.and_eq_true] at h
    have := iht h.1.1; have := ihv h.1.2; have := ihb h.2; simp only [rangeS]; omega
  | mdata _ x ih => intro k h; exact ih h
  | proj _ _ x ih =>
    intro k h
    rw [TrS_proj, ConLeche.Expr.looseBVarsBounded] at h
    exact ih h
  | fvar _ | mvar _ | sort _ | const _ _ | lit _ => intro _ _; simp [rangeS]

/-- **The closedness guard holds on a closed translation** (`Expr.closedBV`,
read off the cached range). -/
theorem closedBV_of_lbb {s : InLean.CState} {e : Expr} (he : OkS s e = true)
    (hc : (TrS s e).looseBVarsBounded 0 = true) : InLean.Expr.closedBV e = true := by
  have h0 := rangeS_le_of_lbb hc
  unfold InLean.Expr.closedBV Expr.hasLooseBVars
  rw [Expr.looseBVarRange_eq (RangeOk_of_OkS he)]
  simp; omega

/-! ## The leaf guard's closure -/

/-- The ids an id's interned type mentions (`leafGuardM.closure`'s `more`). -/
@[expose] def succIds (tys : Array Expr) (id : FVarId) : List FVarId :=
  match fvParts? id with
  | some (_, n) =>
    match tys[n]? with
    | some ty => (EO.fvarIds ty).toList
    | none => []
  | none => []

/-- The ids reachable from those `P` holds of, through the interned types. -/
inductive RReach (tys : Array Expr) (P : FVarId → Prop) : FVarId → Prop where
  | base {x} : P x → RReach tys P x
  | step {x y} : RReach tys P y → x ∈ succIds tys y → RReach tys P x

theorem RReach.mono {tys : Array Expr} {P Q : FVarId → Prop} (h : ∀ x, P x → Q x) {x : FVarId}
    (hx : RReach tys P x) : RReach tys Q x := by
  induction hx with
  | base hp => exact .base (h _ hp)
  | step _ hs ih => exact .step ih hs

theorem RReach.cons_of_succ {tys : Array Expr} {id : FVarId} {todo more : List FVarId}
    {x : FVarId} (hmore : ∀ y ∈ more, y ∈ succIds tys id)
    (h : RReach tys (· ∈ more ++ todo) x) : RReach tys (· ∈ id :: todo) x := by
  induction h with
  | base hp =>
    rcases List.mem_append.1 hp with hp | hp
    · exact .step (.base List.mem_cons_self) (hmore _ hp)
    · exact .base (List.mem_cons_of_mem _ hp)
  | step _ hs ih => exact .step ih hs

/-- A set of numbers below `N` has at most `N` elements. -/
theorem hashSetNat_size_le {S : Std.HashSet Nat} {N : Nat}
    (h : ∀ m, S.contains m = true → m < N) : S.size ≤ N := by
  rw [← Std.HashSet.length_toList]
  have hnd : S.toList.Nodup :=
    Std.HashSet.distinct_toList.imp fun {a b} hab he => by subst he; simp at hab
  have := hnd.length_le_of_subset (l₂ := List.range N) fun x hx => by
    rw [List.mem_range]
    apply h x
    rw [← Std.HashSet.contains_toList]
    exact List.contains_iff_mem.2 hx
  simpa using this

/-- **The closure's invariant**: an expanded number's successors are seen or
pending, a seen id with an interned type has its number expanded, the
expanded numbers index the table, and the fuel covers the numbers not yet
expanded. -/
structure ClosureInv (tys : Array Expr) (fuel : Nat) (todo : List FVarId)
    (seen : Std.HashSet FVarId) (done : Std.HashSet Nat) : Prop where
  succ : ∀ n ty, done.contains n = true → tys[n]? = some ty → ∀ y ∈ (EO.fvarIds ty).toList,
    seen.contains y = true ∨ y ∈ todo
  exp : ∀ x d n ty, seen.contains x = true → fvParts? x = some (d, n) → tys[n]? = some ty →
    done.contains n = true
  lt : ∀ n, done.contains n = true → n < tys.size
  fuel : tys.size ≤ done.size + fuel

/-- What the closure answers, at its start's worklist and seen set. -/
@[expose] def ClosureOut (tys : Array Expr) (todo : List FVarId) (seen r : Std.HashSet FVarId) :
    Prop :=
  (∀ x, seen.contains x = true → r.contains x = true) ∧ (∀ x ∈ todo, r.contains x = true) ∧
  (∀ x, r.contains x = true → ∀ y ∈ succIds tys x, r.contains y = true) ∧
  (∀ x, r.contains x = true → seen.contains x = true ∨ RReach tys (· ∈ todo) x)

theorem contains_insert_self {seen : Std.HashSet FVarId} {id : FVarId} :
    (seen.insert id).contains id = true := by
  rw [Std.HashSet.contains_insert, beq_self_eq_true, Bool.true_or]

theorem contains_insert_of {seen : Std.HashSet FVarId} {id x : FVarId}
    (h : seen.contains x = true) : (seen.insert id).contains x = true := by
  rw [Std.HashSet.contains_insert, h, Bool.or_true]

/-- An id taken off the worklist into the seen set, its successors pushed
(`more`, a sublist of what it reaches in one step). -/
theorem ClosureOut.pop {tys : Array Expr} {id : FVarId} {todo more : List FVarId}
    {seen r : Std.HashSet FVarId} (hmore : ∀ y ∈ more, y ∈ succIds tys id)
    (h : ClosureOut tys (more ++ todo) (seen.insert id) r) : ClosureOut tys (id :: todo) seen r := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun x hx => h1 x (contains_insert_of hx), fun x hx => ?_, h3, fun x hx => ?_⟩
  · rcases List.mem_cons.1 hx with h | h
    · subst h; exact h1 _ contains_insert_self
    · exact h2 x (List.mem_append_right _ h)
  · rcases h4 x hx with h | h
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · subst h; exact .inr (.base List.mem_cons_self)
      · exact .inl h
    · exact .inr (h.cons_of_succ hmore)

/-- An id taken off the worklist whose number is expanded already, or that
has no interned type: the invariant at the rest. -/
theorem ClosureInv.skip {tys : Array Expr} {fuel : Nat} {id : FVarId} {todo : List FVarId}
    {seen : Std.HashSet FVarId} {done : Std.HashSet Nat} (h : ClosureInv tys fuel (id :: todo) seen done)
    (hid : ∀ d n ty, fvParts? id = some (d, n) → tys[n]? = some ty → done.contains n = true) :
    ClosureInv tys fuel todo (seen.insert id) done where
  succ n ty hn hty y hy := by
    rcases h.succ n ty hn hty y hy with h | h
    · exact .inl (contains_insert_of h)
    · rcases List.mem_cons.1 h with h | h
      · subst h; exact .inl contains_insert_self
      · exact .inr h
  exp x d n ty hx hp hty := by
    rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with hx | hx
    · subst hx; exact hid d n ty hp hty
    · exact h.exp x d n ty hx hp hty
  lt := h.lt
  fuel := h.fuel

/-- **The closure, from its invariant, is the reachable set** (with what was
seen). -/
theorem closure_spec (tys : Array Expr) (fuel : Nat) (todo : List FVarId)
    (seen : Std.HashSet FVarId) (done : Std.HashSet Nat) (hinv : ClosureInv tys fuel todo seen done) :
    ClosureOut tys todo seen (leafGuardM.closure tys fuel todo seen done) := by
  induction fuel, todo, seen, done using leafGuardM.closure.induct tys with
  | case1 fuel seen done =>
    rw [leafGuardM.closure.eq_1]
    refine ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil, fun x hx y hy => ?_,
      fun _ h => .inl h⟩
    unfold succIds at hy
    split at hy
    · rename_i d n hp
      split at hy
      · rename_i ty hty
        rcases hinv.succ n ty (hinv.exp x d n ty hx hp hty) hty y hy with h | h
        · exact h
        · exact absurd h List.not_mem_nil
      · exact absurd hy List.not_mem_nil
    · exact absurd hy List.not_mem_nil
  | case2 fuel seen done id todo _ fst n hp rest hty hdone ih =>
    rw [leafGuardM.closure.eq_2]
    simp only [hp, hty, hdone, ↓reduceIte]
    refine ClosureOut.pop (more := []) (fun _ h => absurd h List.not_mem_nil) ?_
    exact ih (hinv.skip fun d n' ty hp' hty' => by
      rw [hp] at hp'; cases hp'; exact hdone)
  | case3 seen done id todo fst n hp rest hty hdone =>
    exfalso
    have hlt : n < tys.size := (Array.getElem?_eq_some_iff.1 hty).1
    have hle := hashSetNat_size_le (S := done.insert n) (N := tys.size) fun m hm => by
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | hm
      · exact hlt
      · exact hinv.lt m hm
    have hnm : n ∉ done := by rw [Std.HashSet.mem_iff_contains]; exact hdone
    simp only [Std.HashSet.size_insert, hnm, ↓reduceIte] at hle
    have := hinv.fuel
    omega
  | case4 seen done id todo _ fst n hp rest hty hdone k ih =>
    rw [leafGuardM.closure.eq_2]
    simp only [hp, hty, hdone, Bool.false_eq_true, ↓reduceIte]
    have hsucc : succIds tys id = (EO.fvarIds rest).toList := by
      simp only [succIds, hp, hty]
    refine ClosureOut.pop (fun y hy => by rw [hsucc]; exact hy) (ih ?_)
    refine { succ := ?_, exp := ?_, lt := ?_, fuel := ?_ }
    · intro n' ty hn' hty' y hy
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hn'
      rcases hn' with rfl | hn'
      · rw [hty] at hty'; cases hty'; exact .inr (List.mem_append_left _ hy)
      · rcases hinv.succ n' ty hn' hty' y hy with h | h
        · exact .inl (contains_insert_of h)
        · rcases List.mem_cons.1 h with h | h
          · subst h; exact .inl contains_insert_self
          · exact .inr (List.mem_append_right _ h)
    · intro x d n' ty hx hp' hty'
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with rfl | hx
      · rw [hp] at hp'; cases hp'; exact .inl rfl
      · exact .inr (hinv.exp x d n' ty hx hp' hty')
    · intro m hm
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | hm
      · exact (Array.getElem?_eq_some_iff.1 hty).1
      · exact hinv.lt m hm
    · have hnm : n ∉ done := by rw [Std.HashSet.mem_iff_contains]; exact hdone
      simp only [Std.HashSet.size_insert, hnm, ↓reduceIte]
      have := hinv.fuel
      omega
  | case5 fuel seen done id todo _ fst n hp hty ih =>
    rw [leafGuardM.closure.eq_2]
    simp only [hp, hty]
    refine ClosureOut.pop (more := []) (fun _ h => absurd h List.not_mem_nil) ?_
    exact ih (hinv.skip fun d n' ty hp' hty' => by
      rw [hp] at hp'; cases hp'; rw [hty] at hty'; cases hty')
  | case6 fuel seen done id todo _ hp ih =>
    rw [leafGuardM.closure.eq_2]
    simp only [hp]
    refine ClosureOut.pop (more := []) (fun _ h => absurd h List.not_mem_nil) ?_
    exact ih (hinv.skip fun d n' ty hp' _ => by rw [hp] at hp'; cases hp')

/-- From nothing seen or expanded, at the fuel `tys.size`, the closure holds
exactly the reachable ids. -/
theorem closure_contains_iff {tys : Array Expr} {init : List FVarId} (x : FVarId) :
    (leafGuardM.closure tys tys.size init ∅ ∅).contains x = true ↔ RReach tys (· ∈ init) x := by
  have hinv : ClosureInv tys tys.size init ∅ ∅ :=
    { succ := fun n _ h => by simp at h
      exp := fun x _ _ _ h => by simp at h
      lt := fun n h => by simp at h
      fuel := by simp }
  obtain ⟨-, h2, h3, h4⟩ := closure_spec tys tys.size init ∅ ∅ hinv
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h4 x h with h | h
    · simp at h
    · exact h
  · induction h with
    | base hp => exact h2 _ hp
    | step _ hs ih => exact h3 _ ih _ hs

/-! ## The leaves of a translation -/

theorem RReach.none {tys : Array Expr} {P : FVarId → Prop} (h : ∀ x, ¬ P x) {y : FVarId} :
    ¬ RReach tys P y := by
  intro hy
  induction hy with
  | base hp => exact h _ hp
  | step _ _ ih => exact ih

theorem RReach.or_iff {tys : Array Expr} {P Q : FVarId → Prop} {y : FVarId} :
    RReach tys (fun x => P x ∨ Q x) y ↔ RReach tys P y ∨ RReach tys Q y := by
  constructor
  · intro h
    induction h with
    | base hp =>
      rcases hp with hp | hp
      · exact .inl (.base hp)
      · exact .inr (.base hp)
    | step _ hs ih =>
      rcases ih with ih | ih
      · exact .inl (.step ih hs)
      · exact .inr (.step ih hs)
  · rintro (h | h)
    · exact h.mono fun _ h => .inl h
    · exact h.mono fun _ h => .inr h

theorem RReach.or3_iff {tys : Array Expr} {P Q R : FVarId → Prop} {y : FVarId} :
    RReach tys (fun x => P x ∨ Q x ∨ R x) y ↔ RReach tys P y ∨ RReach tys Q y ∨ RReach tys R y := by
  rw [RReach.or_iff (P := P), RReach.or_iff]

/-- From one id: itself, or what its successors reach. -/
theorem RReach.single_iff {tys : Array Expr} {x y : FVarId} :
    RReach tys (fun z => x = z) y ↔ x = y ∨ RReach tys (· ∈ succIds tys x) y := by
  constructor
  · intro h
    induction h with
    | base hp => exact .inl hp
    | step _ hs ih =>
      rcases ih with ih | ih
      · subst ih; exact .inr (.base hs)
      · exact .inr (.step ih hs)
  · rintro (h | h)
    · exact .base h
    · induction h with
      | base hp => exact .step (.base rfl) hp
      | step _ hs ih => exact .step ih hs

/-- An occurring id of a term with a reading has one. -/
theorem occF_trans {g : FVarId → Option ConLeche.Expr} {y : FVarId} :
    ∀ {e : Expr} {c : ConLeche.Expr}, toExpr g e = some c → OccF y e → ∃ c', g y = some c' := by
  intro e
  induction e with
  | fvar id => intro c h ho; simp only [OccF] at ho; subst ho; exact ⟨c, h⟩
  | app f a ihf iha =>
    intro c h ho
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, -⟩ := h
    rcases ho with ho | ho
    · exact ihf hf ho
    · exact iha ha ho
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    intro c h ho
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cb, hb, -⟩ := h
    rcases ho with ho | ho
    · exact iht ht ho
    · exact ihb hb ho
  | letE _ t v b _ iht ihv ihb =>
    intro c h ho
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, -⟩ := h
    rcases ho with ho | ho | ho
    · exact iht ht ho
    · exact ihv hv ho
    · exact ihb hb ho
  | mdata _ x ih => intro c h ho; exact ih h ho
  | proj _ _ x ih =>
    intro c h ho
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, -⟩ := h
    exact ih hx ho
  | bvar _ | mvar _ | sort _ | const _ _ | lit _ => intro _ _ ho; simp only [OccF] at ho

/-- The id translation at `s`. -/
abbrev fvT (s : InLean.CState) : FVarId → Option ConLeche.Expr := FVarTable.trans (tableOf s)

/-- The leaves of an id's translation are the translations of the ids it
reaches. -/
@[expose] def IdLeaves (s : InLean.CState) (x : FVarId) : Prop :=
  ∀ c, fvT s x = some c → ∀ p : Nat × ConLeche.Expr, p ∈ c.fvarLeaves ↔
    ∃ y, RReach s.fvTys (fun z => x = z) y ∧ fvT s y = some (.fvar p.1 p.2)

/-- **The leaves of a term's reading** are the translations of the ids its
free variables reach. -/
theorem term_leaves {s : InLean.CState} {g : FVarId → Option ConLeche.Expr} (hg : FvLe g (fvT s)) :
    ∀ {e : Expr} {c : ConLeche.Expr}, toExpr g e = some c → (∀ x, OccF x e → IdLeaves s x) →
    ∀ p : Nat × ConLeche.Expr, p ∈ c.fvarLeaves ↔
      ∃ y, RReach s.fvTys (fun z => OccF z e) y ∧ fvT s y = some (.fvar p.1 p.2) := by
  have hnone : ∀ {e : Expr} {c : ConLeche.Expr}, (∀ x, ¬ OccF x e) → c.fvarLeaves = [] →
      ∀ p : Nat × ConLeche.Expr, p ∈ c.fvarLeaves ↔
        ∃ y, RReach s.fvTys (fun z => OccF z e) y ∧ fvT s y = some (.fvar p.1 p.2) := by
    intro e c hn hl p
    rw [hl]
    simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro y hy; exact absurd hy (RReach.none hn)
  intro e
  induction e with
  | fvar id =>
    intro c h hid p
    exact hid id rfl c (hg _ _ h) p
  | app f a ihf iha =>
    intro c h hid p
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, rfl⟩ := h
    rw [ConLeche.Expr.fvarLeaves, List.mem_append, ihf hf (fun x hx => hid x (.inl hx)),
      iha ha (fun x hx => hid x (.inr hx))]
    simp only [OccF, RReach.or_iff]
    constructor
    · rintro (⟨y, hy, hy'⟩ | ⟨y, hy, hy'⟩)
      · exact ⟨y, .inl hy, hy'⟩
      · exact ⟨y, .inr hy, hy'⟩
    · rintro ⟨y, hy | hy, hy'⟩
      · exact .inl ⟨y, hy, hy'⟩
      · exact .inr ⟨y, hy, hy'⟩
  | lam _ f a _ ihf iha =>
    intro c h hid p
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, rfl⟩ := h
    rw [ConLeche.Expr.fvarLeaves, List.mem_append, ihf hf (fun x hx => hid x (.inl hx)),
      iha ha (fun x hx => hid x (.inr hx))]
    simp only [OccF, RReach.or_iff]
    constructor
    · rintro (⟨y, hy, hy'⟩ | ⟨y, hy, hy'⟩)
      · exact ⟨y, .inl hy, hy'⟩
      · exact ⟨y, .inr hy, hy'⟩
    · rintro ⟨y, hy | hy, hy'⟩
      · exact .inl ⟨y, hy, hy'⟩
      · exact .inr ⟨y, hy, hy'⟩
  | forallE _ f a _ ihf iha =>
    intro c h hid p
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, rfl⟩ := h
    rw [ConLeche.Expr.fvarLeaves, List.mem_append, ihf hf (fun x hx => hid x (.inl hx)),
      iha ha (fun x hx => hid x (.inr hx))]
    simp only [OccF, RReach.or_iff]
    constructor
    · rintro (⟨y, hy, hy'⟩ | ⟨y, hy, hy'⟩)
      · exact ⟨y, .inl hy, hy'⟩
      · exact ⟨y, .inr hy, hy'⟩
    · rintro ⟨y, hy | hy, hy'⟩
      · exact .inl ⟨y, hy, hy'⟩
      · exact .inr ⟨y, hy, hy'⟩
  | letE _ t v b _ iht ihv ihb =>
    intro c h hid p
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
    rw [ConLeche.Expr.fvarLeaves, List.mem_append, List.mem_append,
      iht ht (fun x hx => hid x (.inl hx)), ihv hv (fun x hx => hid x (.inr (.inl hx))),
      ihb hb (fun x hx => hid x (.inr (.inr hx)))]
    simp only [OccF, RReach.or3_iff]
    constructor
    · rintro ((⟨y, hy, hy'⟩ | ⟨y, hy, hy'⟩) | ⟨y, hy, hy'⟩)
      · exact ⟨y, .inl hy, hy'⟩
      · exact ⟨y, .inr (.inl hy), hy'⟩
      · exact ⟨y, .inr (.inr hy), hy'⟩
    · rintro ⟨y, hy | hy | hy, hy'⟩
      · exact .inl (.inl ⟨y, hy, hy'⟩)
      · exact .inl (.inr ⟨y, hy, hy'⟩)
      · exact .inr ⟨y, hy, hy'⟩
  | mdata _ x ih => intro c h hid p; exact ih h hid p
  | proj _ _ x ih =>
    intro c h hid p
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    rw [ConLeche.Expr.fvarLeaves]
    exact ih hx hid p
  | mvar _ => intro c h; simp [toExpr] at h
  | bvar _ =>
    intro c h _
    simp only [toExpr, Option.some.injEq] at h; subst h
    exact hnone (fun _ h => by simp only [OccF] at h) (by simp [ConLeche.Expr.fvarLeaves])
  | sort _ =>
    intro c h _
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h
    exact hnone (fun _ h => by simp only [OccF] at h) (by simp [ConLeche.Expr.fvarLeaves])
  | const _ _ =>
    intro c h _
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h
    exact hnone (fun _ h => by simp only [OccF] at h) (by simp [ConLeche.Expr.fvarLeaves])
  | lit _ =>
    intro c h _
    simp only [toExpr, Option.some.injEq] at h; subst h
    exact hnone (fun _ h => by simp only [OccF] at h) (by simp [ConLeche.Expr.fvarLeaves])

/-- **Every id's leaves are the translations of what it reaches.** -/
theorem idLeaves {s : InLean.CState} (hfv : FVTableOK s) : ∀ x, IdLeaves s x := by
  have key : ∀ n d, IdLeaves s (fvId d n) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro d c hc p
      have htn : (tableOf s).transNum d n = some c := by
        simpa [fvT, FVarTable.trans, fvParts_fvId] using hc
      obtain ⟨-, ty, cty, hty', hcty, rfl⟩ := FVarTable.transNum_some htn
      have hids : ∀ x, OccF x ty → IdLeaves s x := by
        intro x hx
        obtain ⟨c', hc'⟩ := occF_trans hcty hx
        obtain ⟨d', m, rfl, hm, -⟩ := FVarTable.inner_some hc'
        exact ih m hm d'
      have hT := term_leaves (FVarTable.inner_le_trans _ n) hcty hids
      have hsucc : succIds s.fvTys (fvId d n) = (EO.fvarIds ty).toList := by
        simp only [succIds, fvParts_fvId]
        simp only [tableOf] at hty'
        rw [hty']
      have hr : Expr.RangeOk ty := hfv.range n ty (by simpa [tableOf] using hty')
      rw [ConLeche.Expr.fvarLeaves, List.mem_cons, hT p]
      simp only [RReach.single_iff, hsucc]
      constructor
      · rintro (h | ⟨y, hy, hy'⟩)
        · exact ⟨fvId d n, .inl rfl, by rw [hc, h]⟩
        · exact ⟨y, .inr (hy.mono fun z hz => by
            rw [Array.mem_toList_iff, mem_fvarIds hr]; exact hz), hy'⟩
      · rintro ⟨y, rfl | hy, hy'⟩
        · rw [hc] at hy'; simp only [Option.some.injEq, ConLeche.Expr.fvar.injEq] at hy'
          exact .inl (by rw [hy'.1, hy'.2])
        · exact .inr ⟨y, hy.mono fun z hz => by
            rw [Array.mem_toList_iff, mem_fvarIds hr] at hz; exact hz, hy'⟩
  intro x c hc
  obtain ⟨d, n, rfl, -⟩ := FVarTable.trans_some hc
  exact key n d c hc

/-! ## The leaf guard -/

/-- **The leaf guard's answer** is the pure one at the translations. -/
theorem leafGuard_value {s : InLean.CState} (hfv : FVTableOK s)
    {fab base : Expr} (hf : OkS s fab = true) (hb : OkS s base = true) :
    (if (!fab.hasFVar) = true then true else
      (EO.fvarIds fab).all
        (leafGuardM.closure s.fvTys s.fvTys.size (EO.fvarIds base).toList ∅ ∅).contains)
      = ConLeche.Cached.leafGuardP (TrS s fab) (TrS s base) := by
  have hid := idLeaves hfv
  have htf : toExpr (fvT s) fab = some (TrS s fab) := TransS_of_ok hf
  have htb : toExpr (fvT s) base = some (TrS s base) := TransS_of_ok hb
  have hLf := term_leaves (s := s) (fun _ _ h => h) htf (fun x _ => hid x)
  have hLb := term_leaves (s := s) (fun _ _ h => h) htb (fun x _ => hid x)
  have hrf := RangeOk_of_OkS hf
  have hrb := RangeOk_of_OkS hb
  have hcl : ∀ x, (leafGuardM.closure s.fvTys s.fvTys.size (EO.fvarIds base).toList ∅ ∅).contains x
      = true ↔ RReach s.fvTys (fun z => OccF z base) x := by
    intro x
    rw [closure_contains_iff]
    constructor
    · exact fun h => h.mono fun z hz => by rw [Array.mem_toList_iff, mem_fvarIds hrb] at hz; exact hz
    · exact fun h => h.mono fun z hz => by rw [Array.mem_toList_iff, mem_fvarIds hrb]; exact hz
  unfold ConLeche.Cached.leafGuardP
  split
  · rename_i hn
    rw [Bool.not_eq_true', Expr.hasFVar_eq hrf] at hn
    symm
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨y, hy, -⟩ := (hLf p).1 hp
    exact absurd hy (RReach.none fun x => not_occF_of_fvarS hn)
  · apply Bool.eq_iff_iff.2
    rw [Array.all_eq_true_iff_forall_mem, List.all_eq_true]
    constructor
    · intro H p hp
      rw [List.contains_iff_mem]
      obtain ⟨y, hy, hy'⟩ := (hLf p).1 hp
      have hreach : ∀ y, RReach s.fvTys (fun z => OccF z fab) y →
          RReach s.fvTys (fun z => OccF z base) y := by
        intro y hy
        induction hy with
        | base h => exact (hcl _).1 (H _ ((mem_fvarIds hrf _).2 h))
        | step _ hs ih => exact .step ih hs
      exact (hLb p).2 ⟨y, hreach y hy, hy'⟩
    · intro H x hx
      have hox := (mem_fvarIds hrf x).1 hx
      obtain ⟨c', hc'⟩ := occF_trans htf hox
      obtain ⟨d, n, rfl, hn⟩ := FVarTable.trans_some hc'
      obtain ⟨-, -, cty, -, -, rfl⟩ := FVarTable.transNum_some hn
      have hp : (d, cty) ∈ (TrS s fab).fvarLeaves := (hLf (d, cty)).2 ⟨_, .base hox, hc'⟩
      have hp' := H _ hp
      rw [List.contains_iff_mem] at hp'
      obtain ⟨y, hy, hy'⟩ := (hLb _).1 hp'
      obtain ⟨d', n', rfl, hn'⟩ := FVarTable.trans_some hy'
      obtain ⟨rfl, rfl⟩ := hfv.transNum_inj (max n n' + 1) d n d' n' _ (by omega) (by omega) hn hn'
      exact (hcl _).2 hy

/-- `leafGuardM`'s spec, the form the ι step's rescues consume. -/
abbrev LeafGuardSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env) : Prop :=
  ∀ {s₀ : InLean.CState} {fab base : Expr}, CSOKI mode eager env s₀ → OkS s₀ fab = true →
    OkS s₀ base = true →
    ⦃fun s => s = s₀⦄ InLean.leafGuardM fab base
    ⦃fun v s' => s' = s₀ ∧ v = ConLeche.Cached.leafGuardP (TrS s₀ fab) (TrS s₀ base); ⊤⦄

/-- **The leaf guard simulates the pure one.** -/
theorem leafGuardSpecI {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env} :
    LeafGuardSpecI mode eager env := by
  intro s₀ fab base hs hf hb
  refine tripleI_iff_run.2 fun v s' hr => ?_
  rw [← leafGuard_value hs.fv hf hb]
  unfold InLean.leafGuardM at hr
  split at hr
  · rename_i h
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨rfl, by simp only [h, ↓reduceIte]⟩
  · rename_i h
    obtain ⟨g, s₁, hg, hr⟩ := bind_run hr
    simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨rfl, by simp only [h, Bool.false_eq_true, ↓reduceIte]⟩

end InLeanProof
