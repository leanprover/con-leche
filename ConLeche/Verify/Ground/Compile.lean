module

public import ConLeche.Cached.Ground4
public import ConLeche.Verify.Ground.Erased

public section

/-!
# The ground engine's compiler, correct up to erasure (task #423 soundness, layer (a))

The ground engine compiles every term it evaluates into a code array
(`g4Comp`, `ConLeche/Cached/Ground4.lean`).  This file reads the code back:
`Den P o s` says that the node at offset `o` of the program `P` denotes the
erased term `s` (`ConLeche/Verify/Ground/Erased.lean`): binder domains, sorts,
Π-types, erased arguments and neutral constants read back as `bot`, a shared
closed term as the term it wraps.  The compiler's
correctness is `g4Comp_den`: the node it returns denotes a term that
approximates (`Approx`) the term it compiled, and the program it returns
extends the one it was given (`Ext`), so every node already compiled keeps its
denotation.

The program's two memos are part of the invariant (`Inv`): a closed argument
term's node (`closedNode`) denotes an approximation of that term, and a
constant's table entry (`kMap`) one of that constant.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-- The term a table entry's information denotes: the constant, or `bot`
for a neutral entry. -/
@[expose] def infoTerm : G4Info → Expr
  | .defn c _ us _ => .const c us
  | .ctor c us _ _ => .const c us
  | .recr c _ us .. => .const c us
  | .neutral => bot

mutual
/-- **The denotation of a code node** (`g4Comp`'s tags). -/
inductive Den (P : G4Prog) : Nat → Expr → Prop where
  | bvar {o i : Nat} : P.code[o]? = some 0 → P.code[o + 1]? = some i → Den P o (.bvar i)
  | spine {o h n : Nat} {sh : Expr} {ss : List Expr} :
      P.code[o]? = some 1 → P.code[o + 1]? = some h → P.code[o + 2]? = some n →
      h < o → Den P h sh → DenArgs P o (o + 3) n ss → Den P o (Expr.mkAppN sh ss)
  /-- a λ: `[2, body, tn, inner]`, `tn` the telescope's length from here and
  `inner` its innermost body -/
  | lam {o b tn inner : Nat} {sb : Expr} :
      P.code[o]? = some 2 → P.code[o + 1]? = some b → P.code[o + 2]? = some tn →
      P.code[o + 3]? = some inner → b < o → Den P b sb →
      ((P.code[b]? = some 2 ∧ P.code[b + 2]? = some (tn - 1) ∧ P.code[b + 3]? = some inner ∧
          tn ≥ 2) ∨
        (P.code[b]? ≠ some 2 ∧ tn = 1 ∧ inner = b)) →
      Den P o (.lam bot sb)
  | letE {o v b : Nat} {sv sb : Expr} :
      P.code[o]? = some 3 → P.code[o + 1]? = some v → P.code[o + 2]? = some b →
      v < o → b < o → Den P v sv → Den P b sb → Den P o (.letE bot sv sb)
  | const {o k : Nat} {info : G4Info} :
      P.code[o]? = some 4 → P.code[o + 1]? = some k → P.kInfo[k]? = some info →
      Den P o (infoTerm info)
  | natLit {o n : Nat} : P.code[o]? = some 5 → P.code[o + 1]? = some n →
      Den P o (.lit (.natVal n))
  | strLit {o si : Nat} {s : String} : P.code[o]? = some 6 → P.code[o + 1]? = some si →
      P.strs[si]? = some s → Den P o (.lit (.strVal s))
  | proj {o q e : Nat} {pj : G4Proj} {se : Expr} :
      P.code[o]? = some 7 → P.code[o + 1]? = some (q + 1) → P.projs[q]? = some pj →
      P.code[o + 2]? = some e → e < o → Den P e se → Den P o (.proj pj.sn pj.idx se)
  | neutral {o : Nat} : P.code[o]? = some 8 → Den P o bot
  | shared {o sl a : Nat} {s : Expr} : P.code[o]? = some 9 → P.code[o + 1]? = some sl →
      P.code[o + 2]? = some a → a < o → Den P a s →
      (∃ a' : Expr, P.closedNode[a']? = some o) → Den P o s

/-- The `n` argument nodes of a spine node `o`, read from offset `p`. -/
inductive DenArgs (P : G4Prog) : Nat → Nat → Nat → List Expr → Prop where
  | nil {o p : Nat} : DenArgs P o p 0 []
  | cons {o p n a : Nat} {s : Expr} {ss : List Expr} :
      P.code[p]? = some a → a < o → Den P a s → DenArgs P o (p + 1) n ss →
      DenArgs P o p (n + 1) (s :: ss)
end

/-- **Program extension**: what a node's denotation reads only grows. -/
structure Ext (P P' : G4Prog) : Prop where
  code : ∀ i, i < P.code.size → P'.code[i]? = P.code[i]?
  codeSize : P.code.size ≤ P'.code.size
  kInfo : ∀ i, i < P.kInfo.size → P'.kInfo[i]? = P.kInfo[i]?
  kInfoSize : P.kInfo.size ≤ P'.kInfo.size
  projs : ∀ i, i < P.projs.size → P'.projs[i]? = P.projs[i]?
  strs : ∀ i, i < P.strs.size → P'.strs[i]? = P.strs[i]?
  closedNode : ∀ (a : Expr) (o : Nat), P.closedNode[a]? = some o → P'.closedNode[a]? = some o
  kSlot : ∀ i, i < P.kSlot.size → P'.kSlot[i]? = P.kSlot[i]?

theorem Ext.refl (P : G4Prog) : Ext P P :=
  ⟨fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, fun _ _ => rfl⟩

theorem Ext.trans {P₁ P₂ P₃ : G4Prog} (h₁ : Ext P₁ P₂) (h₂ : Ext P₂ P₃) : Ext P₁ P₃ where
  code i hi := (h₂.code i (Nat.lt_of_lt_of_le hi h₁.codeSize)).trans (h₁.code i hi)
  codeSize := Nat.le_trans h₁.codeSize h₂.codeSize
  kInfo i hi := (h₂.kInfo i (Nat.lt_of_lt_of_le hi h₁.kInfoSize)).trans (h₁.kInfo i hi)
  kInfoSize := Nat.le_trans h₁.kInfoSize h₂.kInfoSize
  projs i hi := by
    have h := h₁.projs i hi
    have hs : i < P₂.projs.size := by
      rcases Nat.lt_or_ge i P₂.projs.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h
        exact absurd h.symm (by simp [Array.getElem?_eq_getElem hi])
    exact (h₂.projs i hs).trans h
  strs i hi := by
    have h := h₁.strs i hi
    have hs : i < P₂.strs.size := by
      rcases Nat.lt_or_ge i P₂.strs.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h
        exact absurd h.symm (by simp [Array.getElem?_eq_getElem hi])
    exact (h₂.strs i hs).trans h
  closedNode a o h := h₂.closedNode a o (h₁.closedNode a o h)
  kSlot i hi := by
    have h := h₁.kSlot i hi
    have hs : i < P₂.kSlot.size := by
      rcases Nat.lt_or_ge i P₂.kSlot.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at h
        exact absurd h.symm (by simp [Array.getElem?_eq_getElem hi])
    exact (h₂.kSlot i hs).trans h

theorem Ext.code_some {P P' : G4Prog} (h : Ext P P') {i x : Nat} (hx : P.code[i]? = some x) :
    P'.code[i]? = some x := by
  have hi : i < P.code.size := by
    rcases Nat.lt_or_ge i P.code.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.code i hi, hx]

theorem Ext.kInfo_some {P P' : G4Prog} (h : Ext P P') {i : Nat} {x : G4Info}
    (hx : P.kInfo[i]? = some x) : P'.kInfo[i]? = some x := by
  have hi : i < P.kInfo.size := by
    rcases Nat.lt_or_ge i P.kInfo.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.kInfo i hi, hx]

theorem Ext.projs_some {P P' : G4Prog} (h : Ext P P') {i : Nat} {x : G4Proj}
    (hx : P.projs[i]? = some x) : P'.projs[i]? = some x := by
  have hi : i < P.projs.size := by
    rcases Nat.lt_or_ge i P.projs.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.projs i hi, hx]

theorem Ext.strs_some {P P' : G4Prog} (h : Ext P P') {i : Nat} {x : String}
    (hx : P.strs[i]? = some x) : P'.strs[i]? = some x := by
  have hi : i < P.strs.size := by
    rcases Nat.lt_or_ge i P.strs.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.strs i hi, hx]

/-- A node that denotes has a tag. -/
theorem Den.tag {P : G4Prog} {o : Nat} {s : Expr} : Den P o s → ∃ x, P.code[o]? = some x
  | .bvar h₀ _ | .spine h₀ .. | .lam h₀ .. | .letE h₀ .. | .const h₀ .. | .natLit h₀ _
  | .strLit h₀ .. | .proj h₀ .. | .neutral h₀ | .shared h₀ .. =>
    ⟨_, h₀⟩

mutual
/-- **A node keeps its denotation** in every extension of the program. -/
theorem Den.ext {P P' : G4Prog} (hx : Ext P P') {o : Nat} {s : Expr} : Den P o s → Den P' o s
  | .bvar h₀ h₁ => .bvar (hx.code_some h₀) (hx.code_some h₁)
  | .spine h₀ h₁ h₂ hlt hh ha =>
    .spine (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) hlt (Den.ext hx hh)
      (DenArgs.ext hx ha)
  | .lam h₀ h₁ h₂ h₃ hlt hb htel =>
    .lam (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) (hx.code_some h₃) hlt
      (Den.ext hx hb) (by
        rcases htel with ⟨t₀, t₁, t₂, t₃⟩ | ⟨t₀, t₁, t₂⟩
        · exact .inl ⟨hx.code_some t₀, hx.code_some t₁, hx.code_some t₂, t₃⟩
        · refine .inr ⟨?_, t₁, t₂⟩
          intro h'
          -- the body node exists (it denotes), so its tag is preserved
          have hb' : ∃ x, P.code[_]? = some x := Den.tag hb
          obtain ⟨x, hxb⟩ := hb'
          rw [hx.code_some hxb] at h'
          exact t₀ (hxb.trans h'))
  | .letE h₀ h₁ h₂ hv hb dv db =>
    .letE (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) hv hb (Den.ext hx dv) (Den.ext hx db)
  | .const h₀ h₁ h₂ => .const (hx.code_some h₀) (hx.code_some h₁) (hx.kInfo_some h₂)
  | .natLit h₀ h₁ => .natLit (hx.code_some h₀) (hx.code_some h₁)
  | .strLit h₀ h₁ h₂ => .strLit (hx.code_some h₀) (hx.code_some h₁) (hx.strs_some h₂)
  | .proj h₀ h₁ h₂ h₃ hlt he =>
    .proj (hx.code_some h₀) (hx.code_some h₁) (hx.projs_some h₂) (hx.code_some h₃) hlt (Den.ext hx he)
  | .neutral h₀ => .neutral (hx.code_some h₀)
  | .shared h₀ h₁ h₂ hlt ha ⟨a', hr⟩ => .shared (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) hlt
      (Den.ext hx ha) ⟨a', hx.closedNode a' _ hr⟩

theorem DenArgs.ext {P P' : G4Prog} (hx : Ext P P') {o p n : Nat} {ss : List Expr} :
    DenArgs P o p n ss → DenArgs P' o p n ss
  | .nil => .nil
  | .cons h₀ hlt ha hr => .cons (hx.code_some h₀) hlt (Den.ext hx ha) (DenArgs.ext hx hr)

end

mutual
/-- **A node denotes one term.** -/
theorem Den.unique {P : G4Prog} : ∀ {o : Nat} {s s' : Expr}, Den P o s → Den P o s' → s = s'
  | _, _, _, .bvar h₀ h₁, h' => by
    cases h' with
    | bvar _ h₁' => rw [h₁] at h₁'; cases h₁'; rfl
    | _ => simp_all
  | _, _, _, .spine h₀ h₁ h₂ _ hh ha, h' => by
    cases h' with
    | spine _ h₁' h₂' _ hh' ha' =>
      rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'
      rw [Den.unique hh hh', DenArgs.unique ha ha']
    | _ => simp_all
  | _, _, _, .lam h₀ h₁ _ _ _ hb _, h' => by
    cases h' with
    | lam _ h₁' _ _ _ hb' _ => rw [h₁] at h₁'; cases h₁'; rw [Den.unique hb hb']
    | _ => simp_all
  | _, _, _, .letE h₀ h₁ h₂ _ _ dv db, h' => by
    cases h' with
    | letE _ h₁' h₂' _ _ dv' db' =>
      rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'
      rw [Den.unique dv dv', Den.unique db db']
    | _ => simp_all
  | _, _, _, .const h₀ h₁ h₂, h' => by
    cases h' with
    | const _ h₁' h₂' => rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rfl
    | _ => simp_all
  | _, _, _, .natLit h₀ h₁, h' => by
    cases h' with
    | natLit _ h₁' => rw [h₁] at h₁'; cases h₁'; rfl
    | _ => simp_all
  | _, _, _, .strLit h₀ h₁ h₂, h' => by
    cases h' with
    | strLit _ h₁' h₂' => rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rfl
    | _ => simp_all
  | _, _, _, .proj h₀ h₁ h₂ h₃ _ he, h' => by
    cases h' with
    | proj _ h₁' h₂' h₃' _ he' =>
      rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rw [h₃] at h₃'; cases h₃'
      rw [Den.unique he he']
    | _ => simp_all
  | _, _, _, .neutral h₀, h' => by
    cases h' with
    | neutral _ => rfl
    | _ => simp_all
  | _, _, _, .shared h₀ h₁ h₂ _ ha _, h' => by
    cases h' with
    | shared _ _ h₂' _ ha' _ => rw [h₂] at h₂'; cases h₂'; exact Den.unique ha ha'
    | _ => simp_all

theorem DenArgs.unique {P : G4Prog} : ∀ {o p n : Nat} {ss ss' : List Expr},
    DenArgs P o p n ss → DenArgs P o p n ss' → ss = ss'
  | _, _, _, _, _, .nil, .nil => rfl
  | _, _, _, _, _, .cons h₀ _ ha hr, .cons h₀' _ ha' hr' => by
    rw [h₀] at h₀'; cases h₀'
    rw [Den.unique ha ha', DenArgs.unique hr hr']
end

/-! ## Reading appended code -/

theorem push_append (c : Array Nat) (a : Nat) : c.push a = c ++ #[a] := Array.push_eq_append

theorem rd0 (c ws : Array Nat) : (c ++ ws)[c.size]? = ws[0]? := by
  rw [Array.getElem?_append_right (by omega)]; simp

theorem rdR (c ws : Array Nat) (j : Nat) : (c ++ ws)[c.size + j]? = ws[j]? := by
  rw [Array.getElem?_append_right (by omega)]; simp

theorem rdL {c : Array Nat} (ws : Array Nat) {i : Nat} (h : i < c.size) : (c ++ ws)[i]? = c[i]? :=
  Array.getElem?_append_left h

theorem push_lt {α : Type} {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]? = a[i]? := by
  rw [Array.getElem?_push]; simp [Nat.ne_of_lt h]

theorem emit_code (P : G4Prog) (g : Array Nat → Array Nat) : (P.emit g).code = g P.code := rfl

/-- Appending code extends the program. -/
theorem Ext.emit (P : G4Prog) (ws : Array Nat) : Ext P (P.emit (· ++ ws)) where
  code i hi := rdL ws hi
  codeSize := by simp [G4Prog.emit]
  kInfo _ _ := rfl
  kInfoSize := Nat.le_refl _
  projs _ _ := rfl
  strs _ _ := rfl
  closedNode _ _ h := h
  kSlot _ _ := rfl

/-! ## The program invariant -/

/-- **A sharing slot's owner** and the term it denotes: the shared node
registered for a closed term, or a table entry (its constant). -/
@[expose] def Owns (P : G4Prog) (sl : Nat) (t : Expr) : Prop :=
  (∃ (a : Expr) (o : Nat), P.closedNode[a]? = some o ∧ P.code[o + 1]? = some sl ∧ Den P o t) ∨
  (∃ (k : Nat) (info : G4Info), P.kSlot[k]? = some sl ∧ P.kInfo[k]? = some info ∧ t = infoTerm info)

theorem Ext.kSlot_some {P P' : G4Prog} (h : Ext P P') {i x : Nat} (hx : P.kSlot[i]? = some x) :
    P'.kSlot[i]? = some x := by
  have hi : i < P.kSlot.size := by
    rcases Nat.lt_or_ge i P.kSlot.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.kSlot i hi, hx]

/-- Ownership survives extension. -/
theorem Owns.ext {P P' : G4Prog} (hx : Ext P P') {sl : Nat}
    {t : Expr} : Owns P sl t → Owns P' sl t
  | .inl ⟨a, o, h₁, h₂, h₃⟩ => .inl ⟨a, o, hx.closedNode a o h₁, hx.code_some h₂, h₃.ext hx⟩
  | .inr ⟨k, info, h₁, h₂, h₃⟩ => .inr ⟨k, info, hx.kSlot_some h₁, hx.kInfo_some h₂, h₃⟩

/-- **The program's memos denote what they key**, and every sharing slot
has one term. -/
structure Inv (P : G4Prog) : Prop where
  sizes : P.kTag.size = P.kInfo.size
  kSlotSize : P.kSlot.size = P.kInfo.size
  kMap : ∀ c us k, P.kMap[(c, us)]? = some k →
    ∃ info, P.kInfo[k]? = some info ∧ Approx (infoTerm info) (.const c us)
  closed : ∀ (a : Expr) (o : Nat), P.closedNode[a]? = some o →
    ∃ s sl, P.code[o + 1]? = some sl ∧ Den P o s ∧ Approx s a
  slots : ∃ σ : Nat → Expr, ∀ sl t, Owns P sl t → sl < P.nslots ∧ σ sl = t

/-- A slot denotes one term. -/
theorem Inv.owns_unique {P : G4Prog} (hI : Inv P) {sl : Nat} {t t' : Expr} (h : Owns P sl t)
    (h' : Owns P sl t') : t = t' := by
  obtain ⟨σ, hσ⟩ := hI.slots
  rw [← (hσ sl t h).2, (hσ sl t' h').2]

/-- One new owner at the next slot: a table entry or a shared node. -/
theorem Inv.slots_new {P Q : G4Prog} (hI : Inv P) (hn : Q.nslots = P.nslots + 1)
    (t₀ : Expr) (hnew : ∀ sl t, Owns Q sl t → Owns P sl t ∨ (sl = P.nslots ∧ t = t₀)) :
    ∃ σ : Nat → Expr, ∀ sl t, Owns Q sl t → sl < Q.nslots ∧ σ sl = t := by
  obtain ⟨σ, hσ⟩ := hI.slots
  refine ⟨fun x => if x = P.nslots then t₀ else σ x, ?_⟩
  intro sl t h
  rcases hnew sl t h with h' | ⟨rfl, rfl⟩
  · have := hσ sl t h'
    refine ⟨by omega, ?_⟩
    simp only [Nat.ne_of_lt this.1, ↓reduceIte, this.2]
  · exact ⟨by omega, by simp⟩

/-- A registered shared node of an extension is an owner before it. -/
theorem Owns.back_node {P Q : G4Prog} (hI : Inv P) (hx : Ext P Q) {a : Expr} {o sl : Nat} {t : Expr}
    (h₁ : P.closedNode[a]? = some o) (h₂ : Q.code[o + 1]? = some sl) (h₃ : Den Q o t) :
    Owns P sl t := by
  obtain ⟨s, sl', hsl', hd, -⟩ := hI.closed a o h₁
  rw [hx.code_some hsl'] at h₂
  obtain rfl : sl' = sl := Option.some.inj h₂
  obtain rfl := Den.unique (hd.ext hx) h₃
  exact .inl ⟨a, o, h₁, hsl', hd⟩

/-- An entry of an extension below the old table is an owner before it. -/
theorem Owns.back_entry {P Q : G4Prog} (hI : Inv P) (hx : Ext P Q) {k sl : Nat} {info : G4Info}
    {t : Expr} (h₁ : P.kSlot[k]? = some sl) (h₂ : Q.kInfo[k]? = some info) (h₃ : t = infoTerm info) :
    Owns P sl t := by
  have hk' : k < P.kInfo.size := by
    rw [← hI.kSlotSize]
    rcases Nat.lt_or_ge k P.kSlot.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h₁; cases h₁
  rw [hx.kInfo k hk'] at h₂
  exact .inr ⟨k, info, h₁, h₂, h₃⟩

/-- An owner of an extension that keeps the closed-term memo and the slot
column is an owner before it. -/
theorem Owns.back {P Q : G4Prog} (hI : Inv P) (hx : Ext P Q)
    (hc : ∀ (a : Expr) (o : Nat), Q.closedNode[a]? = some o → P.closedNode[a]? = some o)
    {sl : Nat} {t : Expr} (h : Owns Q sl t) (hk : ∀ k : Nat, Q.kSlot[k]? = some sl → P.kSlot[k]? = some sl) :
    Owns P sl t := by
  rcases h with ⟨a, o, h₁, h₂, h₃⟩ | ⟨k, info, h₁, h₂, h₃⟩
  · exact Owns.back_node hI hx (hc a o h₁) h₂ h₃
  · exact Owns.back_entry hI hx (hk k h₁) h₂ h₃

/-- An extension that adds no owner keeps the slots. -/
theorem Inv.slots_ext {P P' : G4Prog} (hI : Inv P) (hx : Ext P P')
    (hc : ∀ (a : Expr) (o : Nat), P'.closedNode[a]? = some o → P.closedNode[a]? = some o)
    (hsl : P'.kSlot = P.kSlot) (hn : P.nslots ≤ P'.nslots) :
    ∃ σ : Nat → Expr, ∀ sl t, Owns P' sl t → sl < P'.nslots ∧ σ sl = t := by
  obtain ⟨σ, hσ⟩ := hI.slots
  refine ⟨σ, ?_⟩
  intro sl t h
  have := hσ sl t (Owns.back hI hx hc h (fun k hk => by rw [hsl] at hk; exact hk))
  exact ⟨Nat.lt_of_lt_of_le this.1 hn, this.2⟩

/-- The invariant survives an extension that keeps the memos and the table
sizes' agreement. -/
theorem Inv.ext {P P' : G4Prog} (hI : Inv P) (hx : Ext P P') (hs : P'.kTag.size = P'.kInfo.size)
    (hks : P'.kSlot.size = P'.kInfo.size) (hk : P'.kMap = P.kMap) (hc : P'.closedNode = P.closedNode) (hsl : P'.kSlot = P.kSlot)
    (hn : P'.nslots = P.nslots) : Inv P' where
  sizes := hs
  kSlotSize := hks
  kMap c us k h := by
    rw [hk] at h
    obtain ⟨info, hi, ha⟩ := hI.kMap c us k h
    exact ⟨info, hx.kInfo_some hi, ha⟩
  closed a o h := by
    rw [hc] at h
    obtain ⟨s, sl, hsl', hd, ha⟩ := hI.closed a o h
    exact ⟨s, sl, hx.code_some hsl', hd.ext hx, ha⟩
  slots := hI.slots_ext hx (fun a o h => by rw [hc] at h; exact h) hsl (by rw [hn]; exact Nat.le_refl _)

theorem Inv.emit {P : G4Prog} (hI : Inv P) (ws : Array Nat) : Inv (P.emit (· ++ ws)) :=
  hI.ext (Ext.emit P ws) hI.sizes hI.kSlotSize rfl rfl rfl rfl

/-- A program with empty tables and memos (the engine's fresh program, with
its flags) satisfies the invariant. -/
theorem Inv.fresh (natOk strOk : Bool) (maxNat : Nat) :
    Inv ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog) where
  sizes := rfl
  kSlotSize := rfl
  kMap c us k h := by simp at h
  closed a o h := by simp at h
  slots := ⟨fun _ => bot, fun sl t h => by simp [Owns] at h⟩

/-! ## The constant table -/

/-- Two programs agree on everything a denotation and the invariant read. -/
structure KeyEq (P P' : G4Prog) : Prop where
  code : P'.code = P.code
  kTag : P'.kTag = P.kTag
  kInfo : P'.kInfo = P.kInfo
  kMap : P'.kMap = P.kMap
  closedNode : P'.closedNode = P.closedNode
  projs : P'.projs = P.projs
  strs : P'.strs = P.strs
  kSlot : P'.kSlot = P.kSlot
  nslots : P'.nslots = P.nslots

theorem KeyEq.refl (P : G4Prog) : KeyEq P P := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem KeyEq.trans {P₁ P₂ P₃ : G4Prog} (h₁ : KeyEq P₁ P₂) (h₂ : KeyEq P₂ P₃) : KeyEq P₁ P₃ :=
  ⟨h₂.code.trans h₁.code, h₂.kTag.trans h₁.kTag, h₂.kInfo.trans h₁.kInfo, h₂.kMap.trans h₁.kMap,
    h₂.closedNode.trans h₁.closedNode, h₂.projs.trans h₁.projs, h₂.strs.trans h₁.strs,
    h₂.kSlot.trans h₁.kSlot, h₂.nslots.trans h₁.nslots⟩

theorem KeyEq.ext {P P' : G4Prog} (h : KeyEq P P') : Ext P P' where
  code i _ := by rw [h.code]
  codeSize := by rw [h.code]; exact Nat.le_refl _
  kInfo i _ := by rw [h.kInfo]
  kInfoSize := by rw [h.kInfo]; exact Nat.le_refl _
  projs i _ := by rw [h.projs]
  strs i _ := by rw [h.strs]
  closedNode a o hh := by rw [h.closedNode]; exact hh
  kSlot i _ := by rw [h.kSlot]

theorem KeyEq.inv {P P' : G4Prog} (h : KeyEq P P') (hI : Inv P) : Inv P' :=
  hI.ext h.ext (by rw [h.kTag, h.kInfo]; exact hI.sizes) (by rw [h.kSlot, h.kInfo]; exact hI.kSlotSize)
    h.kMap h.closedNode h.kSlot h.nslots

theorem KeyEq.nid (P : G4Prog) (c : Name) : KeyEq P (P.nid c).2 := by
  unfold G4Prog.nid; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem KeyEq.foldl {α : Type} (g : G4Prog → α → G4Prog) (hg : ∀ P x, KeyEq P (g P x)) :
    ∀ (l : List α) (P : G4Prog), KeyEq P (l.foldl g P)
  | [], P => KeyEq.refl P
  | x :: l, P => (hg P x).trans (KeyEq.foldl g hg l (g P x))

/-- Prove the middle conjunct first, then use it. -/
theorem and_mid_first {A B C : Prop} (hb : B) (h : B → A ∧ C) : A ∧ B ∧ C :=
  ⟨(h hb).1, hb, (h hb).2⟩

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- **A new entry** denotes its constant (or is neutral). -/
theorem g4Entry_spec (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : Inv P) :
    Inv (g4Entry find? P c us kfab).2 ∧ Ext P (g4Entry find? P c us kfab).2 ∧
      (g4Entry find? P c us kfab).2.closedNode = P.closedNode ∧
      ∃ info, (g4Entry find? P c us kfab).2.kInfo[(g4Entry find? P c us kfab).1]? = some info ∧
        Approx (infoTerm info) (.const c us) := by
  unfold g4Entry
  split
  rename_i tag ar b c' d e' info P' hm
  have key : KeyEq P P' ∧ Approx (infoTerm info) (.const c us) := by
    revert hm
    split
    · split
      · intro hm; cases hm; exact ⟨KeyEq.refl P, .bot _⟩
      · intro hm; cases hm; exact ⟨KeyEq.refl P, Approx.refl _⟩
    · split
      rename_i ni P₁ hn
      intro hm; cases hm
      have := KeyEq.nid P c
      rw [hn] at this
      exact ⟨this, Approx.refl _⟩
    · split
      · intro hm; cases hm; exact ⟨KeyEq.refl P, .bot _⟩
      · intro hm; cases hm
        refine ⟨KeyEq.foldl _ (fun P rl => ?_) _ P, Approx.refl _⟩
        have := KeyEq.nid P rl.ctor
        dsimp only
        split <;> exact ⟨this.code, this.kTag, this.kInfo, this.kMap, this.closedNode, this.projs, this.strs,
          this.kSlot, this.nslots⟩
    · intro hm; cases hm; exact ⟨KeyEq.refl P, .bot _⟩
  obtain ⟨hk, hinfo⟩ := key
  have hs : P.kTag.size = P.kInfo.size := hI.sizes
  dsimp only
  have hks : P.kSlot.size = P.kInfo.size := hI.kSlotSize
  refine and_mid_first ?_ (fun hx => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, info, ?_, hinfo⟩)
  · exact (hk.ext).trans ⟨fun _ _ => rfl, Nat.le_refl _,
      fun i hi => show (P'.kInfo.push info)[i]? = P'.kInfo[i]? from push_lt hi,
      by simp, fun _ _ => rfl, fun _ _ => rfl, fun _ _ h => h,
      fun i hi => show (P'.kSlot.push P'.nslots)[i]? = P'.kSlot[i]? from push_lt hi⟩
  · simp only [Array.size_push, hk.kTag, hk.kInfo, hs]
  · simp only [Array.size_push, hk.kSlot, hk.kInfo, hks]
  · intro c₂ us₂ k₂ h₂
    rw [Std.HashMap.getElem?_insert] at h₂
    split at h₂
    · rename_i heq
      obtain rfl := (Option.some.inj h₂)
      have heq' : (c, us) = (c₂, us₂) := eq_of_beq heq
      cases heq'
      refine ⟨info, ?_, hinfo⟩
      show (P'.kInfo.push info)[P.kTag.size]? = some info
      rw [hk.kInfo, hs]; exact Array.getElem?_push_size
    · obtain ⟨i₂, hi₂, ha₂⟩ := hI.kMap c₂ us₂ k₂ (by rw [← hk.kMap]; exact h₂)
      refine ⟨i₂, ?_, ha₂⟩
      have hlt : k₂ < P.kInfo.size := by
        rcases Nat.lt_or_ge k₂ P.kInfo.size with h' | h'
        · exact h'
        · rw [Array.getElem?_eq_none h'] at hi₂; cases hi₂
      show (P'.kInfo.push info)[k₂]? = some i₂
      rw [hk.kInfo, push_lt hlt]; exact hi₂
  · intro a o h
    obtain ⟨sa, sl, hsl, hd, ha⟩ := hI.closed a o (by rw [← hk.closedNode]; exact h)
    exact ⟨sa, sl, hx.code_some hsl, hd.ext hx, ha⟩
  · refine Inv.slots_new (Q := _) hI (by show P'.nslots + 1 = _; rw [hk.nslots]) (infoTerm info) ?_
    intro sl t h
    rcases h with ⟨a, o, h₁, h₂, h₃⟩ | ⟨k, info', h₁, h₂, h₃⟩
    · exact .inl (Owns.back_node hI hx (by rw [← hk.closedNode]; exact h₁) h₂ h₃)
    · change (P'.kSlot.push P'.nslots)[k]? = some sl at h₁
      rw [Array.getElem?_push] at h₁
      split at h₁
      · rename_i hkk
        obtain rfl := Option.some.inj h₁
        change (P'.kInfo.push info)[k]? = some info' at h₂
        rw [hkk, hk.kSlot, hks, ← hk.kInfo, Array.getElem?_push_size] at h₂
        obtain rfl := Option.some.inj h₂
        exact .inr ⟨hk.nslots, h₃⟩
      · rw [hk.kSlot] at h₁
        exact .inl (Owns.back_entry hI hx h₁ h₂ h₃)
  · exact hk.closedNode
  · show (P'.kInfo.push info)[P.kTag.size]? = some info
    rw [hk.kInfo, hI.sizes]; exact Array.getElem?_push_size

/-- The entry spec, composed with a program step before it. -/
theorem g4Entry_after {P Pm : G4Prog} (c : Name) (us : List Level) (kfab : Nat) (hI : Inv Pm)
    (hx : Ext P Pm) (hcl : Pm.closedNode = P.closedNode) :
    Inv (g4Entry find? Pm c us kfab).2 ∧ Ext P (g4Entry find? Pm c us kfab).2 ∧
      (g4Entry find? Pm c us kfab).2.closedNode = P.closedNode ∧
      ∃ info, (g4Entry find? Pm c us kfab).2.kInfo[(g4Entry find? Pm c us kfab).1]? = some info ∧
        Approx (infoTerm info) (.const c us) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := g4Entry_spec find? Pm c us kfab hI
  exact ⟨h₁, hx.trans h₂, h₃.trans hcl, h₄⟩

/-- **Resolution** returns an entry that denotes the constant. -/
theorem g4ResolveF_spec : ∀ (fuel : Nat) (P : G4Prog) (c : Name) (us : List Level), Inv P →
    Inv (g4ResolveF find? findProj? fuel P c us).2 ∧ Ext P (g4ResolveF find? findProj? fuel P c us).2 ∧
      (g4ResolveF find? findProj? fuel P c us).2.closedNode = P.closedNode ∧
      ∃ info, (g4ResolveF find? findProj? fuel P c us).2.kInfo[
          (g4ResolveF find? findProj? fuel P c us).1]? = some info ∧
        Approx (infoTerm info) (.const c us) := by
  intro fuel
  induction fuel with
  | zero =>
    intro P c us hI
    unfold g4ResolveF
    split
    · rename_i k hk
      obtain ⟨info, hi, ha⟩ := hI.kMap c us k hk
      exact ⟨hI, Ext.refl P, rfl, info, hi, ha⟩
    · exact g4Entry_after find? c us 0 hI (Ext.refl P) rfl
  | succ f ih =>
    intro P c us hI
    unfold g4ResolveF
    split
    · rename_i k hk
      obtain ⟨info, hi, ha⟩ := hI.kMap c us k hk
      exact ⟨hI, Ext.refl P, rfl, info, hi, ha⟩
    · dsimp only
      split
      · split
        · split
          · rename_i f' _ _ _ rl hf _ _ _ cvj _ _
            obtain rfl : f = f' := Nat.succ.inj hf
            obtain ⟨h₁, h₂, h₃, -⟩ := ih P rl.ctor (gCmpLevels rl _ us cvj.levelParams) hI
            exact g4Entry_after find? c us _ h₁ h₂ h₃
          · exact g4Entry_after find? c us 0 hI (Ext.refl P) rfl
        · exact g4Entry_after find? c us 0 hI (Ext.refl P) rfl
      · exact g4Entry_after find? c us 0 hI (Ext.refl P) rfl

theorem g4Resolve_spec (P : G4Prog) (c : Name) (us : List Level) (hI : Inv P) :
    Inv (g4Resolve find? findProj? P c us).2 ∧ Ext P (g4Resolve find? findProj? P c us).2 ∧
      (g4Resolve find? findProj? P c us).2.closedNode = P.closedNode ∧
      ∃ info, (g4Resolve find? findProj? P c us).2.kInfo[(g4Resolve find? findProj? P c us).1]? =
          some info ∧ Approx (infoTerm info) (.const c us) :=
  g4ResolveF_spec find? findProj? 1 P c us hI

end

/-! ## The compiler -/

theorem emit_append1 (P : G4Prog) (a : Nat) : P.emit (fun c => c.push a) = P.emit (· ++ #[a]) := rfl

theorem emit_append2 (P : G4Prog) (a b : Nat) :
    P.emit (fun c => (c.push a).push b) = P.emit (· ++ #[a, b]) := by
  unfold G4Prog.emit; simp only [Array.push_eq_append, Array.append_assoc]; rfl

theorem emit_append3 (P : G4Prog) (a b d : Nat) :
    P.emit (fun c => ((c.push a).push b).push d) = P.emit (· ++ #[a, b, d]) := by
  unfold G4Prog.emit; simp only [Array.push_eq_append, Array.append_assoc]; rfl

theorem emit_append4 (P : G4Prog) (a b d e : Nat) :
    P.emit (fun c => (((c.push a).push b).push d).push e) = P.emit (· ++ #[a, b, d, e]) := by
  unfold G4Prog.emit; simp only [Array.push_eq_append, Array.append_assoc]; rfl

/-- What the compiler promises for one compiled term. -/
def CompOK (P : G4Prog) (e : Expr) (r : Nat × G4Prog) : Prop :=
  Inv r.2 ∧ Ext P r.2 ∧ ∃ s, Den r.2 r.1 s ∧ Approx s e

theorem CompOK.neutral {P : G4Prog} (hI : Inv P) (e : Expr) :
    CompOK P e (P.code.size, P.emit (fun c => c.push 8)) := by
  rw [emit_append1]
  refine ⟨hI.emit _, Ext.emit P _, bot, .neutral ?_, .bot e⟩
  show (P.code ++ #[8])[P.code.size]? = some 8
  rw [rd0]; rfl

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

theorem Den.lt_size {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) : o < P.code.size := by
  obtain ⟨x, hx⟩ := h.tag
  rcases Nat.lt_or_ge o P.code.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at hx; cases hx

theorem get!_of_some {a : Array Nat} {i x : Nat} (h : a[i]? = some x) : a[i]! = x := by
  have hi : i < a.size := by
    rcases Nat.lt_or_ge i a.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h; cases h
  rw [getElem!_pos a i hi]
  rw [Array.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

theorem some_of_lt {a : Array Nat} {i : Nat} (h : i < a.size) : a[i]? = some a[i]! := by
  rw [getElem!_pos a i h, Array.getElem?_eq_getElem h]

/-- A λ node's telescope fields. -/
theorem Den.lam_fields {P : G4Prog} {b : Nat} {s : Expr} (h : Den P b s) (h2 : P.code[b]? = some 2) :
    ∃ tn inner, P.code[b + 2]? = some tn ∧ P.code[b + 3]? = some inner ∧ tn ≥ 1 :=
  match h with
  | .lam _ _ h₂ h₃ _ _ htel => ⟨_, _, h₂, h₃, by
      rcases htel with ⟨-, -, -, h⟩ | ⟨-, h, -⟩ <;> omega⟩
  | .bvar h₀ _ | .spine h₀ .. | .letE h₀ .. | .const h₀ .. | .natLit h₀ _ | .strLit h₀ ..
  | .proj h₀ .. | .neutral h₀ | .shared h₀ .. => by
    rw [h₀] at h2; cases h2

theorem getD_append_left {l l' : List Expr} {i : Nat} (d : Expr) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len (l : List Expr) (a d : Expr) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_lt {l : List Expr} {i : Nat} (d : Expr) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem mkAppN_getApp' : ∀ (e : Expr), Expr.mkAppN e.getAppFn e.getAppArgs = e
  | .app f a => by
    simp only [Expr.getAppFn, Expr.getAppArgs]
    rw [show ∀ (g : Expr) (l : List Expr) (x : Expr),
        Expr.mkAppN g (l ++ [x]) = .app (Expr.mkAppN g l) x from by
      intro g l x
      induction l generalizing g with
      | nil => rfl
      | cons y ys ih => exact ih _]
    rw [mkAppN_getApp' f]
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _ | .proj .. => rfl

theorem getAppFn_not_app : ∀ (e : Expr), ∀ f a, e.getAppFn ≠ .app f a
  | .app g _ => getAppFn_not_app g
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _ | .proj .. =>
    fun _ _ h => by cases h

/-- The argument nodes of a fold: each denotes an approximation of its
argument and lies below the code's end. -/
def ArgsOK (P : G4Prog) (aos : Array Nat) (args : List Expr) : Prop :=
  aos.size = args.length ∧
    ∀ j (hj : j < aos.size), aos[j] < P.code.size ∧ ∃ s, Den P aos[j] s ∧ Approx s (args.getD j bot)

theorem ArgsOK.ext {P P' : G4Prog} (hx : Ext P P') {aos : Array Nat} {args : List Expr}
    (h : ArgsOK P aos args) : ArgsOK P' aos args := by
  refine ⟨h.1, fun j hj => ?_⟩
  obtain ⟨hlt, s, hd, ha⟩ := h.2 j hj
  exact ⟨Nat.lt_of_lt_of_le hlt hx.codeSize, s, hd.ext hx, ha⟩

theorem ArgsOK.push {P : G4Prog} {aos : Array Nat} {args : List Expr} (h : ArgsOK P aos args)
    {o : Nat} {a s : Expr} (ho : o < P.code.size) (hd : Den P o s) (ha : Approx s a) :
    ArgsOK P (aos.push o) (args ++ [a]) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  rw [Array.size_push] at hj
  rcases Nat.lt_or_ge j aos.size with hj' | hj'
  · obtain ⟨hlt, s', hd', ha'⟩ := h.2 j hj'
    rw [Array.getElem_push_lt hj']
    refine ⟨hlt, s', hd', ?_⟩
    rw [getD_append_left _ (by rw [← h.1]; exact hj')]
    exact ha'
  · obtain rfl : j = aos.size := by omega
    rw [Array.getElem_push_eq]
    refine ⟨ho, s, hd, ?_⟩
    rw [h.1, getD_append_len]
    exact ha

/-- The spine node's arguments, read back. -/
theorem ArgsOK.denArgs {P : G4Prog} {aos : Array Nat} {args : List Expr} (h : ArgsOK P aos args)
    {o : Nat} (hlt : ∀ j (hj : j < aos.size), aos[j] < o)
    (hcode : ∀ j (hj : j < aos.size), P.code[o + 3 + j]? = some aos[j]) :
    ∃ ss, DenArgs P o (o + 3) aos.size ss ∧ Approx.Args ss args := by
  obtain ⟨hlen, hall⟩ := h
  suffices hgen : ∀ k, k ≤ aos.size → ∃ ss, DenArgs P o (o + 3 + (aos.size - k)) k ss ∧
      Approx.Args ss (args.drop (aos.size - k)) by
    obtain ⟨ss, hd, ha⟩ := hgen aos.size (Nat.le_refl _)
    simp only [Nat.sub_self, Nat.add_zero, List.drop_zero] at hd ha
    exact ⟨ss, hd, ha⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], .nil, ?_⟩
    rw [Nat.sub_zero, hlen, List.drop_length]; exact .nil
  | succ k ih =>
    intro hk
    obtain ⟨ss, hd, ha⟩ := ih (by omega)
    have hj : aos.size - (k + 1) < aos.size := by omega
    obtain ⟨-, s, hds, has⟩ := hall _ hj
    refine ⟨s :: ss, .cons (hcode _ hj) (hlt _ hj) hds ?_, ?_⟩
    · rw [show o + 3 + (aos.size - (k + 1)) + 1 = o + 3 + (aos.size - k) by omega]; exact hd
    · rw [List.drop_eq_getElem_cons (by rw [← hlen]; exact hj)]
      rw [show aos.size - (k + 1) + 1 = aos.size - k by omega]
      refine .cons ?_ ha
      rw [getD_lt _ (by rw [← hlen]; exact hj)] at has
      exact has

end

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- A program step that the invariant and the denotations survive. -/
def Step (P P' : G4Prog) : Prop := Inv P' ∧ Ext P P'

theorem Step.trans {P₁ P₂ P₃ : G4Prog} (h₁ : Step P₁ P₂) (h₂ : Step P₂ P₃) : Step P₁ P₃ :=
  ⟨h₂.1, h₁.2.trans h₂.2⟩

theorem CompOK.step {P P' : G4Prog} {e : Expr} {r : Nat × G4Prog} (h : CompOK P' e r)
    (hs : Ext P P') : CompOK P e r :=
  ⟨h.1, hs.trans h.2.1, h.2.2⟩

theorem proj_emit_ok {P P₁ Q : G4Prog} {sn : Name} {i so : Nat} {e se : Expr} {pj : G4Proj}
    (hI₁ : Inv P₁) (hx₁ : Ext P P₁) (hde : Den P₁ so se) (hae : Approx se e)
    (hc : Q.code = P₁.code) (ht : Q.kTag = P₁.kTag) (hi : Q.kInfo = P₁.kInfo)
    (hm : Q.kMap = P₁.kMap) (hcl : Q.closedNode = P₁.closedNode) (hs : Q.strs = P₁.strs)
    (hks : Q.kSlot = P₁.kSlot) (hn : Q.nslots = P₁.nslots) (hp : Q.projs = P₁.projs.push pj) (hsn : pj.sn = sn) (hidx : pj.idx = i) (q : Nat)
    (hq : q = P₁.projs.size) :
    CompOK P (.proj sn i e) (Q.code.size, Q.emit (fun c => ((c.push 7).push (q + 1)).push so)) := by
  rw [emit_append3]
  have hx : Ext P₁ (Q.emit (· ++ #[7, q + 1, so])) := by
    refine ⟨fun j hj => ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, fun j hj => ?_,
      fun a o h => ?_, fun j hj => ?_⟩
    · show (Q.code ++ _)[j]? = _; rw [hc, rdL _ hj]
    · show P₁.code.size ≤ (Q.code ++ _).size; rw [hc]; simp
    · show Q.kInfo[j]? = _; rw [hi]
    · show P₁.kInfo.size ≤ Q.kInfo.size; rw [hi]; exact Nat.le_refl _
    · show Q.projs[j]? = _; rw [hp]; exact push_lt hj
    · show Q.strs[j]? = _; rw [hs]
    · show Q.closedNode[a]? = _; rw [hcl]; exact h
    · show Q.kSlot[j]? = _; rw [hks]
  refine ⟨hI₁.ext hx (by show Q.kTag.size = Q.kInfo.size; rw [ht, hi]; exact hI₁.sizes)
    (by show Q.kSlot.size = Q.kInfo.size; rw [hks, hi]; exact hI₁.kSlotSize) hm hcl hks hn, hx₁.trans hx, _,
    .proj (q := q) (pj := pj) ?_ ?_ ?_ ?_ (Nat.lt_of_lt_of_le hde.lt_size (by rw [hc]; exact Nat.le_refl _))
      (hde.ext hx), ?_⟩
  · show (Q.code ++ _)[Q.code.size]? = _; rw [rd0]; rfl
  · show (Q.code ++ _)[Q.code.size + 1]? = _; rw [rdR]; rfl
  · show Q.projs[q]? = some pj; rw [hp, hq]; exact Array.getElem?_push_size
  · show (Q.code ++ _)[Q.code.size + 2]? = _; rw [rdR]; rfl
  · rw [← hsn, ← hidx]; exact .proj hae

theorem g4MaskOf_key (P : G4Prog) (hd : Expr) : KeyEq P (g4MaskOf find? P hd).2 := by
  unfold g4MaskOf; split
  · split
    · exact KeyEq.refl P
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact KeyEq.refl P

theorem emit_spine (P : G4Prog) (ho : Nat) (aos : Array Nat) :
    P.emit (fun c => aos.foldl (fun c a => c.push a) (((c.push 1).push ho).push aos.size)) =
      P.emit (· ++ (#[1, ho, aos.size] ++ aos)) := by
  unfold G4Prog.emit
  rw [show (fun c : Array Nat => aos.foldl (fun c a => c.push a) (((c.push 1).push ho).push aos.size))
      = (· ++ (#[1, ho, aos.size] ++ aos)) from ?_]
  funext c
  rw [show (fun c a => Array.push c a) = (fun (c : Array Nat) (a : Nat) => c.push (id a)) from rfl,
    Array.foldl_push_eq_append rfl, Array.map_id]
  simp only [Array.push_eq_append, Array.append_assoc]
  congr 1
  rw [← Array.append_assoc, ← Array.append_assoc]
  rfl

/-- One argument step keeps the fold's invariant. -/
theorem g4ArgStep_spec (compArg : G4Prog → Expr → Nat × G4Prog)
    (harg : ∀ P a, Inv P → CompOK P a (compArg P a)) (mask : Array Bool)
    {P₁ : G4Prog} (acc : Array Nat × G4Prog) (done : List Expr) (a : Expr)
    (h₁ : Inv acc.2) (h₂ : Ext P₁ acc.2) (h₃ : ArgsOK acc.2 acc.1 done) :
    Inv (g4ArgStep compArg mask acc a).2 ∧ Ext P₁ (g4ArgStep compArg mask acc a).2 ∧
      ArgsOK (g4ArgStep compArg mask acc a).2 (g4ArgStep compArg mask acc a).1
        (done ++ [a]) := by
  unfold g4ArgStep
  split
  · dsimp only
    rw [emit_append1]
    have hx := Ext.emit acc.2 #[8]
    refine ⟨h₁.emit _, h₂.trans hx, (h₃.ext hx).push (by simp [G4Prog.emit]) (.neutral ?_) (.bot a)⟩
    show (acc.2.code ++ #[8])[acc.2.code.size]? = some 8; rw [rd0]; rfl
  · obtain ⟨hI', hx', s, hd, ha⟩ := harg acc.2 a h₁
    generalize compArg acc.2 a = r at hI' hx' hd ⊢
    obtain ⟨ao, P'⟩ := r
    dsimp only at hI' hx' hd ⊢
    exact ⟨hI', h₂.trans hx', (h₃.ext hx').push hd.lt_size hd ha⟩

theorem g4ArgFold_spec (compArg : G4Prog → Expr → Nat × G4Prog)
    (harg : ∀ P a, Inv P → CompOK P a (compArg P a)) (mask : Array Bool)
    {P₁ : G4Prog} : ∀ (l : List Expr) (acc : Array Nat × G4Prog) (done : List Expr),
      Inv acc.2 → Ext P₁ acc.2 → ArgsOK acc.2 acc.1 done →
      Inv (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        Ext P₁ (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        ArgsOK (l.foldl (g4ArgStep compArg mask) acc).2
          (l.foldl (g4ArgStep compArg mask) acc).1 (done ++ l)
  | [], acc, done, h₁, h₂, h₃ => by simpa using ⟨h₁, h₂, h₃⟩
  | a :: l, acc, done, h₁, h₂, h₃ => by
    obtain ⟨h₁', h₂', h₃'⟩ := g4ArgStep_spec compArg harg mask acc done a h₁ h₂ h₃
    have := g4ArgFold_spec compArg harg mask l _ _ h₁' h₂' h₃'
    simpa using this

/-- **A spine** compiled by compilers that keep the promise keeps it. -/
theorem g4CompSpine_spec (comp compArg : G4Prog → Expr → Nat × G4Prog)
    (hcomp : ∀ P e, Inv P → CompOK P e (comp P e))
    (harg : ∀ P a, Inv P → CompOK P a (compArg P a))
    (P : G4Prog) (hd : Expr) (args : List Expr) (mask : Array Bool) (hI : Inv P) :
    CompOK P (Expr.mkAppN hd args) (g4CompSpine comp compArg P hd args mask) := by
  unfold g4CompSpine
  obtain ⟨hI₁, hx₁, sh, hdh, hah⟩ := hcomp P hd hI
  generalize comp P hd = r at hI₁ hx₁ hdh ⊢
  obtain ⟨ho, P₁⟩ := r
  dsimp only at hI₁ hx₁ hdh ⊢
  obtain ⟨hI₂, hx₂, hargs⟩ := g4ArgFold_spec compArg harg mask (P₁ := P₁) args (#[], P₁) []
    hI₁ (Ext.refl _) ⟨rfl, fun j hj => absurd hj (by simp)⟩
  generalize args.foldl (g4ArgStep compArg mask) (#[], P₁) = r at hI₂ hx₂ hargs ⊢
  obtain ⟨aos, P₂⟩ := r
  dsimp only at hI₂ hx₂ hargs ⊢
  rw [List.nil_append] at hargs
  rw [emit_spine]
  have hx := Ext.emit P₂ (#[1, ho, aos.size] ++ aos)
  have hcode : ∀ j (hj : j < aos.size),
      (P₂.emit (· ++ (#[1, ho, aos.size] ++ aos))).code[P₂.code.size + 3 + j]? = some aos[j] := by
    intro j hj
    show (P₂.code ++ _)[P₂.code.size + 3 + j]? = _
    rw [Nat.add_assoc, rdR, Array.getElem?_append_right (by simp)]
    simp [hj]
  obtain ⟨ss, hds, hass⟩ := (hargs.ext hx).denArgs (o := P₂.code.size)
    (fun j hj => (hargs.2 j hj).1) hcode
  refine ⟨hI₂.emit _, hx₁.trans (hx₂.trans hx), _, .spine ?_ ?_ ?_
    (Nat.lt_of_lt_of_le hdh.lt_size hx₂.codeSize) ((hdh.ext hx₂).ext hx) hds,
    Approx.mkAppN hah hass⟩
  · show (P₂.code ++ _)[P₂.code.size]? = _
    rw [rd0, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 1]? = _
    rw [rdR, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 2]? = _
    rw [rdR, Array.getElem?_append_left (by simp)]; rfl

/-- **A shared closed argument** keeps the promise. -/
theorem g4CompShared_spec (comp : G4Prog → Expr → Nat × G4Prog)
    (hcomp : ∀ P e, Inv P → CompOK P e (comp P e)) (P : G4Prog) (a : Expr) (hI : Inv P) :
    CompOK P a (g4CompShared comp P a) := by
  unfold g4CompShared
  split
  · split
    · rename_i o ho
      obtain ⟨s, -, -, hd, ha⟩ := hI.closed a o ho
      exact ⟨hI, Ext.refl P, s, hd, ha⟩
    · obtain ⟨hI₁, hx₁, s, hd, ha⟩ := hcomp P a hI
      generalize comp P a = r at hI₁ hx₁ hd ⊢
      obtain ⟨ao, P₁⟩ := r
      dsimp only at hI₁ hx₁ hd ⊢
      split
      · rename_i o ho
        obtain ⟨s', -, -, hd', ha'⟩ := hI₁.closed a o ho
        exact ⟨hI₁, hx₁, s', hd', ha'⟩
      rename_i hnone
      rw [emit_append3]
      have hx : Ext P₁ { { (P₁.emit (· ++ #[9, P₁.nslots, ao])) with nslots := P₁.nslots + 1 } with
          closedNode := P₁.closedNode.insert a P₁.code.size } := by
        refine ⟨fun i hi => rdL _ hi, by simp [G4Prog.emit], fun _ _ => rfl, Nat.le_refl _,
          fun _ _ => rfl, fun _ _ => rfl, fun a' o h => ?_, fun _ _ => rfl⟩
        show (P₁.closedNode.insert a P₁.code.size)[a']? = some o
        rw [Std.HashMap.getElem?_insert]
        split
        · rename_i heq
          obtain rfl : a = a' := eq_of_beq heq
          rw [hnone] at h; cases h
        · exact h
      have hreg : (P₁.closedNode.insert a P₁.code.size)[a]? = some P₁.code.size := by
        rw [Std.HashMap.getElem?_insert]; simp
      have hc1 : (P₁.code ++ #[9, P₁.nslots, ao])[P₁.code.size + 1]? = some P₁.nslots := by
        rw [rdR]; rfl
      have hden : Den { { (P₁.emit (· ++ #[9, P₁.nslots, ao])) with nslots := P₁.nslots + 1 } with
          closedNode := P₁.closedNode.insert a P₁.code.size } P₁.code.size s := by
        refine .shared (sl := P₁.nslots) ?_ hc1 ?_ hd.lt_size (hd.ext hx) ⟨a, hreg⟩
        · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
        · show (P₁.code ++ _)[P₁.code.size + 2]? = _; rw [rdR]; rfl
      refine ⟨⟨hI₁.sizes, hI₁.kSlotSize, fun c us k h => ?_, fun a' o h => ?_, ?_⟩, hx₁.trans hx, s,
        hden, ha⟩
      · obtain ⟨info, hi, ha'⟩ := hI₁.kMap c us k h; exact ⟨info, hi, ha'⟩
      · change (P₁.closedNode.insert a P₁.code.size)[a']? = some o at h
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i heq
          obtain rfl := Option.some.inj h
          obtain rfl : a = a' := eq_of_beq heq
          exact ⟨s, P₁.nslots, hc1, hden, ha⟩
        · obtain ⟨sa, sl, hsl, hd', ha'⟩ := hI₁.closed a' o h
          exact ⟨sa, sl, hx.code_some hsl, hd'.ext hx, ha'⟩
      · refine Inv.slots_new hI₁ rfl s ?_
        intro sl t h
        rcases h with ⟨a', o, h₁, h₂, h₃⟩ | ⟨k, info, h₁, h₂, h₃⟩
        · change (P₁.closedNode.insert a P₁.code.size)[a']? = some o at h₁
          rw [Std.HashMap.getElem?_insert] at h₁
          split at h₁
          · obtain rfl := Option.some.inj h₁
            change (P₁.code ++ #[9, P₁.nslots, ao])[P₁.code.size + 1]? = some sl at h₂
            rw [hc1] at h₂
            exact .inr ⟨(Option.some.inj h₂).symm, (Den.unique h₃ hden)⟩
          · exact .inl (Owns.back_node hI₁ hx h₁ h₂ h₃)
        · exact .inl (Owns.back_entry hI₁ hx h₁ h₂ h₃)
  · exact hcomp P a hI

/-- **The compiler is correct up to erasure**: the node it returns denotes a
term approximating the one it compiled, in a program that extends the one
it was given, with the invariant kept. -/
theorem g4Comp_spec : ∀ (f : Nat),
    (∀ (P : G4Prog) (e : Expr), Inv P → CompOK P e (g4Comp find? findProj? f P e)) ∧
    (∀ (P : G4Prog) (a : Expr), Inv P → CompOK P a (g4CompArg find? findProj? f P a)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨fun P e hI => ?_, fun P a hI => ?_⟩
    · unfold g4Comp; exact CompOK.neutral hI e
    · unfold g4CompArg; exact CompOK.neutral hI a
  | succ f ih =>
    obtain ⟨ihC, ihA⟩ := ih
    have hC : ∀ (P : G4Prog) (e : Expr), Inv P → CompOK P e (g4Comp find? findProj? (f + 1) P e) := by
      intro P e hI
      cases e with
      | bvar i =>
        unfold g4Comp; dsimp only
        rw [emit_append2]
        refine ⟨hI.emit _, Ext.emit P _, _, .bvar ?_ ?_, Approx.bvar i⟩
        · show (P.code ++ #[0, i])[P.code.size]? = some 0; rw [rd0]; rfl
        · show (P.code ++ #[0, i])[P.code.size + 1]? = some i; rw [rdR]; rfl
      | fvar i ty => unfold g4Comp; exact CompOK.neutral hI _
      | sort u => unfold g4Comp; exact CompOK.neutral hI _
      | forallE ty b => unfold g4Comp; exact CompOK.neutral hI _
      | lit l =>
        cases l with
        | natVal n =>
          unfold g4Comp; dsimp only
          rw [emit_append2]
          refine ⟨hI.emit _, Ext.emit P _, _, .natLit ?_ ?_, Approx.refl _⟩
          · show (P.code ++ #[5, n])[P.code.size]? = some 5; rw [rd0]; rfl
          · show (P.code ++ #[5, n])[P.code.size + 1]? = some n; rw [rdR]; rfl
        | strVal str =>
          unfold g4Comp; dsimp only
          rw [emit_append2]
          have hx : Ext P { P.emit (· ++ #[6, P.strs.size]) with strs := P.strs.push str } :=
            ⟨(Ext.emit P _).code, (Ext.emit P _).codeSize, fun _ _ => rfl, Nat.le_refl _,
              fun _ _ => rfl, fun i hi => push_lt hi, fun _ _ h => h, fun _ _ => rfl⟩
          refine ⟨hI.ext hx hI.sizes hI.kSlotSize rfl rfl rfl rfl, hx, _,
            .strLit (si := P.strs.size) ?_ ?_ ?_, Approx.refl _⟩
          · show (P.code ++ #[6, P.strs.size])[P.code.size]? = some 6; rw [rd0]; rfl
          · show (P.code ++ #[6, P.strs.size])[P.code.size + 1]? = some P.strs.size; rw [rdR]; rfl
          · show (P.strs.push str)[P.strs.size]? = some str; exact Array.getElem?_push_size
      | lam ty b =>
        unfold g4Comp; dsimp only
        obtain ⟨hI₁, hx₁, sb, hdb, hab⟩ := ihC P b hI
        generalize g4Comp find? findProj? f P b = r at hI₁ hx₁ hdb ⊢
        obtain ⟨bo, P₁⟩ := r
        dsimp only at hI₁ hx₁ hdb ⊢
        have hbo : bo < P₁.code.size := hdb.lt_size
        have hrd : ∀ j, P₁.code[bo + j]? = some P₁.code[bo + j]! ∨ bo + j ≥ P₁.code.size := by
          intro j
          rcases Nat.lt_or_ge (bo + j) P₁.code.size with h' | h'
          · exact .inl (some_of_lt h')
          · exact .inr h'
        by_cases h2 : (P₁.code[bo]! == 2) = true
        · simp only [h2, ↓reduceIte]
          rw [emit_append4]
          have hb2 : P₁.code[bo]? = some 2 := by
            rw [some_of_lt hbo]; exact congrArg some (eq_of_beq h2)
          obtain ⟨tn', inner', ht, hin, htn⟩ := hdb.lam_fields hb2
          rw [get!_of_some ht, get!_of_some hin]
          have hx := Ext.emit P₁ #[2, bo, tn' + 1, inner']
          refine ⟨hI₁.emit _, hx₁.trans hx, _, .lam (tn := tn' + 1) (inner := inner') ?_ ?_ ?_ ?_ hbo
            (hdb.ext hx) (.inl ⟨?_, ?_, ?_, ?_⟩), .lam (.bot _) hab⟩
          · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 2]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 3]? = _; rw [rdR]; rfl
          · exact hx.code_some hb2
          · rw [Nat.add_sub_cancel]; exact hx.code_some ht
          · exact hx.code_some hin
          · omega
        · simp only [h2, Bool.false_eq_true, ↓reduceIte]
          rw [emit_append4]
          have hx := Ext.emit P₁ #[2, bo, 1, bo]
          refine ⟨hI₁.emit _, hx₁.trans hx, _, .lam (tn := 1) (inner := bo) ?_ ?_ ?_ ?_ hbo
            (hdb.ext hx) (.inr ⟨?_, rfl, rfl⟩), .lam (.bot _) hab⟩
          · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 2]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 3]? = _; rw [rdR]; rfl
          · rw [hx.code bo hbo, some_of_lt hbo]
            intro h; apply h2; rw [Option.some.inj h]; rfl
      | letE ty v b =>
        unfold g4Comp; dsimp only
        obtain ⟨hI₁, hx₁, sv, hdv, hav⟩ := ihA P v hI
        generalize g4CompArg find? findProj? f P v = r at hI₁ hx₁ hdv ⊢
        obtain ⟨vo, P₁⟩ := r
        dsimp only at hI₁ hx₁ hdv ⊢
        obtain ⟨hI₂, hx₂, sb, hdb, hab⟩ := ihC P₁ b hI₁
        generalize g4Comp find? findProj? f P₁ b = r at hI₂ hx₂ hdb ⊢
        obtain ⟨bo, P₂⟩ := r
        dsimp only at hI₂ hx₂ hdb ⊢
        rw [emit_append3]
        have hx := Ext.emit P₂ #[3, vo, bo]
        refine ⟨hI₂.emit _, hx₁.trans (hx₂.trans hx), _,
          .letE ?_ ?_ ?_ (Nat.lt_of_lt_of_le hdv.lt_size hx₂.codeSize) hdb.lt_size
            ((hdv.ext hx₂).ext hx) (hdb.ext hx), .letE (.bot _) hav hab⟩
        · show (P₂.code ++ _)[P₂.code.size]? = _; rw [rd0]; rfl
        · show (P₂.code ++ _)[P₂.code.size + 1]? = _; rw [rdR]; rfl
        · show (P₂.code ++ _)[P₂.code.size + 2]? = _; rw [rdR]; rfl
      | const c us =>
        unfold g4Comp; dsimp only
        obtain ⟨hI₁, hx₁, -, info, hinfo, ha⟩ := g4Resolve_spec find? findProj? P c us hI
        generalize g4Resolve find? findProj? P c us = r at hI₁ hx₁ hinfo ⊢
        obtain ⟨k, P₁⟩ := r
        dsimp only at hI₁ hx₁ hinfo ⊢
        rw [emit_append2]
        have hx := Ext.emit P₁ #[4, k]
        refine ⟨hI₁.emit _, hx₁.trans hx, _, .const ?_ ?_ (hx.kInfo_some hinfo), ha⟩
        · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
        · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
      | proj sn i e =>
        unfold g4Comp; dsimp only
        split
        · rename_i en _
          obtain ⟨hI₁, hx₁, se, hde, hae⟩ := ihC P e hI
          generalize g4Comp find? findProj? f P e = r at hI₁ hx₁ hde ⊢
          obtain ⟨so, P₁⟩ := r
          dsimp only at hI₁ hx₁ hde ⊢
          generalize hn : P₁.nid en.ctor = rn
          obtain ⟨ni, P₂⟩ := rn
          have hk : KeyEq P₁ P₂ := by have := KeyEq.nid P₁ en.ctor; rw [hn] at this; exact this
          dsimp only
          refine proj_emit_ok (pj := ⟨sn, en.ctor, i, en.numParams, en.numFields,
              en.levelParams.length, true, en⟩) (sn := sn) (i := i) hI₁ hx₁ hde hae ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ rfl rfl _ ?_
          · exact hk.code
          · exact hk.kTag
          · exact hk.kInfo
          · exact hk.kMap
          · exact hk.closedNode
          · exact hk.strs
          · exact hk.kSlot
          · exact hk.nslots
          · show P₂.projs.push _ = _; rw [hk.projs]
          · rw [hk.projs]
        · exact CompOK.neutral hI _
      | app fn arg =>
        unfold g4Comp; dsimp only
        have hk₁ := g4MaskOf_key find? P (Expr.app fn arg).getAppFn
        generalize g4MaskOf find? P (Expr.app fn arg).getAppFn = r at hk₁ ⊢
        obtain ⟨mask, P₁⟩ := r
        dsimp only at hk₁ ⊢
        have := g4CompSpine_spec (g4Comp find? findProj? f) (g4CompArg find? findProj? f) ihC ihA P₁
          (Expr.app fn arg).getAppFn (Expr.app fn arg).getAppArgs mask (hk₁.inv hI)
        rw [mkAppN_getApp'] at this
        exact this.step hk₁.ext
    refine ⟨hC, fun P a hI => ?_⟩
    have hdef : CompOK P a (g4Comp find? findProj? f P a) := ihC P a hI
    unfold g4CompArg
    split
    all_goals first
      | exact g4CompShared_spec _ ihC P _ hI
      | exact hdef

end

end ConLeche.Verify.Ground
