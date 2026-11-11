module

public import ConLeche.Kernel.Ground
public import ConLeche.Verify.Ground.Erased

public section

/-!
# The ground engine's compiler, correct up to erasure (task #423 soundness, layer (a))

The ground engine compiles every term it evaluates into a code array
(`g4Comp`, `ConLeche/Kernel/Ground.lean`).  This file reads the code back:
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

open ConLeche

variable {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}

/-- The term a table entry's information denotes: the constant, or `bot`
for a neutral entry. -/
@[expose] def infoTerm : G4Info → Expr
  | .defn c _ us _ => .const c us
  | .ctor c us _ _ => .const c us
  | .recr c _ us .. => .const c us
  | .neutral c us => .const c us

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

/-- The words of table entry `k`. -/
@[expose] def _root_.ConLeche.G4Prog.entW (P : G4Prog) (k : Nat) : List (Option Nat) :=
  [P.kTag[k]?, P.kCode[k]?, P.kArity[k]?, P.kB[k]?, P.kC[k]?, P.kD[k]?, P.kE[k]?]

/-- The words of rule row `r`. -/
@[expose] def _root_.ConLeche.G4Prog.rowW (P : G4Prog) (r : Nat) : Option G4Rule × List (Option Nat) :=
  (P.rules[r]?, [P.ruleCode[r]?, P.rNid[r]?, P.rNF[r]?, P.rCP[r]?, P.rC3[r]?])

/-- The words of projection row `q`. -/
@[expose] def _root_.ConLeche.G4Prog.prjW (P : G4Prog) (q : Nat) : List (Option Nat) :=
  [P.pNid[q]?, P.pIdx[q]?, P.pNP[q]?, P.pNF[q]?, P.pNl[q]?, P.pAlw[q]?]

/-- The run's flags: what the compiled code's meaning depends on. -/
@[expose] def _root_.ConLeche.G4Prog.flags (P : G4Prog) : Bool × Bool × Nat :=
  (P.natOk, P.strOk, P.maxNat)

/-- The site's words: the four basis entries, the slot epoch and the slot
array.  Growth (`ExtR`) does not fix them, so the site may set them; the
compiler (`Ext`) leaves them alone. -/
@[expose] def _root_.ConLeche.G4Prog.site (P : G4Prog) : Nat × Nat × Nat × Nat × Nat × Array Nat :=
  (P.kTrue, P.kFalse, P.kZero, P.kSucc, P.epBase, P.slotA)

theorem size_le_of_get {α : Type} {a b : Array α} (h : ∀ i, i < a.size → b[i]? = a[i]?) :
    a.size ≤ b.size := by
  rcases Nat.lt_or_ge b.size a.size with h' | h'
  · have := h b.size h'
    rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h'] at this; cases this
  · exact h'

/-- The words of table entry `k` but its compiled body. -/
@[expose] def _root_.ConLeche.G4Prog.entR (P : G4Prog) (k : Nat) : List (Option Nat) :=
  [P.kTag[k]?, P.kArity[k]?, P.kB[k]?, P.kC[k]?, P.kD[k]?, P.kE[k]?]

/-- The words of rule row `r` but its compiled right-hand side. -/
@[expose] def _root_.ConLeche.G4Prog.rowR (P : G4Prog) (r : Nat) : Option G4Rule × List (Option Nat) :=
  (P.rules[r]?, [P.rNid[r]?, P.rNF[r]?, P.rCP[r]?, P.rC3[r]?])

/-- **Program growth up to the code columns**: what a node's denotation and
the machine's reading read only grows; the compiled-body columns `kCode` and
`ruleCode` may change (the run stores a body it compiles). -/
structure ExtR (P P' : G4Prog) : Prop where
  code : ∀ i, i < P.code.size → P'.code[i]? = P.code[i]?
  codeSize : P.code.size ≤ P'.code.size
  kInfo : ∀ i, i < P.kInfo.size → P'.kInfo[i]? = P.kInfo[i]?
  kInfoSize : P.kInfo.size ≤ P'.kInfo.size
  projs : ∀ i, i < P.projs.size → P'.projs[i]? = P.projs[i]?
  strs : ∀ i, i < P.strs.size → P'.strs[i]? = P.strs[i]?
  closedNode : ∀ (a : Expr) (o : Nat), P.closedNode[a]? = some o → P'.closedNode[a]? = some o
  kSlot : ∀ i, i < P.kSlot.size → P'.kSlot[i]? = P.kSlot[i]?
  ent : ∀ k, k < P.kInfo.size → P'.entR k = P.entR k
  rulesSize : P.rules.size ≤ P'.rules.size
  row : ∀ r, r < P.rules.size → P'.rowR r = P.rowR r
  prj : ∀ q, q < P.projs.size → P'.prjW q = P.prjW q
  nids : ∀ (c : Name) (i : Nat), P.nids[c]? = some i → P'.nids[c]? = some i
  flags : P'.flags = P.flags

/-- **Program extension**: growth that also keeps the compiled bodies. -/
structure Ext (P P' : G4Prog) : Prop extends ExtR P P' where
  kCode : ∀ k, k < P.kInfo.size → P'.kCode[k]? = P.kCode[k]?
  ruleCode : ∀ r, r < P.rules.size → P'.ruleCode[r]? = P.ruleCode[r]?
  site : P'.site = P.site

theorem ExtR.refl (P : G4Prog) : ExtR P P :=
  ⟨fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, fun _ _ => rfl, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, rfl⟩

theorem Ext.refl (P : G4Prog) : Ext P P := ⟨ExtR.refl P, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem get?_size_le {α : Type} {a b : Array α} {i : Nat} (hi : i < a.size) (h : b[i]? = a[i]?) :
    i < b.size := by
  rcases Nat.lt_or_ge i b.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h
    exact absurd h.symm (by simp [Array.getElem?_eq_getElem hi])

theorem ExtR.trans {P₁ P₂ P₃ : G4Prog} (h₁ : ExtR P₁ P₂) (h₂ : ExtR P₂ P₃) : ExtR P₁ P₃ where
  code i hi := (h₂.code i (Nat.lt_of_lt_of_le hi h₁.codeSize)).trans (h₁.code i hi)
  codeSize := Nat.le_trans h₁.codeSize h₂.codeSize
  kInfo i hi := (h₂.kInfo i (Nat.lt_of_lt_of_le hi h₁.kInfoSize)).trans (h₁.kInfo i hi)
  kInfoSize := Nat.le_trans h₁.kInfoSize h₂.kInfoSize
  projs i hi := (h₂.projs i (get?_size_le hi (h₁.projs i hi))).trans (h₁.projs i hi)
  strs i hi := (h₂.strs i (get?_size_le hi (h₁.strs i hi))).trans (h₁.strs i hi)
  closedNode a o h := h₂.closedNode a o (h₁.closedNode a o h)
  kSlot i hi := (h₂.kSlot i (get?_size_le hi (h₁.kSlot i hi))).trans (h₁.kSlot i hi)
  ent k hk := (h₂.ent k (Nat.lt_of_lt_of_le hk h₁.kInfoSize)).trans (h₁.ent k hk)
  rulesSize := Nat.le_trans h₁.rulesSize h₂.rulesSize
  row r hr := (h₂.row r (Nat.lt_of_lt_of_le hr h₁.rulesSize)).trans (h₁.row r hr)
  prj q hq := (h₂.prj q (get?_size_le hq (h₁.projs q hq))).trans (h₁.prj q hq)
  nids c i h := h₂.nids c i (h₁.nids c i h)
  flags := h₂.flags.trans h₁.flags

theorem Ext.trans {P₁ P₂ P₃ : G4Prog} (h₁ : Ext P₁ P₂) (h₂ : Ext P₂ P₃) : Ext P₁ P₃ :=
  ⟨h₁.toExtR.trans h₂.toExtR,
    fun k hk => (h₂.kCode k (Nat.lt_of_lt_of_le hk h₁.kInfoSize)).trans (h₁.kCode k hk),
    fun r hr => (h₂.ruleCode r (Nat.lt_of_lt_of_le hr h₁.rulesSize)).trans (h₁.ruleCode r hr),
    h₂.site.trans h₁.site⟩

/-- Growth up to the code columns, then extension. -/
theorem ExtR.trans_ext {P₁ P₂ P₃ : G4Prog} (h₁ : ExtR P₁ P₂) (h₂ : Ext P₂ P₃) : ExtR P₁ P₃ :=
  h₁.trans h₂.toExtR

theorem ExtR.code_some {P P' : G4Prog} (h : ExtR P P') {i x : Nat} (hx : P.code[i]? = some x) :
    P'.code[i]? = some x := by
  have hi : i < P.code.size := by
    rcases Nat.lt_or_ge i P.code.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.code i hi, hx]

theorem ExtR.kInfo_some {P P' : G4Prog} (h : ExtR P P') {i : Nat} {x : G4Info}
    (hx : P.kInfo[i]? = some x) : P'.kInfo[i]? = some x := by
  have hi : i < P.kInfo.size := by
    rcases Nat.lt_or_ge i P.kInfo.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.kInfo i hi, hx]

theorem ExtR.projs_some {P P' : G4Prog} (h : ExtR P P') {i : Nat} {x : G4Proj}
    (hx : P.projs[i]? = some x) : P'.projs[i]? = some x := by
  have hi : i < P.projs.size := by
    rcases Nat.lt_or_ge i P.projs.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.projs i hi, hx]

theorem ExtR.strs_some {P P' : G4Prog} (h : ExtR P P') {i : Nat} {x : String}
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
theorem Den.ext {P P' : G4Prog} (hx : ExtR P P') {o : Nat} {s : Expr} : Den P o s → Den P' o s
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

theorem DenArgs.ext {P P' : G4Prog} (hx : ExtR P P') {o p n : Nat} {ss : List Expr} :
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
  ent _ _ := rfl
  rulesSize := Nat.le_refl _
  row _ _ := rfl
  prj _ _ := rfl
  nids _ _ h := h
  flags := rfl
  kCode _ _ := rfl
  ruleCode _ _ := rfl
  site := rfl

/-! ## The program invariant -/

/-- **A sharing slot's owner** and the term it denotes: the shared node
registered for a closed term, or a table entry (its constant). -/
@[expose] def Owns (P : G4Prog) (sl : Nat) (t : Expr) : Prop :=
  (∃ (a : Expr) (o : Nat), P.closedNode[a]? = some o ∧ P.code[o + 1]? = some sl ∧ Den P o t) ∨
  (∃ (k : Nat) (info : G4Info), P.kSlot[k]? = some sl ∧ P.kInfo[k]? = some info ∧ t = infoTerm info)

theorem ExtR.kSlot_some {P P' : G4Prog} (h : ExtR P P') {i x : Nat} (hx : P.kSlot[i]? = some x) :
    P'.kSlot[i]? = some x := by
  have hi : i < P.kSlot.size := by
    rcases Nat.lt_or_ge i P.kSlot.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hx; cases hx
  rw [h.kSlot i hi, hx]

/-- Ownership survives extension. -/
theorem Owns.ext {P P' : G4Prog} (hx : ExtR P P') {sl : Nat}
    {t : Expr} : Owns P sl t → Owns P' sl t
  | .inl ⟨a, o, h₁, h₂, h₃⟩ => .inl ⟨a, o, hx.closedNode a o h₁, hx.code_some h₂, h₃.ext hx⟩
  | .inr ⟨k, info, h₁, h₂, h₃⟩ => .inr ⟨k, info, hx.kSlot_some h₁, hx.kInfo_some h₂, h₃⟩

/-- The table's parallel arrays agree in size. -/
@[expose] def Sizes (P : G4Prog) : Prop :=
  (P.kCode.size = P.kInfo.size ∧ P.kArity.size = P.kInfo.size ∧ P.kB.size = P.kInfo.size ∧
    P.kC.size = P.kInfo.size ∧ P.kD.size = P.kInfo.size ∧ P.kE.size = P.kInfo.size) ∧
  (P.ruleCode.size = P.rules.size ∧ P.rNid.size = P.rules.size ∧ P.rNF.size = P.rules.size ∧
    P.rCP.size = P.rules.size ∧ P.rC3.size = P.rules.size) ∧
  (P.pNid.size = P.projs.size ∧ P.pIdx.size = P.projs.size ∧ P.pNP.size = P.projs.size ∧
    P.pNF.size = P.projs.size ∧ P.pNl.size = P.projs.size ∧ P.pAlw.size = P.projs.size)

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

theorem lt_of_some {α : Type} {a : Array α} {i : Nat} {x : α} (h : a[i]? = some x) : i < a.size := by
  rcases Nat.lt_or_ge i a.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

/-! ## The table invariant -/

/-- A compiled-body word: `0` not compiled yet, `o + 1` the node `o`, which
denotes an approximation of `t`. -/
@[expose] def CodeOK (P : G4Prog) (w : Nat) (t : Expr) : Prop :=
  w = 0 ∨ ∃ o s, w = o + 1 ∧ Den P o s ∧ Approx s t

/-- Case 3 of a rule's ι split, as `g4Entry` records it. -/
@[expose] def ruleCase3 (find? : Name → Option ConstantInfo) (isK : Bool) (lps : List Name)
    (us : List Level) (rl : RecRule) : Bool :=
  match find? rl.ctor with
  | some (.ctorInfo cvj _ _) => gCase3 find? isK cvj (gCmpLevels rl lps us cvj.levelParams)
  | _ => true

/-- **A rule row** `r` is the recursor rule `rl` at the levels `us`. -/
@[expose] def RowOK (find? : Name → Option ConstantInfo) (P : G4Prog) (r : Nat) (isK : Bool)
    (lps : List Name) (us : List Level) (rl : RecRule) : Prop :=
  P.rules[r]? = some ⟨rl.ctor, rl.nfields, gCtorParams find? rl.ctor, ruleCase3 find? isK lps us rl,
      rl.rhs⟩ ∧
    P.rNF[r]? = some rl.nfields ∧ P.rCP[r]? = some (gCtorParams find? rl.ctor) ∧
    P.rC3[r]? = some (if ruleCase3 find? isK lps us rl then 1 else 0) ∧
    (∃ i, P.nids[rl.ctor]? = some i ∧ P.rNid[r]? = some i) ∧
    ∃ w, P.ruleCode[r]? = some w ∧ CodeOK P w (rl.rhs.instantiateLevelParams lps us)

/-- **The K step's constructor entry** (`kfab`, the entry plus one, or `0`):
a K recursor's single rule binds no field, and the entry's arity is within
the recursor's leading arguments. -/
@[expose] def KfabOK (P : G4Prog) (mI : Nat) (isK : Bool) (rules : List RecRule) (kfab : Nat) : Prop :=
  kfab = 0 ∨ ∃ kc rl, kfab = kc + 1 ∧ kc < P.kInfo.size ∧ (∃ a, P.kArity[kc]? = some a ∧ a ≤ mI + 1) ∧
    isK = true ∧ rules = [rl] ∧ rl.nfields = 0

/-- A definition entry: the stored definition at the levels; tag `3` an
accelerated operation. -/
@[expose] def DefnOK (find? : Name → Option ConstantInfo) (P : G4Prog) (k : Nat) (c : Name)
    (lps : List Name) (us : List Level) (v : Expr) : Prop :=
  (∃ cv h, find? c = some (.defnInfo cv v h) ∧ cv.levelParams = lps) ∧ us.length = lps.length ∧
    (P.kTag[k]? = some 0 ∨
      (P.kTag[k]? = some 3 ∧ us = [] ∧ P.natOk = true ∧ natBin14 c = true ∧
        P.kE[k]? = some ((natBin14Names.idxOf? c).getD 0))) ∧
    ∃ w, P.kCode[k]? = some w ∧ CodeOK P w (v.instantiateLevelParams lps us)

/-- A constructor entry: its arity, its name's id and its level count. -/
@[expose] def CtorOK (find? : Name → Option ConstantInfo) (P : G4Prog) (k : Nat) (c : Name)
    (us : List Level) (nP nF : Nat) : Prop :=
  (∃ cv, find? c = some (.ctorInfo cv nP nF) ∧ P.kArity[k]? = some (g4Pis cv.type 0)) ∧
    P.kTag[k]? = some 1 ∧ (∃ i, P.nids[c]? = some i ∧ P.kB[k]? = some i) ∧
    P.kD[k]? = some us.length

/-- A recursor entry: the stored recursor at the levels, its words, its K
step and its rule rows. -/
@[expose] def RecOK (find? : Name → Option ConstantInfo) (P : G4Prog) (k : Nat) (c : Name)
    (lps : List Name) (us : List Level) (mI rP base nr : Nat) (isK isEta : Bool) : Prop :=
  ∃ cv rules, find? c = some (.recInfo cv mI rP isK rules) ∧ cv.levelParams = lps ∧
    us.length = lps.length ∧ (Expr.peelPis (mI + 1) cv.type).isSome = true ∧
    P.kTag[k]? = some 2 ∧ P.kArity[k]? = some mI ∧ P.kB[k]? = some rP ∧ P.kC[k]? = some base ∧
    P.kD[k]? = some nr ∧ nr = rules.length ∧ base + nr ≤ P.rules.size ∧
    (∃ kfab, P.kE[k]? = some ((if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * kfab) ∧
      KfabOK P mI isK rules kfab) ∧
    ∀ i (h : i < rules.length), RowOK find? P (base + i) isK lps us rules[i]

/-- **A table entry** is the declaration it names: its tag, arity and words
are the ones `g4Entry` computes from it. -/
@[expose] def EntOK (find? : Name → Option ConstantInfo) (P : G4Prog) (k : Nat) : Prop :=
  match P.kInfo[k]? with
  | some (.neutral _ _) => P.kTag[k]? = some 5
  | some (.defn c lps us v) => DefnOK find? P k c lps us v
  | some (.ctor c us nP nF) => CtorOK find? P k c us nP nF
  | some (.recr c lps us mI rP base nr isK isEta) => RecOK find? P k c lps us mI rP base nr isK isEta
  | none => True

/-- **A projection row** `q` is the projection table's entry it names. -/
@[expose] def PrjOK (findProj? : Name → Nat → Option ProjEntry) (P : G4Prog) (q : Nat) : Prop :=
  ∃ sn i en, P.projs[q]? = some ⟨sn, en.ctor, i, en.numParams, en.numFields,
      en.levelParams.length, true, en⟩ ∧
    findProj? sn i = some en ∧ (∃ ni, P.nids[en.ctor]? = some ni ∧ P.pNid[q]? = some ni) ∧
    P.pIdx[q]? = some i ∧ P.pNP[q]? = some en.numParams ∧ P.pNF[q]? = some en.numFields ∧
    P.pNl[q]? = some en.levelParams.length ∧ P.pAlw[q]? = some 1

/-- **Name ids** are below the map's size and injective. -/
@[expose] def NidOK (P : G4Prog) : Prop :=
  (∀ (c : Name) (i : Nat), P.nids[c]? = some i → i < P.nids.size) ∧
    ∀ (c c' : Name) (i : Nat), P.nids[c]? = some i → P.nids[c']? = some i → c = c'

theorem entW_eq {P P' : G4Prog} {k : Nat} (h : P'.entW k = P.entW k) :
    P'.kTag[k]? = P.kTag[k]? ∧ P'.kCode[k]? = P.kCode[k]? ∧ P'.kArity[k]? = P.kArity[k]? ∧
      P'.kB[k]? = P.kB[k]? ∧ P'.kC[k]? = P.kC[k]? ∧ P'.kD[k]? = P.kD[k]? ∧ P'.kE[k]? = P.kE[k]? := by
  simpa [G4Prog.entW] using h

theorem entR_eq {P P' : G4Prog} {k : Nat} (h : P'.entR k = P.entR k) :
    P'.kTag[k]? = P.kTag[k]? ∧ P'.kArity[k]? = P.kArity[k]? ∧
      P'.kB[k]? = P.kB[k]? ∧ P'.kC[k]? = P.kC[k]? ∧ P'.kD[k]? = P.kD[k]? ∧ P'.kE[k]? = P.kE[k]? := by
  simpa [G4Prog.entR] using h

theorem entR_of_entW {P P' : G4Prog} {k : Nat} (h : P'.entW k = P.entW k) : P'.entR k = P.entR k := by
  obtain ⟨e₁, -, e₃, e₄, e₅, e₆, e₇⟩ := entW_eq h
  simp only [G4Prog.entR, e₁, e₃, e₄, e₅, e₆, e₇]

theorem rowW_eq {P P' : G4Prog} {r : Nat} (h : P'.rowW r = P.rowW r) :
    P'.rules[r]? = P.rules[r]? ∧ P'.ruleCode[r]? = P.ruleCode[r]? ∧ P'.rNid[r]? = P.rNid[r]? ∧
      P'.rNF[r]? = P.rNF[r]? ∧ P'.rCP[r]? = P.rCP[r]? ∧ P'.rC3[r]? = P.rC3[r]? := by
  simpa [G4Prog.rowW] using h

theorem rowR_eq {P P' : G4Prog} {r : Nat} (h : P'.rowR r = P.rowR r) :
    P'.rules[r]? = P.rules[r]? ∧ P'.rNid[r]? = P.rNid[r]? ∧
      P'.rNF[r]? = P.rNF[r]? ∧ P'.rCP[r]? = P.rCP[r]? ∧ P'.rC3[r]? = P.rC3[r]? := by
  simpa [G4Prog.rowR] using h

theorem rowR_of_rowW {P P' : G4Prog} {r : Nat} (h : P'.rowW r = P.rowW r) : P'.rowR r = P.rowR r := by
  obtain ⟨e₁, -, e₃, e₄, e₅, e₆⟩ := rowW_eq h
  simp only [G4Prog.rowR, e₁, e₃, e₄, e₅, e₆]

theorem prjW_eq {P P' : G4Prog} {q : Nat} (h : P'.prjW q = P.prjW q) :
    P'.pNid[q]? = P.pNid[q]? ∧ P'.pIdx[q]? = P.pIdx[q]? ∧ P'.pNP[q]? = P.pNP[q]? ∧
      P'.pNF[q]? = P.pNF[q]? ∧ P'.pNl[q]? = P.pNl[q]? ∧ P'.pAlw[q]? = P.pAlw[q]? := by
  simpa [G4Prog.prjW] using h

theorem ExtR.natOk {P P' : G4Prog} (hx : ExtR P P') : P'.natOk = P.natOk :=
  congrArg Prod.fst hx.flags

theorem Ext.epBase {P P' : G4Prog} (hx : Ext P P') : P'.epBase = P.epBase := by
  have := hx.site; simp only [G4Prog.site, Prod.mk.injEq] at this; exact this.2.2.2.2.1

theorem CodeOK.ext {P P' : G4Prog} (hx : ExtR P P') {w : Nat} {t : Expr} :
    CodeOK P w t → CodeOK P' w t
  | .inl h => .inl h
  | .inr ⟨o, s, h₁, h₂, h₃⟩ => .inr ⟨o, s, h₁, h₂.ext hx, h₃⟩

/-- A rule row survives growth that keeps its compiled right-hand side. -/
theorem RowOK.extR {P P' : G4Prog} (hx : ExtR P P') {r : Nat} (hr : r < P.rules.size)
    (hc : P'.ruleCode[r]? = P.ruleCode[r]?) {isK : Bool}
    {lps : List Name} {us : List Level} {rl : RecRule} (h : RowOK find? P r isK lps us rl) :
    RowOK find? P' r isK lps us rl := by
  obtain ⟨e₁, e₃, e₄, e₅, e₆⟩ := rowR_eq (hx.row r hr)
  obtain ⟨h₁, h₂, h₃, h₄, ⟨i, hi, hi'⟩, w, hw, hc'⟩ := h
  exact ⟨e₁ ▸ h₁, e₄ ▸ h₂, e₅ ▸ h₃, e₆ ▸ h₄, ⟨i, hx.nids _ _ hi, e₃ ▸ hi'⟩, w, hc ▸ hw, hc'.ext hx⟩

theorem RowOK.ext {P P' : G4Prog} (hx : Ext P P') {r : Nat} (hr : r < P.rules.size) {isK : Bool}
    {lps : List Name} {us : List Level} {rl : RecRule} (h : RowOK find? P r isK lps us rl) :
    RowOK find? P' r isK lps us rl :=
  h.extR hx.toExtR hr (hx.ruleCode r hr)

theorem KfabOK.ext {P P' : G4Prog} (hx : ExtR P P') {mI : Nat} {isK : Bool} {rules : List RecRule}
    {kfab : Nat} : KfabOK P mI isK rules kfab → KfabOK P' mI isK rules kfab
  | .inl h => .inl h
  | .inr ⟨kc, rl, h₁, h₂, ⟨a, ha, ha'⟩, h₄⟩ =>
    .inr ⟨kc, rl, h₁, Nat.lt_of_lt_of_le h₂ hx.kInfoSize,
      ⟨a, (entR_eq (hx.ent kc h₂)).2.1 ▸ ha, ha'⟩, h₄⟩

/-- **A table entry survives growth up to the code columns**, given its
compiled body and its rule rows. -/
theorem EntOK.extR {P P' : G4Prog} (hx : ExtR P P') {k : Nat} (hk : k < P.kInfo.size)
    (hkc : P'.kCode[k]? = P.kCode[k]?)
    (hrow : ∀ c lps us mI rP base nr isK isEta,
      P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) → ∀ (i : Nat) (rl : RecRule), i < nr →
      RowOK find? P (base + i) isK lps us rl → RowOK find? P' (base + i) isK lps us rl)
    (h : EntOK find? P k) : EntOK find? P' k := by
  obtain ⟨e₁, e₃, e₄, e₅, e₆, e₇⟩ := entR_eq (hx.ent k hk)
  unfold EntOK at h ⊢
  rw [hx.kInfo k hk]
  revert hrow
  unfold DefnOK CtorOK RecOK at *
  rw [e₁, hkc, e₃, e₄, e₅, e₆, e₇, hx.natOk]
  intro hrow
  split at h
  · exact h
  · obtain ⟨h₁, h₂, h₃, w, hw, hc⟩ := h
    exact ⟨h₁, h₂, h₃, w, hw, hc.ext hx⟩
  · obtain ⟨h₁, h₂, ⟨i, hi, hi'⟩, h₄⟩ := h
    exact ⟨h₁, h₂, ⟨i, hx.nids _ _ hi, hi'⟩, h₄⟩
  · rename_i heq
    obtain ⟨cv, rules, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, ⟨kfab, hf, hf'⟩, hr⟩ := h
    exact ⟨cv, rules, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, Nat.le_trans h₁₁ hx.rulesSize,
      ⟨kfab, hf, hf'.ext hx⟩, fun i hi => hrow _ _ _ _ _ _ _ _ _ heq i _ (by omega) (hr i hi)⟩
  · exact h

theorem EntOK.ext {P P' : G4Prog} (hx : Ext P P') {k : Nat} (hk : k < P.kInfo.size)
    (h : EntOK find? P k) : EntOK find? P' k := by
  refine h.extR hx.toExtR hk (hx.kCode k hk) (fun c lps us mI rP base nr isK isEta hi i rl hi' hr => ?_)
  have hb : base + nr ≤ P.rules.size := by
    unfold EntOK at h; rw [hi] at h; obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h
  exact hr.ext hx (by omega)

/-- An entry tagged `2` is a recursor's. -/
theorem EntOK.tag2 {P : G4Prog} {k : Nat} (h : EntOK find? P k) (hk : k < P.kInfo.size)
    (ht : P.kTag[k]? = some 2) :
    ∃ c lps us mI rP base nr isK isEta, P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) ∧
      RecOK find? P k c lps us mI rP base nr isK isEta := by
  unfold EntOK at h
  split at h
  · rw [ht] at h; cases h
  · obtain ⟨-, -, h3, -⟩ := h; rw [ht] at h3; rcases h3 with h3 | ⟨h3, -⟩ <;> cases h3
  · obtain ⟨-, h2, -⟩ := h; rw [ht] at h2; cases h2
  · rename_i heq; exact ⟨_, _, _, _, _, _, _, _, _, heq, h⟩
  · rename_i heq; rw [Array.getElem?_eq_getElem hk] at heq; cases heq

/-- An entry tagged `1` is a constructor's. -/
theorem EntOK.tag1 {P : G4Prog} {k : Nat} (h : EntOK find? P k) (hk : k < P.kInfo.size)
    (ht : P.kTag[k]? = some 1) :
    ∃ c us nP nF, P.kInfo[k]? = some (.ctor c us nP nF) ∧ CtorOK find? P k c us nP nF := by
  unfold EntOK at h
  split at h
  · rw [ht] at h; cases h
  · obtain ⟨-, -, h3, -⟩ := h; rw [ht] at h3; rcases h3 with h3 | ⟨h3, -⟩ <;> cases h3
  · rename_i heq; exact ⟨_, _, _, _, heq, h⟩
  · obtain ⟨-, -, -, -, -, -, h2, -⟩ := h; rw [ht] at h2; cases h2
  · rename_i heq; rw [Array.getElem?_eq_getElem hk] at heq; cases heq

/-- **The K step's entry**: past the flags, `kE` names a constructor entry
whose arity is within the recursor's leading arguments. -/
theorem RecOK.kstep {P : G4Prog} {k : Nat} {c : Name} {lps : List Name} {us : List Level}
    {mI rP base nr : Nat} {isK isEta : Bool} (h : RecOK find? P k c lps us mI rP base nr isK isEta)
    (h4 : 4 ≤ P.kE[k]!) :
    P.kE[k]! / 4 - 1 < P.kInfo.size ∧ ∃ a, P.kArity[P.kE[k]! / 4 - 1]? = some a ∧ a ≤ mI + 1 := by
  obtain ⟨cv, rules, -, -, -, -, -, -, -, -, -, -, -, ⟨kfab, he, hkf⟩, -⟩ := h
  rw [get!_of_some he] at h4 ⊢
  rcases hkf with rfl | ⟨kc, rl, rfl, hlt, ha, -⟩
  · exfalso; cases isK <;> cases isEta <;> simp at h4
  · have e : ((if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * (kc + 1)) / 4 - 1 = kc := by
      cases isK <;> cases isEta <;> simp <;> omega
    rw [e]; exact ⟨hlt, ha⟩

theorem PrjOK.ext {P P' : G4Prog} (hx : ExtR P P') {q : Nat} (hq : q < P.projs.size)
    (h : PrjOK findProj? P q) : PrjOK findProj? P' q := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := prjW_eq (hx.prj q hq)
  obtain ⟨sn, i, en, h₁, h₂, ⟨ni, hn, hn'⟩, h₄⟩ := h
  rw [← e₂, ← e₃, ← e₄, ← e₅, ← e₆] at h₄
  exact ⟨sn, i, en, by rw [hx.projs q hq]; exact h₁, h₂, ⟨ni, hx.nids _ _ hn, e₁ ▸ hn'⟩, h₄⟩

/-- A fresh name's id is the map's size. -/
theorem NidOK.nid {P : G4Prog} (h : NidOK P) (c : Name) : NidOK (P.nid c).2 := by
  unfold G4Prog.nid; split
  · exact h
  · rename_i hn
    show NidOK { P with nids := P.nids.insert c P.nids.size }
    have hc : c ∉ P.nids := by
      intro hm; rw [Std.HashMap.mem_iff_isSome_getElem?, hn] at hm; cases hm
    have hsz : (P.nids.insert c P.nids.size).size = P.nids.size + 1 := by
      rw [Std.HashMap.size_insert]; simp [hc]
    refine ⟨fun c' i hi => ?_, fun c₁ c₂ i h₁ h₂ => ?_⟩
    · change (P.nids.insert c P.nids.size)[c']? = some i at hi
      rw [hsz]; rw [Std.HashMap.getElem?_insert] at hi
      split at hi
      · cases hi; omega
      · have := h.1 c' i hi; omega
    · change (P.nids.insert c P.nids.size)[c₁]? = some i at h₁
      change (P.nids.insert c P.nids.size)[c₂]? = some i at h₂
      rw [Std.HashMap.getElem?_insert] at h₁ h₂
      split at h₁ <;> split at h₂
      · rename_i e₁ e₂; exact (eq_of_beq e₁).symm.trans (eq_of_beq e₂)
      · rename_i e₁ _; cases h₁; have := h.1 c₂ _ h₂; omega
      · rename_i _ e₂; cases h₂; have := h.1 c₁ _ h₁; omega
      · exact h.2 c₁ c₂ i h₁ h₂

/-- The id the map gives a name. -/
theorem nid_get (P : G4Prog) (c : Name) : (P.nid c).2.nids[c]? = some (P.nid c).1 := by
  unfold G4Prog.nid; split
  · rename_i i hi; exact hi
  · show (P.nids.insert c P.nids.size)[c]? = some P.nids.size
    rw [Std.HashMap.getElem?_insert]; simp

/-- Entry `k` is a recursor's whose rule rows include `r`. -/
@[expose] def RowsOf (P : G4Prog) (k r : Nat) : Prop :=
  ∃ c lps us mI rP base nr isK isEta, P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) ∧
    base ≤ r ∧ r < base + nr

/-- Growth that keeps the table's size keeps the rows' owners. -/
theorem RowsOf.back {P P' : G4Prog} (hx : ExtR P P') (hkI : P'.kInfo.size = P.kInfo.size) {k r : Nat}
    (h : RowsOf P' k r) : RowsOf P k r := by
  obtain ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, h₁, h₂⟩ := h
  have hk : k < P.kInfo.size := hkI ▸ lt_of_some hi
  exact ⟨c, lps, us, mI, rP, base, nr, isK, isEta, by rw [← hx.kInfo k hk]; exact hi, h₁, h₂⟩

/-- **The program's memos denote what they key**, every sharing slot
has one term, and the table is the declarations'. -/
structure Inv (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Prop where
  szs : Sizes P
  sizes : P.kTag.size = P.kInfo.size
  kSlotSize : P.kSlot.size = P.kInfo.size
  kMap : ∀ c us k, P.kMap[(c, us)]? = some k →
    ∃ info, P.kInfo[k]? = some info ∧ Approx (infoTerm info) (.const c us)
  closed : ∀ (a : Expr) (o : Nat), P.closedNode[a]? = some o →
    ∃ s sl, P.code[o + 1]? = some sl ∧ Den P o s ∧ Approx s a ∧ a.looseBVarsBounded 0 = true
  slots : ∃ σ : Nat → Expr, ∀ sl t, Owns P sl t → sl < P.nslots ∧ σ sl = t
  ents : ∀ k, k < P.kInfo.size → EntOK find? P k
  prjs : ∀ q, q < P.projs.size → PrjOK findProj? P q
  nidOK : NidOK P
  rowsDisj : ∀ k k' r, RowsOf P k r → RowsOf P k' r → k = k'

/-- A recursor entry's rule rows are in the rule table. -/
theorem Inv.rows_lt {P : G4Prog} (hI : Inv find? findProj? P) {k r : Nat} (h : RowsOf P k r) :
    r < P.rules.size := by
  obtain ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, h₁, h₂⟩ := h
  have := hI.ents k (lt_of_some hi)
  unfold EntOK at this; rw [hi] at this
  obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := this; omega

/-- A slot denotes one term. -/
theorem Inv.owns_unique {P : G4Prog} (hI : Inv find? findProj? P) {sl : Nat} {t t' : Expr} (h : Owns P sl t)
    (h' : Owns P sl t') : t = t' := by
  obtain ⟨σ, hσ⟩ := hI.slots
  rw [← (hσ sl t h).2, (hσ sl t' h').2]

/-- One new owner at the next slot: a table entry or a shared node. -/
theorem Inv.slots_new {P Q : G4Prog} (hI : Inv find? findProj? P) (hn : Q.nslots = P.nslots + 1)
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
theorem Owns.back_node {P Q : G4Prog} (hI : Inv find? findProj? P) (hx : Ext P Q) {a : Expr} {o sl : Nat} {t : Expr}
    (h₁ : P.closedNode[a]? = some o) (h₂ : Q.code[o + 1]? = some sl) (h₃ : Den Q o t) :
    Owns P sl t := by
  obtain ⟨s, sl', hsl', hd, -, -⟩ := hI.closed a o h₁
  rw [hx.code_some hsl'] at h₂
  obtain rfl : sl' = sl := Option.some.inj h₂
  obtain rfl := Den.unique (hd.ext hx.toExtR) h₃
  exact .inl ⟨a, o, h₁, hsl', hd⟩

/-- An entry of an extension below the old table is an owner before it. -/
theorem Owns.back_entry {P Q : G4Prog} (hI : Inv find? findProj? P) (hx : Ext P Q) {k sl : Nat} {info : G4Info}
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
theorem Owns.back {P Q : G4Prog} (hI : Inv find? findProj? P) (hx : Ext P Q)
    (hc : ∀ (a : Expr) (o : Nat), Q.closedNode[a]? = some o → P.closedNode[a]? = some o)
    {sl : Nat} {t : Expr} (h : Owns Q sl t) (hk : ∀ k : Nat, Q.kSlot[k]? = some sl → P.kSlot[k]? = some sl) :
    Owns P sl t := by
  rcases h with ⟨a, o, h₁, h₂, h₃⟩ | ⟨k, info, h₁, h₂, h₃⟩
  · exact Owns.back_node hI hx (hc a o h₁) h₂ h₃
  · exact Owns.back_entry hI hx (hk k h₁) h₂ h₃

/-- An extension that adds no owner keeps the slots. -/
theorem Inv.slots_ext {P P' : G4Prog} (hI : Inv find? findProj? P) (hx : Ext P P')
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
theorem Inv.ext {P P' : G4Prog} (hI : Inv find? findProj? P) (hx : Ext P P') (hs : P'.kTag.size = P'.kInfo.size)
    (hks : P'.kSlot.size = P'.kInfo.size) (hk : P'.kMap = P.kMap) (hc : P'.closedNode = P.closedNode) (hsl : P'.kSlot = P.kSlot)
    (hn : P'.nslots = P.nslots) (hsz : Sizes P') (hkI : P'.kInfo.size = P.kInfo.size)
    (hpj : ∀ q, q < P'.projs.size → P.projs.size ≤ q → PrjOK findProj? P' q) (hnid : NidOK P') :
    Inv find? findProj? P' where
  szs := hsz
  sizes := hs
  kSlotSize := hks
  kMap c us k h := by
    rw [hk] at h
    obtain ⟨info, hi, ha⟩ := hI.kMap c us k h
    exact ⟨info, hx.kInfo_some hi, ha⟩
  closed a o h := by
    rw [hc] at h
    obtain ⟨s, sl, hsl', hd, ha, hc0⟩ := hI.closed a o h
    exact ⟨s, sl, hx.code_some hsl', hd.ext hx.toExtR, ha, hc0⟩
  slots := hI.slots_ext hx (fun a o h => by rw [hc] at h; exact h) hsl (by rw [hn]; exact Nat.le_refl _)
  ents k hk' := (hI.ents k (by omega)).ext hx (by omega)
  prjs q hq := by
    rcases Nat.lt_or_ge q P.projs.size with h | h
    · exact (hI.prjs q h).ext hx.toExtR h
    · exact hpj q hq h
  nidOK := hnid
  rowsDisj k k' r h h' := hI.rowsDisj k k' r (h.back hx.toExtR hkI) (h'.back hx.toExtR hkI)

theorem Inv.emit {P : G4Prog} (hI : Inv find? findProj? P) (ws : Array Nat) :
    Inv find? findProj? (P.emit (· ++ ws)) :=
  hI.ext (Ext.emit P ws) hI.sizes hI.kSlotSize rfl rfl rfl rfl hI.szs rfl
    (fun _ hq h => absurd hq (Nat.not_lt.mpr h)) hI.nidOK

/-- A program with empty tables and memos (the engine's fresh program, with
its flags) satisfies the invariant. -/
theorem Inv.fresh (natOk strOk : Bool) (maxNat : Nat) :
    Inv find? findProj? ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog) where
  szs := by simp [Sizes]
  sizes := rfl
  kSlotSize := rfl
  kMap c us k h := by simp at h
  closed a o h := by simp at h
  slots := ⟨fun _ => bot, fun sl t h => by simp [Owns] at h⟩
  ents _ hk := by simp at hk
  prjs _ hq := by simp at hq
  nidOK := ⟨fun c i h => by simp at h, fun c c' i h => by simp at h⟩
  rowsDisj k _ _ h := by obtain ⟨_, _, _, _, _, _, _, _, _, hi, -⟩ := h; simp at hi

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
  entW : ∀ k, P'.entW k = P.entW k
  rulesSize : P.rules.size ≤ P'.rules.size
  row : Sizes P → ∀ r, r < P.rules.size → P'.rowW r = P.rowW r
  prjW : ∀ q, P'.prjW q = P.prjW q
  sizes : Sizes P → Sizes P'
  nids : ∀ (c : Name) (i : Nat), P.nids[c]? = some i → P'.nids[c]? = some i
  flags : P'.flags = P.flags
  site : P'.site = P.site

theorem KeyEq.refl (P : G4Prog) : KeyEq P P :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, Nat.le_refl _, fun _ _ _ => rfl,
    fun _ => rfl, id, fun _ _ h => h, rfl, rfl⟩

theorem KeyEq.trans {P₁ P₂ P₃ : G4Prog} (h₁ : KeyEq P₁ P₂) (h₂ : KeyEq P₂ P₃) : KeyEq P₁ P₃ :=
  ⟨h₂.code.trans h₁.code, h₂.kTag.trans h₁.kTag, h₂.kInfo.trans h₁.kInfo, h₂.kMap.trans h₁.kMap,
    h₂.closedNode.trans h₁.closedNode, h₂.projs.trans h₁.projs, h₂.strs.trans h₁.strs,
    h₂.kSlot.trans h₁.kSlot, h₂.nslots.trans h₁.nslots, fun k => (h₂.entW k).trans (h₁.entW k),
    Nat.le_trans h₁.rulesSize h₂.rulesSize,
    fun hs r hr => (h₂.row (h₁.sizes hs) r (Nat.lt_of_lt_of_le hr h₁.rulesSize)).trans (h₁.row hs r hr),
    fun q => (h₂.prjW q).trans (h₁.prjW q), fun hs => h₂.sizes (h₁.sizes hs),
    fun c i h => h₂.nids c i (h₁.nids c i h),
    h₂.flags.trans h₁.flags, h₂.site.trans h₁.site⟩

theorem KeyEq.ext {P P' : G4Prog} (h : KeyEq P P') (hs : Sizes P) : Ext P P' where
  code i _ := by rw [h.code]
  codeSize := by rw [h.code]; exact Nat.le_refl _
  kInfo i _ := by rw [h.kInfo]
  kInfoSize := by rw [h.kInfo]; exact Nat.le_refl _
  projs i _ := by rw [h.projs]
  strs i _ := by rw [h.strs]
  closedNode a o hh := by rw [h.closedNode]; exact hh
  kSlot i _ := by rw [h.kSlot]
  ent k _ := entR_of_entW (h.entW k)
  rulesSize := h.rulesSize
  row r hr := rowR_of_rowW (h.row hs r hr)
  prj q _ := h.prjW q
  nids := h.nids
  flags := h.flags
  kCode k _ := (entW_eq (h.entW k)).2.1
  ruleCode r hr := (rowW_eq (h.row hs r hr)).2.1
  site := h.site

theorem KeyEq.inv {P P' : G4Prog} (h : KeyEq P P') (hI : Inv find? findProj? P) (hn : NidOK P') :
    Inv find? findProj? P' :=
  hI.ext (h.ext hI.szs) (by rw [h.kTag, h.kInfo]; exact hI.sizes)
    (by rw [h.kSlot, h.kInfo]; exact hI.kSlotSize) h.kMap h.closedNode h.kSlot h.nslots (h.sizes hI.szs)
    (by rw [h.kInfo]) (fun q hq h' => absurd hq (by rw [h.projs]; exact Nat.not_lt.mpr h')) hn

theorem KeyEq.nid (P : G4Prog) (c : Name) : KeyEq P (P.nid c).2 := by
  unfold G4Prog.nid; split
  · exact KeyEq.refl P
  · rename_i hn
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, Nat.le_refl _, fun _ _ _ => rfl,
      fun _ => rfl, id, fun c' i h => ?_, rfl, rfl⟩
    show (P.nids.insert c P.nids.size)[c']? = some i
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i heq; obtain rfl : c = c' := eq_of_beq heq; rw [hn] at h; cases h
    · exact h

theorem nid_eq (P : G4Prog) (c : Name) : (P.nid c).2 = { P with nids := (P.nid c).2.nids } := by
  unfold G4Prog.nid; split <;> rfl

theorem KeyEq.foldl {α : Type} (g : G4Prog → α → G4Prog) (hg : ∀ P x, KeyEq P (g P x)) :
    ∀ (l : List α) (P : G4Prog), KeyEq P (l.foldl g P)
  | [], P => KeyEq.refl P
  | x :: l, P => (hg P x).trans (KeyEq.foldl g hg l (g P x))

/-- Prove the middle conjunct first, then use it. -/
theorem and_mid_first {A B C : Prop} (hb : B) (h : B → A ∧ C) : A ∧ B ∧ C :=
  ⟨(h hb).1, hb, (h hb).2⟩

section
variable (find?) (findProj?)

/-- **A rule row** is its rule. -/
theorem g4RuleRow_spec (isK : Bool) (lps : List Name) (us : List Level) (P : G4Prog) (rl : RecRule)
    (hs : Sizes P) (hn : NidOK P) :
    KeyEq P (g4RuleRow find? isK lps us P rl) ∧
      (g4RuleRow find? isK lps us P rl).rules.size = P.rules.size + 1 ∧
      NidOK (g4RuleRow find? isK lps us P rl) ∧
      RowOK find? (g4RuleRow find? isK lps us P rl) P.rules.size isK lps us rl := by
  have hk := KeyEq.nid P rl.ctor
  have hget := nid_get P rl.ctor
  have hnn := hn.nid rl.ctor
  obtain ⟨-, ⟨h₁, h₂, h₃, h₄, h₅⟩, -⟩ := hs
  unfold g4RuleRow
  dsimp only
  rw [nid_eq P rl.ctor] at hk hget hnn ⊢
  refine ⟨⟨hk.code, hk.kTag, hk.kInfo, hk.kMap, hk.closedNode, hk.projs, hk.strs,
    hk.kSlot, hk.nslots, fun _ => rfl, by simp, fun hs r hr => ?_, fun _ => rfl, fun hs => ?_,
    hk.nids, rfl, rfl⟩, by simp, hnn, ?_⟩
  · obtain ⟨-, ⟨h₁, h₂, h₃, h₄, h₅⟩, -⟩ := hs
    simp only [G4Prog.rowW]
    rw [push_lt hr, push_lt (by omega), push_lt (by omega), push_lt (by omega),
      push_lt (by omega), push_lt (by omega)]
  · obtain ⟨h₀, ⟨h₁, h₂, h₃, h₄, h₅⟩, h₆⟩ := hs
    exact ⟨h₀, ⟨by simp [h₁], by simp [h₂], by simp [h₃], by simp [h₄], by simp [h₅]⟩, h₆⟩
  · refine ⟨?_, ?_, ?_, ?_, ⟨_, hget, ?_⟩, 0, ?_, .inl rfl⟩
    · exact Array.getElem?_push_size
    · show (P.rNF.push _)[P.rules.size]? = _; rw [← h₃]; exact Array.getElem?_push_size
    · show (P.rCP.push _)[P.rules.size]? = _; rw [← h₄]; exact Array.getElem?_push_size
    · show (P.rC3.push _)[P.rules.size]? = _; rw [← h₅]; exact Array.getElem?_push_size
    · show (P.rNid.push _)[P.rules.size]? = _; rw [← h₂]; exact Array.getElem?_push_size
    · show (P.ruleCode.push _)[P.rules.size]? = _; rw [← h₁]; exact Array.getElem?_push_size

/-- The rule fold of a new recursor entry: each new row is its rule. -/
theorem rows_fold (g : G4Prog → RecRule → G4Prog) {isK : Bool} {lps : List Name} {us : List Level}
    (hg : ∀ P rl, Sizes P → NidOK P → KeyEq P (g P rl) ∧ (g P rl).rules.size = P.rules.size + 1 ∧
      NidOK (g P rl) ∧ RowOK find? (g P rl) P.rules.size isK lps us rl) :
    ∀ (l : List RecRule) (P : G4Prog), Sizes P → NidOK P →
      KeyEq P (l.foldl g P) ∧ (l.foldl g P).rules.size = P.rules.size + l.length ∧
        NidOK (l.foldl g P) ∧
        ∀ i (h : i < l.length), RowOK find? (l.foldl g P) (P.rules.size + i) isK lps us l[i]
  | [], P, _, hn => ⟨KeyEq.refl P, rfl, hn, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | x :: l, P, hs, hn => by
    obtain ⟨k₁, s₁, n₁, r₁⟩ := hg P x hs hn
    obtain ⟨k₂, s₂, n₂, r₂⟩ := rows_fold g hg l (g P x) (k₁.sizes hs) n₁
    refine ⟨k₁.trans k₂, by simp only [List.foldl_cons, List.length_cons]; omega, n₂, fun i hi => ?_⟩
    cases i with
    | zero => exact r₁.ext (k₂.ext (k₁.sizes hs)) (by omega)
    | succ i =>
      have := r₂ i (by simpa using hi)
      rw [s₁, show P.rules.size + 1 + i = P.rules.size + (i + 1) by omega] at this
      exact this

/-- **A new entry** denotes its constant and is the declaration it names. -/
theorem g4Entry_spec (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : Inv find? findProj? P)
    (hkf : ∀ cv mI rP isK rules, find? c = some (.recInfo cv mI rP isK rules) →
      KfabOK P mI isK rules kfab) :
    Inv find? findProj? (g4Entry find? P c us kfab).2 ∧ Ext P (g4Entry find? P c us kfab).2 ∧
      (g4Entry find? P c us kfab).2.closedNode = P.closedNode ∧
      ∃ info, (g4Entry find? P c us kfab).2.kInfo[(g4Entry find? P c us kfab).1]? = some info ∧
        Approx (infoTerm info) (.const c us) := by
  unfold g4Entry
  split
  rename_i tag ar b c' d e' info P' hm
  have key : KeyEq P P' ∧ Approx (infoTerm info) (.const c us) ∧ NidOK P' ∧
      (∀ c lps us mI rP base nr isK isEta, info = .recr c lps us mI rP base nr isK isEta →
        P.rules.size ≤ base) ∧
      ∀ (k : Nat) (Q : G4Prog), Ext P' Q → Q.kInfo[k]? = some info → Q.kTag[k]? = some tag →
        Q.kCode[k]? = some 0 → Q.kArity[k]? = some ar → Q.kB[k]? = some b → Q.kC[k]? = some c' →
        Q.kD[k]? = some d → Q.kE[k]? = some e' → EntOK find? Q k := by
    have neu : ∀ (k : Nat) (Q : G4Prog), Q.kInfo[k]? = some (.neutral c us) → Q.kTag[k]? = some 5 →
        EntOK find? Q k := fun k Q hi ht => by unfold EntOK; rw [hi]; exact ht
    revert hm
    cases hf : find? c with
    | none =>
      intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨KeyEq.refl P, Approx.refl _, hI.nidOK, fun _ _ _ _ _ _ _ _ _ h => (nomatch h),
            fun k Q _ hi ht _ _ _ _ _ _ => neu k Q hi ht⟩
    | some ci =>
      cases ci with
      | defnInfo cv v hh =>
        dsimp only
        split
        · intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
          exact ⟨KeyEq.refl P, Approx.refl _, hI.nidOK, fun _ _ _ _ _ _ _ _ _ h => (nomatch h),
            fun k Q _ hi ht _ _ _ _ _ _ => neu k Q hi ht⟩
        · rename_i hlen
          intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
          refine ⟨KeyEq.refl P, Approx.refl _, hI.nidOK, fun _ _ _ _ _ _ _ _ _ h => (nomatch h),
            fun k Q hQ hi ht hc _ _ _ _ he => ?_⟩
          unfold EntOK; rw [hi]; dsimp only; unfold DefnOK
          rw [ht, hc, he, hQ.natOk]
          refine ⟨⟨cv, hh, hf, rfl⟩, by simpa using hlen, ?_, 0, rfl, .inl rfl⟩
          split
          · rename_i hcond
            simp only [Bool.and_eq_true, List.isEmpty_iff] at hcond
            exact .inr ⟨rfl, hcond.1.1, hcond.1.2, hcond.2, rfl⟩
          · exact .inl rfl
      | ctorInfo cv nP nF =>
        dsimp only
        intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
        refine ⟨KeyEq.nid P c, Approx.refl _, hI.nidOK.nid c, fun _ _ _ _ _ _ _ _ _ h => (nomatch h),
          fun k Q hQ hi ht _ ha hb _ hd _ => ?_⟩
        unfold EntOK; rw [hi]; dsimp only; unfold CtorOK
        exact ⟨⟨cv, hf, ha⟩, ht, ⟨_, hQ.nids _ _ (nid_get P c), hb⟩, hd⟩
      | recInfo cv mI rP isK rules =>
        dsimp only
        split
        · intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
          exact ⟨KeyEq.refl P, Approx.refl _, hI.nidOK, fun _ _ _ _ _ _ _ _ _ h => (nomatch h),
            fun k Q _ hi ht _ _ _ _ _ _ => neu k Q hi ht⟩
        · rename_i hcond
          intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
          have hcond' : us.length = cv.levelParams.length ∧
              (Expr.peelPis (mI + 1) cv.type).isSome = true := by
            simp only [Bool.or_eq_true, not_or] at hcond
            exact ⟨by simpa using hcond.1, Option.isSome_iff_ne_none.mpr (by simpa using hcond.2)⟩
          obtain ⟨hk, hsz, hn, hrows⟩ := rows_fold find? (g4RuleRow find? isK cv.levelParams us)
            (fun P rl hs hn => g4RuleRow_spec find? isK cv.levelParams us P rl hs hn) rules P hI.szs hI.nidOK
          refine ⟨hk, Approx.refl _, hn, fun _ _ _ _ _ _ _ _ _ h => by
              simp only [G4Info.recr.injEq] at h; obtain ⟨-, -, -, -, -, h, -⟩ := h; omega,
            fun k Q hQ hi ht _ ha hb hc hd he => ?_⟩
          unfold EntOK; rw [hi]; dsimp only; unfold RecOK
          refine ⟨cv, rules, hf, rfl, hcond'.1, hcond'.2, ht, ha, hb, hc, hd, rfl, ?_,
            ⟨kfab, he, (hkf cv mI rP isK rules hf).ext ((hk.ext hI.szs).trans hQ).toExtR⟩,
            fun i hi => (hrows i hi).ext hQ (by omega)⟩
          have := hQ.rulesSize; omega
      | _ =>
        intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
        exact ⟨KeyEq.refl P, Approx.refl _, hI.nidOK, fun _ _ _ _ _ _ _ _ _ h => (nomatch h),
            fun k Q _ hi ht _ _ _ _ _ _ => neu k Q hi ht⟩
  obtain ⟨hk, hinfo, hnid, hbase, hent⟩ := key
  have hs : P.kTag.size = P.kInfo.size := hI.sizes
  dsimp only
  have hks : P.kSlot.size = P.kInfo.size := hI.kSlotSize
  obtain ⟨⟨e₁, e₂, e₃, e₄, e₅, e₆⟩, -, -⟩ := hk.sizes hI.szs
  have hkI : P'.kInfo.size = P.kInfo.size := by rw [hk.kInfo]
  have hs' : P'.kTag.size = P'.kInfo.size := by rw [hk.kTag, hk.kInfo]; exact hs
  refine and_mid_first ((hk.ext hI.szs).trans ?hx') (fun hx =>
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun k hk' => ?_, fun q hq => ?_, hnid, ?_⟩, ?_, info, ?_, hinfo⟩)
  · exact ⟨⟨fun _ _ => rfl, Nat.le_refl _,
      fun i hi => show (P'.kInfo.push info)[i]? = P'.kInfo[i]? from push_lt hi,
      by simp, fun _ _ => rfl, fun _ _ => rfl, fun _ _ h => h,
      fun i hi => show (P'.kSlot.push P'.nslots)[i]? = P'.kSlot[i]? from push_lt hi,
      fun i hi => by
        simp only [G4Prog.entR]
        rw [push_lt (by omega), push_lt (by omega), push_lt (by omega), push_lt (by omega),
          push_lt (by omega), push_lt (by omega)],
      Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ h => h, rfl⟩,
      fun i hi => show (P'.kCode.push 0)[i]? = P'.kCode[i]? from push_lt (by omega),
      fun _ _ => rfl, rfl⟩
  · obtain ⟨-, hr, hp⟩ := hk.sizes hI.szs
    exact ⟨⟨by simp [e₁], by simp [e₂], by simp [e₃], by simp [e₄], by simp [e₅], by simp [e₆]⟩, hr, hp⟩
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
    obtain ⟨sa, sl, hsl, hd, ha, hc0⟩ := hI.closed a o (by rw [← hk.closedNode]; exact h)
    exact ⟨sa, sl, hx.code_some hsl, hd.ext hx.toExtR, ha, hc0⟩
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
  · change k < (P'.kInfo.push info).size at hk'
    rw [Array.size_push, hkI] at hk'
    rcases Nat.lt_or_ge k P.kInfo.size with h | h
    · exact (hI.ents k h).ext hx h
    · obtain rfl : k = P.kInfo.size := by omega
      refine hent _ _ ?hx' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · show (P'.kInfo.push info)[P.kInfo.size]? = _; rw [← hkI]; exact Array.getElem?_push_size
      · show (P'.kTag.push tag)[P.kInfo.size]? = _; rw [← hs, ← hk.kTag]; exact Array.getElem?_push_size
      · show (P'.kCode.push 0)[P.kInfo.size]? = _; rw [← hkI, ← e₁]; exact Array.getElem?_push_size
      · show (P'.kArity.push ar)[P.kInfo.size]? = _; rw [← hkI, ← e₂]; exact Array.getElem?_push_size
      · show (P'.kB.push b)[P.kInfo.size]? = _; rw [← hkI, ← e₃]; exact Array.getElem?_push_size
      · show (P'.kC.push c')[P.kInfo.size]? = _; rw [← hkI, ← e₄]; exact Array.getElem?_push_size
      · show (P'.kD.push d)[P.kInfo.size]? = _; rw [← hkI, ← e₅]; exact Array.getElem?_push_size
      · show (P'.kE.push e')[P.kInfo.size]? = _; rw [← hkI, ← e₆]; exact Array.getElem?_push_size
  · have hq' : q < P.projs.size := by
      have : P'.projs = P.projs := hk.projs
      change q < P'.projs.size at hq; rw [this] at hq; exact hq
    exact (hI.prjs q hq').ext hx.toExtR hq'
  · intro k₁ k₂ r h₁ h₂
    have hro : ∀ k, (∃ c lps us' mI rP base nr isK isEta,
        (P'.kInfo.push info)[k]? = some (.recr c lps us' mI rP base nr isK isEta) ∧ base ≤ r ∧
          r < base + nr) → (k < P.kInfo.size ∧ RowsOf P k r) ∨ (k = P.kInfo.size ∧ P.rules.size ≤ r) := by
      intro k ⟨c₁, lps, us', mI, rP, base, nr, isK, isEta, hi, hb₁, hb₂⟩
      rw [Array.getElem?_push] at hi
      split at hi
      · rename_i hkk
        have := hbase _ _ _ _ _ _ _ _ _ (Option.some.inj hi)
        exact .inr ⟨by rw [hkk, hkI], by omega⟩
      · rw [hk.kInfo] at hi
        exact .inl ⟨lt_of_some hi, ⟨_, _, _, _, _, _, _, _, _, hi, hb₁, hb₂⟩⟩
    rcases hro k₁ h₁ with ⟨-, a₁⟩ | ⟨e₁, b₁⟩ <;> rcases hro k₂ h₂ with ⟨-, a₂⟩ | ⟨e₂, b₂⟩
    · exact hI.rowsDisj k₁ k₂ r a₁ a₂
    · have := hI.rows_lt a₁; omega
    · have := hI.rows_lt a₂; omega
    · omega
  · exact hk.closedNode
  · show (P'.kInfo.push info)[P.kTag.size]? = some info
    rw [hk.kInfo, hI.sizes]; exact Array.getElem?_push_size

/-- The entry spec, composed with a program step before it. -/
theorem g4Entry_after {P Pm : G4Prog} (c : Name) (us : List Level) (kfab : Nat) (hI : Inv find? findProj? Pm)
    (hx : Ext P Pm) (hcl : Pm.closedNode = P.closedNode)
    (hkf : ∀ cv mI rP isK rules, find? c = some (.recInfo cv mI rP isK rules) →
      KfabOK Pm mI isK rules kfab) :
    Inv find? findProj? (g4Entry find? Pm c us kfab).2 ∧ Ext P (g4Entry find? Pm c us kfab).2 ∧
      (g4Entry find? Pm c us kfab).2.closedNode = P.closedNode ∧
      ∃ info, (g4Entry find? Pm c us kfab).2.kInfo[(g4Entry find? Pm c us kfab).1]? = some info ∧
        Approx (infoTerm info) (.const c us) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := g4Entry_spec find? findProj? Pm c us kfab hI hkf
  exact ⟨h₁, hx.trans h₂, h₃.trans hcl, h₄⟩

/-- **Resolution** returns an entry that denotes the constant. -/
theorem g4ResolveF_spec : ∀ (fuel : Nat) (P : G4Prog) (c : Name) (us : List Level), Inv find? findProj? P →
    Inv find? findProj? (g4ResolveF find? findProj? fuel P c us).2 ∧ Ext P (g4ResolveF find? findProj? fuel P c us).2 ∧
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
    · exact g4Entry_after find? findProj? c us 0 hI (Ext.refl P) rfl (fun _ _ _ _ _ _ => .inl rfl)
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
          · rename_i f' cv mI rP rl hf hfind _ _ cvj _ _
            obtain rfl : f = f' := Nat.succ.inj hf
            obtain ⟨h₁, h₂, h₃, info, hinfo, -⟩ := ih P rl.ctor (gCmpLevels rl cv.levelParams us cvj.levelParams) hI
            generalize g4ResolveF find? findProj? f P rl.ctor (gCmpLevels rl cv.levelParams us cvj.levelParams) = r
              at h₁ h₂ h₃ hinfo ⊢
            obtain ⟨kc, P₁⟩ := r
            dsimp only at h₁ h₂ h₃ hinfo ⊢
            split
            · rename_i hc
              refine g4Entry_after find? findProj? c us _ h₁ h₂ h₃ (fun cv' mI' rP' isK' rules' hf' => ?_)
              rw [hfind] at hf'; cases hf'
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
              have hlt : kc < P₁.kInfo.size := lt_of_some hinfo
              exact .inr ⟨kc, rl, rfl, hlt,
                ⟨_, some_of_lt (by rw [h₁.szs.1.2.1]; exact hlt), hc.2⟩, rfl, rfl, hc.1⟩
            · exact g4Entry_after find? findProj? c us _ h₁ h₂ h₃ (fun _ _ _ _ _ _ => .inl rfl)
          · exact g4Entry_after find? findProj? c us 0 hI (Ext.refl P) rfl (fun _ _ _ _ _ _ => .inl rfl)
        · exact g4Entry_after find? findProj? c us 0 hI (Ext.refl P) rfl (fun _ _ _ _ _ _ => .inl rfl)
      · exact g4Entry_after find? findProj? c us 0 hI (Ext.refl P) rfl (fun _ _ _ _ _ _ => .inl rfl)

theorem g4Resolve_spec (P : G4Prog) (c : Name) (us : List Level) (hI : Inv find? findProj? P) :
    Inv find? findProj? (g4Resolve find? findProj? P c us).2 ∧ Ext P (g4Resolve find? findProj? P c us).2 ∧
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
@[expose] def CompOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (e : Expr) (r : Nat × G4Prog) : Prop :=
  Inv find? findProj? r.2 ∧ Ext P r.2 ∧ ∃ s, Den r.2 r.1 s ∧ Approx s e

theorem CompOK.neutral {P : G4Prog} (hI : Inv find? findProj? P) (e : Expr) :
    CompOK find? findProj? P e (P.code.size, P.emit (fun c => c.push 8)) := by
  rw [emit_append1]
  refine ⟨hI.emit _, Ext.emit P _, bot, .neutral ?_, .bot e⟩
  show (P.code ++ #[8])[P.code.size]? = some 8
  rw [rd0]; rfl

section
variable (find?) (findProj?)

theorem Den.lt_size {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) : o < P.code.size := by
  obtain ⟨x, hx⟩ := h.tag
  rcases Nat.lt_or_ge o P.code.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at hx; cases hx

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
  exact ⟨Nat.lt_of_lt_of_le hlt hx.codeSize, s, hd.ext hx.toExtR, ha⟩

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
variable (find?) (findProj?)

theorem CompOK.step {P P' : G4Prog} {e : Expr} {r : Nat × G4Prog} (h : CompOK find? findProj? P' e r)
    (hs : Ext P P') : CompOK find? findProj? P e r :=
  ⟨h.1, hs.trans h.2.1, h.2.2⟩

theorem proj_emit_ok {P P₁ Q : G4Prog} {sn : Name} {i so : Nat} {e se : Expr} {pj : G4Proj}
    (hI₁ : Inv find? findProj? P₁) (hx₁ : Ext P P₁) (hde : Den P₁ so se) (hae : Approx se e)
    (hc : Q.code = P₁.code) (ht : Q.kTag = P₁.kTag) (hi : Q.kInfo = P₁.kInfo)
    (hm : Q.kMap = P₁.kMap) (hcl : Q.closedNode = P₁.closedNode) (hs : Q.strs = P₁.strs)
    (hks : Q.kSlot = P₁.kSlot) (hn : Q.nslots = P₁.nslots) (hp : Q.projs = P₁.projs.push pj) (hsn : pj.sn = sn) (hidx : pj.idx = i) (q : Nat)
    (hq : q = P₁.projs.size) (he : ∀ k, Q.entW k = P₁.entW k) (hrow : ∀ r, Q.rowW r = P₁.rowW r)
    (hrs : Q.rules.size = P₁.rules.size) (hprj : ∀ q', q' < P₁.projs.size → Q.prjW q' = P₁.prjW q')
    (hnid : ∀ (c : Name) (i : Nat), P₁.nids[c]? = some i → Q.nids[c]? = some i) (hfl : Q.flags = P₁.flags)
    (hep : Q.site = P₁.site)
    (hszQ : Sizes Q) (hpq : PrjOK findProj? Q q) (hnQ : NidOK Q) :
    CompOK find? findProj? P (.proj sn i e) (Q.code.size, Q.emit (fun c => ((c.push 7).push (q + 1)).push so)) := by
  rw [emit_append3]
  have hx : Ext P₁ (Q.emit (· ++ #[7, q + 1, so])) := by
    refine ⟨⟨fun j hj => ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, fun j hj => ?_,
      fun a o h => ?_, fun j hj => ?_, fun k _ => entR_of_entW (he k), by rw [← hrs]; exact Nat.le_refl _,
      fun r _ => rowR_of_rowW (hrow r), hprj, hnid, hfl⟩, fun k _ => (entW_eq (he k)).2.1,
      fun r _ => (rowW_eq (hrow r)).2.1, hep⟩
    · show (Q.code ++ _)[j]? = _; rw [hc, rdL _ hj]
    · show P₁.code.size ≤ (Q.code ++ _).size; rw [hc]; simp
    · show Q.kInfo[j]? = _; rw [hi]
    · show P₁.kInfo.size ≤ Q.kInfo.size; rw [hi]; exact Nat.le_refl _
    · show Q.projs[j]? = _; rw [hp]; exact push_lt hj
    · show Q.strs[j]? = _; rw [hs]
    · show Q.closedNode[a]? = _; rw [hcl]; exact h
    · show Q.kSlot[j]? = _; rw [hks]
  refine ⟨hI₁.ext hx (by show Q.kTag.size = Q.kInfo.size; rw [ht, hi]; exact hI₁.sizes)
    (by show Q.kSlot.size = Q.kInfo.size; rw [hks, hi]; exact hI₁.kSlotSize) hm hcl hks hn hszQ
    (by show Q.kInfo.size = _; rw [hi])
    (fun q' hq' hge => by
      obtain rfl : q' = q := by
        change q' < Q.projs.size at hq'; rw [hp, Array.size_push] at hq'; omega
      exact hpq) hnQ, hx₁.trans hx, _,
    .proj (q := q) (pj := pj) ?_ ?_ ?_ ?_ (Nat.lt_of_lt_of_le hde.lt_size (by rw [hc]; exact Nat.le_refl _))
      (hde.ext hx.toExtR), ?_⟩
  · show (Q.code ++ _)[Q.code.size]? = _; rw [rd0]; rfl
  · show (Q.code ++ _)[Q.code.size + 1]? = _; rw [rdR]; rfl
  · show Q.projs[q]? = some pj; rw [hp, hq]; exact Array.getElem?_push_size
  · show (Q.code ++ _)[Q.code.size + 2]? = _; rw [rdR]; rfl
  · rw [← hsn, ← hidx]; exact .proj hae

theorem g4MaskOf_key (P : G4Prog) (hd : Expr) : KeyEq P (g4MaskOf find? P hd).2 := by
  unfold g4MaskOf; split
  · split
    · exact KeyEq.refl P
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, Nat.le_refl _, fun _ _ _ => rfl,
        fun _ => rfl, id, fun _ _ h => h, rfl, rfl⟩
  · exact KeyEq.refl P

theorem g4MaskOf_nids (P : G4Prog) (hd : Expr) : (g4MaskOf find? P hd).2.nids = P.nids := by
  unfold g4MaskOf; split
  · split <;> rfl
  · rfl

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
theorem g4ArgStep_spec {α : Type} (ev : α → Expr) (compArg : G4Prog → α → Nat × G4Prog)
    (harg : ∀ P a, Inv find? findProj? P → CompOK find? findProj? P (ev a) (compArg P a)) (mask : Array Bool)
    {P₁ : G4Prog} (acc : Array Nat × G4Prog) (done : List Expr) (a : α)
    (h₁ : Inv find? findProj? acc.2) (h₂ : Ext P₁ acc.2) (h₃ : ArgsOK acc.2 acc.1 done) :
    Inv find? findProj? (g4ArgStep compArg mask acc a).2 ∧ Ext P₁ (g4ArgStep compArg mask acc a).2 ∧
      ArgsOK (g4ArgStep compArg mask acc a).2 (g4ArgStep compArg mask acc a).1
        (done ++ [ev a]) := by
  unfold g4ArgStep
  split
  · dsimp only
    rw [emit_append1]
    have hx := Ext.emit acc.2 #[8]
    refine ⟨h₁.emit _, h₂.trans hx, (h₃.ext hx).push (by simp [G4Prog.emit]) (.neutral ?_) (.bot (ev a))⟩
    show (acc.2.code ++ #[8])[acc.2.code.size]? = some 8; rw [rd0]; rfl
  · obtain ⟨hI', hx', s, hd, ha⟩ := harg acc.2 a h₁
    generalize compArg acc.2 a = r at hI' hx' hd ⊢
    obtain ⟨ao, P'⟩ := r
    dsimp only at hI' hx' hd ⊢
    exact ⟨hI', h₂.trans hx', (h₃.ext hx').push hd.lt_size hd ha⟩

theorem g4ArgFold_spec {α : Type} (ev : α → Expr) (compArg : G4Prog → α → Nat × G4Prog)
    (harg : ∀ P a, Inv find? findProj? P → CompOK find? findProj? P (ev a) (compArg P a)) (mask : Array Bool)
    {P₁ : G4Prog} : ∀ (l : List α) (acc : Array Nat × G4Prog) (done : List Expr),
      Inv find? findProj? acc.2 → Ext P₁ acc.2 → ArgsOK acc.2 acc.1 done →
      Inv find? findProj? (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        Ext P₁ (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        ArgsOK (l.foldl (g4ArgStep compArg mask) acc).2
          (l.foldl (g4ArgStep compArg mask) acc).1 (done ++ l.map ev)
  | [], acc, done, h₁, h₂, h₃ => by simpa using ⟨h₁, h₂, h₃⟩
  | a :: l, acc, done, h₁, h₂, h₃ => by
    obtain ⟨h₁', h₂', h₃'⟩ := g4ArgStep_spec find? findProj? ev compArg harg mask acc done a h₁ h₂ h₃
    have := g4ArgFold_spec ev compArg harg mask l _ _ h₁' h₂' h₃'
    simpa using this

/-- **A spine** compiled by compilers that keep the promise keeps it. -/
theorem g4CompSpine_spec {α : Type} (ev : α → Expr) (hd : Expr) (comp : G4Prog → Nat × G4Prog)
    (compArg : G4Prog → α → Nat × G4Prog)
    (hcomp : ∀ P, Inv find? findProj? P → CompOK find? findProj? P hd (comp P))
    (harg : ∀ P a, Inv find? findProj? P → CompOK find? findProj? P (ev a) (compArg P a))
    (P : G4Prog) (args : List α) (mask : Array Bool) (hI : Inv find? findProj? P) :
    CompOK find? findProj? P (Expr.mkAppN hd (args.map ev)) (g4CompSpine comp compArg P args mask) := by
  unfold g4CompSpine
  obtain ⟨hI₁, hx₁, sh, hdh, hah⟩ := hcomp P hI
  generalize comp P = r at hI₁ hx₁ hdh ⊢
  obtain ⟨ho, P₁⟩ := r
  dsimp only at hI₁ hx₁ hdh ⊢
  obtain ⟨hI₂, hx₂, hargs⟩ := g4ArgFold_spec find? findProj? ev compArg harg mask (P₁ := P₁) args (#[], P₁) []
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
    (Nat.lt_of_lt_of_le hdh.lt_size hx₂.codeSize) ((hdh.ext hx₂.toExtR).ext hx.toExtR) hds,
    Approx.mkAppN hah hass⟩
  · show (P₂.code ++ _)[P₂.code.size]? = _
    rw [rd0, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 1]? = _
    rw [rdR, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 2]? = _
    rw [rdR, Array.getElem?_append_left (by simp)]; rfl

theorem closed_of_bvarBRaw {a : Expr} (h : a.bvarBRaw = 0) : a.looseBVarsBounded 0 = true :=
  Expr.looseBVarsBounded_iff.mpr (by
    rw [← Expr.bvarBRaw_exact a (by rw [h]; unfold satRange; omega)]; omega)

/-- **A shared closed argument** keeps the promise. -/
theorem g4CompShared_spec (a : Expr) (comp : G4Prog → Nat × G4Prog)
    (hcomp : ∀ P, Inv find? findProj? P → CompOK find? findProj? P a (comp P)) (P : G4Prog) (hI : Inv find? findProj? P) :
    CompOK find? findProj? P a (g4CompShared comp P a) := by
  unfold g4CompShared
  split
  · rename_i hbr
    split
    · rename_i o ho
      obtain ⟨s, -, -, hd, ha, -⟩ := hI.closed a o ho
      exact ⟨hI, Ext.refl P, s, hd, ha⟩
    · obtain ⟨hI₁, hx₁, s, hd, ha⟩ := hcomp P hI
      generalize comp P = r at hI₁ hx₁ hd ⊢
      obtain ⟨ao, P₁⟩ := r
      dsimp only at hI₁ hx₁ hd ⊢
      split
      · rename_i o ho
        obtain ⟨s', -, -, hd', ha', -⟩ := hI₁.closed a o ho
        exact ⟨hI₁, hx₁, s', hd', ha'⟩
      rename_i hnone
      rw [emit_append3]
      have hx : Ext P₁ { { (P₁.emit (· ++ #[9, P₁.nslots, ao])) with nslots := P₁.nslots + 1 } with
          closedNode := P₁.closedNode.insert a P₁.code.size } := by
        refine ⟨⟨fun i hi => rdL _ hi, by simp [G4Prog.emit], fun _ _ => rfl, Nat.le_refl _,
          fun _ _ => rfl, fun _ _ => rfl, fun a' o h => ?_, fun _ _ => rfl, fun _ _ => rfl,
          Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ h => h, rfl⟩, fun _ _ => rfl,
          fun _ _ => rfl, rfl⟩
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
        refine .shared (sl := P₁.nslots) ?_ hc1 ?_ hd.lt_size (hd.ext hx.toExtR) ⟨a, hreg⟩
        · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
        · show (P₁.code ++ _)[P₁.code.size + 2]? = _; rw [rdR]; rfl
      refine ⟨⟨hI₁.szs, hI₁.sizes, hI₁.kSlotSize, fun c us k h => ?_, fun a' o h => ?_, ?_,
        fun k hk => (hI₁.ents k hk).ext hx hk, fun q hq => (hI₁.prjs q hq).ext hx.toExtR hq, hI₁.nidOK,
        fun k k' r h h' => hI₁.rowsDisj k k' r (h.back hx.toExtR rfl) (h'.back hx.toExtR rfl)⟩,
        hx₁.trans hx, s,
        hden, ha⟩
      · obtain ⟨info, hi, ha'⟩ := hI₁.kMap c us k h; exact ⟨info, hi, ha'⟩
      · change (P₁.closedNode.insert a P₁.code.size)[a']? = some o at h
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i heq
          obtain rfl := Option.some.inj h
          obtain rfl : a = a' := eq_of_beq heq
          exact ⟨s, P₁.nslots, hc1, hden, ha, closed_of_bvarBRaw (by simpa using hbr)⟩
        · obtain ⟨sa, sl, hsl, hd', ha', hc0⟩ := hI₁.closed a' o h
          exact ⟨sa, sl, hx.code_some hsl, hd'.ext hx.toExtR, ha', hc0⟩
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
  · exact hcomp P hI

/-- **The compiler is correct up to erasure**: the node it returns denotes a
term approximating the one it compiled, in a program that extends the one
it was given, with the invariant kept. -/
theorem g4Comp_spec_lt : ∀ (n : Nat),
    (∀ (P : G4Prog) (e : Expr), sizeOf e < n → Inv find? findProj? P →
      CompOK find? findProj? P e (g4Comp find? findProj? P e)) ∧
    (∀ (P : G4Prog) (a : Expr), sizeOf a < n → Inv find? findProj? P →
      CompOK find? findProj? P a (g4CompArg find? findProj? P a)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ihC, ihA⟩ := ih
    have hC : ∀ (P : G4Prog) (e : Expr), sizeOf e < n + 1 → Inv find? findProj? P →
        CompOK find? findProj? P e (g4Comp find? findProj? P e) := by
      intro P e hs hI
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
            ⟨⟨(Ext.emit P _).code, (Ext.emit P _).codeSize, fun _ _ => rfl, Nat.le_refl _,
              fun _ _ => rfl, fun i hi => push_lt hi, fun _ _ h => h, fun _ _ => rfl, fun _ _ => rfl,
              Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl, fun _ _ h => h, rfl⟩, fun _ _ => rfl,
              fun _ _ => rfl, rfl⟩
          refine ⟨hI.ext hx hI.sizes hI.kSlotSize rfl rfl rfl rfl hI.szs rfl
              (fun _ hq h => absurd hq (Nat.not_lt.mpr h)) hI.nidOK, hx, _,
            .strLit (si := P.strs.size) ?_ ?_ ?_, Approx.refl _⟩
          · show (P.code ++ #[6, P.strs.size])[P.code.size]? = some 6; rw [rd0]; rfl
          · show (P.code ++ #[6, P.strs.size])[P.code.size + 1]? = some P.strs.size; rw [rdR]; rfl
          · show (P.strs.push str)[P.strs.size]? = some str; exact Array.getElem?_push_size
      | lam ty b =>
        unfold g4Comp; dsimp only
        obtain ⟨hI₁, hx₁, sb, hdb, hab⟩ := ihC P b (by simp only [Expr.lam.sizeOf_spec] at hs; omega) hI
        generalize g4Comp find? findProj? P b = r at hI₁ hx₁ hdb ⊢
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
            (hdb.ext hx.toExtR) (.inl ⟨?_, ?_, ?_, ?_⟩), .lam (.bot _) hab⟩
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
            (hdb.ext hx.toExtR) (.inr ⟨?_, rfl, rfl⟩), .lam (.bot _) hab⟩
          · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 2]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 3]? = _; rw [rdR]; rfl
          · rw [hx.code bo hbo, some_of_lt hbo]
            intro h; apply h2; rw [Option.some.inj h]; rfl
      | letE ty v b =>
        unfold g4Comp; dsimp only
        obtain ⟨hI₁, hx₁, sv, hdv, hav⟩ := ihA P v (by simp only [Expr.letE.sizeOf_spec] at hs; omega) hI
        generalize g4CompArg find? findProj? P v = r at hI₁ hx₁ hdv ⊢
        obtain ⟨vo, P₁⟩ := r
        dsimp only at hI₁ hx₁ hdv ⊢
        obtain ⟨hI₂, hx₂, sb, hdb, hab⟩ := ihC P₁ b (by simp only [Expr.letE.sizeOf_spec] at hs; omega) hI₁
        generalize g4Comp find? findProj? P₁ b = r at hI₂ hx₂ hdb ⊢
        obtain ⟨bo, P₂⟩ := r
        dsimp only at hI₂ hx₂ hdb ⊢
        rw [emit_append3]
        have hx := Ext.emit P₂ #[3, vo, bo]
        refine ⟨hI₂.emit _, hx₁.trans (hx₂.trans hx), _,
          .letE ?_ ?_ ?_ (Nat.lt_of_lt_of_le hdv.lt_size hx₂.codeSize) hdb.lt_size
            ((hdv.ext hx₂.toExtR).ext hx.toExtR) (hdb.ext hx.toExtR), .letE (.bot _) hav hab⟩
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
          obtain ⟨hI₁, hx₁, se, hde, hae⟩ := ihC P e (by simp only [Expr.proj.sizeOf_spec] at hs; omega) hI
          generalize g4Comp find? findProj? P e = r at hI₁ hx₁ hde ⊢
          obtain ⟨so, P₁⟩ := r
          dsimp only at hI₁ hx₁ hde ⊢
          generalize hn : P₁.nid en.ctor = rn
          obtain ⟨ni, P₂⟩ := rn
          have hk : KeyEq P₁ P₂ := by have := KeyEq.nid P₁ en.ctor; rw [hn] at this; exact this
          have hP₂ : P₂ = { P₁ with nids := P₂.nids } := by
            rw [show P₂ = (P₁.nid en.ctor).2 by rw [hn]]; exact nid_eq P₁ en.ctor
          dsimp only
          refine proj_emit_ok find? findProj? (pj := ⟨sn, en.ctor, i, en.numParams, en.numFields,
              en.levelParams.length, true, en⟩) (sn := sn) (i := i) hI₁ hx₁ hde hae ?_ ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ rfl rfl _ ?_ (fun k => hk.entW k) ?_ ?_ ?_ hk.nids ?_ ?_ ?_ ?_ ?_
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
          · intro r; rw [hP₂]; rfl
          · rw [hP₂]
          · intro q' hq'
            obtain ⟨-, -, ⟨p₁, p₂, p₃, p₄, p₅, p₆⟩⟩ := hI₁.szs
            rw [hP₂]; simp only [G4Prog.prjW]
            rw [push_lt (by omega), push_lt (by omega), push_lt (by omega), push_lt (by omega),
              push_lt (by omega), push_lt (by omega)]
          · rw [hP₂]; rfl
          · rw [hP₂]; rfl
          · obtain ⟨a, b, ⟨p₁, p₂, p₃, p₄, p₅, p₆⟩⟩ := hI₁.szs
            rw [hP₂]
            exact ⟨a, b, by simp [p₁], by simp [p₂], by simp [p₃], by simp [p₄], by simp [p₅], by simp [p₆]⟩
          · have hget := nid_get P₁ en.ctor
            rw [hn] at hget
            obtain ⟨-, -, ⟨p₁, p₂, p₃, p₄, p₅, p₆⟩⟩ := hI₁.szs
            have e₀ : P₂.projs = P₁.projs := hk.projs
            have e₁ : P₂.pNid = P₁.pNid := by rw [hP₂]
            have e₂ : P₂.pIdx = P₁.pIdx := by rw [hP₂]
            have e₃ : P₂.pNP = P₁.pNP := by rw [hP₂]
            have e₄ : P₂.pNF = P₁.pNF := by rw [hP₂]
            have e₅ : P₂.pNl = P₁.pNl := by rw [hP₂]
            have e₆ : P₂.pAlw = P₁.pAlw := by rw [hP₂]
            refine ⟨sn, i, en, Array.getElem?_push_size, by assumption, ⟨ni, hget, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
            · show (P₂.pNid.push ni)[P₂.projs.size]? = _; rw [e₀, e₁, ← p₁]; exact Array.getElem?_push_size
            · show (P₂.pIdx.push i)[P₂.projs.size]? = _; rw [e₀, e₂, ← p₂]; exact Array.getElem?_push_size
            · show (P₂.pNP.push _)[P₂.projs.size]? = _; rw [e₀, e₃, ← p₃]; exact Array.getElem?_push_size
            · show (P₂.pNF.push _)[P₂.projs.size]? = _; rw [e₀, e₄, ← p₄]; exact Array.getElem?_push_size
            · show (P₂.pNl.push _)[P₂.projs.size]? = _; rw [e₀, e₅, ← p₅]; exact Array.getElem?_push_size
            · show (P₂.pAlw.push _)[P₂.projs.size]? = _; rw [e₀, e₆, ← p₆]; exact Array.getElem?_push_size
          · have := hI₁.nidOK.nid en.ctor; rw [hn] at this; exact this
        · exact CompOK.neutral hI _
      | app fn arg =>
        unfold g4Comp; dsimp only
        have hk₁ := g4MaskOf_key find? P (Expr.app fn arg).getAppFn
        have hn₁ := g4MaskOf_nids find? P (Expr.app fn arg).getAppFn
        generalize g4MaskOf find? P (Expr.app fn arg).getAppFn = r at hk₁ hn₁ ⊢
        obtain ⟨mask, P₁⟩ := r
        dsimp only at hk₁ ⊢
        have hsf := Expr.sizeOf_getAppFn_le fn
        simp only [Expr.app.sizeOf_spec] at hs
        have := g4CompSpine_spec find? findProj? Subtype.val (Expr.app fn arg).getAppFn
          (fun P => g4Comp find? findProj? P (Expr.app fn arg).getAppFn)
          (fun P (a : {a // a ∈ (Expr.app fn arg).getAppArgs}) => g4CompArg find? findProj? P a.1)
          (fun P hI => ihC P _ (by simp only [Expr.getAppFn]; omega) hI)
          (fun P a hI => ihA P a.1 (by
            have := Expr.sizeOf_lt_of_mem_getAppArgs a.2
            simp only [Expr.app.sizeOf_spec] at this; omega) hI) P₁
          (Expr.app fn arg).getAppArgs.attach mask (hk₁.inv hI (by unfold NidOK; rw [hn₁]; exact hI.nidOK))
        rw [List.attach_map_subtype_val, mkAppN_getApp'] at this
        exact CompOK.step find? findProj? this (hk₁.ext hI.szs)
    refine ⟨hC, fun P a hs hI => ?_⟩
    have hdef : CompOK find? findProj? P a (g4Comp find? findProj? P a) := hC P a hs hI
    unfold g4CompArg
    split
    all_goals first
      | exact g4CompShared_spec find? findProj? _ _ (fun P hI => hC P _ (by assumption) hI) P hI
      | exact hdef

/-- **The compiler is correct up to erasure** (`g4Comp_spec_lt` at the term's size). -/
theorem g4Comp_spec (P : G4Prog) (e : Expr) (hI : Inv find? findProj? P) :
    CompOK find? findProj? P e (g4Comp find? findProj? P e) :=
  (g4Comp_spec_lt find? findProj? (sizeOf e + 1)).1 P e (Nat.lt_succ_self _) hI

end

/-! ## The run's code stores

The run compiles a definition's body or a rule's right-hand side on first
use and stores the node in `kCode` / `ruleCode`.  That is not an `Ext` (the
column changes at an old index), but it is an `ExtR` both ways, and the
invariant holds after it when the stored word is right. -/

theorem set!_get?_self {a : Array Nat} {i w : Nat} (h : i < a.size) : (a.set! i w)[i]? = some w := by
  simp [Array.set!_eq_setIfInBounds, h]

theorem set!_get?_ne {a : Array Nat} {i j w : Nat} (h : j ≠ i) : (a.set! i w)[j]? = a[j]? := by
  simp [Array.set!_eq_setIfInBounds, Ne.symm h]

/-- Storing compiled-body words is growth up to the code columns. -/
theorem ExtR.codes (P : G4Prog) (a b : Array Nat) : ExtR P { P with kCode := a, ruleCode := b } :=
  ⟨fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, fun _ _ => rfl, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, rfl⟩

/-- And back. -/
theorem ExtR.codes_back (P : G4Prog) (a b : Array Nat) : ExtR { P with kCode := a, ruleCode := b } P :=
  ⟨fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, fun _ _ => rfl, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ h => h, rfl⟩

/-- **The invariant after a code store**: every entry is still the
declaration it names. -/
theorem Inv.codes {P : G4Prog} (hI : Inv find? findProj? P) {a b : Array Nat} (ha : a.size = P.kCode.size)
    (hb : b.size = P.ruleCode.size)
    (hent : ∀ k, k < P.kInfo.size → EntOK find? { P with kCode := a, ruleCode := b } k) :
    Inv find? findProj? { P with kCode := a, ruleCode := b } where
  szs := by
    obtain ⟨⟨e₁, e₂⟩, ⟨r₁, r₂⟩, e₃⟩ := hI.szs
    exact ⟨⟨by rw [← e₁]; exact ha, e₂⟩, ⟨by rw [← r₁]; exact hb, r₂⟩, e₃⟩
  sizes := hI.sizes
  kSlotSize := hI.kSlotSize
  kMap := hI.kMap
  closed a' o h := by
    obtain ⟨s, sl, h₁, h₂, h₃, h₄⟩ := hI.closed a' o h
    exact ⟨s, sl, h₁, h₂.ext (ExtR.codes P a b), h₃, h₄⟩
  slots := by
    obtain ⟨σ, hσ⟩ := hI.slots
    exact ⟨σ, fun sl t h => hσ sl t (h.ext (ExtR.codes_back P a b))⟩
  ents := hent
  prjs q hq := (hI.prjs q hq).ext (ExtR.codes P a b) hq
  nidOK := hI.nidOK
  rowsDisj k k' r h h' := hI.rowsDisj k k' r h h'

/-- **The δ store**: a definition entry's compiled body. -/
theorem Inv.setKCode {P : G4Prog} (hI : Inv find? findProj? P) {k o : Nat} {s : Expr} {c : Name}
    {lps : List Name} {us : List Level} {v : Expr} (hi : P.kInfo[k]? = some (.defn c lps us v))
    (hd : Den P o s) (ha : Approx s (v.instantiateLevelParams lps us)) :
    Inv find? findProj? { P with kCode := P.kCode.set! k (o + 1) } := by
  have hk : k < P.kInfo.size := lt_of_some hi
  have hks : k < P.kCode.size := by rw [hI.szs.1.1]; exact hk
  refine hI.codes (b := P.ruleCode) (by simp) rfl (fun j hj => ?_)
  by_cases hjk : j = k
  · subst hjk
    have h := hI.ents j hj
    unfold EntOK at h ⊢
    rw [hi] at h
    show match P.kInfo[j]? with
      | some (.neutral _ _) => _ | some (.defn c lps us v) => _ | some (.ctor c us nP nF) => _
      | some (.recr c lps us mI rP base nr isK isEta) => _ | none => True
    rw [hi]
    obtain ⟨h₁, h₂, h₃, -⟩ := h
    exact ⟨h₁, h₂, h₃, o + 1, set!_get?_self hks, .inr ⟨o, s, rfl, hd.ext (ExtR.codes P _ _), ha⟩⟩
  · have hx := ExtR.codes P (P.kCode.set! k (o + 1)) P.ruleCode
    exact (hI.ents j hj).extR hx hj (set!_get?_ne hjk)
      (fun _ _ _ _ _ _ _ _ _ hi' i _ hi₁ hr => hr.extR hx (hI.rows_lt ⟨_, _, _, _, _, _, _, _, _,
        hi', Nat.le_add_right _ _, by omega⟩) rfl)

/-- **The ι store**: a rule row's compiled right-hand side, at the levels of
the recursor entry that owns the row. -/
theorem Inv.setRuleCode {P : G4Prog} (hI : Inv find? findProj? P) {k ri o : Nat} {s : Expr} {c : Name}
    {lps : List Name} {us : List Level} {mI rP base nr : Nat} {isK isEta : Bool}
    (hi : P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta)) (hr₁ : base ≤ ri) (hr₂ : ri < base + nr)
    (hd : Den P o s) (ha : Approx s ((P.rules[ri]!).rhs.instantiateLevelParams lps us)) :
    Inv find? findProj? { P with ruleCode := P.ruleCode.set! ri (o + 1) } := by
  have hown : RowsOf P k ri := ⟨_, _, _, _, _, _, _, _, _, hi, hr₁, hr₂⟩
  have hrs : ri < P.ruleCode.size := by rw [hI.szs.2.1.1]; exact hI.rows_lt hown
  refine hI.codes (a := P.kCode) rfl (by simp) (fun j hj => ?_)
  have hx := ExtR.codes P P.kCode (P.ruleCode.set! ri (o + 1))
  refine (hI.ents j hj).extR hx hj rfl
    (fun c' lps' us' mI' rP' base' nr' isK' isEta' hi' i rl hi₁ hrow => ?_)
  have hown' : RowsOf P j (base' + i) := ⟨_, _, _, _, _, _, _, _, _, hi', Nat.le_add_right _ _, by omega⟩
  by_cases he : base' + i = ri
  · rw [he] at hown' hrow ⊢
    obtain rfl := hI.rowsDisj j k ri hown' hown
    rw [hi] at hi'
    simp only [Option.some.injEq, G4Info.recr.injEq] at hi'
    obtain ⟨-, rfl, rfl, -, -, -, -, rfl, -⟩ := hi'
    obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := hrow
    have hrhs : (P.rules[ri]!).rhs = rl.rhs := by
      rw [getElem!_pos P.rules ri (lt_of_some h₁)]
      rw [Array.getElem?_eq_getElem (lt_of_some h₁)] at h₁
      rw [Option.some.inj h₁]
    exact ⟨h₁, h₂, h₃, h₄, h₅, o + 1, set!_get?_self hrs,
      .inr ⟨o, s, rfl, hd.ext hx, hrhs ▸ ha⟩⟩
  · exact hrow.extR hx (hI.rows_lt hown') (set!_get?_ne he)

end ConLeche.Verify.Ground
