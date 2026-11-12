module

public import ConLeche.Kernel.Ground
public import ConLeche.Verify.Ground.Erased

public section

/-!
# The ground engine's program and its invariant (task #423 soundness, layers (a) and (d))

The ground engine compiles every term it evaluates into a code array
(`g4Comp`, `ConLeche/Kernel/Ground.lean`).  This file reads the code back,
twice over one reading:
* `Comp P o t` says that node `o` of the program `P` is exactly what `g4Comp`
  builds for `t`: the tag per term constructor, a spine's head and its
  arguments under the head's erasure mask, a closed argument as its shared
  node, an entry by its key (constant and levels), a string and a projection
  row by their contents.  Two programs' nodes for the same term have the same
  layout, which is what the independence of the answer from the program needs.
* `Den P o s`, derived from it (`Comp.den`), forgets what the machine does not
  read: the node denotes the erased term `s` (`ConLeche/Verify/Ground/Erased.lean`),
  binder domains, sorts, Π-types, erased arguments and neutral constants read
  back as `bot`, a shared closed term as the term it wraps.

The invariant `Inv` is the table invariant `TabInv` (every entry and
projection row is the declaration it names, the constant map names entries
that denote their keys) and the key invariant `CompInv` (a closed term's node
is its shared node, a memoised mask is the head's, every entry is registered at
its key, slots have one owner each, the words `g4Entry` computes).  The
compiler's correctness, `g4Comp_spec`, is in `ConLeche/Verify/Ground/Keys.lean`.
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
      Den P h sh → DenArgs P (o + 3) n ss → Den P o (Expr.mkAppN sh ss)
  /-- a λ: `[2, body, tn, inner]`, `tn` the telescope's length from here and
  `inner` its innermost body -/
  | lam {o b tn inner : Nat} {sb : Expr} :
      P.code[o]? = some 2 → P.code[o + 1]? = some b → P.code[o + 2]? = some tn →
      P.code[o + 3]? = some inner → Den P b sb →
      ((P.code[b]? = some 2 ∧ P.code[b + 2]? = some (tn - 1) ∧ P.code[b + 3]? = some inner ∧
          tn ≥ 2) ∨
        (P.code[b]? ≠ some 2 ∧ tn = 1 ∧ inner = b)) →
      Den P o (.lam bot sb)
  | letE {o v b : Nat} {sv sb : Expr} :
      P.code[o]? = some 3 → P.code[o + 1]? = some v → P.code[o + 2]? = some b →
      Den P v sv → Den P b sb → Den P o (.letE bot sv sb)
  | const {o k : Nat} {info : G4Info} :
      P.code[o]? = some 4 → P.code[o + 1]? = some k → P.kInfo[k]? = some info →
      Den P o (infoTerm info)
  | natLit {o n : Nat} : P.code[o]? = some 5 → P.code[o + 1]? = some n →
      Den P o (.lit (.natVal n))
  | strLit {o si : Nat} {s : String} : P.code[o]? = some 6 → P.code[o + 1]? = some si →
      P.strs[si]? = some s → Den P o (.lit (.strVal s))
  | proj {o q e : Nat} {pj : G4Proj} {se : Expr} :
      P.code[o]? = some 7 → P.code[o + 1]? = some (q + 1) → P.projs[q]? = some pj →
      P.code[o + 2]? = some e → Den P e se → Den P o (.proj pj.sn pj.idx se)
  | neutral {o : Nat} : P.code[o]? = some 8 → Den P o bot
  | shared {o sl a : Nat} {s : Expr} : P.code[o]? = some 9 → P.code[o + 1]? = some sl →
      P.code[o + 2]? = some a → Den P a s →
      (∃ a' : Expr, P.closedNode[a']? = some o) → Den P o s

/-- The `n` argument nodes of a spine, read from offset `p`. -/
inductive DenArgs (P : G4Prog) : Nat → Nat → List Expr → Prop where
  | nil {p : Nat} : DenArgs P p 0 []
  | cons {p n a : Nat} {s : Expr} {ss : List Expr} :
      P.code[p]? = some a → Den P a s → DenArgs P (p + 1) n ss →
      DenArgs P p (n + 1) (s :: ss)
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
  | .spine h₀ h₁ h₂ hh ha =>
    .spine (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) (Den.ext hx hh)
      (DenArgs.ext hx ha)
  | .lam h₀ h₁ h₂ h₃ hb htel =>
    .lam (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) (hx.code_some h₃)
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
  | .letE h₀ h₁ h₂ dv db =>
    .letE (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) (Den.ext hx dv) (Den.ext hx db)
  | .const h₀ h₁ h₂ => .const (hx.code_some h₀) (hx.code_some h₁) (hx.kInfo_some h₂)
  | .natLit h₀ h₁ => .natLit (hx.code_some h₀) (hx.code_some h₁)
  | .strLit h₀ h₁ h₂ => .strLit (hx.code_some h₀) (hx.code_some h₁) (hx.strs_some h₂)
  | .proj h₀ h₁ h₂ h₃ he =>
    .proj (hx.code_some h₀) (hx.code_some h₁) (hx.projs_some h₂) (hx.code_some h₃) (Den.ext hx he)
  | .neutral h₀ => .neutral (hx.code_some h₀)
  | .shared h₀ h₁ h₂ ha ⟨a', hr⟩ => .shared (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂)
      (Den.ext hx ha) ⟨a', hx.closedNode a' _ hr⟩

theorem DenArgs.ext {P P' : G4Prog} (hx : ExtR P P') {p n : Nat} {ss : List Expr} :
    DenArgs P p n ss → DenArgs P' p n ss
  | .nil => .nil
  | .cons h₀ ha hr => .cons (hx.code_some h₀) (Den.ext hx ha) (DenArgs.ext hx hr)

end

mutual
/-- **A node denotes one term.** -/
theorem Den.unique {P : G4Prog} : ∀ {o : Nat} {s s' : Expr}, Den P o s → Den P o s' → s = s'
  | _, _, _, .bvar h₀ h₁, h' => by
    cases h' with
    | bvar _ h₁' => rw [h₁] at h₁'; cases h₁'; rfl
    | _ => simp_all
  | _, _, _, .spine h₀ h₁ h₂ hh ha, h' => by
    cases h' with
    | spine _ h₁' h₂' hh' ha' =>
      rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'
      rw [Den.unique hh hh', DenArgs.unique ha ha']
    | _ => simp_all
  | _, _, _, .lam h₀ h₁ _ _ hb _, h' => by
    cases h' with
    | lam _ h₁' _ _ hb' _ => rw [h₁] at h₁'; cases h₁'; rw [Den.unique hb hb']
    | _ => simp_all
  | _, _, _, .letE h₀ h₁ h₂ dv db, h' => by
    cases h' with
    | letE _ h₁' h₂' dv' db' =>
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
  | _, _, _, .proj h₀ h₁ h₂ h₃ he, h' => by
    cases h' with
    | proj _ h₁' h₂' h₃' he' =>
      rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; cases h₂'; rw [h₃] at h₃'; cases h₃'
      rw [Den.unique he he']
    | _ => simp_all
  | _, _, _, .neutral h₀, h' => by
    cases h' with
    | neutral _ => rfl
    | _ => simp_all
  | _, _, _, .shared h₀ h₁ h₂ ha _, h' => by
    cases h' with
    | shared _ _ h₂' ha' _ => rw [h₂] at h₂'; cases h₂'; exact Den.unique ha ha'
    | _ => simp_all

theorem DenArgs.unique {P : G4Prog} : ∀ {p n : Nat} {ss ss' : List Expr},
    DenArgs P p n ss → DenArgs P p n ss' → ss = ss'
  | _, _, _, _, .nil, .nil => rfl
  | _, _, _, _, .cons h₀ ha hr, .cons h₀' ha' hr' => by
    rw [h₀] at h₀'; cases h₀'
    rw [Den.unique ha ha', DenArgs.unique hr hr']
end

/-! ## The compile, exactly -/

/-- The erasure mask `g4MaskOf` memoises for a head constant. -/
@[expose] def maskName (find? : Name → Option ConstantInfo) (c : Name) : Array Bool :=
  match find? c with
  | some ci => g4Mask find? (match ci with | .recInfo .. => true | _ => false) ci.toConstantVal.type #[]
  | none => #[]

/-- The erasure mask of a spine head. -/
@[expose] def maskHead (find? : Name → Option ConstantInfo) : Expr → Array Bool
  | .const c _ => maskName find? c
  | _ => #[]

/-- The argument terms `g4CompArg` shares when they are closed. -/
@[expose] def shKind : Expr → Bool
  | .app .. | .letE .. | .proj .. => true
  | _ => false

/-- The key of a table entry: its constant and levels. -/
@[expose] def infoKey : G4Info → Name × List Level
  | .defn c _ us _ => (c, us)
  | .ctor c us _ _ => (c, us)
  | .recr c _ us .. => (c, us)
  | .neutral c us => (c, us)

theorem infoTerm_key (info : G4Info) : infoTerm info = .const (infoKey info).1 (infoKey info).2 := by
  cases info <;> rfl

mutual
/-- **Node `o` is the compile of `t`** (`g4Comp`'s cases, exactly). -/
inductive Comp (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Nat → Expr → Prop where
  | bvar {o i : Nat} : P.code[o]? = some 0 → P.code[o + 1]? = some i → Comp find? findProj? P o (.bvar i)
  | fvar {o i : Nat} {ty : Expr} : P.code[o]? = some 8 → Comp find? findProj? P o (.fvar i ty)
  | sort {o : Nat} {u : Level} : P.code[o]? = some 8 → Comp find? findProj? P o (.sort u)
  | forallE {o : Nat} {ty b : Expr} : P.code[o]? = some 8 → Comp find? findProj? P o (.forallE ty b)
  | lam {o b tn inner : Nat} {ty body : Expr} :
      P.code[o]? = some 2 → P.code[o + 1]? = some b → P.code[o + 2]? = some tn →
      P.code[o + 3]? = some inner → Comp find? findProj? P b body →
      ((P.code[b]? = some 2 ∧ P.code[b + 2]? = some (tn - 1) ∧ P.code[b + 3]? = some inner ∧
          tn ≥ 2) ∨
        (P.code[b]? ≠ some 2 ∧ tn = 1 ∧ inner = b)) →
      Comp find? findProj? P o (.lam ty body)
  | letE {o v b : Nat} {ty val body : Expr} :
      P.code[o]? = some 3 → P.code[o + 1]? = some v → P.code[o + 2]? = some b →
      CompArg find? findProj? P v val → Comp find? findProj? P b body →
      Comp find? findProj? P o (.letE ty val body)
  | const {o k : Nat} {info : G4Info} {c : Name} {us : List Level} :
      P.code[o]? = some 4 → P.code[o + 1]? = some k → P.kInfo[k]? = some info →
      infoKey info = (c, us) → Comp find? findProj? P o (.const c us)
  | natLit {o n : Nat} : P.code[o]? = some 5 → P.code[o + 1]? = some n →
      Comp find? findProj? P o (.lit (.natVal n))
  | strLit {o si : Nat} {s : String} : P.code[o]? = some 6 → P.code[o + 1]? = some si →
      P.strs[si]? = some s → Comp find? findProj? P o (.lit (.strVal s))
  | proj {o q so i : Nat} {sn : Name} {s : Expr} {en : ProjEntry} :
      findProj? sn i = some en → P.code[o]? = some 7 → P.code[o + 1]? = some (q + 1) →
      P.projs[q]? = some ⟨sn, en.ctor, i, en.numParams, en.numFields, en.levelParams.length, true, en⟩ →
      P.code[o + 2]? = some so → Comp find? findProj? P so s →
      Comp find? findProj? P o (.proj sn i s)
  | projNone {o i : Nat} {sn : Name} {s : Expr} : findProj? sn i = none → P.code[o]? = some 8 →
      Comp find? findProj? P o (.proj sn i s)
  | app {o h n : Nat} {f x : Expr} :
      P.code[o]? = some 1 → P.code[o + 1]? = some h → P.code[o + 2]? = some n →
      n = (Expr.app f x).getAppArgs.length → Comp find? findProj? P h (Expr.app f x).getAppFn →
      CompArgs find? findProj? P (maskHead find? (Expr.app f x).getAppFn) (o + 3) 0
        (Expr.app f x).getAppArgs →
      Comp find? findProj? P o (.app f x)

/-- The argument nodes of a spine, read from offset `p`, the `j`-th on. -/
inductive CompArgs (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Array Bool → Nat → Nat → List Expr → Prop where
  | nil {mask : Array Bool} {p j : Nat} : CompArgs find? findProj? P mask p j []
  | erased {mask : Array Bool} {p j a : Nat} {x : Expr} {xs : List Expr} : P.code[p]? = some a →
      mask.getD j false = true → P.code[a]? = some 8 → CompArgs find? findProj? P mask (p + 1) (j + 1) xs →
      CompArgs find? findProj? P mask p j (x :: xs)
  | arg {mask : Array Bool} {p j a : Nat} {x : Expr} {xs : List Expr} : P.code[p]? = some a →
      mask.getD j false = false → CompArg find? findProj? P a x →
      CompArgs find? findProj? P mask (p + 1) (j + 1) xs → CompArgs find? findProj? P mask p j (x :: xs)

/-- An argument position (`g4CompArg`): a closed application, `let` or
projection is its shared node `[9, sl, e]`, `e` the term's compile. -/
inductive CompArg (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Nat → Expr → Prop where
  | shared {o sl e : Nat} {a : Expr} : shKind a = true → a.bvarBRaw = 0 → P.closedNode[a]? = some o →
      P.code[o]? = some 9 → P.code[o + 1]? = some sl → P.code[o + 2]? = some e →
      Comp find? findProj? P e a → CompArg find? findProj? P o a
  | plain {o : Nat} {a : Expr} : (shKind a = true → a.bvarBRaw ≠ 0) → Comp find? findProj? P o a →
      CompArg find? findProj? P o a
end

theorem Comp.tag {P : G4Prog} {o : Nat} {t : Expr} (h : Comp find? findProj? P o t) :
    ∃ x, P.code[o]? = some x := by
  cases h <;> exact ⟨_, by assumption⟩

/-- A compiled node is a λ node exactly for a λ. -/
theorem Comp.lam_tag {P : G4Prog} {o : Nat} {t : Expr} (h : Comp find? findProj? P o t) :
    P.code[o]? = some 2 ↔ ∃ ty b, t = .lam ty b := by
  cases h <;> simp_all

mutual
theorem Comp.extR {P P' : G4Prog} (hx : ExtR P P') {o : Nat} {t : Expr} :
    Comp find? findProj? P o t → Comp find? findProj? P' o t
  | .bvar h₀ h₁ => .bvar (hx.code_some h₀) (hx.code_some h₁)
  | .fvar h₀ => .fvar (hx.code_some h₀)
  | .sort h₀ => .sort (hx.code_some h₀)
  | .forallE h₀ => .forallE (hx.code_some h₀)
  | .lam h₀ h₁ h₂ h₃ hb htel =>
    .lam (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) (hx.code_some h₃) (Comp.extR hx hb) (by
      rcases htel with ⟨t₀, t₁, t₂, t₃⟩ | ⟨t₀, t₁, t₂⟩
      · exact .inl ⟨hx.code_some t₀, hx.code_some t₁, hx.code_some t₂, t₃⟩
      · refine .inr ⟨?_, t₁, t₂⟩
        intro h'
        obtain ⟨x, hxb⟩ := Comp.tag hb
        rw [hx.code_some hxb] at h'
        exact t₀ (hxb.trans h'))
  | .letE h₀ h₁ h₂ hv hb =>
    .letE (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) (CompArg.extR hx hv) (Comp.extR hx hb)
  | .const h₀ h₁ h₂ h₃ => .const (hx.code_some h₀) (hx.code_some h₁) (hx.kInfo_some h₂) h₃
  | .natLit h₀ h₁ => .natLit (hx.code_some h₀) (hx.code_some h₁)
  | .strLit h₀ h₁ h₂ => .strLit (hx.code_some h₀) (hx.code_some h₁) (hx.strs_some h₂)
  | .proj hf h₀ h₁ h₂ h₃ he =>
    .proj hf (hx.code_some h₀) (hx.code_some h₁) (hx.projs_some h₂) (hx.code_some h₃) (Comp.extR hx he)
  | .projNone hf h₀ => .projNone hf (hx.code_some h₀)
  | .app h₀ h₁ h₂ hn hh ha =>
    .app (hx.code_some h₀) (hx.code_some h₁) (hx.code_some h₂) hn (Comp.extR hx hh) (CompArgs.extR hx ha)

theorem CompArgs.extR {P P' : G4Prog} (hx : ExtR P P') {mask : Array Bool} {p j : Nat}
    {xs : List Expr} : CompArgs find? findProj? P mask p j xs → CompArgs find? findProj? P' mask p j xs
  | .nil => .nil
  | .erased h₀ hm h₈ hr => .erased (hx.code_some h₀) hm (hx.code_some h₈) (CompArgs.extR hx hr)
  | .arg h₀ hm ha hr => .arg (hx.code_some h₀) hm (CompArg.extR hx ha) (CompArgs.extR hx hr)

theorem CompArg.extR {P P' : G4Prog} (hx : ExtR P P') {o : Nat} {a : Expr} :
    CompArg find? findProj? P o a → CompArg find? findProj? P' o a
  | .shared h₀ h₁ h₂ h₃ h₄ h₅ hc => .shared h₀ h₁ (hx.closedNode _ _ h₂) (hx.code_some h₃)
    (hx.code_some h₄) (hx.code_some h₅) (Comp.extR hx hc)
  | .plain h₀ h₁ => .plain h₀ (Comp.extR hx h₁)
end

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

mutual
/-- **The denotation, read off the compile**: a compiled node denotes an
approximation of the term it is the compile of. -/
theorem Comp.den {P : G4Prog} {o : Nat} {t : Expr} :
    Comp find? findProj? P o t → ∃ s, Den P o s ∧ Approx s t
  | .bvar h₀ h₁ => ⟨_, .bvar h₀ h₁, .bvar _⟩
  | .fvar h₀ => ⟨_, .neutral h₀, .bot _⟩
  | .sort h₀ => ⟨_, .neutral h₀, .bot _⟩
  | .forallE h₀ => ⟨_, .neutral h₀, .bot _⟩
  | .lam h₀ h₁ h₂ h₃ hb htel =>
    let ⟨_, hd, ha⟩ := Comp.den hb
    ⟨_, .lam h₀ h₁ h₂ h₃ hd htel, .lam (.bot _) ha⟩
  | .letE h₀ h₁ h₂ hv hb =>
    let ⟨_, hdv, hav⟩ := CompArg.den hv
    let ⟨_, hdb, hab⟩ := Comp.den hb
    ⟨_, .letE h₀ h₁ h₂ hdv hdb, .letE (.bot _) hav hab⟩
  | .const h₀ h₁ h₂ h₃ => ⟨_, .const h₀ h₁ h₂, by rw [infoTerm_key, h₃]; exact Approx.refl _⟩
  | .natLit h₀ h₁ => ⟨_, .natLit h₀ h₁, Approx.refl _⟩
  | .strLit h₀ h₁ h₂ => ⟨_, .strLit h₀ h₁ h₂, Approx.refl _⟩
  | .proj _ h₀ h₁ h₂ h₃ he =>
    let ⟨_, hd, ha⟩ := Comp.den he
    ⟨_, .proj h₀ h₁ h₂ h₃ hd, .proj ha⟩
  | .projNone _ h₀ => ⟨_, .neutral h₀, .bot _⟩
  | .app (f := f) (x := x) h₀ h₁ h₂ hn hh ha => by
    obtain ⟨_, hdh, hah⟩ := Comp.den hh
    obtain ⟨_, hds, has⟩ := CompArgs.den ha
    subst hn
    refine ⟨_, .spine h₀ h₁ h₂ hdh hds, ?_⟩
    have := Approx.mkAppN hah has
    rwa [mkAppN_getApp' (.app f x)] at this

theorem CompArgs.den {P : G4Prog} {mask : Array Bool} {p j : Nat} {xs : List Expr} :
    CompArgs find? findProj? P mask p j xs → ∃ ss, DenArgs P p xs.length ss ∧ Approx.Args ss xs
  | .nil => ⟨[], .nil, .nil⟩
  | .erased h₀ _ h₈ hr =>
    let ⟨_, hd, ha⟩ := CompArgs.den hr
    ⟨_, .cons h₀ (.neutral h₈) hd, .cons (.bot _) ha⟩
  | .arg h₀ _ hx hr =>
    let ⟨_, hdx, hax⟩ := CompArg.den hx
    let ⟨_, hd, ha⟩ := CompArgs.den hr
    ⟨_, .cons h₀ hdx hd, .cons hax ha⟩

theorem CompArg.den {P : G4Prog} {o : Nat} {a : Expr} :
    CompArg find? findProj? P o a → ∃ s, Den P o s ∧ Approx s a
  | .shared _ _ hcn h₀ h₁ h₂ hc =>
    let ⟨_, hd, ha⟩ := Comp.den hc
    ⟨_, .shared h₀ h₁ h₂ hd ⟨_, hcn⟩, ha⟩
  | .plain _ hc => Comp.den hc
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

theorem Den.lt_size {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) : o < P.code.size := by
  obtain ⟨x, hx⟩ := h.tag
  rcases Nat.lt_or_ge o P.code.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at hx; cases hx

theorem closed_of_bvarBRaw {a : Expr} (h : a.bvarBRaw = 0) : a.looseBVarsBounded 0 = true :=
  Expr.looseBVarsBounded_iff.mpr (by
    rw [← Expr.bvarBRaw_exact a (by rw [h]; unfold satRange; omega)]; omega)


/-! ## The table invariant -/

/-- A compiled-body word: `0` not compiled yet, `o + 1` the node `o`, the
compile of `t`. -/
@[expose] def CodeOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry) (P : G4Prog) (w : Nat)
    (t : Expr) : Prop :=
  w = 0 ∨ ∃ o, w = o + 1 ∧ Comp find? findProj? P o t

/-- Case 3 of a rule's ι split, as `g4Entry` records it. -/
@[expose] def ruleCase3 (find? : Name → Option ConstantInfo) (isK : Bool) (lps : List Name)
    (us : List Level) (rl : RecRule) : Bool :=
  match find? rl.ctor with
  | some (.ctorInfo cvj _ _) => gCase3 find? isK cvj (gCmpLevels rl lps us cvj.levelParams)
  | _ => true

/-- **A rule row** `r` is the recursor rule `rl` at the levels `us`. -/
@[expose] def RowOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (r : Nat) (isK : Bool)
    (lps : List Name) (us : List Level) (rl : RecRule) : Prop :=
  P.rules[r]? = some ⟨rl.ctor, rl.nfields, gCtorParams find? rl.ctor, ruleCase3 find? isK lps us rl,
      rl.rhs⟩ ∧
    P.rNF[r]? = some rl.nfields ∧ P.rCP[r]? = some (gCtorParams find? rl.ctor) ∧
    P.rC3[r]? = some (if ruleCase3 find? isK lps us rl then 1 else 0) ∧
    (∃ i, P.nids[rl.ctor]? = some i ∧ P.rNid[r]? = some i) ∧
    ∃ w, P.ruleCode[r]? = some w ∧ CodeOK find? findProj? P w (rl.rhs.instantiateLevelParams lps us)

/-- **The K step's constructor entry** (`kfab`, the entry plus one, or `0`):
a K recursor's single rule binds no field, and the entry's arity is within
the recursor's leading arguments. -/
@[expose] def KfabOK (P : G4Prog) (mI : Nat) (isK : Bool) (rules : List RecRule) (kfab : Nat) : Prop :=
  kfab = 0 ∨ ∃ kc rl, kfab = kc + 1 ∧ kc < P.kInfo.size ∧ (∃ a, P.kArity[kc]? = some a ∧ a ≤ mI + 1) ∧
    isK = true ∧ rules = [rl] ∧ rl.nfields = 0

/-- A definition entry: the stored definition at the levels; tag `3` an
accelerated operation. -/
@[expose] def DefnOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (k : Nat) (c : Name)
    (lps : List Name) (us : List Level) (v : Expr) : Prop :=
  (∃ cv h, find? c = some (.defnInfo cv v h) ∧ cv.levelParams = lps) ∧ us.length = lps.length ∧
    (P.kTag[k]? = some 0 ∨
      (P.kTag[k]? = some 3 ∧ us = [] ∧ P.natOk = true ∧ natBin14 c = true ∧
        P.kE[k]? = some ((natBin14Names.idxOf? c).getD 0))) ∧
    ∃ w, P.kCode[k]? = some w ∧ CodeOK find? findProj? P w (v.instantiateLevelParams lps us)

/-- A constructor entry: its arity, its name's id and its level count. -/
@[expose] def CtorOK (find? : Name → Option ConstantInfo) (P : G4Prog) (k : Nat) (c : Name)
    (us : List Level) (nP nF : Nat) : Prop :=
  (∃ cv, find? c = some (.ctorInfo cv nP nF) ∧ P.kArity[k]? = some (g4Pis cv.type 0)) ∧
    P.kTag[k]? = some 1 ∧ (∃ i, P.nids[c]? = some i ∧ P.kB[k]? = some i) ∧
    P.kD[k]? = some us.length

/-- A recursor entry: the stored recursor at the levels, its words, its K
step and its rule rows. -/
@[expose] def RecOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (k : Nat) (c : Name)
    (lps : List Name) (us : List Level) (mI rP base nr : Nat) (isK isEta : Bool) : Prop :=
  ∃ cv rules, find? c = some (.recInfo cv mI rP isK rules) ∧ cv.levelParams = lps ∧
    us.length = lps.length ∧ (Expr.peelPis (mI + 1) cv.type).isSome = true ∧
    P.kTag[k]? = some 2 ∧ P.kArity[k]? = some mI ∧ P.kB[k]? = some rP ∧ P.kC[k]? = some base ∧
    P.kD[k]? = some nr ∧ nr = rules.length ∧ base + nr ≤ P.rules.size ∧
    (∃ kfab, P.kE[k]? = some ((if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * kfab) ∧
      KfabOK P mI isK rules kfab) ∧
    ∀ i (h : i < rules.length), RowOK find? findProj? P (base + i) isK lps us rules[i]

/-- **A table entry** is the declaration it names: its tag, arity and words
are the ones `g4Entry` computes from it. -/
@[expose] def EntOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (k : Nat) : Prop :=
  match P.kInfo[k]? with
  | some (.neutral _ _) => P.kTag[k]? = some 5
  | some (.defn c lps us v) => DefnOK find? findProj? P k c lps us v
  | some (.ctor c us nP nF) => CtorOK find? P k c us nP nF
  | some (.recr c lps us mI rP base nr isK isEta) => RecOK find? findProj? P k c lps us mI rP base nr isK isEta
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
    CodeOK find? findProj? P w t → CodeOK find? findProj? P' w t
  | .inl h => .inl h
  | .inr ⟨o, h₁, h₂⟩ => .inr ⟨o, h₁, h₂.extR hx⟩

/-- A compiled body's denotation. -/
theorem CodeOK.den {P : G4Prog} {w : Nat} {t : Expr} (h : CodeOK find? findProj? P w t) :
    w = 0 ∨ ∃ o s, w = o + 1 ∧ Den P o s ∧ Approx s t := by
  rcases h with h | ⟨o, h₁, h₂⟩
  · exact .inl h
  · obtain ⟨s, hd, ha⟩ := h₂.den; exact .inr ⟨o, s, h₁, hd, ha⟩

/-- A rule row survives growth that keeps its compiled right-hand side. -/
theorem RowOK.extR {P P' : G4Prog} (hx : ExtR P P') {r : Nat} (hr : r < P.rules.size)
    (hc : P'.ruleCode[r]? = P.ruleCode[r]?) {isK : Bool}
    {lps : List Name} {us : List Level} {rl : RecRule} (h : RowOK find? findProj? P r isK lps us rl) :
    RowOK find? findProj? P' r isK lps us rl := by
  obtain ⟨e₁, e₃, e₄, e₅, e₆⟩ := rowR_eq (hx.row r hr)
  obtain ⟨h₁, h₂, h₃, h₄, ⟨i, hi, hi'⟩, w, hw, hc'⟩ := h
  exact ⟨e₁ ▸ h₁, e₄ ▸ h₂, e₅ ▸ h₃, e₆ ▸ h₄, ⟨i, hx.nids _ _ hi, e₃ ▸ hi'⟩, w, hc ▸ hw, hc'.ext hx⟩

theorem RowOK.ext {P P' : G4Prog} (hx : Ext P P') {r : Nat} (hr : r < P.rules.size) {isK : Bool}
    {lps : List Name} {us : List Level} {rl : RecRule} (h : RowOK find? findProj? P r isK lps us rl) :
    RowOK find? findProj? P' r isK lps us rl :=
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
      RowOK find? findProj? P (base + i) isK lps us rl → RowOK find? findProj? P' (base + i) isK lps us rl)
    (h : EntOK find? findProj? P k) : EntOK find? findProj? P' k := by
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
    (h : EntOK find? findProj? P k) : EntOK find? findProj? P' k := by
  refine h.extR hx.toExtR hk (hx.kCode k hk) (fun c lps us mI rP base nr isK isEta hi i rl hi' hr => ?_)
  have hb : base + nr ≤ P.rules.size := by
    unfold EntOK at h; rw [hi] at h; obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h
  exact hr.ext hx (by omega)

/-- An entry tagged `2` is a recursor's. -/
theorem EntOK.tag2 {P : G4Prog} {k : Nat} (h : EntOK find? findProj? P k) (hk : k < P.kInfo.size)
    (ht : P.kTag[k]? = some 2) :
    ∃ c lps us mI rP base nr isK isEta, P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) ∧
      RecOK find? findProj? P k c lps us mI rP base nr isK isEta := by
  unfold EntOK at h
  split at h
  · rw [ht] at h; cases h
  · obtain ⟨-, -, h3, -⟩ := h; rw [ht] at h3; rcases h3 with h3 | ⟨h3, -⟩ <;> cases h3
  · obtain ⟨-, h2, -⟩ := h; rw [ht] at h2; cases h2
  · rename_i heq; exact ⟨_, _, _, _, _, _, _, _, _, heq, h⟩
  · rename_i heq; rw [Array.getElem?_eq_getElem hk] at heq; cases heq

/-- An entry tagged `1` is a constructor's. -/
theorem EntOK.tag1 {P : G4Prog} {k : Nat} (h : EntOK find? findProj? P k) (hk : k < P.kInfo.size)
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
    {mI rP base nr : Nat} {isK isEta : Bool} (h : RecOK find? findProj? P k c lps us mI rP base nr isK isEta)
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

/-- **The table invariant**: the constant map names entries that denote its
keys, and every entry and projection row is the declaration it names. -/
structure TabInv (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Prop where
  szs : Sizes P
  sizes : P.kTag.size = P.kInfo.size
  kSlotSize : P.kSlot.size = P.kInfo.size
  kMap : ∀ c us k, P.kMap[(c, us)]? = some k →
    ∃ info, P.kInfo[k]? = some info ∧ Approx (infoTerm info) (.const c us)
  ents : ∀ k, k < P.kInfo.size → EntOK find? findProj? P k
  prjs : ∀ q, q < P.projs.size → PrjOK findProj? P q
  nidOK : NidOK P
  rowsDisj : ∀ k k' r, RowsOf P k r → RowsOf P k' r → k = k'

/-- A recursor entry's rule rows are in the rule table. -/
theorem TabInv.rows_lt {P : G4Prog} (hI : TabInv find? findProj? P) {k r : Nat} (h : RowsOf P k r) :
    r < P.rules.size := by
  obtain ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, h₁, h₂⟩ := h
  have := hI.ents k (lt_of_some hi)
  unfold EntOK at this; rw [hi] at this
  obtain ⟨_, _, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := this; omega

/-- The table invariant survives an extension that keeps the constant map
and the table sizes' agreement. -/
theorem TabInv.ext {P P' : G4Prog} (hI : TabInv find? findProj? P) (hx : Ext P P')
    (hs : P'.kTag.size = P'.kInfo.size) (hks : P'.kSlot.size = P'.kInfo.size) (hk : P'.kMap = P.kMap)
    (hsz : Sizes P') (hkI : P'.kInfo.size = P.kInfo.size)
    (hpj : ∀ q, q < P'.projs.size → P.projs.size ≤ q → PrjOK findProj? P' q) (hnid : NidOK P') :
    TabInv find? findProj? P' where
  szs := hsz
  sizes := hs
  kSlotSize := hks
  kMap c us k h := by
    rw [hk] at h
    obtain ⟨info, hi, ha⟩ := hI.kMap c us k h
    exact ⟨info, hx.kInfo_some hi, ha⟩
  ents k hk' := (hI.ents k (by omega)).ext hx (by omega)
  prjs q hq := by
    rcases Nat.lt_or_ge q P.projs.size with h | h
    · exact (hI.prjs q h).ext hx.toExtR h
    · exact hpj q hq h
  nidOK := hnid
  rowsDisj k k' r h h' := hI.rowsDisj k k' r (h.back hx.toExtR hkI) (h'.back hx.toExtR hkI)

theorem TabInv.emit {P : G4Prog} (hI : TabInv find? findProj? P) (ws : Array Nat) :
    TabInv find? findProj? (P.emit (· ++ ws)) :=
  hI.ext (Ext.emit P ws) hI.sizes hI.kSlotSize rfl hI.szs rfl
    (fun _ hq h => absurd hq (Nat.not_lt.mpr h)) hI.nidOK

/-- A program with empty tables and memos (the engine's fresh program, with
its flags) satisfies the table invariant. -/
theorem TabInv.fresh (natOk strOk : Bool) (maxNat : Nat) :
    TabInv find? findProj? ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog) where
  szs := by simp [Sizes]
  sizes := rfl
  kSlotSize := rfl
  kMap c us k h := by simp at h
  ents _ hk := by simp at hk
  prjs _ hq := by simp at hq
  nidOK := ⟨fun c i h => by simp at h, fun c c' i h => by simp at h⟩
  rowsDisj k _ _ h := by obtain ⟨_, _, _, _, _, _, _, _, _, hi, -⟩ := h; simp at hi

/-! ## The program's key invariant -/

/-- A slot's owner: a closed argument term (its shared node's slot word) or
a table entry (`kSlot`). -/
@[expose] def SlotOwn (P : G4Prog) (sl : Nat) : Expr ⊕ Nat → Prop
  | .inl a => ∃ o, P.closedNode[a]? = some o ∧ P.code[o + 1]? = some sl
  | .inr k => P.kSlot[k]? = some sl

/-- `g4ResolveF`'s K word for the constant `c` at levels `us`: the key of
the K constructor's entry, when the K step applies. -/
@[expose] def kfabKey (find? : Name → Option ConstantInfo) (c : Name) (us : List Level) :
    Option (Name × List Level) :=
  match find? c with
  | some (.recInfo cv mI _ true [rl]) =>
    if us.length == cv.levelParams.length && (Expr.peelPis (mI + 1) cv.type).isSome then
      match find? rl.ctor with
      | some (.ctorInfo cvj _ 0) =>
        if rl.nfields == 0 && g4Pis cvj.type 0 ≤ mI + 1 then
          some (rl.ctor, gCmpLevels rl cv.levelParams us cvj.levelParams)
        else none
      | _ => none
    else none
  | _ => none

/-- A recursor entry's K word is the one `g4ResolveF` computes. -/
@[expose] def KfabKey (find? : Name → Option ConstantInfo) (P : G4Prog) (c : Name) (us : List Level)
    (kfab : Nat) : Prop :=
  (kfabKey find? c us = none ∧ kfab = 0) ∨
    ∃ key kc info, kfabKey find? c us = some key ∧ kfab = kc + 1 ∧ P.kInfo[kc]? = some info ∧
      infoKey info = key

/-- **What a program keeps for the keys** (beyond `TabInv`). -/
structure CompInv (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Prop where
  closed : ∀ (a : Expr) (o : Nat), P.closedNode[a]? = some o →
    ∃ sl e, P.code[o]? = some 9 ∧ P.code[o + 1]? = some sl ∧ P.code[o + 2]? = some e ∧
      Comp find? findProj? P e a ∧ a.bvarBRaw = 0
  masks : ∀ (c : Name) (m : Array Bool), P.masks[c]? = some m → m = maskName find? c
  kMapAll : ∀ (k : Nat) (info : G4Info), P.kInfo[k]? = some info → P.kMap[infoKey info]? = some k
  slotLt : ∀ (sl : Nat) (x : Expr ⊕ Nat), SlotOwn P sl x → sl < P.nslots
  slotUniq : ∀ (sl : Nat) (x y : Expr ⊕ Nat), SlotOwn P sl x → SlotOwn P sl y → x = y
  defTag : ∀ (k : Nat) (c : Name) (lps : List Name) (us : List Level) (v : Expr),
    P.kInfo[k]? = some (.defn c lps us v) →
      P.kTag[k]? = some (if us.isEmpty && P.natOk && natBin14 c then 3 else 0)
  kfab : ∀ (k : Nat) (c : Name) (lps : List Name) (us : List Level) (mI rP base nr : Nat)
    (isK isEta : Bool), P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) →
      ∃ kfab, P.kE[k]? = some ((if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * kfab) ∧
        KfabKey find? P c us kfab
  ctorAr : ∀ (k : Nat) (info : G4Info) (cv : ConstantVal) (nP nF : Nat), P.kInfo[k]? = some info →
    find? (infoKey info).1 = some (.ctorInfo cv nP nF) → P.kArity[k]? = some (g4Pis cv.type 0)

theorem kInfo_back {P P' : G4Prog} (hx : ExtR P P') (hkI : P'.kInfo.size = P.kInfo.size) {k : Nat}
    {info : G4Info} (h : P'.kInfo[k]? = some info) : P.kInfo[k]? = some info := by
  have hk : k < P.kInfo.size := by rw [← hkI]; exact lt_of_some h
  rw [← hx.kInfo k hk]; exact h

theorem KfabKey.extR {P P' : G4Prog} (hx : ExtR P P') {c : Name} {us : List Level} {kfab : Nat}
    (h : KfabKey find? P c us kfab) : KfabKey find? P' c us kfab := by
  rcases h with h | ⟨key, kc, info, h₁, h₂, h₃, h₄⟩
  · exact .inl h
  · exact .inr ⟨key, kc, info, h₁, h₂, hx.kInfo_some h₃, h₄⟩

/-- A recursor entry's rows are in the rule table. -/
theorem TabInv.recr_rows {P : G4Prog} (hI : TabInv find? findProj? P) {k : Nat} {c : Name} {lps : List Name}
    {us : List Level} {mI rP base nr : Nat} {isK isEta : Bool}
    (h : P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta)) : base + nr ≤ P.rules.size := by
  have := hI.ents k (lt_of_some h)
  unfold EntOK at this; rw [h] at this
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hle, _⟩ := this
  exact hle

/-- Slot owners in a grown program with no new closed node or entry slot
are the old ones. -/
theorem SlotOwn.back {P P' : G4Prog} (hC : CompInv find? findProj? P) (hx : ExtR P P')
    (hcl : P'.closedNode = P.closedNode) (hks : P'.kSlot = P.kSlot) {sl : Nat} {x : Expr ⊕ Nat}
    (h : SlotOwn P' sl x) : SlotOwn P sl x := by
  cases x with
  | inl a =>
    obtain ⟨o, h₁, h₂⟩ := h
    rw [hcl] at h₁
    obtain ⟨sl', e, -, h₃, -, -, -⟩ := hC.closed a o h₁
    rw [hx.code_some h₃] at h₂
    exact ⟨o, h₁, by rw [h₃, h₂]⟩
  | inr k => show P.kSlot[k]? = some sl; rw [← hks]; exact h

/-- The empty program keeps the key invariant. -/
theorem CompInv.fresh (natOk strOk : Bool) (maxNat : Nat) :
    CompInv find? findProj? ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog) where
  closed a o h := by simp at h
  masks c m h := by simp at h
  kMapAll k info h := by simp at h
  slotLt sl x h := by cases x <;> simp [SlotOwn] at h
  slotUniq sl x y h := by cases x <;> simp [SlotOwn] at h
  defTag k c lps us v h := by simp at h
  kfab k c lps us mI rP base nr isK isEta h := by simp at h
  ctorAr k info cv nP nF h := by simp at h

section
variable (find?) (findProj?)

/-- **The key invariant survives growth** that adds no entry, closed node,
mask or slot. -/
theorem CompInv.ext_gen {P P' : G4Prog} (hC : CompInv find? findProj? P)
    (hx : Ext P P') (hkI : P'.kInfo.size = P.kInfo.size)
    (hcl : ∀ (a : Expr) (o : Nat), P'.closedNode[a]? = some o →
      ∃ sl e, P'.code[o]? = some 9 ∧ P'.code[o + 1]? = some sl ∧ P'.code[o + 2]? = some e ∧
        Comp find? findProj? P' e a ∧ a.bvarBRaw = 0)
    (hm : ∀ (c : Name) (m : Array Bool), P'.masks[c]? = some m → m = maskName find? c)
    (hkm : P'.kMap = P.kMap)
    (hsl : ∀ (sl : Nat) (x : Expr ⊕ Nat), SlotOwn P' sl x → sl < P'.nslots)
    (hsu : ∀ (sl : Nat) (x y : Expr ⊕ Nat), SlotOwn P' sl x → SlotOwn P' sl y → x = y) :
    CompInv find? findProj? P' where
  closed := hcl
  masks := hm
  kMapAll k info h := by rw [hkm]; exact hC.kMapAll k info (kInfo_back hx.toExtR hkI h)
  slotLt := hsl
  slotUniq := hsu
  defTag k c lps us v h := by
    have h' := kInfo_back hx.toExtR hkI h
    rw [(entR_eq (hx.ent k (lt_of_some h'))).1, hx.natOk]
    exact hC.defTag k c lps us v h'
  kfab k c lps us mI rP base nr isK isEta h := by
    have h' := kInfo_back hx.toExtR hkI h
    obtain ⟨kfab, h₁, h₂⟩ := hC.kfab k c lps us mI rP base nr isK isEta h'
    exact ⟨kfab, by rw [(entR_eq (hx.ent k (lt_of_some h'))).2.2.2.2.2]; exact h₁, h₂.extR hx.toExtR⟩
  ctorAr k info cv nP nF h hf := by
    have h' := kInfo_back hx.toExtR hkI h
    rw [(entR_eq (hx.ent k (lt_of_some h'))).2.1]
    exact hC.ctorAr k info cv nP nF h' hf

theorem CompInv.ext {P P' : G4Prog} (hC : CompInv find? findProj? P)
    (hx : Ext P P') (hkI : P'.kInfo.size = P.kInfo.size) (hcl : P'.closedNode = P.closedNode)
    (hm : P'.masks = P.masks) (hkm : P'.kMap = P.kMap) (hks : P'.kSlot = P.kSlot)
    (hns : P'.nslots = P.nslots) : CompInv find? findProj? P' :=
  hC.ext_gen find? findProj? hx hkI (fun a o h => by
      rw [hcl] at h
      obtain ⟨sl, e, h₀, h₁, h₂, h₃, h₄⟩ := hC.closed a o h
      exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR, h₄⟩)
    (fun c m h => hC.masks c m (by rw [← hm]; exact h)) hkm
    (fun sl x h => by rw [hns]; exact hC.slotLt sl x (h.back hC hx.toExtR hcl hks))
    (fun sl x y h h' => hC.slotUniq sl x y (h.back hC hx.toExtR hcl hks) (h'.back hC hx.toExtR hcl hks))

theorem CompInv.emit {P : G4Prog} (hC : CompInv find? findProj? P)
    (ws : Array Nat) : CompInv find? findProj? (P.emit (· ++ ws)) :=
  hC.ext find? findProj? (Ext.emit P ws) rfl rfl rfl rfl rfl rfl

end


/-! ## The program invariant -/

/-- **The program invariant**: the table invariant and the key invariant. -/
structure Inv (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Prop extends TabInv find? findProj? P, CompInv find? findProj? P

/-- A closed term's shared node denotes an approximation of it. -/
theorem Inv.closedDen {P : G4Prog} (hI : Inv find? findProj? P) (a : Expr) (o : Nat)
    (h : P.closedNode[a]? = some o) :
    ∃ s sl, P.code[o + 1]? = some sl ∧ Den P o s ∧ Approx s a ∧ a.looseBVarsBounded 0 = true := by
  obtain ⟨sl, e, h₀, h₁, h₂, h₃, hb⟩ := hI.closed a o h
  obtain ⟨s, hd, ha⟩ := h₃.den
  exact ⟨s, sl, h₁, .shared h₀ h₁ h₂ hd ⟨a, h⟩, ha, closed_of_bvarBRaw hb⟩

/-- A slot denotes one term. -/
theorem Inv.owns_unique {P : G4Prog} (hI : Inv find? findProj? P) {sl : Nat} {t t' : Expr}
    (h : Owns P sl t) (h' : Owns P sl t') : t = t' := by
  rcases h with ⟨a, o, h₁, h₂, h₃⟩ | ⟨k, info, h₁, h₂, h₃⟩ <;>
    rcases h' with ⟨a', o', h₁', h₂', h₃'⟩ | ⟨k', info', h₁', h₂', h₃'⟩
  · cases hI.slotUniq sl (.inl a) (.inl a') ⟨o, h₁, h₂⟩ ⟨o', h₁', h₂'⟩
    rw [h₁] at h₁'; cases h₁'
    exact Den.unique h₃ h₃'
  · cases hI.slotUniq sl (.inl a) (.inr k') ⟨o, h₁, h₂⟩ h₁'
  · cases hI.slotUniq sl (.inr k) (.inl a') h₁ ⟨o', h₁', h₂'⟩
  · cases hI.slotUniq sl (.inr k) (.inr k') h₁ h₁'
    rw [h₂] at h₂'; cases h₂'
    rw [h₃, h₃']

/-- The invariant survives an extension that keeps the memos and the table
sizes' agreement. -/
theorem Inv.ext {P P' : G4Prog} (hI : Inv find? findProj? P) (hx : Ext P P')
    (hs : P'.kTag.size = P'.kInfo.size) (hks : P'.kSlot.size = P'.kInfo.size) (hk : P'.kMap = P.kMap)
    (hc : P'.closedNode = P.closedNode) (hsl : P'.kSlot = P.kSlot) (hn : P'.nslots = P.nslots)
    (hm : P'.masks = P.masks) (hsz : Sizes P') (hkI : P'.kInfo.size = P.kInfo.size)
    (hpj : ∀ q, q < P'.projs.size → P.projs.size ≤ q → PrjOK findProj? P' q) (hnid : NidOK P') :
    Inv find? findProj? P' :=
  ⟨hI.toTabInv.ext hx hs hks hk hsz hkI hpj hnid,
    hI.toCompInv.ext find? findProj? hx hkI hc hm hk hsl hn⟩

theorem Inv.emit {P : G4Prog} (hI : Inv find? findProj? P) (ws : Array Nat) :
    Inv find? findProj? (P.emit (· ++ ws)) :=
  ⟨hI.toTabInv.emit ws, hI.toCompInv.emit find? findProj? ws⟩

/-- The engine's fresh program satisfies the invariant. -/
theorem Inv.fresh (natOk strOk : Bool) (maxNat : Nat) :
    Inv find? findProj? ({ natOk := natOk, strOk := strOk, maxNat := maxNat } : G4Prog) :=
  ⟨TabInv.fresh natOk strOk maxNat, CompInv.fresh natOk strOk maxNat⟩


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

theorem KeyEq.inv {P P' : G4Prog} (h : KeyEq P P') (hI : TabInv find? findProj? P) (hn : NidOK P') :
    TabInv find? findProj? P' :=
  hI.ext (h.ext hI.szs) (by rw [h.kTag, h.kInfo]; exact hI.sizes)
    (by rw [h.kSlot, h.kInfo]; exact hI.kSlotSize) h.kMap (h.sizes hI.szs)
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
      RowOK find? findProj? (g4RuleRow find? isK lps us P rl) P.rules.size isK lps us rl := by
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
      NidOK (g P rl) ∧ RowOK find? findProj? (g P rl) P.rules.size isK lps us rl) :
    ∀ (l : List RecRule) (P : G4Prog), Sizes P → NidOK P →
      KeyEq P (l.foldl g P) ∧ (l.foldl g P).rules.size = P.rules.size + l.length ∧
        NidOK (l.foldl g P) ∧
        ∀ i (h : i < l.length), RowOK find? findProj? (l.foldl g P) (P.rules.size + i) isK lps us l[i]
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
theorem g4Entry_tab (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : TabInv find? findProj? P)
    (hkf : ∀ cv mI rP isK rules, find? c = some (.recInfo cv mI rP isK rules) →
      KfabOK P mI isK rules kfab) :
    TabInv find? findProj? (g4Entry find? P c us kfab).2 ∧ Ext P (g4Entry find? P c us kfab).2 ∧
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
        Q.kD[k]? = some d → Q.kE[k]? = some e' → EntOK find? findProj? Q k := by
    have neu : ∀ (k : Nat) (Q : G4Prog), Q.kInfo[k]? = some (.neutral c us) → Q.kTag[k]? = some 5 →
        EntOK find? findProj? Q k := fun k Q hi ht => by unfold EntOK; rw [hi]; exact ht
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
          obtain ⟨hk, hsz, hn, hrows⟩ := rows_fold find? findProj? (g4RuleRow find? isK cv.levelParams us)
            (fun P rl hs hn => g4RuleRow_spec find? findProj? isK cv.levelParams us P rl hs hn) rules P hI.szs hI.nidOK
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
    ⟨⟨?_, ?_, ?_, ?_, fun k hk' => ?_, fun q hq => ?_, hnid, ?_⟩, ?_, info, ?_, hinfo⟩)
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
theorem g4Entry_after {P Pm : G4Prog} (c : Name) (us : List Level) (kfab : Nat) (hI : TabInv find? findProj? Pm)
    (hx : Ext P Pm) (hcl : Pm.closedNode = P.closedNode)
    (hkf : ∀ cv mI rP isK rules, find? c = some (.recInfo cv mI rP isK rules) →
      KfabOK Pm mI isK rules kfab) :
    TabInv find? findProj? (g4Entry find? Pm c us kfab).2 ∧ Ext P (g4Entry find? Pm c us kfab).2 ∧
      (g4Entry find? Pm c us kfab).2.closedNode = P.closedNode ∧
      ∃ info, (g4Entry find? Pm c us kfab).2.kInfo[(g4Entry find? Pm c us kfab).1]? = some info ∧
        Approx (infoTerm info) (.const c us) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := g4Entry_tab find? findProj? Pm c us kfab hI hkf
  exact ⟨h₁, hx.trans h₂, h₃.trans hcl, h₄⟩

/-- **Resolution** returns an entry that denotes the constant. -/
theorem g4ResolveF_tab : ∀ (fuel : Nat) (P : G4Prog) (c : Name) (us : List Level), TabInv find? findProj? P →
    TabInv find? findProj? (g4ResolveF find? findProj? fuel P c us).2 ∧ Ext P (g4ResolveF find? findProj? fuel P c us).2 ∧
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

theorem g4Resolve_tab (P : G4Prog) (c : Name) (us : List Level) (hI : TabInv find? findProj? P) :
    TabInv find? findProj? (g4Resolve find? findProj? P c us).2 ∧ Ext P (g4Resolve find? findProj? P c us).2 ∧
      (g4Resolve find? findProj? P c us).2.closedNode = P.closedNode ∧
      ∃ info, (g4Resolve find? findProj? P c us).2.kInfo[(g4Resolve find? findProj? P c us).1]? =
          some info ∧ Approx (infoTerm info) (.const c us) :=
  g4ResolveF_tab find? findProj? 1 P c us hI


theorem g4RuleRow_eqs (isK : Bool) (lps : List Name) (us : List Level) (P : G4Prog) (rl : RecRule) :
    (g4RuleRow find? isK lps us P rl).ruleCode = P.ruleCode.push 0 ∧
      (g4RuleRow find? isK lps us P rl).masks = P.masks ∧
      (g4RuleRow find? isK lps us P rl).natOk = P.natOk := by
  unfold g4RuleRow; dsimp only; rw [nid_eq]; exact ⟨rfl, rfl, rfl⟩

/-- The rule fold leaves the masks and flags, and its new rows are not compiled. -/
theorem rows_fold_eqs (isK : Bool) (lps : List Name) (us : List Level) (b : Nat) :
    ∀ (l : List RecRule) (P : G4Prog), (∀ r w, b ≤ r → P.ruleCode[r]? = some w → w = 0) →
      (l.foldl (g4RuleRow find? isK lps us) P).masks = P.masks ∧
        (l.foldl (g4RuleRow find? isK lps us) P).natOk = P.natOk ∧
        ∀ r w, b ≤ r → (l.foldl (g4RuleRow find? isK lps us) P).ruleCode[r]? = some w → w = 0
  | [], P, h => ⟨rfl, rfl, h⟩
  | x :: l, P, h => by
    obtain ⟨e₁, e₂, e₃⟩ := g4RuleRow_eqs find? isK lps us P x
    obtain ⟨f₁, f₂, f₃⟩ := rows_fold_eqs isK lps us b l (g4RuleRow find? isK lps us P x) (by
      intro r w hr hw
      rw [e₁, Array.getElem?_push] at hw
      split at hw
      · exact (Option.some.inj hw).symm
      · exact h r w hr hw)
    exact ⟨f₁.trans e₂, f₂.trans e₃, f₃⟩

/-- **A new entry, unfolded**: the program before the pushes and the
words `g4Entry` computes. -/
theorem g4Entry_facts (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : TabInv find? findProj? P) :
    ∃ (P' : G4Prog) (tag ar b c' d e' : Nat) (info : G4Info),
      g4Entry find? P c us kfab = (P.kTag.size, ({ P' with
        kTag := P'.kTag.push tag, kCode := P'.kCode.push 0, kArity := P'.kArity.push ar, kSlot := P'.kSlot.push P'.nslots,
        nslots := P'.nslots + 1, kInfo := P'.kInfo.push info,
        kMap := P'.kMap.insert (c, us) P.kTag.size, kB := P'.kB.push b, kC := P'.kC.push c',
        kD := P'.kD.push d, kE := P'.kE.push e' } : G4Prog)) ∧
      KeyEq P P' ∧ P'.masks = P.masks ∧ infoKey info = (c, us) ∧
      (∀ r w, P.rules.size ≤ r → P'.ruleCode[r]? = some w → w = 0) ∧
      (∀ c₁ lps us₁ v, info = .defn c₁ lps us₁ v →
        tag = if us₁.isEmpty && P.natOk && natBin14 c₁ then 3 else 0) ∧
      (∀ c₁ lps us₁ mI rP base nr isK isEta, info = .recr c₁ lps us₁ mI rP base nr isK isEta →
        e' = (if isK then 1 else 0) + (if isEta then 2 else 0) + 4 * kfab ∧ base = P.rules.size) ∧
      (∀ cv nP nF, find? c = some (.ctorInfo cv nP nF) → ar = g4Pis cv.type 0) := by
  have h0 : ∀ r w, P.rules.size ≤ r → P.ruleCode[r]? = some w → w = 0 := by
    intro r w hr hw
    have := lt_of_some hw; rw [hI.szs.2.1.1] at this; omega
  unfold g4Entry
  split
  rename_i tag ar b c' d e' info P' hm
  refine ⟨P', tag, ar, b, c', d, e', info, rfl, ?_⟩
  revert hm
  cases hf : find? c with
  | none =>
    intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
    exact ⟨KeyEq.refl P, rfl, rfl, h0, (by intro _ _ _ _ h; cases h), (by intro _ _ _ _ _ _ _ _ _ h; cases h),
      (by intro _ _ _ h; cases h)⟩
  | some ci =>
    cases ci with
    | defnInfo cv v hh =>
      dsimp only
      split
      · intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
        exact ⟨KeyEq.refl P, rfl, rfl, h0, (by intro _ _ _ _ h; cases h),
          (by intro _ _ _ _ _ _ _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
      · intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
        refine ⟨KeyEq.refl P, rfl, rfl, h0, fun c₁ lps us₁ v' h => ?_,
          (by intro _ _ _ _ _ _ _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
        simp only [G4Info.defn.injEq] at h; obtain ⟨rfl, -, rfl, -⟩ := h; rfl
    | ctorInfo cv nP nF =>
      dsimp only
      intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
      refine ⟨KeyEq.nid P c, by rw [nid_eq], rfl, ?_, (by intro _ _ _ _ h; cases h),
        (by intro _ _ _ _ _ _ _ _ _ h; cases h), fun cv' nP' nF' h => ?_⟩
      · rw [nid_eq]; exact h0
      · cases h; rfl
    | recInfo cv mI rP isK rules =>
      dsimp only
      split
      · intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
        exact ⟨KeyEq.refl P, rfl, rfl, h0, (by intro _ _ _ _ h; cases h),
          (by intro _ _ _ _ _ _ _ _ _ h; cases h), (by intro _ _ _ h; cases h)⟩
      · intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
        obtain ⟨hk, -, -, -⟩ := rows_fold find? findProj? (g4RuleRow find? isK cv.levelParams us)
          (fun P rl hs hn => g4RuleRow_spec find? findProj? isK cv.levelParams us P rl hs hn) rules P hI.szs hI.nidOK
        obtain ⟨f₁, -, f₃⟩ := rows_fold_eqs find? isK cv.levelParams us P.rules.size rules P h0
        refine ⟨hk, f₁, rfl, f₃, (by intro _ _ _ _ h; cases h), fun c₁ lps us₁ mI' rP' base nr isK' isEta h => ?_,
          (by intro _ _ _ h; cases h)⟩
        simp only [G4Info.recr.injEq] at h
        obtain ⟨-, -, -, -, -, rfl, -, rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
    | _ =>
      intro hm; simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨KeyEq.refl P, rfl, rfl, h0, (by intro _ _ _ _ h; cases h), (by intro _ _ _ _ _ _ _ _ _ h; cases h),
        (by intro _ _ _ h; cases h)⟩

/-- **A new entry keeps the key invariant** when its key is new. -/
theorem g4Entry_comp (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : TabInv find? findProj? P)
    (hC : CompInv find? findProj? P) (hnone : P.kMap[(c, us)]? = none)
    (hkf₀ : ∀ cv mI rP isK rules, find? c = some (.recInfo cv mI rP isK rules) →
      KfabOK P mI isK rules kfab)
    (hkf : KfabKey find? P c us kfab) : CompInv find? findProj? (g4Entry find? P c us kfab).2 := by
  obtain ⟨-, hx, -, -⟩ := g4Entry_tab find? findProj? P c us kfab hI hkf₀
  obtain ⟨P', tag, ar, b, c', d, e', info, heq, hk, hm, hkey, hrc, hdt, hke, har⟩ :=
    g4Entry_facts find? findProj? P c us kfab hI
  rw [heq] at hx ⊢
  have hs : P.kTag.size = P.kInfo.size := hI.sizes
  have hks : P.kSlot.size = P.kInfo.size := hI.kSlotSize
  obtain ⟨⟨e₁, e₂, e₃, e₄, e₅, e₆⟩, -, -⟩ := hk.sizes hI.szs
  have hkI : P'.kInfo.size = P.kInfo.size := by rw [hk.kInfo]
  -- the new program's entries: the old ones, then `info`
  have hinfo : ∀ k i, (P'.kInfo.push info)[k]? = some i →
      (k < P.kInfo.size ∧ P.kInfo[k]? = some i) ∨ (k = P.kInfo.size ∧ i = info) := by
    intro k i h
    rw [Array.getElem?_push] at h
    split at h
    · rename_i hkk; exact .inr ⟨by rw [hkk, hkI], (Option.some.inj h).symm⟩
    · rw [hk.kInfo] at h; exact .inl ⟨lt_of_some h, h⟩
  have hnew : ∀ {α : Type} (a : Array α) (x : α), a.size = P.kInfo.size → (a.push x)[P.kInfo.size]? = some x :=
    fun a x ha => by rw [← ha]; exact Array.getElem?_push_size
  have hown : ∀ sl x, SlotOwn ({ P' with
        kTag := P'.kTag.push tag, kCode := P'.kCode.push 0, kArity := P'.kArity.push ar,
        kSlot := P'.kSlot.push P'.nslots, nslots := P'.nslots + 1, kInfo := P'.kInfo.push info,
        kMap := P'.kMap.insert (c, us) P.kTag.size, kB := P'.kB.push b, kC := P'.kC.push c',
        kD := P'.kD.push d, kE := P'.kE.push e' } : G4Prog) sl x →
      SlotOwn P sl x ∨ (x = .inr P.kInfo.size ∧ sl = P.nslots) := by
    intro sl x h
    cases x with
    | inl a =>
      obtain ⟨o, h₁, h₂⟩ := h
      exact .inl ⟨o, by rw [← hk.closedNode]; exact h₁, by rw [← hk.code]; exact h₂⟩
    | inr k =>
      change (P'.kSlot.push P'.nslots)[k]? = some sl at h
      rw [Array.getElem?_push] at h
      split at h
      · rename_i hkk
        refine .inr ⟨by rw [hkk, hk.kSlot, hks], ?_⟩
        rw [← hk.nslots]; exact (Option.some.inj h).symm
      · rw [hk.kSlot] at h; exact .inl h
  refine ⟨fun a o h => ?_, fun c₁ m h => ?_, fun k i h => ?_, fun sl x h => ?_, fun sl x y h h' => ?_,
    fun k c₁ lps us₁ v h => ?_, fun k c₁ lps us₁ mI rP base nr isK isEta h => ?_,
    fun k i cv nP nF h hf => ?_⟩
  · change P'.closedNode[a]? = some o at h
    rw [hk.closedNode] at h
    obtain ⟨sl, e, h₀, h₁, h₂, h₃, h₄⟩ := hC.closed a o h
    exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR, h₄⟩
  · change P'.masks[c₁]? = some m at h
    rw [hm] at h; exact hC.masks c₁ m h
  · change (P'.kMap.insert (c, us) P.kTag.size)[infoKey i]? = some k
    rw [hk.kMap, Std.HashMap.getElem?_insert]
    rcases hinfo k i h with ⟨hlt, h'⟩ | ⟨rfl, rfl⟩
    · have hm' := hC.kMapAll k i h'
      split
      · rename_i hb; rw [← eq_of_beq hb, hnone] at hm'; cases hm'
      · exact hm'
    · rw [hkey]; simp [hs]
  · rcases hown sl x h with h | ⟨-, rfl⟩
    · have := hC.slotLt sl x h; show sl < P'.nslots + 1; rw [hk.nslots]; omega
    · show P.nslots < P'.nslots + 1; rw [hk.nslots]; omega
  · rcases hown sl x h with h₁ | ⟨hx₁, hs₁⟩ <;> rcases hown sl y h' with h₂ | ⟨hy₂, hs₂⟩
    · exact hC.slotUniq sl x y h₁ h₂
    · have := hC.slotLt _ x h₁; omega
    · have := hC.slotLt _ y h₂; omega
    · rw [hx₁, hy₂]
  · change (P'.kInfo.push info)[k]? = some _ at h
    show (P'.kTag.push tag)[k]? = some (if us₁.isEmpty && P'.natOk && natBin14 c₁ then 3 else 0)
    have hn : P'.natOk = P.natOk := congrArg Prod.fst hk.flags
    rcases hinfo k _ h with ⟨hlt, h'⟩ | ⟨rfl, hi⟩
    · rw [push_lt (by rw [hk.kTag, hs]; exact hlt), hk.kTag, hn]; exact hC.defTag k c₁ lps us₁ v h'
    · rw [hnew _ _ (by rw [hk.kTag, hs]), hn, hdt c₁ lps us₁ v hi.symm]
  · change (P'.kInfo.push info)[k]? = some _ at h
    rcases hinfo k _ h with ⟨hlt, h'⟩ | ⟨rfl, hi⟩
    · obtain ⟨kf, h₁, h₂⟩ := hC.kfab k c₁ lps us₁ mI rP base nr isK isEta h'
      refine ⟨kf, ?_, h₂.extR hx.toExtR⟩
      show (P'.kE.push e')[k]? = _
      rw [push_lt (by omega), (entW_eq (hk.entW k)).2.2.2.2.2.2]; exact h₁
    · rw [← hi] at hkey; simp only [infoKey, Prod.mk.injEq] at hkey; obtain ⟨rfl, rfl⟩ := hkey
      refine ⟨kfab, ?_, hkf.extR hx.toExtR⟩
      show (P'.kE.push e')[P.kInfo.size]? = _
      rw [hnew _ _ (by omega), (hke _ _ _ _ _ _ _ _ _ hi.symm).1]
  · change (P'.kInfo.push info)[k]? = some _ at h
    show (P'.kArity.push ar)[k]? = _
    rcases hinfo k _ h with ⟨hlt, h'⟩ | ⟨rfl, rfl⟩
    · rw [push_lt (by omega), (entW_eq (hk.entW k)).2.2.1]; exact hC.ctorAr k i cv nP nF h' hf
    · rw [hkey] at hf; rw [hnew _ _ (by omega), har cv nP nF hf]

theorem g4Entry_kMap (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : TabInv find? findProj? P) :
    (g4Entry find? P c us kfab).2.kMap = P.kMap.insert (c, us) P.kTag.size := by
  obtain ⟨P', _, _, _, _, _, _, _, heq, hk, -⟩ := g4Entry_facts find? findProj? P c us kfab hI
  rw [heq]; show P'.kMap.insert _ _ = _; rw [hk.kMap]

/-- The nested resolution changes the constant map at its own key only. -/
theorem g4ResolveF0_kMap (P : G4Prog) (c : Name) (us : List Level) (hI : TabInv find? findProj? P)
    (x : Name × List Level) (hx : x ≠ (c, us)) :
    (g4ResolveF find? findProj? 0 P c us).2.kMap[x]? = P.kMap[x]? := by
  unfold g4ResolveF
  split
  · rfl
  · dsimp only
    rw [g4Entry_kMap find? findProj? P c us 0 hI, Std.HashMap.getElem?_insert]
    split
    · rename_i hb; exact absurd (eq_of_beq hb).symm hx
    · rfl

/-- An entry's key from the compiler spec's `Approx`. -/
theorem infoKey_of_approx {info : G4Info} {c : Name} {us : List Level}
    (h : Approx (infoTerm info) (.const c us)) : infoKey info = (c, us) := by
  rw [infoTerm_key] at h
  have := h.const_inv
  simp only [Expr.const.injEq] at this
  rw [this.1, this.2]

/-- The nested resolution (no K step) keeps the key invariant. -/
theorem g4ResolveF0_comp (P : G4Prog) (c : Name) (us : List Level) (hI : TabInv find? findProj? P)
    (hC : CompInv find? findProj? P) (hk : kfabKey find? c us = none) :
    CompInv find? findProj? (g4ResolveF find? findProj? 0 P c us).2 := by
  unfold g4ResolveF
  split
  · exact hC
  · rename_i hn
    exact g4Entry_comp find? findProj? P c us 0 hI hC hn (fun _ _ _ _ _ _ => .inl rfl) (.inl ⟨hk, rfl⟩)

/-- **Resolution keeps the key invariant.** -/
theorem g4Resolve_comp (P : G4Prog) (c : Name) (us : List Level) (hI : TabInv find? findProj? P)
    (hC : CompInv find? findProj? P) : CompInv find? findProj? (g4Resolve find? findProj? P c us).2 := by
  unfold g4Resolve g4ResolveF
  split
  · exact hC
  · rename_i hn
    dsimp only
    split
    · split
      · split
        · rename_i f' cv mI rP rl hf hfind hcond _ cvj _ hctor
          have hnk : kfabKey find? rl.ctor (gCmpLevels rl cv.levelParams us cvj.levelParams) = none := by
            unfold kfabKey; rw [hctor]
          have hC₁ := g4ResolveF0_comp find? findProj? P rl.ctor _ hI hC hnk
          have hne : (c, us) ≠ (rl.ctor, gCmpLevels rl cv.levelParams us cvj.levelParams) := by
            intro h; simp only [Prod.mk.injEq] at h; rw [h.1, hctor] at hfind; cases hfind
          have hn₁ := g4ResolveF0_kMap find? findProj? P rl.ctor
            (gCmpLevels rl cv.levelParams us cvj.levelParams) hI (c, us) hne
          obtain ⟨h₁, -, -, info, hinfo, hap⟩ := g4ResolveF_tab find? findProj? 0 P rl.ctor
            (gCmpLevels rl cv.levelParams us cvj.levelParams) hI
          obtain rfl : f' = 0 := (Nat.succ.inj hf).symm
          generalize g4ResolveF find? findProj? 0 P rl.ctor (gCmpLevels rl cv.levelParams us cvj.levelParams) = r
            at h₁ hinfo hC₁ hn₁ ⊢
          obtain ⟨kc, P₁⟩ := r
          dsimp only at h₁ hinfo hC₁ hn₁ ⊢
          rw [hn] at hn₁
          have har := hC₁.ctorAr kc info cvj _ _ hinfo (by rw [infoKey_of_approx hap]; exact hctor)
          rw [get!_of_some har]
          have hkey : kfabKey find? c us = if rl.nfields == 0 && g4Pis cvj.type 0 ≤ mI + 1 then
              some (rl.ctor, gCmpLevels rl cv.levelParams us cvj.levelParams) else none := by
            unfold kfabKey; rw [hfind]; simp only [hcond, ↓reduceIte, hctor]
          split
          · rename_i hc
            refine g4Entry_comp find? findProj? P₁ c us _ h₁ hC₁ hn₁
              (fun cv' mI' rP' isK' rules' hf' => ?_) (.inr ⟨_, kc, info, by simp only [hkey, hc, ↓reduceIte], rfl, hinfo,
                infoKey_of_approx hap⟩)
            rw [hfind] at hf'; cases hf'
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            exact .inr ⟨kc, rl, rfl, lt_of_some hinfo, ⟨_, har, hc.2⟩, rfl, rfl, hc.1⟩
          · rename_i hc
            exact g4Entry_comp find? findProj? P₁ c us 0 h₁ hC₁ hn₁ (fun _ _ _ _ _ _ => .inl rfl)
              (.inl ⟨by simp only [hkey, hc, Bool.false_eq_true, ↓reduceIte], rfl⟩)
        · rename_i f' cv mI rP rl hf hfind hcond _ hctor
          refine g4Entry_comp find? findProj? P c us 0 hI hC hn (fun _ _ _ _ _ _ => .inl rfl) (.inl ⟨?_, rfl⟩)
          unfold kfabKey; rw [hfind]; simp only [hcond, ↓reduceIte]
      · rename_i f' cv mI rP rl hf hfind hcond
        refine g4Entry_comp find? findProj? P c us 0 hI hC hn (fun _ _ _ _ _ _ => .inl rfl) (.inl ⟨?_, rfl⟩)
        unfold kfabKey; rw [hfind]; simp only [hcond]; rfl
    · rename_i hno
      refine g4Entry_comp find? findProj? P c us 0 hI hC hn (fun _ _ _ _ _ _ => .inl rfl) (.inl ⟨?_, rfl⟩)
      unfold kfabKey
      split
      · rename_i cv mI rP rl hfind; exact absurd hfind (hno 0 cv mI rP rl rfl)
      · rfl

/-- **Resolution** returns an entry that denotes the constant, and keeps the
invariant. -/
theorem g4Resolve_spec (P : G4Prog) (c : Name) (us : List Level) (hI : Inv find? findProj? P) :
    Inv find? findProj? (g4Resolve find? findProj? P c us).2 ∧ Ext P (g4Resolve find? findProj? P c us).2 ∧
      (g4Resolve find? findProj? P c us).2.closedNode = P.closedNode ∧
      ∃ info, (g4Resolve find? findProj? P c us).2.kInfo[(g4Resolve find? findProj? P c us).1]? =
          some info ∧ Approx (infoTerm info) (.const c us) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := g4Resolve_tab find? findProj? P c us hI.toTabInv
  exact ⟨⟨h₁, g4Resolve_comp find? findProj? P c us hI.toTabInv hI.toCompInv⟩, h₂, h₃, h₄⟩

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

/-- The key invariant after a code store. -/
theorem CompInv.codes {P : G4Prog} (hC : CompInv find? findProj? P) (a b : Array Nat) :
    CompInv find? findProj? { P with kCode := a, ruleCode := b } where
  closed a' o h := by
    obtain ⟨sl, e, h₀, h₁, h₂, h₃, h₄⟩ := hC.closed a' o h
    exact ⟨sl, e, h₀, h₁, h₂, h₃.extR (ExtR.codes P a b), h₄⟩
  masks := hC.masks
  kMapAll := hC.kMapAll
  slotLt := hC.slotLt
  slotUniq := hC.slotUniq
  defTag := hC.defTag
  kfab k c lps us mI rP base nr isK isEta h := by
    obtain ⟨kf, h₁, h₂⟩ := hC.kfab k c lps us mI rP base nr isK isEta h
    exact ⟨kf, h₁, h₂.extR (ExtR.codes P a b)⟩
  ctorAr := hC.ctorAr

/-- **The invariant after a code store**: every entry is still the
declaration it names. -/
theorem Inv.codes {P : G4Prog} (hI : Inv find? findProj? P) {a b : Array Nat} (ha : a.size = P.kCode.size)
    (hb : b.size = P.ruleCode.size)
    (hent : ∀ k, k < P.kInfo.size → EntOK find? findProj? { P with kCode := a, ruleCode := b } k) :
    Inv find? findProj? { P with kCode := a, ruleCode := b } where
  toCompInv := hI.toCompInv.codes a b
  szs := by
    obtain ⟨⟨e₁, e₂⟩, ⟨r₁, r₂⟩, e₃⟩ := hI.szs
    exact ⟨⟨by rw [← e₁]; exact ha, e₂⟩, ⟨by rw [← r₁]; exact hb, r₂⟩, e₃⟩
  sizes := hI.sizes
  kSlotSize := hI.kSlotSize
  kMap := hI.kMap
  ents := hent
  prjs q hq := (hI.prjs q hq).ext (ExtR.codes P a b) hq
  nidOK := hI.nidOK
  rowsDisj k k' r h h' := hI.rowsDisj k k' r h h'

/-- **The δ store**: a definition entry's compiled body. -/
theorem Inv.setKCode {P : G4Prog} (hI : Inv find? findProj? P) {k o : Nat} {c : Name}
    {lps : List Name} {us : List Level} {v : Expr} (hi : P.kInfo[k]? = some (.defn c lps us v))
    (hc : Comp find? findProj? P o (v.instantiateLevelParams lps us)) :
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
    exact ⟨h₁, h₂, h₃, o + 1, set!_get?_self hks, .inr ⟨o, rfl, hc.extR (ExtR.codes P _ _)⟩⟩
  · have hx := ExtR.codes P (P.kCode.set! k (o + 1)) P.ruleCode
    exact (hI.ents j hj).extR hx hj (set!_get?_ne hjk)
      (fun _ _ _ _ _ _ _ _ _ hi' i _ hi₁ hr => hr.extR hx (hI.rows_lt ⟨_, _, _, _, _, _, _, _, _,
        hi', Nat.le_add_right _ _, by omega⟩) rfl)

/-- **The ι store**: a rule row's compiled right-hand side, at the levels of
the recursor entry that owns the row. -/
theorem Inv.setRuleCode {P : G4Prog} (hI : Inv find? findProj? P) {k ri o : Nat} {c : Name}
    {lps : List Name} {us : List Level} {mI rP base nr : Nat} {isK isEta : Bool}
    (hi : P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta)) (hr₁ : base ≤ ri) (hr₂ : ri < base + nr)
    (hc : Comp find? findProj? P o ((P.rules[ri]!).rhs.instantiateLevelParams lps us)) :
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
      .inr ⟨o, rfl, by rw [← hrhs]; exact hc.extR hx⟩⟩
  · exact hrow.extR hx (hI.rows_lt hown') (set!_get?_ne he)

end ConLeche.Verify.Ground
