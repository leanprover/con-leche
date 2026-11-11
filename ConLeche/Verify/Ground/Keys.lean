module

public import ConLeche.Verify.Ground.Compile

public section

/-!
# The compiled code, exactly (task #423 soundness, layer (d): the compile lemma)

The answer of the ground engine does not depend on the program it starts
from (DESIGN #423 §S.18–§S.19): a run on the declaration's kept program and
a run on a fresh one take the same steps but for the compile stutters of
the fresh one.  The two programs number their nodes, entries, rows, slots,
name ids and strings differently, but every number has a *key* both share:
the term a node was compiled from, an entry's constant and levels, a
slot's owner.  This file states the key of a code node exactly: `Comp P o
t` says that node `o` of `P` is what `g4Comp` builds for `t` (the shape,
the erasure mask, the shared closed arguments), with entries, strings and
projection rows by their contents.  Unlike `Den` it loses nothing, so two
programs' nodes for the same term have the same layout.

`CompInv` is what a program keeps beyond `Inv` for that: a closed
argument's node is the shared node of its term, a memoised mask is the
head's mask, every entry is registered at its key, the slot numbers are
unique per owner, a definition entry's tag and a recursor entry's K word
are the ones `g4Entry` computes, and a stored body is the compile of the
body.  The compile lemma is `g4Comp_comp`.
-/

namespace ConLeche.Verify.Ground

open ConLeche

variable {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}

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
projection is its shared node. -/
inductive CompArg (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Nat → Expr → Prop where
  | shared {o : Nat} {a : Expr} : shKind a = true → a.bvarBRaw = 0 → P.closedNode[a]? = some o →
      CompArg find? findProj? P o a
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
  | .shared h₀ h₁ h₂ => .shared h₀ h₁ (hx.closedNode _ _ h₂)
  | .plain h₀ h₁ => .plain h₀ (Comp.extR hx h₁)
end

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

/-- **What a program keeps for the keys** (beyond `Inv`). -/
structure CompInv (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) : Prop where
  closed : ∀ (a : Expr) (o : Nat), P.closedNode[a]? = some o →
    ∃ sl e, P.code[o]? = some 9 ∧ P.code[o + 1]? = some sl ∧ P.code[o + 2]? = some e ∧
      Comp find? findProj? P e a
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
  codeK : ∀ (k o : Nat) (c : Name) (lps : List Name) (us : List Level) (v : Expr),
    P.kInfo[k]? = some (.defn c lps us v) → P.kCode[k]? = some (o + 1) →
      Comp find? findProj? P o (v.instantiateLevelParams lps us)
  codeR : ∀ (k : Nat) (c : Name) (lps : List Name) (us : List Level) (mI rP base nr : Nat)
    (isK isEta : Bool), P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta) →
      ∀ (i o : Nat) (rl : G4Rule), i < nr → P.ruleCode[base + i]? = some (o + 1) →
        P.rules[base + i]? = some rl → Comp find? findProj? P o (rl.rhs.instantiateLevelParams lps us)

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
theorem Inv.recr_rows {P : G4Prog} (hI : Inv find? findProj? P) {k : Nat} {c : Name} {lps : List Name}
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
    obtain ⟨sl', e, -, h₃, -, -⟩ := hC.closed a o h₁
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
  codeK k o c lps us v h := by simp at h
  codeR k c lps us mI rP base nr isK isEta h := by simp at h

section
variable (find?) (findProj?)

/-- **The key invariant survives growth** that adds no entry, closed node,
mask or slot. -/
theorem CompInv.ext_gen {P P' : G4Prog} (hI : Inv find? findProj? P) (hC : CompInv find? findProj? P)
    (hx : Ext P P') (hkI : P'.kInfo.size = P.kInfo.size)
    (hcl : ∀ (a : Expr) (o : Nat), P'.closedNode[a]? = some o →
      ∃ sl e, P'.code[o]? = some 9 ∧ P'.code[o + 1]? = some sl ∧ P'.code[o + 2]? = some e ∧
        Comp find? findProj? P' e a)
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
  codeK k o c lps us v h hc := by
    have h' := kInfo_back hx.toExtR hkI h
    rw [hx.kCode k (lt_of_some h')] at hc
    exact (hC.codeK k o c lps us v h' hc).extR hx.toExtR
  codeR k c lps us mI rP base nr isK isEta h i o rl hi hc hr := by
    have h' := kInfo_back hx.toExtR hkI h
    have hlt : base + i < P.rules.size := by have := hI.recr_rows h'; omega
    rw [hx.ruleCode _ hlt] at hc
    rw [(rowR_eq (hx.row _ hlt)).1] at hr
    exact (hC.codeR k c lps us mI rP base nr isK isEta h' i o rl hi hc hr).extR hx.toExtR

theorem CompInv.ext {P P' : G4Prog} (hI : Inv find? findProj? P) (hC : CompInv find? findProj? P)
    (hx : Ext P P') (hkI : P'.kInfo.size = P.kInfo.size) (hcl : P'.closedNode = P.closedNode)
    (hm : P'.masks = P.masks) (hkm : P'.kMap = P.kMap) (hks : P'.kSlot = P.kSlot)
    (hns : P'.nslots = P.nslots) : CompInv find? findProj? P' :=
  hC.ext_gen find? findProj? hI hx hkI (fun a o h => by
      rw [hcl] at h
      obtain ⟨sl, e, h₀, h₁, h₂, h₃⟩ := hC.closed a o h
      exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR⟩)
    (fun c m h => hC.masks c m (by rw [← hm]; exact h)) hkm
    (fun sl x h => by rw [hns]; exact hC.slotLt sl x (h.back hC hx.toExtR hcl hks))
    (fun sl x y h h' => hC.slotUniq sl x y (h.back hC hx.toExtR hcl hks) (h'.back hC hx.toExtR hcl hks))

theorem CompInv.emit {P : G4Prog} (hI : Inv find? findProj? P) (hC : CompInv find? findProj? P)
    (ws : Array Nat) : CompInv find? findProj? (P.emit (· ++ ws)) :=
  hC.ext find? findProj? hI (Ext.emit P ws) rfl rfl rfl rfl rfl rfl

theorem CompInv.nid {P : G4Prog} (hI : Inv find? findProj? P) (hC : CompInv find? findProj? P)
    (c : Name) : CompInv find? findProj? (P.nid c).2 := by
  have hk := KeyEq.nid P c
  have hm : (P.nid c).2.masks = P.masks := by rw [nid_eq]
  exact hC.ext find? findProj? hI (hk.ext hI.szs) (by rw [hk.kInfo]) hk.closedNode hm hk.kMap hk.kSlot
    hk.nslots

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
theorem g4Entry_facts (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : Inv find? findProj? P) :
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
        obtain ⟨hk, -, -, -⟩ := rows_fold find? (g4RuleRow find? isK cv.levelParams us)
          (fun P rl hs hn => g4RuleRow_spec find? isK cv.levelParams us P rl hs hn) rules P hI.szs hI.nidOK
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
theorem g4Entry_comp (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : Inv find? findProj? P)
    (hC : CompInv find? findProj? P) (hnone : P.kMap[(c, us)]? = none)
    (hkf₀ : ∀ cv mI rP isK rules, find? c = some (.recInfo cv mI rP isK rules) →
      KfabOK P mI isK rules kfab)
    (hkf : KfabKey find? P c us kfab) : CompInv find? findProj? (g4Entry find? P c us kfab).2 := by
  obtain ⟨-, hx, -, -⟩ := g4Entry_spec find? findProj? P c us kfab hI hkf₀
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
    fun k i cv nP nF h hf => ?_, fun k o c₁ lps us₁ v h hc => ?_,
    fun k c₁ lps us₁ mI rP base nr isK isEta h i o rl hi hc hr => ?_⟩
  · change P'.closedNode[a]? = some o at h
    rw [hk.closedNode] at h
    obtain ⟨sl, e, h₀, h₁, h₂, h₃⟩ := hC.closed a o h
    exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR⟩
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
  · change (P'.kInfo.push info)[k]? = some _ at h
    change (P'.kCode.push 0)[k]? = some (o + 1) at hc
    rcases hinfo k _ h with ⟨hlt, h'⟩ | ⟨rfl, -⟩
    · rw [push_lt (by omega), (entW_eq (hk.entW k)).2.1] at hc
      exact (hC.codeK k o c₁ lps us₁ v h' hc).extR hx.toExtR
    · rw [hnew _ _ (by omega)] at hc; cases hc
  · change (P'.kInfo.push info)[k]? = some _ at h
    change P'.ruleCode[base + i]? = some (o + 1) at hc
    change P'.rules[base + i]? = some rl at hr
    rcases hinfo k _ h with ⟨hlt, h'⟩ | ⟨rfl, hi⟩
    · have hb : base + i < P.rules.size := by have := hI.recr_rows h'; omega
      rw [(rowW_eq (hk.row hI.szs _ hb)).2.1] at hc
      rw [(rowW_eq (hk.row hI.szs _ hb)).1] at hr
      exact (hC.codeR k c₁ lps us₁ mI rP base nr isK isEta h' i o rl hi hc hr).extR hx.toExtR
    · have := hrc _ _ (by rw [(hke _ _ _ _ _ _ _ _ _ hi.symm).2]; omega) hc; omega

theorem g4Entry_kMap (P : G4Prog) (c : Name) (us : List Level) (kfab : Nat) (hI : Inv find? findProj? P) :
    (g4Entry find? P c us kfab).2.kMap = P.kMap.insert (c, us) P.kTag.size := by
  obtain ⟨P', _, _, _, _, _, _, _, heq, hk, -⟩ := g4Entry_facts find? findProj? P c us kfab hI
  rw [heq]; show P'.kMap.insert _ _ = _; rw [hk.kMap]

/-- The nested resolution changes the constant map at its own key only. -/
theorem g4ResolveF0_kMap (P : G4Prog) (c : Name) (us : List Level) (hI : Inv find? findProj? P)
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
theorem g4ResolveF0_comp (P : G4Prog) (c : Name) (us : List Level) (hI : Inv find? findProj? P)
    (hC : CompInv find? findProj? P) (hk : kfabKey find? c us = none) :
    CompInv find? findProj? (g4ResolveF find? findProj? 0 P c us).2 := by
  unfold g4ResolveF
  split
  · exact hC
  · rename_i hn
    exact g4Entry_comp find? findProj? P c us 0 hI hC hn (fun _ _ _ _ _ _ => .inl rfl) (.inl ⟨hk, rfl⟩)

/-- **Resolution keeps the key invariant.** -/
theorem g4Resolve_comp (P : G4Prog) (c : Name) (us : List Level) (hI : Inv find? findProj? P)
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
          obtain ⟨h₁, -, -, info, hinfo, hap⟩ := g4ResolveF_spec find? findProj? 0 P rl.ctor
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

/-- **The mask memo keeps the key invariant**, and its mask is the head's. -/
theorem g4MaskOf_comp (P : G4Prog) (hd : Expr) (hI : Inv find? findProj? P)
    (hC : CompInv find? findProj? P) :
    CompInv find? findProj? (g4MaskOf find? P hd).2 ∧ (g4MaskOf find? P hd).1 = maskHead find? hd := by
  have hk := g4MaskOf_key find? P hd
  have hx := hk.ext hI.szs
  have hkI : (g4MaskOf find? P hd).2.kInfo.size = P.kInfo.size := by rw [hk.kInfo]
  revert hk hx hkI
  unfold g4MaskOf
  split
  · rename_i c us
    split
    · rename_i m hm
      intro _ _ _
      exact ⟨hC, hC.masks c m hm⟩
    · intro hk hx hkI
      refine ⟨hC.ext_gen find? findProj? hI hx hkI (fun a o h => ?_) (fun c' m h => ?_) hk.kMap
        (fun sl x h => ?_) (fun sl x y h h' => ?_), rfl⟩
      · rw [hk.closedNode] at h
        obtain ⟨sl, e, h₀, h₁, h₂, h₃⟩ := hC.closed a o h
        exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR⟩
      · change (P.masks.insert c _)[c']? = some m at h
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i hb; rw [← eq_of_beq hb]; exact (Option.some.inj h).symm
        · exact hC.masks c' m h
      · rw [hk.nslots]; exact hC.slotLt sl x (h.back hC hx.toExtR hk.closedNode hk.kSlot)
      · exact hC.slotUniq sl x y (h.back hC hx.toExtR hk.closedNode hk.kSlot)
          (h'.back hC hx.toExtR hk.closedNode hk.kSlot)
  · rename_i hnc
    intro _ _ _
    refine ⟨hC, ?_⟩
    unfold maskHead; split
    · rename_i c us; exact absurd rfl (hnc c us)
    · rfl

/-- **A shared closed argument keeps the key invariant**, and its node is
the term's shared node. -/
theorem g4CompShared_comp (a : Expr) (comp : G4Prog → Nat × G4Prog)
    (hok : ∀ P, Inv find? findProj? P → CompOK find? findProj? P a (comp P))
    (hcomp : ∀ P, Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (comp P).2 ∧ Comp find? findProj? (comp P).2 (comp P).1 a)
    (P : G4Prog) (hI : Inv find? findProj? P) (hC : CompInv find? findProj? P) (hsh : shKind a = true) :
    CompInv find? findProj? (g4CompShared comp P a).2 ∧
      CompArg find? findProj? (g4CompShared comp P a).2 (g4CompShared comp P a).1 a := by
  unfold g4CompShared
  split
  · rename_i hbr
    have hbr' : a.bvarBRaw = 0 := by simpa using hbr
    split
    · rename_i o ho; exact ⟨hC, .shared hsh hbr' ho⟩
    · obtain ⟨hI₁, -, -⟩ := hok P hI
      obtain ⟨hC₁, hc₁⟩ := hcomp P hI hC
      generalize comp P = r at hI₁ hC₁ hc₁ ⊢
      obtain ⟨ao, P₁⟩ := r
      dsimp only at hI₁ hC₁ hc₁ ⊢
      split
      · rename_i o ho; exact ⟨hC₁, .shared hsh hbr' ho⟩
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
      have hc0 : (P₁.code ++ #[9, P₁.nslots, ao])[P₁.code.size]? = some 9 := by rw [rd0]; rfl
      have hc1 : (P₁.code ++ #[9, P₁.nslots, ao])[P₁.code.size + 1]? = some P₁.nslots := by
        rw [rdR]; rfl
      have hc2 : (P₁.code ++ #[9, P₁.nslots, ao])[P₁.code.size + 2]? = some ao := by rw [rdR]; rfl
      have hlook : ∀ a' o, (P₁.closedNode.insert a P₁.code.size)[a']? = some o →
          (a' = a ∧ o = P₁.code.size) ∨ P₁.closedNode[a']? = some o := by
        intro a' o h
        rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i heq; exact .inl ⟨(eq_of_beq heq).symm, (Option.some.inj h).symm⟩
        · exact .inr h
      have hown : ∀ sl x, SlotOwn { { (P₁.emit (· ++ #[9, P₁.nslots, ao])) with nslots := P₁.nslots + 1 } with
          closedNode := P₁.closedNode.insert a P₁.code.size } sl x →
          SlotOwn P₁ sl x ∨ (x = .inl a ∧ sl = P₁.nslots) := by
        intro sl x h
        cases x with
        | inl a' =>
          obtain ⟨o, h₁, h₂⟩ := h
          change (P₁.code ++ #[9, P₁.nslots, ao])[o + 1]? = some sl at h₂
          rcases hlook a' o h₁ with ⟨rfl, rfl⟩ | h₁
          · rw [hc1] at h₂; exact .inr ⟨rfl, (Option.some.inj h₂).symm⟩
          · obtain ⟨sl', e, -, h₃, -, -⟩ := hC₁.closed a' o h₁
            rw [rdL _ (lt_of_some h₃), h₃] at h₂
            exact .inl ⟨o, h₁, by rw [h₃, h₂]⟩
        | inr k => exact .inl h
      refine ⟨hC₁.ext_gen find? findProj? hI₁ hx rfl (fun a' o h => ?_) hC₁.masks rfl
        (fun sl x h => ?_) (fun sl x y h h' => ?_), .shared hsh hbr' hreg⟩
      · rcases hlook a' o h with ⟨rfl, rfl⟩ | h
        · exact ⟨P₁.nslots, ao, hc0, hc1, hc2, hc₁.extR hx.toExtR⟩
        · obtain ⟨sl, e, h₀, h₁, h₂, h₃⟩ := hC₁.closed a' o h
          exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR⟩
      · show sl < P₁.nslots + 1
        rcases hown sl x h with h | ⟨-, rfl⟩
        · have := hC₁.slotLt sl x h; omega
        · omega
      · rcases hown sl x h with h₁ | ⟨hx₁, hs₁⟩ <;> rcases hown sl y h' with h₂ | ⟨hy₂, hs₂⟩
        · exact hC₁.slotUniq sl x y h₁ h₂
        · have := hC₁.slotLt _ x h₁; omega
        · have := hC₁.slotLt _ y h₂; omega
        · rw [hx₁, hy₂]
  · rename_i hbr
    obtain ⟨hC₁, hc₁⟩ := hcomp P hI hC
    exact ⟨hC₁, .plain (fun _ => by simpa using hbr) hc₁⟩

end

/-- A spine's argument nodes so far, by the mask. -/
@[expose] def ArgsK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (mask : Array Bool) (aos : Array Nat) (args : List Expr) : Prop :=
  aos.size = args.length ∧ ∀ j (hj : j < aos.size),
    (mask.getD j false = true ∧ P.code[aos[j]]? = some 8) ∨
      (mask.getD j false = false ∧ CompArg find? findProj? P aos[j] (args.getD j bot))

theorem ArgsK.extR {P P' : G4Prog} (hx : ExtR P P') {mask : Array Bool} {aos : Array Nat}
    {args : List Expr} (h : ArgsK find? findProj? P mask aos args) : ArgsK find? findProj? P' mask aos args :=
  ⟨h.1, fun j hj => (h.2 j hj).imp (fun ⟨a, b⟩ => ⟨a, hx.code_some b⟩) (fun ⟨a, b⟩ => ⟨a, b.extR hx⟩)⟩

theorem ArgsK.push {P : G4Prog} {mask : Array Bool} {aos : Array Nat} {args : List Expr}
    (h : ArgsK find? findProj? P mask aos args) {o : Nat} {a : Expr}
    (ho : (mask.getD aos.size false = true ∧ P.code[o]? = some 8) ∨
      (mask.getD aos.size false = false ∧ CompArg find? findProj? P o a)) :
    ArgsK find? findProj? P mask (aos.push o) (args ++ [a]) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  rw [Array.size_push] at hj
  rcases Nat.lt_or_ge j aos.size with hj' | hj'
  · rw [Array.getElem_push_lt hj', getD_append_left _ (by rw [← h.1]; exact hj')]
    exact h.2 j hj'
  · obtain rfl : j = aos.size := by omega
    rw [Array.getElem_push_eq, h.1, getD_append_len, ← h.1]
    exact ho

/-- The spine node's argument nodes, read from the code. -/
theorem ArgsK.compArgs {P : G4Prog} {mask : Array Bool} {aos : Array Nat} {args : List Expr}
    (h : ArgsK find? findProj? P mask aos args) {p : Nat}
    (hcode : ∀ j (hj : j < aos.size), P.code[p + j]? = some aos[j]) :
    ∀ m i, i + m = args.length → CompArgs find? findProj? P mask (p + i) i (args.drop i) := by
  intro m
  induction m with
  | zero => intro i hi; rw [List.drop_eq_nil_of_le (by omega)]; exact .nil
  | succ m ih =>
    intro i hi
    have hi' : i < aos.size := by rw [h.1]; omega
    have hr := ih (i + 1) (by omega)
    rw [show p + (i + 1) = p + i + 1 by omega] at hr
    rw [List.drop_eq_getElem_cons (by omega)]
    have hg : args.getD i bot = args[i]'(by omega) := getD_lt _ (by omega)
    rcases h.2 i hi' with ⟨hm, h8⟩ | ⟨hm, ha⟩
    · exact .erased (hcode i hi') hm h8 hr
    · rw [hg] at ha; exact .arg (hcode i hi') hm ha hr

section
variable (find?) (findProj?)

/-- One argument step keeps the key invariant. -/
theorem g4ArgStep_comp {α : Type} (ev : α → Expr) (compArg : G4Prog → α → Nat × G4Prog)
    (harg : ∀ P a, Inv find? findProj? P → CompOK find? findProj? P (ev a) (compArg P a))
    (hargK : ∀ P a, Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (compArg P a).2 ∧ CompArg find? findProj? (compArg P a).2 (compArg P a).1 (ev a))
    (mask : Array Bool) (acc : Array Nat × G4Prog) (done : List Expr) (a : α)
    (h₁ : Inv find? findProj? acc.2)
    (h₄ : CompInv find? findProj? acc.2) (h₅ : ArgsK find? findProj? acc.2 mask acc.1 done) :
    CompInv find? findProj? (g4ArgStep compArg mask acc a).2 ∧
      ArgsK find? findProj? (g4ArgStep compArg mask acc a).2 mask (g4ArgStep compArg mask acc a).1
        (done ++ [ev a]) := by
  unfold g4ArgStep
  split
  · rename_i hm
    dsimp only
    rw [emit_append1]
    have hx := Ext.emit acc.2 #[8]
    refine ⟨h₄.emit find? findProj? h₁ _, (h₅.extR hx.toExtR).push (.inl ⟨by rw [h₅.1] at hm ⊢; exact hm, ?_⟩)⟩
    show (acc.2.code ++ #[8])[acc.2.code.size]? = some 8; rw [rd0]; rfl
  · rename_i hm
    obtain ⟨-, hx', -⟩ := harg acc.2 a h₁
    obtain ⟨hC', hc'⟩ := hargK acc.2 a h₁ h₄
    generalize compArg acc.2 a = r at hx' hC' hc' ⊢
    obtain ⟨ao, P'⟩ := r
    dsimp only at hx' hC' hc' ⊢
    exact ⟨hC', (h₅.extR hx'.toExtR).push (.inr ⟨by simpa using hm, hc'⟩)⟩

theorem g4ArgFold_comp {α : Type} (ev : α → Expr) (compArg : G4Prog → α → Nat × G4Prog)
    (harg : ∀ P a, Inv find? findProj? P → CompOK find? findProj? P (ev a) (compArg P a))
    (hargK : ∀ P a, Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (compArg P a).2 ∧ CompArg find? findProj? (compArg P a).2 (compArg P a).1 (ev a))
    (mask : Array Bool) {P₁ : G4Prog} : ∀ (l : List α) (acc : Array Nat × G4Prog) (done : List Expr),
      Inv find? findProj? acc.2 → Ext P₁ acc.2 → ArgsOK acc.2 acc.1 done →
      CompInv find? findProj? acc.2 → ArgsK find? findProj? acc.2 mask acc.1 done →
      CompInv find? findProj? (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        ArgsK find? findProj? (l.foldl (g4ArgStep compArg mask) acc).2 mask
          (l.foldl (g4ArgStep compArg mask) acc).1 (done ++ l.map ev)
  | [], acc, done, _, _, _, h₄, h₅ => by simpa using ⟨h₄, h₅⟩
  | a :: l, acc, done, h₁, h₂, h₃, h₄, h₅ => by
    obtain ⟨h₁', h₂', h₃'⟩ := g4ArgStep_spec find? findProj? ev compArg harg mask acc done a h₁ h₂ h₃
    obtain ⟨h₄', h₅'⟩ := g4ArgStep_comp find? findProj? ev compArg harg hargK mask acc done a h₁ h₄ h₅
    have := g4ArgFold_comp ev compArg harg hargK mask l _ _ h₁' h₂' h₃' h₄' h₅'
    simpa using this

/-- **A spine keeps the key invariant**, and its node is the spine of the
compiled head and arguments. -/
theorem g4CompSpine_comp {α : Type} (ev : α → Expr) (hd : Expr) (comp : G4Prog → Nat × G4Prog)
    (compArg : G4Prog → α → Nat × G4Prog)
    (hcomp : ∀ P, Inv find? findProj? P → CompOK find? findProj? P hd (comp P))
    (hcompK : ∀ P, Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (comp P).2 ∧ Comp find? findProj? (comp P).2 (comp P).1 hd)
    (harg : ∀ P a, Inv find? findProj? P → CompOK find? findProj? P (ev a) (compArg P a))
    (hargK : ∀ P a, Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (compArg P a).2 ∧ CompArg find? findProj? (compArg P a).2 (compArg P a).1 (ev a))
    (P : G4Prog) (args : List α) (mask : Array Bool) (hI : Inv find? findProj? P)
    (hC : CompInv find? findProj? P) :
    CompInv find? findProj? (g4CompSpine comp compArg P args mask).2 ∧
      ∃ ho, (g4CompSpine comp compArg P args mask).2.code[(g4CompSpine comp compArg P args mask).1]? = some 1 ∧
        (g4CompSpine comp compArg P args mask).2.code[(g4CompSpine comp compArg P args mask).1 + 1]? = some ho ∧
        (g4CompSpine comp compArg P args mask).2.code[(g4CompSpine comp compArg P args mask).1 + 2]? =
          some (args.map ev).length ∧
        Comp find? findProj? (g4CompSpine comp compArg P args mask).2 ho hd ∧
        CompArgs find? findProj? (g4CompSpine comp compArg P args mask).2 mask
          ((g4CompSpine comp compArg P args mask).1 + 3) 0 (args.map ev) := by
  unfold g4CompSpine
  obtain ⟨hI₁, -, -⟩ := hcomp P hI
  obtain ⟨hC₁, hch⟩ := hcompK P hI hC
  generalize comp P = r at hI₁ hC₁ hch ⊢
  obtain ⟨ho, P₁⟩ := r
  dsimp only at hI₁ hC₁ hch ⊢
  obtain ⟨hI₂, hx₂, -⟩ := g4ArgFold_spec find? findProj? ev compArg harg mask (P₁ := P₁) args (#[], P₁) []
    hI₁ (Ext.refl _) ⟨rfl, fun j hj => absurd hj (by simp)⟩
  obtain ⟨hC₂, hargs⟩ := g4ArgFold_comp find? findProj? ev compArg harg hargK mask (P₁ := P₁) args (#[], P₁) []
    hI₁ (Ext.refl _) ⟨rfl, fun j hj => absurd hj (by simp)⟩ hC₁ ⟨rfl, fun j hj => absurd hj (by simp)⟩
  generalize args.foldl (g4ArgStep compArg mask) (#[], P₁) = r at hI₂ hx₂ hC₂ hargs ⊢
  obtain ⟨aos, P₂⟩ := r
  dsimp only at hI₂ hx₂ hC₂ hargs ⊢
  rw [List.nil_append] at hargs
  rw [emit_spine]
  have hx := Ext.emit P₂ (#[1, ho, aos.size] ++ aos)
  have hcode : ∀ j (hj : j < aos.size),
      (P₂.emit (· ++ (#[1, ho, aos.size] ++ aos))).code[P₂.code.size + 3 + j]? = some aos[j] := by
    intro j hj
    show (P₂.code ++ _)[P₂.code.size + 3 + j]? = _
    rw [Nat.add_assoc, rdR, Array.getElem?_append_right (by simp)]
    simp [hj]
  have hca := (hargs.extR hx.toExtR).compArgs hcode (args.map ev).length 0 (by simp)
  rw [Nat.add_zero, List.drop_zero] at hca
  refine ⟨hC₂.emit find? findProj? hI₂ _, ho, ?_, ?_, ?_, (hch.extR hx₂.toExtR).extR hx.toExtR, hca⟩
  · show (P₂.code ++ _)[P₂.code.size]? = _
    rw [rd0, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 1]? = _
    rw [rdR, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 2]? = _
    rw [rdR, Array.getElem?_append_left (by simp), hargs.1]; rfl

/-- A projection node keeps the key invariant (the program steps of `g4Comp`'s
projection case, as `proj_emit_ok` takes them). -/
theorem proj_emit_comp {P₁ Q : G4Prog} {sn : Name} {i so : Nat} {e : Expr} {pj : G4Proj} {en : ProjEntry}
    (hI₁ : Inv find? findProj? P₁) (hC₁ : CompInv find? findProj? P₁) (hce : Comp find? findProj? P₁ so e)
    (hc : Q.code = P₁.code) (hi : Q.kInfo = P₁.kInfo)
    (hm : Q.kMap = P₁.kMap) (hcl : Q.closedNode = P₁.closedNode) (hs : Q.strs = P₁.strs)
    (hks : Q.kSlot = P₁.kSlot) (hn : Q.nslots = P₁.nslots) (hp : Q.projs = P₁.projs.push pj)
    (q : Nat) (hq : q = P₁.projs.size) (he : ∀ k, Q.entW k = P₁.entW k) (hrow : ∀ r, Q.rowW r = P₁.rowW r)
    (hrs : Q.rules.size = P₁.rules.size) (hprj : ∀ q', q' < P₁.projs.size → Q.prjW q' = P₁.prjW q')
    (hnid : ∀ (c : Name) (i : Nat), P₁.nids[c]? = some i → Q.nids[c]? = some i) (hfl : Q.flags = P₁.flags)
    (hep : Q.site = P₁.site) (hmk : Q.masks = P₁.masks) (hf : findProj? sn i = some en)
    (hpj : pj = ⟨sn, en.ctor, i, en.numParams, en.numFields, en.levelParams.length, true, en⟩) :
    CompInv find? findProj? (Q.emit (fun c => ((c.push 7).push (q + 1)).push so)) ∧
      Comp find? findProj? (Q.emit (fun c => ((c.push 7).push (q + 1)).push so)) Q.code.size (.proj sn i e) := by
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
  refine ⟨hC₁.ext find? findProj? hI₁ hx (by show Q.kInfo.size = _; rw [hi]) hcl hmk hm hks hn,
    .proj (q := q) hf ?_ ?_ ?_ ?_ (hce.extR hx.toExtR)⟩
  · show (Q.code ++ _)[Q.code.size]? = _; rw [rd0]; rfl
  · show (Q.code ++ _)[Q.code.size + 1]? = _; rw [rdR]; rfl
  · show Q.projs[q]? = _; rw [hp, hq, ← hpj]; exact Array.getElem?_push_size
  · show (Q.code ++ _)[Q.code.size + 2]? = _; rw [rdR]; rfl

/-- A neutral node `[8]`. -/
theorem comp_neutral {P : G4Prog} (hI : Inv find? findProj? P) (hC : CompInv find? findProj? P) :
    CompInv find? findProj? (P.emit (fun c => c.push 8)) ∧
      (P.emit (fun c => c.push 8)).code[P.code.size]? = some 8 := by
  rw [emit_append1]
  exact ⟨hC.emit find? findProj? hI _, by show (P.code ++ #[8])[P.code.size]? = some 8; rw [rd0]; rfl⟩

/-- **The compile lemma** (`g4Comp`, by `g4Comp_spec_lt`'s size induction):
the node the compiler returns is the compile of the term, and the program
keeps the key invariant. -/
theorem g4Comp_comp_lt : ∀ (n : Nat),
    (∀ (P : G4Prog) (e : Expr), sizeOf e < n → Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (g4Comp find? findProj? P e).2 ∧
        Comp find? findProj? (g4Comp find? findProj? P e).2 (g4Comp find? findProj? P e).1 e) ∧
    (∀ (P : G4Prog) (a : Expr), sizeOf a < n → Inv find? findProj? P → CompInv find? findProj? P →
      CompInv find? findProj? (g4CompArg find? findProj? P a).2 ∧
        CompArg find? findProj? (g4CompArg find? findProj? P a).2 (g4CompArg find? findProj? P a).1 a) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ihC, ihA⟩ := ih
    have hC : ∀ (P : G4Prog) (e : Expr), sizeOf e < n + 1 → Inv find? findProj? P →
        CompInv find? findProj? P →
        CompInv find? findProj? (g4Comp find? findProj? P e).2 ∧
          Comp find? findProj? (g4Comp find? findProj? P e).2 (g4Comp find? findProj? P e).1 e := by
      intro P e hs hI hK
      cases e with
      | bvar i =>
        unfold g4Comp; dsimp only
        rw [emit_append2]
        refine ⟨hK.emit find? findProj? hI _, .bvar ?_ ?_⟩
        · show (P.code ++ #[0, i])[P.code.size]? = some 0; rw [rd0]; rfl
        · show (P.code ++ #[0, i])[P.code.size + 1]? = some i; rw [rdR]; rfl
      | fvar i ty =>
        unfold g4Comp; obtain ⟨h₁, h₂⟩ := comp_neutral find? findProj? hI hK; exact ⟨h₁, .fvar h₂⟩
      | sort u =>
        unfold g4Comp; obtain ⟨h₁, h₂⟩ := comp_neutral find? findProj? hI hK; exact ⟨h₁, .sort h₂⟩
      | forallE ty b =>
        unfold g4Comp; obtain ⟨h₁, h₂⟩ := comp_neutral find? findProj? hI hK; exact ⟨h₁, .forallE h₂⟩
      | lit l =>
        cases l with
        | natVal n =>
          unfold g4Comp; dsimp only
          rw [emit_append2]
          refine ⟨hK.emit find? findProj? hI _, .natLit ?_ ?_⟩
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
          refine ⟨hK.ext find? findProj? hI hx rfl rfl rfl rfl rfl rfl,
            .strLit (si := P.strs.size) ?_ ?_ ?_⟩
          · show (P.code ++ #[6, P.strs.size])[P.code.size]? = some 6; rw [rd0]; rfl
          · show (P.code ++ #[6, P.strs.size])[P.code.size + 1]? = some P.strs.size; rw [rdR]; rfl
          · show (P.strs.push str)[P.strs.size]? = some str; exact Array.getElem?_push_size
      | lam ty b =>
        unfold g4Comp; dsimp only
        have hsb : sizeOf b < n := by simp only [Expr.lam.sizeOf_spec] at hs; omega
        obtain ⟨hI₁, -, -⟩ := g4Comp_spec find? findProj? P b hI
        obtain ⟨hK₁, hcb⟩ := ihC P b hsb hI hK
        generalize g4Comp find? findProj? P b = r at hI₁ hK₁ hcb ⊢
        obtain ⟨bo, P₁⟩ := r
        dsimp only at hI₁ hK₁ hcb ⊢
        by_cases h2 : (P₁.code[bo]! == 2) = true
        · simp only [h2, ↓reduceIte]
          rw [emit_append4]
          obtain ⟨x, hx₀⟩ := hcb.tag
          have hb2 : P₁.code[bo]? = some 2 := by
            rw [hx₀, ← get!_of_some hx₀, eq_of_beq h2]
          obtain ⟨ty', b', rfl⟩ := hcb.lam_tag.mp hb2
          obtain ⟨tn', inner', ht, hin, htn⟩ : ∃ tn' inner', P₁.code[bo + 2]? = some tn' ∧
              P₁.code[bo + 3]? = some inner' ∧ tn' ≥ 1 := by
            cases hcb with
            | lam _ _ h₂ h₃ _ htel =>
              refine ⟨_, _, h₂, h₃, ?_⟩
              rcases htel with ⟨-, -, -, h⟩ | ⟨-, h, -⟩ <;> omega
          rw [get!_of_some ht, get!_of_some hin]
          have hx := Ext.emit P₁ #[2, bo, tn' + 1, inner']
          refine ⟨hK₁.emit find? findProj? hI₁ _, .lam (tn := tn' + 1) (inner := inner') ?_ ?_ ?_ ?_
            (hcb.extR hx.toExtR) (.inl ⟨?_, ?_, ?_, ?_⟩)⟩
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
          have hbo : bo < P₁.code.size := by obtain ⟨x, hx₀⟩ := hcb.tag; exact lt_of_some hx₀
          refine ⟨hK₁.emit find? findProj? hI₁ _, .lam (tn := 1) (inner := bo) ?_ ?_ ?_ ?_
            (hcb.extR hx.toExtR) (.inr ⟨?_, rfl, rfl⟩)⟩
          · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 2]? = _; rw [rdR]; rfl
          · show (P₁.code ++ _)[P₁.code.size + 3]? = _; rw [rdR]; rfl
          · rw [hx.code bo hbo, some_of_lt hbo]
            intro h; apply h2; rw [Option.some.inj h]; rfl
      | letE ty v b =>
        unfold g4Comp; dsimp only
        have hsv : sizeOf v < n := by simp only [Expr.letE.sizeOf_spec] at hs; omega
        have hsb : sizeOf b < n := by simp only [Expr.letE.sizeOf_spec] at hs; omega
        obtain ⟨hI₁, -, -⟩ := g4Comp_spec_lt find? findProj? (sizeOf v + 1) |>.2 P v (Nat.lt_succ_self _) hI
        obtain ⟨hK₁, hcv⟩ := ihA P v hsv hI hK
        generalize g4CompArg find? findProj? P v = r at hI₁ hK₁ hcv ⊢
        obtain ⟨vo, P₁⟩ := r
        dsimp only at hI₁ hK₁ hcv ⊢
        obtain ⟨hI₂, hx₂, -⟩ := g4Comp_spec find? findProj? P₁ b hI₁
        obtain ⟨hK₂, hcb⟩ := ihC P₁ b hsb hI₁ hK₁
        generalize g4Comp find? findProj? P₁ b = r at hI₂ hx₂ hK₂ hcb ⊢
        obtain ⟨bo, P₂⟩ := r
        dsimp only at hI₂ hx₂ hK₂ hcb ⊢
        rw [emit_append3]
        have hx := Ext.emit P₂ #[3, vo, bo]
        refine ⟨hK₂.emit find? findProj? hI₂ _, .letE ?_ ?_ ?_ ((hcv.extR hx₂.toExtR).extR hx.toExtR)
          (hcb.extR hx.toExtR)⟩
        · show (P₂.code ++ _)[P₂.code.size]? = _; rw [rd0]; rfl
        · show (P₂.code ++ _)[P₂.code.size + 1]? = _; rw [rdR]; rfl
        · show (P₂.code ++ _)[P₂.code.size + 2]? = _; rw [rdR]; rfl
      | const c us =>
        unfold g4Comp; dsimp only
        obtain ⟨hI₁, -, -, info, hinfo, ha⟩ := g4Resolve_spec find? findProj? P c us hI
        have hK₁ := g4Resolve_comp find? findProj? P c us hI hK
        generalize g4Resolve find? findProj? P c us = r at hI₁ hK₁ hinfo ⊢
        obtain ⟨k, P₁⟩ := r
        dsimp only at hI₁ hK₁ hinfo ⊢
        rw [emit_append2]
        have hx := Ext.emit P₁ #[4, k]
        refine ⟨hK₁.emit find? findProj? hI₁ _, .const ?_ ?_ (hx.kInfo_some hinfo) (infoKey_of_approx ha)⟩
        · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
        · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
      | proj sn i e =>
        unfold g4Comp; dsimp only
        split
        · rename_i en hf
          have hse : sizeOf e < n := by simp only [Expr.proj.sizeOf_spec] at hs; omega
          obtain ⟨hI₁, -, -⟩ := g4Comp_spec find? findProj? P e hI
          obtain ⟨hK₁, hce⟩ := ihC P e hse hI hK
          generalize g4Comp find? findProj? P e = r at hI₁ hK₁ hce ⊢
          obtain ⟨so, P₁⟩ := r
          dsimp only at hI₁ hK₁ hce ⊢
          generalize hn : P₁.nid en.ctor = rn
          obtain ⟨ni, P₂⟩ := rn
          have hk : KeyEq P₁ P₂ := by have := KeyEq.nid P₁ en.ctor; rw [hn] at this; exact this
          have hP₂ : P₂ = { P₁ with nids := P₂.nids } := by
            rw [show P₂ = (P₁.nid en.ctor).2 by rw [hn]]; exact nid_eq P₁ en.ctor
          dsimp only
          refine proj_emit_comp find? findProj? (en := en) (sn := sn) (i := i) hI₁ hK₁ hce ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ _ ?_ (fun k => hk.entW k) ?_ ?_ ?_ hk.nids ?_ ?_ ?_ hf rfl
          · exact hk.code
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
          · rw [hP₂]
        · rename_i hf
          obtain ⟨h₁, h₂⟩ := comp_neutral find? findProj? hI hK; exact ⟨h₁, .projNone hf h₂⟩
      | app fn arg =>
        unfold g4Comp; dsimp only
        have hk₁ := g4MaskOf_key find? P (Expr.app fn arg).getAppFn
        have hn₁ := g4MaskOf_nids find? P (Expr.app fn arg).getAppFn
        obtain ⟨hK₁, hm₁⟩ := g4MaskOf_comp find? findProj? P (Expr.app fn arg).getAppFn hI hK
        generalize g4MaskOf find? P (Expr.app fn arg).getAppFn = r at hk₁ hn₁ hK₁ hm₁ ⊢
        obtain ⟨mask, P₁⟩ := r
        dsimp only at hk₁ hK₁ hm₁ ⊢
        have hI₁ := hk₁.inv hI (by unfold NidOK; rw [hn₁]; exact hI.nidOK)
        have hsf := Expr.sizeOf_getAppFn_le fn
        simp only [Expr.app.sizeOf_spec] at hs
        have hsa : ∀ (a : {a // a ∈ (Expr.app fn arg).getAppArgs}), sizeOf a.1 < n := fun a => by
          have := Expr.sizeOf_lt_of_mem_getAppArgs a.2
          simp only [Expr.app.sizeOf_spec] at this; omega
        have hsh : sizeOf (Expr.app fn arg).getAppFn < n := by simp only [Expr.getAppFn]; omega
        obtain ⟨hK₂, ho, h₀, h₁, h₂, hh, has⟩ := g4CompSpine_comp find? findProj? Subtype.val
          (Expr.app fn arg).getAppFn
          (fun P => g4Comp find? findProj? P (Expr.app fn arg).getAppFn)
          (fun P (a : {a // a ∈ (Expr.app fn arg).getAppArgs}) => g4CompArg find? findProj? P a.1)
          (fun P hI => g4Comp_spec find? findProj? P _ hI)
          (fun P hI hK => ihC P _ hsh hI hK)
          (fun P a hI => (g4Comp_spec_lt find? findProj? (sizeOf a.1 + 1)).2 P a.1 (Nat.lt_succ_self _) hI)
          (fun P a hI hK => ihA P a.1 (hsa a) hI hK) P₁
          (Expr.app fn arg).getAppArgs.attach mask hI₁ hK₁
        rw [List.attach_map_subtype_val] at h₂ has
        subst hm₁
        exact ⟨hK₂, .app h₀ h₁ h₂ rfl hh has⟩
    refine ⟨hC, fun P a hs hI hK => ?_⟩
    unfold g4CompArg
    split
    all_goals first
      | exact g4CompShared_comp find? findProj? _ _ (fun P hI => g4Comp_spec find? findProj? P _ hI)
          (fun P hI hK => hC P _ (by assumption) hI hK) P hI hK rfl
      | (obtain ⟨h₁, h₂⟩ := hC P a hs hI hK
         exact ⟨h₁, .plain (fun h => by simp [shKind] at h) h₂⟩)

/-- **The compile lemma**: `g4Comp_comp_lt` at the term's size. -/
theorem g4Comp_comp (P : G4Prog) (e : Expr) (hI : Inv find? findProj? P) (hK : CompInv find? findProj? P) :
    CompInv find? findProj? (g4Comp find? findProj? P e).2 ∧
      Comp find? findProj? (g4Comp find? findProj? P e).2 (g4Comp find? findProj? P e).1 e :=
  (g4Comp_comp_lt find? findProj? (sizeOf e + 1)).1 P e (Nat.lt_succ_self _) hI hK

end

end ConLeche.Verify.Ground
