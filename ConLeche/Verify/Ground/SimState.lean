module

public import ConLeche.Verify.Ground.SimFrames
public import ConLeche.Verify.Ground.Run
public import ConLeche.Verify.Ground.Memo

public section

/-!
# Two machine states, one run (task #423 soundness, layer (d), item 2(c))

The relation `MRel` between a state of a run on program `PA` (lookups
`f₁`/`p₁`) and one on `PB` (`f₂`/`p₂`) that the step simulation keeps.  The
two runs allocate their cells, values, environment records, argument cells
and memo records in lockstep, so those numbers are one on both sides: `ev`
and `argA` are equal, `cel`, `val` and `mem` have one size and agree word
for word, except where a word names something the two programs number
apart: a code node (two nodes compiled from one term, `TRel`), an entry
(`ERel`), a string (`StrRel`).  The frame stacks are `FsRel`.  The sharing
slots agree by owner (`SlotRel`): a closed term or an entry related on the
other side, and every slot set in this run has an owner on both sides.

Agreement of the lookups is asked only on the names in `N`: every term the
relation names has its constants and projection structures in `N`
(`NamesIn`), and so has every related entry.  For the kept/fresh instance
the lookups are one and `N` is everything; for the environment-extension
instance `N` is the smaller environment's names.
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- The `Nat` basis is in `N`. -/
@[expose] def NatN (N : Name → Prop) : Prop :=
  N natName ∧ N natZeroName ∧ N natSuccName

/-- The names a string literal reads (`strLitStored`'s, which
`strLitToConstructor` mentions) are in `N`. -/
@[expose] def StrNames (N : Name → Prop) : Prop :=
  NatN N ∧ N stringName ∧ N stringOfListName ∧ N listName ∧ N listNilName ∧ N listConsName ∧
    N charName ∧ N charOfNatName

/-- The constants and projection structures of a term are in `N`, a
literal's basis included (as `Expr.constsResolve`). -/
@[expose] def NamesIn (N : Name → Prop) : Expr → Prop
  | .lit (.natVal _) => NatN N
  | .lit (.strVal _) => StrNames N
  | .const c _ => N c
  | .app f x => NamesIn N f ∧ NamesIn N x
  | .lam ty b => NamesIn N ty ∧ NamesIn N b
  | .forallE ty b => NamesIn N ty ∧ NamesIn N b
  | .letE ty v b => NamesIn N ty ∧ NamesIn N v ∧ NamesIn N b
  | .proj sn _ e => N sn ∧ NamesIn N e
  | .fvar _ ty => NamesIn N ty
  | _ => True

theorem NamesIn.univ : ∀ (t : Expr), NamesIn (fun _ => True) t
  | .bvar _ | .sort _ | .const _ _ => trivial
  | .lit (.natVal _) => ⟨trivial, trivial, trivial⟩
  | .lit (.strVal _) => ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  | .fvar _ ty => NamesIn.univ ty
  | .app f x | .lam f x | .forallE f x => ⟨NamesIn.univ f, NamesIn.univ x⟩
  | .letE ty v b => ⟨NamesIn.univ ty, NamesIn.univ v, NamesIn.univ b⟩
  | .proj _ _ e => ⟨trivial, NamesIn.univ e⟩

/-- **A compiled body's key**: an entry of key `κ` whose body is compiled. -/
@[expose] def CodeK (P : G4Prog) (κ : Name × List Level) : Prop :=
  ∃ (k : Nat) (i : G4Info), P.kInfo[k]? = some i ∧ infoKey i = κ ∧ P.kCode[k]! ≠ 0

/-- **A compiled right-hand side's key**: rule `d` of a recursor entry of
key `κ`. -/
@[expose] def RuleK (P : G4Prog) (κ : Name × List Level) (d : Nat) : Prop :=
  ∃ (k : Nat) (c : Name) (lps : List Name) (us : List Level) (mI rP base nr : Nat) (isK isEta : Bool),
    P.kInfo[k]? = some (G4Info.recr c lps us mI rP base nr isK isEta) ∧
    (c, us) = κ ∧ d < nr ∧ P.ruleCode[base + d]! ≠ 0

/-- **Lock-step**: two programs that have compiled the same bodies and
right-hand sides (two fresh runs in step do). -/
@[expose] def CodeSame (PA PB : G4Prog) : Prop :=
  (∀ κ, CodeK PB κ ↔ CodeK PA κ) ∧ ∀ κ d, RuleK PB κ d ↔ RuleK PA κ d

section
variable (j : Nat) (N : Name → Prop) (f₁ : Name → Option ConstantInfo) (p₁ : Name → Nat → Option ProjEntry)
  (f₂ : Name → Option ConstantInfo) (p₂ : Name → Nat → Option ProjEntry)

/-- **Two code words of one term** (a node, or an argument-position node),
the term's names in `N`. -/
@[expose] def TRel (PA PB : G4Prog) (oA oB : Nat) : Prop :=
  ∃ t, NamesIn N t ∧
    ((Comp f₁ p₁ PA oA t ∧ Comp f₂ p₂ PB oB t) ∨ (CompArg f₁ p₁ PA oA t ∧ CompArg f₂ p₂ PB oB t))

/-- Two string indices of one string. -/
@[expose] def StrRel (PA PB : G4Prog) (a b : Nat) : Prop :=
  ∃ s, PA.strs[a]? = some s ∧ PB.strs[b]? = some s

/-- **A value record's payload word** by the record's tag: a closure's λ
node, a constructor's or partial application's entry, a string's index
(the string basis in `N`), a literal (the `Nat` basis in `N`); otherwise
(the neutral) one word. -/
@[expose] def ValW (PA PB : G4Prog) (tag a b : Nat) : Prop :=
  match tag with
  | 0 => TRel N f₁ p₁ f₂ p₂ PA PB a b
  | 1 => ERel N PA PB a b
  | 2 => b = a ∧ NatN N
  | 3 => StrRel PA PB a b ∧ StrNames N
  | 4 => ERel N PA PB a b
  | _ => b = a

/-- **The value records**: one size, and record by record one tag, one
environment and length word, the payload by `ValW`. -/
@[expose] def ValRel (PA PB : G4Prog) (va vb : Array Nat) : Prop :=
  vb.size = va.size ∧ ∀ v, v < va.size / 4 →
    vb[4 * v]! = va[4 * v]! ∧ vb[4 * v + 2]! = va[4 * v + 2]! ∧ vb[4 * v + 3]! = va[4 * v + 3]! ∧
      ValW N f₁ p₁ f₂ p₂ PA PB va[4 * v]! va[4 * v + 1]! vb[4 * v + 1]!

/-- **The cells**: one size, one state; a thunk's code by `TRel` and its
environment one (the machine reads a cell's code and environment only
while it is a thunk). -/
@[expose] def CelRel (PA PB : G4Prog) (ca cb : Array Nat) : Prop :=
  cb.size = ca.size ∧ ∀ c, c < ca.size / 4 → cb[4 * c]! = ca[4 * c]! ∧
    (ca[4 * c]! = 0 → TRel N f₁ p₁ f₂ p₂ PA PB ca[4 * c + 1]! cb[4 * c + 1]! ∧
      cb[4 * c + 2]! = ca[4 * c + 2]!)

/-- **The memo records**: one size, the entries related, the spans and
cells one. -/
@[expose] def MemRel (PA PB : G4Prog) (ma mb : Array Nat) : Prop :=
  mb.size = ma.size ∧ ∀ r, r < ma.size / 4 → ERel N PA PB ma[4 * r]! mb[4 * r]! ∧
    mb[4 * r + 1]! = ma[4 * r + 1]! ∧ mb[4 * r + 2]! = ma[4 * r + 2]! ∧ mb[4 * r + 3]! = ma[4 * r + 3]!

/-- Two slot owners with one key. -/
@[expose] def OwnRel (PA PB : G4Prog) : Expr ⊕ Nat → Expr ⊕ Nat → Prop
  | .inl a, .inl b => a = b
  | .inr kA, .inr kB => EntRel PA PB kA kB
  | _, _ => False

/-- **The sharing slots, by owner**: slots of related owners read alike, and
a slot either side has set in this run has an owner related on the other
side (so an owner one side adds later reads empty on both). -/
@[expose] def SlotRel (PA PB : G4Prog) (sa sb : Array Nat) : Prop :=
  (∀ slA slB x y, SlotOwn PA slA x → SlotOwn PB slB y → OwnRel PA PB x y →
      g4SlotGet sb PB.epBase slB = g4SlotGet sa PA.epBase slA) ∧
    (∀ slA, g4SlotGet sa PA.epBase slA ≠ 0 →
      ∃ x slB y, SlotOwn PA slA x ∧ SlotOwn PB slB y ∧ OwnRel PA PB x y) ∧
    (∀ slB, g4SlotGet sb PB.epBase slB ≠ 0 →
      ∃ x slA y, SlotOwn PA slA x ∧ SlotOwn PB slB y ∧ OwnRel PA PB x y)

/-- **The registers, by mode**: mode 0 a code word of one term, mode 4 a
spine node of one term (the arguments pushed so far one count), mode 3
related entries, modes 1 and 2 one value or cell. -/
@[expose] def RegRel (sA sB : MS) : Prop :=
  sB.env = sA.env ∧
    match sA.mode with
    | 0 => sB.x = sA.x ∧ TRel N f₁ p₁ f₂ p₂ sA.P sB.P sA.pc sB.pc
    | 3 => sB.pc = sA.pc ∧ ERel N sA.P sB.P sA.x sB.x
    | 4 => sB.x = sA.x ∧ ∃ t, NamesIn N t ∧ Comp f₁ p₁ sA.P sA.pc t ∧ Comp f₂ p₂ sB.P sB.pc t
    | _ => sB.x = sA.x ∧ sB.pc = sA.pc

/-- **A basis entry** (`Bool.true` … `Nat.succ`): one key on both sides, and
related as an entry where its constant is in `N`. -/
@[expose] def BasisRel (PA PB : G4Prog) (c : Name) (a b : Nat) : Prop :=
  EntRel PA PB a b ∧ (N c → ERel N PA PB a b)

/-- **The simulation relation** between a state of the run on `PA` and one
of the run on `PB`; at `j = 0` (lock-step) the two programs have compiled
the same bodies.  The `Nat` and `String` flags agree where their basis is
in `N` (a literal's value carries that, `ValW`). -/
structure MRel (sA sB : MS) : Prop where
  invA : Inv f₁ p₁ sA.P
  invB : Inv f₂ p₂ sB.P
  natOk : NatN N → sB.P.natOk = sA.P.natOk
  strOk : StrNames N → sB.P.strOk = sA.P.strOk
  maxNat : sB.P.maxNat = sA.P.maxNat
  kTrue : BasisRel N sA.P sB.P boolTrueName sA.P.kTrue sB.P.kTrue
  kFalse : BasisRel N sA.P sB.P boolFalseName sA.P.kFalse sB.P.kFalse
  kZero : BasisRel N sA.P sB.P natZeroName sA.P.kZero sB.P.kZero
  kSucc : BasisRel N sA.P sB.P natSuccName sA.P.kSucc sB.P.kSucc
  cel : CelRel N f₁ p₁ f₂ p₂ sA.P sB.P sA.cel sB.cel
  val : ValRel N f₁ p₁ f₂ p₂ sA.P sB.P sA.val sB.val
  ev : sB.ev = sA.ev
  argA : sB.argA = sA.argA
  fs : FsRel N sA.P sB.P sA.fs sB.fs
  mem : MemRel N sA.P sB.P sA.mem sB.mem
  memoA : MemoTab sA.mem sA.argA sA.mH
  memoB : MemoTab sB.mem sB.argA sB.mH
  slots : SlotRel sA.P sB.P sA.slots sB.slots
  mode : sB.mode = sA.mode
  st : sB.st = sA.st
  regs : RegRel N f₁ p₁ f₂ p₂ sA sB
  code : j = 0 → CodeSame sA.P sB.P

end

/-! ## Growth of the programs -/

section
variable {j : Nat} {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
  {PA PB PA' PB' : G4Prog}

theorem TRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {oA oB : Nat}
    (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) : TRel N f₁ p₁ f₂ p₂ PA' PB' oA oB := by
  obtain ⟨t, hn, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := h
  · exact ⟨t, hn, .inl ⟨h₁.extR hA, h₂.extR hB⟩⟩
  · exact ⟨t, hn, .inr ⟨h₁.extR hA, h₂.extR hB⟩⟩

theorem StrRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {a b : Nat} (h : StrRel PA PB a b) :
    StrRel PA' PB' a b := by
  obtain ⟨s, h₁, h₂⟩ := h
  exact ⟨s, hA.strs_some h₁, hB.strs_some h₂⟩

theorem ValW.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {t a b : Nat}
    (h : ValW N f₁ p₁ f₂ p₂ PA PB t a b) : ValW N f₁ p₁ f₂ p₂ PA' PB' t a b := by
  unfold ValW at h ⊢
  split at h
  · exact h.ext hA hB
  · exact h.ext hA hB
  · exact h
  · exact ⟨h.1.ext hA hB, h.2⟩
  · exact h.ext hA hB
  · exact h

theorem BasisRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {c : Name} {a b : Nat}
    (h : BasisRel N PA PB c a b) : BasisRel N PA' PB' c a b :=
  ⟨h.1.ext hA hB, fun hc => (h.2 hc).ext hA hB⟩

theorem ValRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {va vb : Array Nat}
    (h : ValRel N f₁ p₁ f₂ p₂ PA PB va vb) : ValRel N f₁ p₁ f₂ p₂ PA' PB' va vb :=
  ⟨h.1, fun v hv => by
    obtain ⟨e₁, e₂, e₃, w⟩ := h.2 v hv
    exact ⟨e₁, e₂, e₃, w.ext hA hB⟩⟩

theorem CelRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {ca cb : Array Nat}
    (h : CelRel N f₁ p₁ f₂ p₂ PA PB ca cb) : CelRel N f₁ p₁ f₂ p₂ PA' PB' ca cb :=
  ⟨h.1, fun c hc => by
    obtain ⟨e₁, e₂⟩ := h.2 c hc
    exact ⟨e₁, fun h0 => ⟨(e₂ h0).1.ext hA hB, (e₂ h0).2⟩⟩⟩

theorem MemRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {ma mb : Array Nat}
    (h : MemRel N PA PB ma mb) : MemRel N PA' PB' ma mb :=
  ⟨h.1, fun r hr => by
    obtain ⟨e₀, e₁, e₂, e₃⟩ := h.2 r hr
    exact ⟨e₀.ext hA hB, e₁, e₂, e₃⟩⟩

/-! ## Pushing records -/

theorem push4_get {a : Array Nat} {w₀ w₁ w₂ w₃ i : Nat} (h : i < a.size) :
    ((((a.push w₀).push w₁).push w₂).push w₃)[i]! = a[i]! := by
  simp only [Array.push_eq_append, Array.append_assoc]
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos a i h, Array.getElem_append_left h]

theorem push4_new {a : Array Nat} {w₀ w₁ w₂ w₃ : Nat} (h : a.size % 4 = 0) :
    ((((a.push w₀).push w₁).push w₂).push w₃)[4 * (a.size / 4)]! = w₀ ∧
      ((((a.push w₀).push w₁).push w₂).push w₃)[4 * (a.size / 4) + 1]! = w₁ ∧
      ((((a.push w₀).push w₁).push w₂).push w₃)[4 * (a.size / 4) + 2]! = w₂ ∧
      ((((a.push w₀).push w₁).push w₂).push w₃)[4 * (a.size / 4) + 3]! = w₃ := by
  have e : 4 * (a.size / 4) = a.size := by omega
  have g : ∀ (b : Array Nat) (x i : Nat), i = b.size → (b.push x)[i]! = x := by
    rintro b x i rfl; exact getElem!_push_eq' b x
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_eq']
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), g _ _ _ (by simp)]
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), g _ _ _ (by simp)]
  · rw [g _ _ _ (by simp)]

/-- **A new value record** with related words. -/
theorem ValRel.push {va vb : Array Nat} (h : ValRel N f₁ p₁ f₂ p₂ PA PB va vb) (h4 : va.size % 4 = 0)
    (t e l a b : Nat) (hw : ValW N f₁ p₁ f₂ p₂ PA PB t a b) :
    ValRel N f₁ p₁ f₂ p₂ PA PB ((((va.push t).push a).push e).push l) ((((vb.push t).push b).push e).push l) := by
  have hs := h.1
  refine ⟨by simp [h.1], fun v hv => ?_⟩
  simp only [Array.size_push] at hv
  rcases Nat.lt_or_ge v (va.size / 4) with hl | hl
  · obtain ⟨e₁, e₂, e₃, w⟩ := h.2 v hl
    rw [push4_get (a := va) (by omega), push4_get (a := va) (by omega), push4_get (a := va) (by omega),
      push4_get (a := va) (by omega), push4_get (a := vb) (by omega), push4_get (a := vb) (by omega),
      push4_get (a := vb) (by omega), push4_get (a := vb) (by omega)]
    exact ⟨e₁, e₂, e₃, w⟩
  · obtain rfl : v = va.size / 4 := by omega
    have hb : vb.size % 4 = 0 := by rw [h.1]; exact h4
    obtain ⟨a₀, a₁, a₂, a₃⟩ := push4_new (a := va) (w₀ := t) (w₁ := a) (w₂ := e) (w₃ := l) h4
    obtain ⟨b₀, b₁, b₂, b₃⟩ := push4_new (a := vb) (w₀ := t) (w₁ := b) (w₂ := e) (w₃ := l) hb
    rw [h.1] at b₀ b₁ b₂ b₃
    rw [a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃]
    exact ⟨rfl, rfl, rfl, hw⟩

/-- **A new cell**: one state; a thunk's code by `TRel`, its environment one. -/
theorem CelRel.push {ca cb : Array Nat} (h : CelRel N f₁ p₁ f₂ p₂ PA PB ca cb) (h4 : ca.size % 4 = 0)
    (st e w oA oB : Nat) (hw : st = 0 → TRel N f₁ p₁ f₂ p₂ PA PB oA oB) :
    CelRel N f₁ p₁ f₂ p₂ PA PB ((((ca.push st).push oA).push e).push w) ((((cb.push st).push oB).push e).push w) := by
  have hs := h.1
  refine ⟨by simp [h.1], fun c hc => ?_⟩
  simp only [Array.size_push] at hc
  rcases Nat.lt_or_ge c (ca.size / 4) with hl | hl
  · obtain ⟨e₁, e₂⟩ := h.2 c hl
    rw [push4_get (a := ca) (by omega), push4_get (a := ca) (by omega), push4_get (a := ca) (by omega),
      push4_get (a := cb) (by omega), push4_get (a := cb) (by omega), push4_get (a := cb) (by omega)]
    exact ⟨e₁, e₂⟩
  · obtain rfl : c = ca.size / 4 := by omega
    have hb : cb.size % 4 = 0 := by rw [h.1]; exact h4
    obtain ⟨a₀, a₁, a₂, -⟩ := push4_new (a := ca) (w₀ := st) (w₁ := oA) (w₂ := e) (w₃ := w) h4
    obtain ⟨b₀, b₁, b₂, -⟩ := push4_new (a := cb) (w₀ := st) (w₁ := oB) (w₂ := e) (w₃ := w) hb
    rw [h.1] at b₀ b₁ b₂
    rw [a₀, a₁, a₂, b₀, b₁, b₂]
    exact ⟨rfl, fun h0 => ⟨hw h0, rfl⟩⟩

/-- **A cell's state set** to one word on both sides (an update, a thunk
entered). -/
theorem CelRel.setState {ca cb : Array Nat} (h : CelRel N f₁ p₁ f₂ p₂ PA PB ca cb) (h4 : ca.size % 4 = 0)
    (c w : Nat) (hw : w ≠ 0) :
    CelRel N f₁ p₁ f₂ p₂ PA PB (ca.set! (g4X4 c) w) (cb.set! (g4X4 c) w) := by
  have hs := h.1
  refine ⟨by simp [h.1], fun d hd => ?_⟩
  simp only [Array.size_set!] at hd
  obtain ⟨e₁, e₂⟩ := h.2 d hd
  rw [g4X4_eq]
  by_cases hdc : d = c
  · subst hdc
    rw [set!_get_self (a := ca) (by omega), set!_get_self (a := cb) (by omega)]
    exact ⟨rfl, fun h0 => absurd h0 hw⟩
  · have n0 : 4 * d ≠ 4 * c := by omega
    have n1 : 4 * d + 1 ≠ 4 * c := by omega
    have n2 : 4 * d + 2 ≠ 4 * c := by omega
    rw [set!_get_other n0, set!_get_other n0, set!_get_other n1, set!_get_other n1, set!_get_other n2,
      set!_get_other n2]
    exact ⟨e₁, e₂⟩

end

end ConLeche.Verify.Ground
