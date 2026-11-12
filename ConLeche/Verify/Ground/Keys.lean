module

public import ConLeche.Verify.Ground.Compile

public section

/-!
# The ground engine's compiler, exactly (task #423 soundness, layers (a) and (d))

`g4Comp_spec`: the node the compiler (`g4Comp`, `ConLeche/Kernel/Ground.lean`)
returns is the compile of the term (`Comp`, `ConLeche/Verify/Ground/Compile.lean`),
in a program that extends the one it was given (`Ext`) and keeps the
invariant (`Inv`).  Its denotation (`Den`, up to erasure) is read off with
`Comp.den`.  The proof is one induction on the term's size; the cases are
`g4Comp`'s: entry resolution (`g4Resolve_spec`), the mask memo, sharing of
closed arguments, spines, projections.
-/

namespace ConLeche.Verify.Ground

open ConLeche

variable {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}

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


/-- What the compiler promises for one compiled term: the invariant, an
extension, and the returned node the compile of the term. -/
@[expose] def CompOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (e : Expr) (r : Nat × G4Prog) : Prop :=
  Inv find? findProj? r.2 ∧ Ext P r.2 ∧ Comp find? findProj? r.2 r.1 e

/-- The same for an argument position (`g4CompArg`). -/
@[expose] def CompArgOK (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)
    (P : G4Prog) (e : Expr) (r : Nat × G4Prog) : Prop :=
  Inv find? findProj? r.2 ∧ Ext P r.2 ∧ CompArg find? findProj? r.2 r.1 e

theorem getD_append_left {l l' : List Expr} {i : Nat} (d : Expr) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len (l : List Expr) (a d : Expr) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_lt {l : List Expr} {i : Nat} (d : Expr) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]


section
variable (find?) (findProj?)

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

/-- **The mask memo keeps the key invariant**, and its mask is the head's. -/
theorem g4MaskOf_comp (P : G4Prog) (hd : Expr) (hI : TabInv find? findProj? P)
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
      refine ⟨hC.ext_gen find? findProj? hx hkI (fun a o h => ?_) (fun c' m h => ?_) hk.kMap
        (fun sl x h => ?_) (fun sl x y h h' => ?_), rfl⟩
      · rw [hk.closedNode] at h
        obtain ⟨sl, e, h₀, h₁, h₂, h₃, h₄⟩ := hC.closed a o h
        exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR, h₄⟩
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

/-- **A shared closed argument** keeps the invariant, and its node is the
term's shared node. -/
theorem g4CompShared_spec (a : Expr) (comp : G4Prog → Nat × G4Prog)
    (hcomp : ∀ P, Inv find? findProj? P → CompOK find? findProj? P a (comp P))
    (P : G4Prog) (hI : Inv find? findProj? P) (hsh : shKind a = true) :
    CompArgOK find? findProj? P a (g4CompShared comp P a) := by
  unfold g4CompShared
  split
  · rename_i hbr
    have hbr' : a.bvarBRaw = 0 := by simpa using hbr
    split
    · rename_i o ho
      obtain ⟨sl, e, h₀, h₁, h₂, h₃, -⟩ := hI.closed a o ho
      exact ⟨hI, Ext.refl P, .shared hsh hbr' ho h₀ h₁ h₂ h₃⟩
    · obtain ⟨hI₁, hx₁, hc₁⟩ := hcomp P hI
      generalize comp P = r at hI₁ hx₁ hc₁ ⊢
      obtain ⟨ao, P₁⟩ := r
      dsimp only at hI₁ hx₁ hc₁ ⊢
      split
      · rename_i o ho
        obtain ⟨sl, e, h₀, h₁, h₂, h₃, -⟩ := hI₁.closed a o ho
        exact ⟨hI₁, hx₁, .shared hsh hbr' ho h₀ h₁ h₂ h₃⟩
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
          · obtain ⟨sl', e, -, h₃, -, -, -⟩ := hI₁.closed a' o h₁
            rw [rdL _ (lt_of_some h₃), h₃] at h₂
            exact .inl ⟨o, h₁, by rw [h₃, h₂]⟩
        | inr k => exact .inl h
      refine ⟨⟨⟨hI₁.szs, hI₁.sizes, hI₁.kSlotSize, fun c us k h => hI₁.kMap c us k h,
          fun k hk => (hI₁.ents k hk).ext hx hk, fun q hq => (hI₁.prjs q hq).ext hx.toExtR hq, hI₁.nidOK,
          fun k k' r h h' => hI₁.rowsDisj k k' r (h.back hx.toExtR rfl) (h'.back hx.toExtR rfl)⟩,
        hI₁.toCompInv.ext_gen find? findProj? hx rfl (fun a' o h => ?_) hI₁.masks rfl
          (fun sl x h => ?_) (fun sl x y h h' => ?_)⟩, hx₁.trans hx,
        .shared hsh hbr' hreg hc0 hc1 hc2 (hc₁.extR hx.toExtR)⟩
      · rcases hlook a' o h with ⟨rfl, rfl⟩ | h
        · exact ⟨P₁.nslots, ao, hc0, hc1, hc2, hc₁.extR hx.toExtR, hbr'⟩
        · obtain ⟨sl, e, h₀, h₁, h₂, h₃, h₄⟩ := hI₁.closed a' o h
          exact ⟨sl, e, hx.code_some h₀, hx.code_some h₁, hx.code_some h₂, h₃.extR hx.toExtR, h₄⟩
      · show sl < P₁.nslots + 1
        rcases hown sl x h with h | ⟨-, rfl⟩
        · have := hI₁.slotLt sl x h; omega
        · omega
      · rcases hown sl x h with h₁ | ⟨hx₁, hs₁⟩ <;> rcases hown sl y h' with h₂ | ⟨hy₂, hs₂⟩
        · exact hI₁.slotUniq sl x y h₁ h₂
        · have := hI₁.slotLt _ x h₁; omega
        · have := hI₁.slotLt _ y h₂; omega
        · rw [hx₁, hy₂]
  · rename_i hbr
    obtain ⟨hI₁, hx₁, hc₁⟩ := hcomp P hI
    exact ⟨hI₁, hx₁, .plain (fun _ => by simpa using hbr) hc₁⟩

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

/-- One argument step keeps the fold's invariant. -/
theorem g4ArgStep_spec {α : Type} (ev : α → Expr) (compArg : G4Prog → α → Nat × G4Prog)
    (harg : ∀ P a, Inv find? findProj? P → CompArgOK find? findProj? P (ev a) (compArg P a))
    (mask : Array Bool) {P₁ : G4Prog} (acc : Array Nat × G4Prog) (done : List Expr) (a : α)
    (h₁ : Inv find? findProj? acc.2) (h₂ : Ext P₁ acc.2) (h₃ : ArgsK find? findProj? acc.2 mask acc.1 done) :
    Inv find? findProj? (g4ArgStep compArg mask acc a).2 ∧ Ext P₁ (g4ArgStep compArg mask acc a).2 ∧
      ArgsK find? findProj? (g4ArgStep compArg mask acc a).2 mask (g4ArgStep compArg mask acc a).1
        (done ++ [ev a]) := by
  unfold g4ArgStep
  split
  · rename_i hm
    dsimp only
    rw [emit_append1]
    have hx := Ext.emit acc.2 #[8]
    refine ⟨h₁.emit _, h₂.trans hx, (h₃.extR hx.toExtR).push (.inl ⟨by rw [h₃.1] at hm ⊢; exact hm, ?_⟩)⟩
    show (acc.2.code ++ #[8])[acc.2.code.size]? = some 8; rw [rd0]; rfl
  · rename_i hm
    obtain ⟨hI', hx', hc'⟩ := harg acc.2 a h₁
    generalize compArg acc.2 a = r at hI' hx' hc' ⊢
    obtain ⟨ao, P'⟩ := r
    dsimp only at hI' hx' hc' ⊢
    exact ⟨hI', h₂.trans hx', (h₃.extR hx'.toExtR).push (.inr ⟨by simpa using hm, hc'⟩)⟩

theorem g4ArgFold_spec {α : Type} (ev : α → Expr) (compArg : G4Prog → α → Nat × G4Prog)
    (harg : ∀ P a, Inv find? findProj? P → CompArgOK find? findProj? P (ev a) (compArg P a))
    (mask : Array Bool) {P₁ : G4Prog} : ∀ (l : List α) (acc : Array Nat × G4Prog) (done : List Expr),
      Inv find? findProj? acc.2 → Ext P₁ acc.2 → ArgsK find? findProj? acc.2 mask acc.1 done →
      Inv find? findProj? (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        Ext P₁ (l.foldl (g4ArgStep compArg mask) acc).2 ∧
        ArgsK find? findProj? (l.foldl (g4ArgStep compArg mask) acc).2 mask
          (l.foldl (g4ArgStep compArg mask) acc).1 (done ++ l.map ev)
  | [], acc, done, h₁, h₂, h₃ => by simpa using ⟨h₁, h₂, h₃⟩
  | a :: l, acc, done, h₁, h₂, h₃ => by
    obtain ⟨h₁', h₂', h₃'⟩ := g4ArgStep_spec find? findProj? ev compArg harg mask acc done a h₁ h₂ h₃
    have := g4ArgFold_spec ev compArg harg mask l _ _ h₁' h₂' h₃'
    simpa using this

/-- **A spine** keeps the invariant, and its node is the spine of the
compiled head and arguments. -/
theorem g4CompSpine_spec {α : Type} (ev : α → Expr) (hd : Expr) (comp : G4Prog → Nat × G4Prog)
    (compArg : G4Prog → α → Nat × G4Prog)
    (hcomp : ∀ P, Inv find? findProj? P → CompOK find? findProj? P hd (comp P))
    (harg : ∀ P a, Inv find? findProj? P → CompArgOK find? findProj? P (ev a) (compArg P a))
    (P : G4Prog) (args : List α) (mask : Array Bool) (hI : Inv find? findProj? P) :
    Inv find? findProj? (g4CompSpine comp compArg P args mask).2 ∧
      Ext P (g4CompSpine comp compArg P args mask).2 ∧
      ∃ ho, (g4CompSpine comp compArg P args mask).2.code[(g4CompSpine comp compArg P args mask).1]? = some 1 ∧
        (g4CompSpine comp compArg P args mask).2.code[(g4CompSpine comp compArg P args mask).1 + 1]? = some ho ∧
        (g4CompSpine comp compArg P args mask).2.code[(g4CompSpine comp compArg P args mask).1 + 2]? =
          some (args.map ev).length ∧
        Comp find? findProj? (g4CompSpine comp compArg P args mask).2 ho hd ∧
        CompArgs find? findProj? (g4CompSpine comp compArg P args mask).2 mask
          ((g4CompSpine comp compArg P args mask).1 + 3) 0 (args.map ev) := by
  unfold g4CompSpine
  obtain ⟨hI₁, hx₁, hch⟩ := hcomp P hI
  generalize comp P = r at hI₁ hx₁ hch ⊢
  obtain ⟨ho, P₁⟩ := r
  dsimp only at hI₁ hx₁ hch ⊢
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
  have hca := (hargs.extR hx.toExtR).compArgs hcode (args.map ev).length 0 (by simp)
  rw [Nat.add_zero, List.drop_zero] at hca
  refine ⟨hI₂.emit _, hx₁.trans (hx₂.trans hx), ho, ?_, ?_, ?_, (hch.extR hx₂.toExtR).extR hx.toExtR, hca⟩
  · show (P₂.code ++ _)[P₂.code.size]? = _
    rw [rd0, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 1]? = _
    rw [rdR, Array.getElem?_append_left (by simp)]; rfl
  · show (P₂.code ++ _)[P₂.code.size + 2]? = _
    rw [rdR, Array.getElem?_append_left (by simp), hargs.1]; rfl

/-- A projection node (the program steps of `g4Comp`'s projection case). -/
theorem proj_emit_spec {P P₁ Q : G4Prog} {sn : Name} {i so : Nat} {e : Expr} {pj : G4Proj} {en : ProjEntry}
    (hI₁ : Inv find? findProj? P₁) (hx₁ : Ext P P₁) (hce : Comp find? findProj? P₁ so e)
    (hc : Q.code = P₁.code) (ht : Q.kTag = P₁.kTag) (hi : Q.kInfo = P₁.kInfo)
    (hm : Q.kMap = P₁.kMap) (hcl : Q.closedNode = P₁.closedNode) (hs : Q.strs = P₁.strs)
    (hks : Q.kSlot = P₁.kSlot) (hn : Q.nslots = P₁.nslots) (hp : Q.projs = P₁.projs.push pj)
    (q : Nat) (hq : q = P₁.projs.size) (he : ∀ k, Q.entW k = P₁.entW k) (hrow : ∀ r, Q.rowW r = P₁.rowW r)
    (hrs : Q.rules.size = P₁.rules.size) (hprj : ∀ q', q' < P₁.projs.size → Q.prjW q' = P₁.prjW q')
    (hnid : ∀ (c : Name) (i : Nat), P₁.nids[c]? = some i → Q.nids[c]? = some i) (hfl : Q.flags = P₁.flags)
    (hep : Q.site = P₁.site) (hmk : Q.masks = P₁.masks) (hf : findProj? sn i = some en)
    (hpj : pj = ⟨sn, en.ctor, i, en.numParams, en.numFields, en.levelParams.length, true, en⟩)
    (hszQ : Sizes Q) (hpq : PrjOK findProj? Q q) (hnQ : NidOK Q) :
    CompOK find? findProj? P (.proj sn i e)
      (Q.code.size, Q.emit (fun c => ((c.push 7).push (q + 1)).push so)) := by
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
  refine ⟨⟨hI₁.toTabInv.ext hx (by show Q.kTag.size = Q.kInfo.size; rw [ht, hi]; exact hI₁.sizes)
      (by show Q.kSlot.size = Q.kInfo.size; rw [hks, hi]; exact hI₁.kSlotSize) hm hszQ
      (by show Q.kInfo.size = _; rw [hi])
      (fun q' hq' hge => by
        obtain rfl : q' = q := by
          change q' < Q.projs.size at hq'; rw [hp, Array.size_push] at hq'; omega
        exact hpq) hnQ,
    hI₁.toCompInv.ext find? findProj? hx (by show Q.kInfo.size = _; rw [hi]) hcl hmk hm hks hn⟩,
    hx₁.trans hx, .proj (q := q) hf ?_ ?_ ?_ ?_ (hce.extR hx.toExtR)⟩
  · show (Q.code ++ _)[Q.code.size]? = _; rw [rd0]; rfl
  · show (Q.code ++ _)[Q.code.size + 1]? = _; rw [rdR]; rfl
  · show Q.projs[q]? = _; rw [hp, hq, ← hpj]; exact Array.getElem?_push_size
  · show (Q.code ++ _)[Q.code.size + 2]? = _; rw [rdR]; rfl

/-- A neutral node `[8]`. -/
theorem comp_neutral {P : G4Prog} (hI : Inv find? findProj? P) :
    Inv find? findProj? (P.emit (fun c => c.push 8)) ∧ Ext P (P.emit (fun c => c.push 8)) ∧
      (P.emit (fun c => c.push 8)).code[P.code.size]? = some 8 := by
  rw [emit_append1]
  exact ⟨hI.emit _, Ext.emit P _, by show (P.code ++ #[8])[P.code.size]? = some 8; rw [rd0]; rfl⟩

/-- **The compile lemma** (by induction on the term's size): the node the
compiler returns is the compile of the term, in an extension of the program
that keeps the invariant. -/
theorem g4Comp_spec_lt : ∀ (n : Nat),
    (∀ (P : G4Prog) (e : Expr), sizeOf e < n → Inv find? findProj? P →
      CompOK find? findProj? P e (g4Comp find? findProj? P e)) ∧
    (∀ (P : G4Prog) (a : Expr), sizeOf a < n → Inv find? findProj? P →
      CompArgOK find? findProj? P a (g4CompArg find? findProj? P a)) := by
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
        refine ⟨hI.emit _, Ext.emit P _, .bvar ?_ ?_⟩
        · show (P.code ++ #[0, i])[P.code.size]? = some 0; rw [rd0]; rfl
        · show (P.code ++ #[0, i])[P.code.size + 1]? = some i; rw [rdR]; rfl
      | fvar i ty =>
        unfold g4Comp; obtain ⟨h₁, h₂', h₂⟩ := comp_neutral find? findProj? hI; exact ⟨h₁, h₂', .fvar h₂⟩
      | sort u =>
        unfold g4Comp; obtain ⟨h₁, h₂', h₂⟩ := comp_neutral find? findProj? hI; exact ⟨h₁, h₂', .sort h₂⟩
      | forallE ty b =>
        unfold g4Comp; obtain ⟨h₁, h₂', h₂⟩ := comp_neutral find? findProj? hI; exact ⟨h₁, h₂', .forallE h₂⟩
      | lit l =>
        cases l with
        | natVal n =>
          unfold g4Comp; dsimp only
          rw [emit_append2]
          refine ⟨hI.emit _, Ext.emit P _, .natLit ?_ ?_⟩
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
          refine ⟨hI.ext hx hI.sizes hI.kSlotSize rfl rfl rfl rfl rfl hI.szs rfl
              (fun _ hq h => absurd hq (Nat.not_lt.mpr h)) hI.nidOK, hx,
            .strLit (si := P.strs.size) ?_ ?_ ?_⟩
          · show (P.code ++ #[6, P.strs.size])[P.code.size]? = some 6; rw [rd0]; rfl
          · show (P.code ++ #[6, P.strs.size])[P.code.size + 1]? = some P.strs.size; rw [rdR]; rfl
          · show (P.strs.push str)[P.strs.size]? = some str; exact Array.getElem?_push_size
      | lam ty b =>
        unfold g4Comp; dsimp only
        have hsb : sizeOf b < n := by simp only [Expr.lam.sizeOf_spec] at hs; omega
        obtain ⟨hI₁, hx₁, hcb⟩ := ihC P b hsb hI
        generalize g4Comp find? findProj? P b = r at hI₁ hx₁ hcb ⊢
        obtain ⟨bo, P₁⟩ := r
        dsimp only at hI₁ hx₁ hcb ⊢
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
          refine ⟨hI₁.emit _, hx₁.trans hx, .lam (tn := tn' + 1) (inner := inner') ?_ ?_ ?_ ?_
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
          refine ⟨hI₁.emit _, hx₁.trans hx, .lam (tn := 1) (inner := bo) ?_ ?_ ?_ ?_
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
        obtain ⟨hI₁, hx₁, hcv⟩ := ihA P v hsv hI
        generalize g4CompArg find? findProj? P v = r at hI₁ hx₁ hcv ⊢
        obtain ⟨vo, P₁⟩ := r
        dsimp only at hI₁ hx₁ hcv ⊢
        obtain ⟨hI₂, hx₂, hcb⟩ := ihC P₁ b hsb hI₁
        generalize g4Comp find? findProj? P₁ b = r at hI₂ hx₂ hcb ⊢
        obtain ⟨bo, P₂⟩ := r
        dsimp only at hI₂ hx₂ hcb ⊢
        rw [emit_append3]
        have hx := Ext.emit P₂ #[3, vo, bo]
        refine ⟨hI₂.emit _, hx₁.trans (hx₂.trans hx), .letE ?_ ?_ ?_ ((hcv.extR hx₂.toExtR).extR hx.toExtR)
          (hcb.extR hx.toExtR)⟩
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
        refine ⟨hI₁.emit _, hx₁.trans hx, .const ?_ ?_ (hx.kInfo_some hinfo) (infoKey_of_approx ha)⟩
        · show (P₁.code ++ _)[P₁.code.size]? = _; rw [rd0]; rfl
        · show (P₁.code ++ _)[P₁.code.size + 1]? = _; rw [rdR]; rfl
      | proj sn i e =>
        unfold g4Comp; dsimp only
        split
        · rename_i en hf
          have hse : sizeOf e < n := by simp only [Expr.proj.sizeOf_spec] at hs; omega
          obtain ⟨hI₁, hx₁, hce⟩ := ihC P e hse hI
          generalize g4Comp find? findProj? P e = r at hI₁ hx₁ hce ⊢
          obtain ⟨so, P₁⟩ := r
          dsimp only at hI₁ hx₁ hce ⊢
          generalize hn : P₁.nid en.ctor = rn
          obtain ⟨ni, P₂⟩ := rn
          have hk : KeyEq P₁ P₂ := by have := KeyEq.nid P₁ en.ctor; rw [hn] at this; exact this
          have hP₂ : P₂ = { P₁ with nids := P₂.nids } := by
            rw [show P₂ = (P₁.nid en.ctor).2 by rw [hn]]; exact nid_eq P₁ en.ctor
          dsimp only
          refine proj_emit_spec find? findProj? (en := en) (sn := sn) (i := i) hI₁ hx₁ hce ?_ ?_ ?_
            ?_ ?_ ?_ ?_ ?_ ?_ _ ?_ (fun k => hk.entW k) ?_ ?_ ?_ hk.nids ?_ ?_ ?_ hf rfl ?_ ?_ ?_
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
          · rw [hP₂]
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
            refine ⟨sn, i, en, Array.getElem?_push_size, hf, ⟨ni, hget, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
            · show (P₂.pNid.push ni)[P₂.projs.size]? = _; rw [e₀, e₁, ← p₁]; exact Array.getElem?_push_size
            · show (P₂.pIdx.push i)[P₂.projs.size]? = _; rw [e₀, e₂, ← p₂]; exact Array.getElem?_push_size
            · show (P₂.pNP.push _)[P₂.projs.size]? = _; rw [e₀, e₃, ← p₃]; exact Array.getElem?_push_size
            · show (P₂.pNF.push _)[P₂.projs.size]? = _; rw [e₀, e₄, ← p₄]; exact Array.getElem?_push_size
            · show (P₂.pNl.push _)[P₂.projs.size]? = _; rw [e₀, e₅, ← p₅]; exact Array.getElem?_push_size
            · show (P₂.pAlw.push _)[P₂.projs.size]? = _; rw [e₀, e₆, ← p₆]; exact Array.getElem?_push_size
          · have := hI₁.nidOK.nid en.ctor; rw [hn] at this; exact this
        · rename_i hf
          obtain ⟨h₁, h₂', h₂⟩ := comp_neutral find? findProj? hI; exact ⟨h₁, h₂', .projNone hf h₂⟩
      | app fn arg =>
        unfold g4Comp; dsimp only
        have hk₁ := g4MaskOf_key find? P (Expr.app fn arg).getAppFn
        have hn₁ := g4MaskOf_nids find? P (Expr.app fn arg).getAppFn
        obtain ⟨hK₁, hm₁⟩ := g4MaskOf_comp find? findProj? P (Expr.app fn arg).getAppFn hI.toTabInv
          hI.toCompInv
        generalize g4MaskOf find? P (Expr.app fn arg).getAppFn = r at hk₁ hn₁ hK₁ hm₁ ⊢
        obtain ⟨mask, P₁⟩ := r
        dsimp only at hk₁ hK₁ hm₁ ⊢
        have hI₁ : Inv find? findProj? P₁ :=
          ⟨hk₁.inv hI.toTabInv (by unfold NidOK; rw [hn₁]; exact hI.nidOK), hK₁⟩
        have hsf := Expr.sizeOf_getAppFn_le fn
        simp only [Expr.app.sizeOf_spec] at hs
        have hsa : ∀ (a : {a // a ∈ (Expr.app fn arg).getAppArgs}), sizeOf a.1 < n := fun a => by
          have := Expr.sizeOf_lt_of_mem_getAppArgs a.2
          simp only [Expr.app.sizeOf_spec] at this; omega
        have hsh : sizeOf (Expr.app fn arg).getAppFn < n := by simp only [Expr.getAppFn]; omega
        obtain ⟨hI₂, hx₂, ho, h₀, h₁, h₂, hh, has⟩ := g4CompSpine_spec find? findProj? Subtype.val
          (Expr.app fn arg).getAppFn
          (fun P => g4Comp find? findProj? P (Expr.app fn arg).getAppFn)
          (fun P (a : {a // a ∈ (Expr.app fn arg).getAppArgs}) => g4CompArg find? findProj? P a.1)
          (fun P hI => ihC P _ hsh hI)
          (fun P a hI => ihA P a.1 (hsa a) hI) P₁
          (Expr.app fn arg).getAppArgs.attach mask hI₁
        rw [List.attach_map_subtype_val] at h₂ has
        subst hm₁
        exact ⟨hI₂, (hk₁.ext hI.szs).trans hx₂, .app h₀ h₁ h₂ rfl hh has⟩
    refine ⟨hC, fun P a hs hI => ?_⟩
    unfold g4CompArg
    split
    all_goals first
      | exact g4CompShared_spec find? findProj? _ _ (fun P hI => hC P _ (by assumption) hI) P hI rfl
      | (obtain ⟨h₁, h₂, h₃⟩ := hC P a hs hI
         exact ⟨h₁, h₂, .plain (fun h => by simp [shKind] at h) h₃⟩)

/-- **The compile lemma**: `g4Comp_spec_lt` at the term's size. -/
theorem g4Comp_spec (P : G4Prog) (e : Expr) (hI : Inv find? findProj? P) :
    CompOK find? findProj? P e (g4Comp find? findProj? P e) :=
  (g4Comp_spec_lt find? findProj? (sizeOf e + 1)).1 P e (Nat.lt_succ_self _) hI

end

end ConLeche.Verify.Ground
