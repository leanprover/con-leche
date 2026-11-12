module

public import ConLeche.Verify.Ground.SimState
import ConLeche.Verify.Ground.Step0

public section

/-!
# The layout bridge (task #423 soundness, layer (d), item 2(c))

The words the machine reads at two related code positions (`TRel`), by the
node's tag: one tag, and the fields either one word or related again.  The
lookups agree on the names the related terms mention (`Agree`): for the
kept/fresh instance the lookups are one (`LookAgree.refl`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- **The lookups agree on `N`**: on the constants, the projection rows and
the erasure masks (a mask reads the constant's type: the agreement there is
the caller's, where `N` is closed under types). -/
structure LookAgree (N : Name → Prop) (f₁ : Name → Option ConstantInfo) (p₁ : Name → Nat → Option ProjEntry)
    (f₂ : Name → Option ConstantInfo) (p₂ : Name → Nat → Option ProjEntry) : Prop where
  find : ∀ c, N c → f₂ c = f₁ c
  proj : ∀ sn i, N sn → p₂ sn i = p₁ sn i
  mask : ∀ c, N c → maskName f₂ c = maskName f₁ c

theorem LookAgree.refl (N : Name → Prop) (f : Name → Option ConstantInfo) (p : Name → Nat → Option ProjEntry) :
    LookAgree N f p f p := ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

section
variable {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}

theorem NamesIn.projAgree (hag : LookAgree N f₁ p₁ f₂ p₂) {t : Expr} (h : NamesIn N t) :
    ProjAgree p₁ p₂ t := by
  cases t with
  | proj sn i e => exact (hag.proj sn i h.1).symm
  | _ => trivial

theorem NamesIn.appFn : ∀ {t : Expr}, NamesIn N t → NamesIn N t.getAppFn
  | .app f _, h => by simp only [Expr.getAppFn]; exact NamesIn.appFn h.1
  | .bvar _, h | .fvar .., h | .sort _, h | .const .., h | .lam .., h | .forallE .., h | .letE .., h
  | .lit _, h | .proj .., h => by simp only [Expr.getAppFn]; exact h

theorem NamesIn.appArgs : ∀ {t a : Expr}, NamesIn N t → a ∈ t.getAppArgs → NamesIn N a
  | .app f x, a, h, hm => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact NamesIn.appArgs h.1 hm
    · exact h.2
  | .bvar _, _, _, hm | .fvar .., _, _, hm | .sort _, _, _, hm | .const .., _, _, hm
  | .lam .., _, _, hm | .forallE .., _, _, hm | .letE .., _, _, hm | .lit _, _, _, hm
  | .proj .., _, _, hm => by simp [Expr.getAppArgs] at hm

theorem NamesIn.maskAgree (hag : LookAgree N f₁ p₁ f₂ p₂) {t : Expr} (h : NamesIn N t) :
    MaskAgree f₁ f₂ t := by
  have h' := h.appFn
  unfold MaskAgree
  revert h'
  cases t.getAppFn with
  | const c _ => intro h'; exact (hag.mask c h').symm
  | _ => intro; rfl

/-- **One term, the two nodes**: a related position is a pair of compiles
of one term, or a pair of shared nodes. -/
theorem TRel.cases {PA PB : G4Prog} {oA oB : Nat} (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) :
    (∃ t, NamesIn N t ∧ Comp f₁ p₁ PA oA t ∧ Comp f₂ p₂ PB oB t) ∨
      ∃ a slA slB eA eB, NamesIn N a ∧ PA.code[oA]? = some 9 ∧ PB.code[oB]? = some 9 ∧
        PA.code[oA + 1]? = some slA ∧ PB.code[oB + 1]? = some slB ∧
        SlotOwn PA slA (.inl a) ∧ SlotOwn PB slB (.inl a) ∧
        PA.code[oA + 2]? = some eA ∧ PB.code[oB + 2]? = some eB ∧
        Comp f₁ p₁ PA eA a ∧ Comp f₂ p₂ PB eB a := by
  obtain ⟨t, hN, ⟨hA, hB⟩ | ⟨hA, hB⟩⟩ := h
  · exact .inl ⟨t, hN, hA, hB⟩
  · rcases comp2_arg hA hB with ⟨slA, slB, eA, eB, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ | ⟨hA, hB⟩
    · exact .inr ⟨t, slA, slB, eA, eB, hN, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
    · exact .inl ⟨t, hN, hA, hB⟩

/-- **One tag.** -/
theorem TRel.tag (hag : LookAgree N f₁ p₁ f₂ p₂) {PA PB : G4Prog} {oA oB : Nat}
    (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) : PB.code[oB]! = PA.code[oA]! := by
  rcases h.cases with ⟨t, hN, hA, hB⟩ | ⟨_, _, _, _, _, _, h₁, h₂, _⟩
  · have e := comp2_tag hA hB (hN.projAgree hag)
    obtain ⟨x, hx⟩ := hA.tag
    rw [hx] at e; rw [get!_of_some hx, get!_of_some e.symm]
  · rw [get!_of_some h₁, get!_of_some h₂]

theorem Comp.not9 {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    {o : Nat} {t : Expr} (h : Comp f p P o t) : P.code[o]! ≠ 9 := by
  cases h <;> (rw [get!_of_some (by assumption)]; decide)

theorem get!_of_some' {a : Array Nat} {i : Nat} (h : ∃ x, a[i]? = some x) : a[i]? = some a[i]! := by
  obtain ⟨x, hx⟩ := h; rw [hx, get!_of_some hx]

theorem lamTel_names : ∀ {t : Expr}, NamesIn N t → NamesIn N (lamTel t).2
  | .lam _ b, h => by simp only [lamTel]; exact lamTel_names h.2
  | .bvar _, h | .fvar .., h | .sort _, h | .const .., h | .app .., h | .forallE .., h | .letE .., h
  | .lit _, h | .proj .., h => h

/-- A related position of a tag other than `9` is a pair of compiles. -/
theorem TRel.comp {PA PB : G4Prog} {oA oB : Nat} (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB)
    (h9 : PA.code[oA]! ≠ 9) : ∃ t, NamesIn N t ∧ Comp f₁ p₁ PA oA t ∧ Comp f₂ p₂ PB oB t := by
  rcases h.cases with h | ⟨_, _, _, _, _, _, h₁, _⟩
  · exact h
  · exact absurd (get!_of_some h₁) h9

theorem TRel.ofComp {PA PB : G4Prog} {oA oB : Nat} {t : Expr} (hN : NamesIn N t)
    (hA : Comp f₁ p₁ PA oA t) (hB : Comp f₂ p₂ PB oB t) : TRel N f₁ p₁ f₂ p₂ PA PB oA oB :=
  ⟨t, hN, .inl ⟨hA, hB⟩⟩

theorem TRel.ofArg {PA PB : G4Prog} {oA oB : Nat} {t : Expr} (hN : NamesIn N t)
    (hA : CompArg f₁ p₁ PA oA t) (hB : CompArg f₂ p₂ PB oB t) : TRel N f₁ p₁ f₂ p₂ PA PB oA oB :=
  ⟨t, hN, .inr ⟨hA, hB⟩⟩

/-! ## The fields, tag by tag -/

section
variable {PA PB : G4Prog} {oA oB : Nat}

/-- A variable: one index. -/
theorem TRel.bvar (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 0) :
    PB.code[oB + 1]! = PA.code[oA + 1]! := by
  obtain ⟨t, -, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | bvar _ h₁ => cases hB with
    | bvar _ h₁' => rw [get!_of_some h₁, get!_of_some h₁']
  | _ => simp_all

/-- A spine: one argument count, the spine itself a pair of compiles of one term. -/
theorem TRel.spine (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 1) :
    PB.code[oB + 2]! = PA.code[oA + 2]! ∧
      ∃ t, NamesIn N t ∧ Comp f₁ p₁ PA oA t ∧ Comp f₂ p₂ PB oB t := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  refine ⟨?_, t, hN, hA, hB⟩
  have hta := get!_of_some' hA.tag
  cases hA with
  | app _ _ h₂ hn => cases hB with
    | app _ _ h₂' hn' => rw [get!_of_some h₂, get!_of_some h₂', hn, hn']
    | _ => simp_all
  | _ => simp_all

/-- A λ's telescope length. -/
theorem TRel.lamTn (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 2) :
    PB.code[oB + 2]! = PA.code[oA + 2]! := by
  obtain ⟨t, -, hA, hB⟩ := h.comp (by rw [ht]; decide)
  obtain ⟨ty, b, rfl⟩ := hA.lam_tag.mp (by rw [get!_of_some' hA.tag, ht])
  obtain ⟨-, h₁, h₂, -⟩ := comp2_lam hA hB
  rw [get!_of_some h₁, get!_of_some h₂]

/-- **The body after `k` binders**, on both sides. -/
theorem comp2_walk : ∀ (k : Nat) {oA oB : Nat} {t : Expr}, NamesIn N t → Comp f₁ p₁ PA oA t →
    Comp f₂ p₂ PB oB t → k ≤ (lamTel t).1 →
    TRel N f₁ p₁ f₂ p₂ PA PB (g4LamWalk PA.code k oA) (g4LamWalk PB.code k oB)
  | 0, _, _, _, hN, hA, hB, _ => TRel.ofComp hN hA hB
  | k + 1, oA, oB, t, hN, hA, hB, hk => by
    cases t with
    | lam ty b =>
      obtain ⟨⟨bA, bB, h₁, h₂, hbA, hbB⟩, -⟩ := comp2_lam hA hB
      have e₁ : g4LamWalk PA.code (k + 1) oA = g4LamWalk PA.code k bA := by
        show g4LamWalk PA.code k PA.code[oA + 1]! = _; rw [get!_of_some h₁]
      have e₂ : g4LamWalk PB.code (k + 1) oB = g4LamWalk PB.code k bB := by
        show g4LamWalk PB.code k PB.code[oB + 1]! = _; rw [get!_of_some h₂]
      rw [e₁, e₂]
      exact comp2_walk k hN.2 hbA hbB (by simp only [lamTel] at hk; omega)
    | _ => simp [lamTel] at hk

/-- **A known call's body**: the innermost body when the call binds the
whole telescope, else the body after `k` binders. -/
theorem TRel.lamBody (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 2) {k : Nat}
    (hk : k ≤ PA.code[oA + 2]!) :
    TRel N f₁ p₁ f₂ p₂ PA PB (if k == PA.code[oA + 2]! then PA.code[oA + 3]! else g4LamWalk PA.code k oA)
      (if k == PA.code[oA + 2]! then PB.code[oB + 3]! else g4LamWalk PB.code k oB) := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  obtain ⟨ty, b, rfl⟩ := hA.lam_tag.mp (by rw [get!_of_some' hA.tag, ht])
  obtain ⟨-, h₁, -, iA, iB, h₃, h₄, hiA, hiB⟩ := comp2_lam hA hB
  rw [get!_of_some h₁] at hk ⊢
  split
  · rw [get!_of_some h₃, get!_of_some h₄]
    exact TRel.ofComp (lamTel_names hN) hiA hiB
  · exact comp2_walk k hN hA hB hk

/-- A `let`: the value's argument positions and the bodies. -/
theorem TRel.letE (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 3) :
    TRel N f₁ p₁ f₂ p₂ PA PB PA.code[oA + 1]! PB.code[oB + 1]! ∧
      TRel N f₁ p₁ f₂ p₂ PA PB PA.code[oA + 2]! PB.code[oB + 2]! := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | letE _ h₁ h₂ hv hb => cases hB with
    | letE _ h₁' h₂' hv' hb' =>
      rw [get!_of_some h₁, get!_of_some h₁', get!_of_some h₂, get!_of_some h₂']
      exact ⟨TRel.ofArg hN.2.1 hv hv', TRel.ofComp hN.2.2 hb hb'⟩
  | _ => simp_all

/-- A constant: related entries. -/
theorem TRel.const (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 4) :
    ERel N PA PB PA.code[oA + 1]! PB.code[oB + 1]! := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | const _ h₁ h₂ h₃ => cases hB with
    | const _ h₁' h₂' h₃' =>
      rw [get!_of_some h₁, get!_of_some h₁']
      refine ⟨⟨_, _, h₂, h₂', h₃.trans h₃'.symm⟩, fun iA hi => ?_⟩
      rw [h₂] at hi; cases hi; rw [h₃]; exact hN
  | _ => simp_all

/-- A numeral: one value. -/
theorem TRel.natLit (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 5) :
    PB.code[oB + 1]! = PA.code[oA + 1]! := by
  obtain ⟨t, -, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | natLit _ h₁ => cases hB with
    | natLit _ h₁' => rw [get!_of_some h₁, get!_of_some h₁']
  | _ => simp_all

/-- A string literal: one string. -/
theorem TRel.strLit (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 6) :
    StrRel PA PB PA.code[oA + 1]! PB.code[oB + 1]! := by
  obtain ⟨t, -, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | strLit _ h₁ h₂ => cases hB with
    | strLit _ h₁' h₂' => rw [get!_of_some h₁, get!_of_some h₁']; exact ⟨_, h₂, h₂'⟩
  | _ => simp_all

/-- A projection: related rows, the projected terms. -/
theorem TRel.proj (hag : LookAgree N f₁ p₁ f₂ p₂) (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB)
    (ht : PA.code[oA]! = 7) :
    PiRel PA PB PA.code[oA + 1]! PB.code[oB + 1]! ∧
      TRel N f₁ p₁ f₂ p₂ PA PB PA.code[oA + 2]! PB.code[oB + 2]! := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have h7 : PA.code[oA]? = some 7 := by rw [get!_of_some' hA.tag, ht]
  cases t with
  | proj sn i e =>
    obtain ⟨qA, qB, pj, h₁, h₂, h₃, h₄, eA, eB, h₅, h₆, heA, heB⟩ :=
      comp2_proj hA hB (hag.proj sn i hN.1).symm h7
    rw [get!_of_some h₁, get!_of_some h₂, get!_of_some h₅, get!_of_some h₆]
    exact ⟨.inr ⟨qA, qB, rfl, rfl, pj, h₃, h₄⟩, TRel.ofComp hN.2 heA heB⟩
  | _ => cases hA <;> simp_all

/-- **A shared node**: slots of one owner, the wrapped compiles. -/
theorem TRel.shared (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 9) :
    (∃ a, SlotOwn PA PA.code[oA + 1]! (.inl a) ∧ SlotOwn PB PB.code[oB + 1]! (.inl a)) ∧
      TRel N f₁ p₁ f₂ p₂ PA PB PA.code[oA + 2]! PB.code[oB + 2]! := by
  rcases h.cases with ⟨t, -, hA, -⟩ | ⟨a, slA, slB, eA, eB, hN, -, -, h₁, h₂, hs₁, hs₂, h₃, h₄, he₁, he₂⟩
  · exact absurd ht hA.not9
  · rw [get!_of_some h₁, get!_of_some h₂, get!_of_some h₃, get!_of_some h₄]
    exact ⟨⟨a, hs₁, hs₂⟩, TRel.ofComp hN he₁ he₂⟩

end

/-- **A spine's words**: the heads related, one argument count, and argument
by argument both erased or related positions. -/
theorem comp2_spine (hag : LookAgree N f₁ p₁ f₂ p₂) {t : Expr} (hN : NamesIn N t)
    (hA : Comp f₁ p₁ PA oA t) (hB : Comp f₂ p₂ PB oB t) (h1 : PA.code[oA]? = some 1) :
    TRel N f₁ p₁ f₂ p₂ PA PB PA.code[oA + 1]! PB.code[oB + 1]! ∧
      PB.code[oB + 2]! = PA.code[oA + 2]! ∧
      ∀ j, j < PA.code[oA + 2]! →
        (PA.code[PA.code[oA + 3 + j]!]! = 8 ∧ PB.code[PB.code[oB + 3 + j]!]! = 8) ∨
          TRel N f₁ p₁ f₂ p₂ PA PB PA.code[oA + 3 + j]! PB.code[oB + 3 + j]! := by
  cases t with
  | app f x =>
    obtain ⟨⟨hA', hB', h₁, h₂, hhA, hhB⟩, h₃, h₄, hargs⟩ := comp2_app hA hB (hN.maskAgree hag)
    rw [get!_of_some h₁, get!_of_some h₂, get!_of_some h₃, get!_of_some h₄]
    refine ⟨TRel.ofComp hN.appFn hhA hhB, rfl, fun j hj => ?_⟩
    obtain ⟨aA, aB, e₁, e₂, e₃⟩ := hargs j hj
    rw [get!_of_some e₁, get!_of_some e₂]
    rcases e₃ with ⟨e₈, e₈'⟩ | ⟨a, ha, haA, haB⟩
    · exact .inl ⟨get!_of_some e₈, get!_of_some e₈'⟩
    · exact .inr (TRel.ofArg (hN.appArgs ha) haA haB)
  | _ => cases hA <;> simp_all

/-- An entry's slot is owned by it. -/
theorem slotOwn_entry {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    (hI : Inv f p P) {k : Nat} {i : G4Info} (h : P.kInfo[k]? = some i) : SlotOwn P P.kSlot[k]! (.inr k) := by
  have hkl : k < P.kSlot.size := by rw [hI.kSlotSize]; exact lt_of_some h
  exact some_of_lt hkl

/-! ## The sharing slots -/

section
variable {PA PB : G4Prog}

/-- An owner's related owners on the other side have one slot. -/
theorem OwnRel.slot_eqB (hA : CompInv f₁ p₁ PA) (hB : CompInv f₂ p₂ PB) {x : Expr ⊕ Nat}
    {y y' : Expr ⊕ Nat} {sl sl' : Nat} (h : SlotOwn PB sl y) (h' : SlotOwn PB sl' y')
    (r : OwnRel PA PB x y) (r' : OwnRel PA PB x y') : sl' = sl := by
  rcases x with a | k <;> rcases y with b | kB <;> rcases y' with b' | kB' <;>
    simp only [OwnRel] at r r'
  · subst r r'
    obtain ⟨o, h₁, h₂⟩ := h; obtain ⟨o', h₁', h₂'⟩ := h'
    rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; exact (Option.some.inj h₂').symm
  · obtain rfl := ((EntRel.iff hA hB r r').mp rfl)
    exact (Option.some.inj (h.symm.trans h')).symm

theorem OwnRel.slot_eqA (hA : CompInv f₁ p₁ PA) (hB : CompInv f₂ p₂ PB) {y : Expr ⊕ Nat}
    {x x' : Expr ⊕ Nat} {sl sl' : Nat} (h : SlotOwn PA sl x) (h' : SlotOwn PA sl' x')
    (r : OwnRel PA PB x y) (r' : OwnRel PA PB x' y) : sl' = sl := by
  rcases y with b | kB <;> rcases x with a | k <;> rcases x' with a' | k' <;>
    simp only [OwnRel] at r r'
  · subst r r'
    obtain ⟨o, h₁, h₂⟩ := h; obtain ⟨o', h₁', h₂'⟩ := h'
    rw [h₁] at h₁'; cases h₁'; rw [h₂] at h₂'; exact (Option.some.inj h₂').symm
  · obtain rfl := ((EntRel.iff hA hB r r').mpr rfl)
    exact (Option.some.inj (h.symm.trans h')).symm

/-- **A slot set on both sides** to one cell `c ≥ 1`, at related owners. -/
theorem SlotRel.set (hA : CompInv f₁ p₁ PA) (hB : CompInv f₂ p₂ PB) {sa sb : Array Nat}
    (h : SlotRel PA PB sa sb) {slA slB : Nat} {x y : Expr ⊕ Nat} (hoA : SlotOwn PA slA x)
    (hoB : SlotOwn PB slB y) (hxy : OwnRel PA PB x y) {c : Nat} (hc : 0 < c) :
    SlotRel PA PB (g4SlotSet sa slA (PA.epBase + c)) (g4SlotSet sb slB (PB.epBase + c)) := by
  have e : ∀ ep, (if ep + c > ep then ep + c - ep else 0) = c := fun ep => by
    rw [ite_eq_left (by omega)]; omega
  refine ⟨fun slA' slB' x' y' hA' hB' r' => ?_, fun slA' hne => ?_, fun slB' hne => ?_⟩
  · rw [slotGet_set, slotGet_set]
    by_cases eA : slA' = slA
    · subst eA
      obtain rfl := hA.slotUniq _ _ _ hA' hoA
      rw [ite_eq_left (OwnRel.slot_eqB hA hB hoB hB' hxy r'), ite_eq_left rfl, e, e]
    · rw [ite_eq_right eA]
      by_cases eB : slB' = slB
      · subst eB
        obtain rfl := hB.slotUniq _ _ _ hB' hoB
        exact absurd (OwnRel.slot_eqA hA hB hoA hA' hxy r') eA
      · rw [ite_eq_right eB]; exact h.1 _ _ _ _ hA' hB' r'
  · rw [slotGet_set] at hne
    by_cases eA : slA' = slA
    · subst eA; exact ⟨x, slB, y, hoA, hoB, hxy⟩
    · rw [ite_eq_right eA] at hne; exact h.2.1 _ hne
  · rw [slotGet_set] at hne
    by_cases eB : slB' = slB
    · subst eB; exact ⟨x, slA, y, hoA, hoB, hxy⟩
    · rw [ite_eq_right eB] at hne; exact h.2.2 _ hne

/-- **Pushing a projection frame** with related row words. -/
theorem FsRel.pushProj {fa fb : Array Nat} (h : FsRel PA PB fa fb) {a b : Nat} (hp : PiRel PA PB a b) :
    FsRel PA PB ((fa.push a).push 4) ((fb.push b).push 4) := by
  refine ⟨by simp [h.1], ?_⟩
  simp only [Array.size_push]
  refine .proj ?_ ?_ ?_ (((h.2.push (Nat.le_refl _) h.1 a b)).push (by simp) (by simp [h.1]) 4 4)
  · rw [show fa.size + 1 = (fa.push a).size by simp, getElem!_push_eq',
      show (fa.push a).size = (fb.push b).size by simp [h.1], getElem!_push_eq']
  · rw [show fa.size + 1 = (fa.push a).size by simp, getElem!_push_eq']; decide
  · have e₁ : ((fa.push a).push 4)[fa.size]! = a := by
      rw [getElem!_push_lt' (by simp), getElem!_push_eq']
    have e₂ : ((fb.push b).push 4)[fa.size]! = b := by
      rw [← h.1, getElem!_push_lt' (by simp), getElem!_push_eq']
    rw [e₁, e₂]; exact hp

end

end

end ConLeche.Verify.Ground
