module

public import ConLeche.Verify.Ground.SimState
import ConLeche.Verify.Ground.Step0

public section

/-!
# The layout bridge (task #423 soundness, layer (d), item 2(c))

The words the machine reads at two related code positions (`TRel`), by the
node's tag: one tag, and the fields either one word or related again.  The
lookups agree on the names the related terms mention (`Agree`): for the
kept/fresh instance the lookups are one (`LookAgree.univ`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- **The lookups agree on `N`**: on the constants, the projection rows and
the erasure masks (a mask reads the constant's type: the agreement there is
the caller's, where `N` is closed under types), and on the K constructor a
recursor names; `N` holds the names of the definition values and of the
recursor rules the run compiles. -/
structure LookAgree (N : Name → Prop) (f₁ : Name → Option ConstantInfo) (p₁ : Name → Nat → Option ProjEntry)
    (f₂ : Name → Option ConstantInfo) (p₂ : Name → Nat → Option ProjEntry) : Prop where
  find : ∀ c, N c → f₂ c = f₁ c
  proj : ∀ sn i, N sn → p₂ sn i = p₁ sn i
  mask : ∀ c, N c → maskName f₂ c = maskName f₁ c
  kfab : ∀ c us, N c → kfabKey f₂ c us = kfabKey f₁ c us
  defVal : ∀ c cv v hs, N c → f₁ c = some (.defnInfo cv v hs) → NamesIn N v
  rules : ∀ c cv mI rP isK rules, N c → f₁ c = some (.recInfo cv mI rP isK rules) →
    ∀ rl ∈ rules, N rl.ctor ∧ NamesIn N rl.rhs ∧
      ∀ cvj nP nF, f₁ rl.ctor = some (.ctorInfo cvj nP nF) →
        ∀ T ls, cvj.type.piResult.getAppFn = .const T ls → N T
  /-- one of the `Nat` basis in `N` brings the others -/
  natTrio : N natName ∨ N natZeroName ∨ N natSuccName → NatN N
  /-- an accelerated operation in `N` brings the `Nat` basis -/
  natOp : ∀ c, N c → natBin14 c = true → NatN N
  /-- a `Bool`-valued operation in `N` brings the `Bool` constructors -/
  boolOp : ∀ c, N c → (c = natBeqName ∨ c = natBleName) → N boolTrueName ∧ N boolFalseName

/-- One lookup, every name. -/
theorem LookAgree.univ (f : Name → Option ConstantInfo) (p : Name → Nat → Option ProjEntry) :
    LookAgree (fun _ => True) f p f p :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ v _ _ _ => NamesIn.univ v, fun _ _ _ _ _ _ _ _ rl _ => ⟨trivial, NamesIn.univ rl.rhs, fun _ _ _ _ _ _ _ => trivial⟩,
    fun _ => ⟨trivial, trivial, trivial⟩, fun _ _ _ => ⟨trivial, trivial, trivial⟩, fun _ _ _ => ⟨trivial, trivial⟩⟩

/-- An entry read back as a constant is that constant's entry. -/
theorem ent_key {P : G4Prog} {k : Nat} (hk : k < P.kInfo.size) {c : Name} {us : List Level}
    (he : entryTerm P k = .const c us) : ∃ i, P.kInfo[k]? = some i ∧ infoKey i = (c, us) := by
  unfold entryTerm at he
  rw [Array.getElem?_eq_getElem hk] at he ⊢
  refine ⟨_, rfl, ?_⟩
  dsimp only at he
  rw [infoTerm_key] at he
  cases he; rfl

/-- An entry related by `ERel` and read back as a constant has its constant in `N`. -/
theorem ERel.nameN {N : Name → Prop} {PA PB : G4Prog} {kA kB : Nat} (hE : ERel N PA PB kA kB)
    {c : Name} {us : List Level} (h : kA < PA.kInfo.size ∧ entryTerm PA kA = .const c us) : N c := by
  obtain ⟨i, hi, hk⟩ := ent_key h.1 h.2
  have := hE.2 i hi
  rw [hk] at this; exact this

/-- A string literal's constructor form has its names in `N`. -/
theorem NamesIn.strLit {N : Name → Prop} (h : StrNames N) (s : String) :
    NamesIn N (strLitToConstructor s) := by
  obtain ⟨hn, -, h₁, -, h₂, h₃, h₄, h₅⟩ := h
  unfold strLitToConstructor
  refine ⟨h₁, ?_⟩
  induction s.toList with
  | nil => exact ⟨h₂, h₄⟩
  | cons c l ih => exact ⟨⟨⟨h₃, h₄⟩, h₅, hn⟩, ih⟩

/-- Level instantiation keeps a term's names. -/
theorem NamesIn.instLP {N : Name → Prop} (ks : List Name) (us : List Level) :
    ∀ {t : Expr}, NamesIn N t → NamesIn N (t.instantiateLevelParams ks us)
  | .bvar _, h | .sort _, h | .lit _, h | .const _ _, h => h
  | .fvar _ ty, h => NamesIn.instLP ks us (t := ty) h
  | .app f x, h | .lam f x, h | .forallE f x, h =>
    ⟨NamesIn.instLP ks us (t := f) h.1, NamesIn.instLP ks us (t := x) h.2⟩
  | .letE ty v b, h =>
    ⟨NamesIn.instLP ks us (t := ty) h.1, NamesIn.instLP ks us (t := v) h.2.1,
      NamesIn.instLP ks us (t := b) h.2.2⟩
  | .proj _ _ e, h => ⟨h.1, NamesIn.instLP ks us (t := e) h.2⟩

section
variable {j : Nat} {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}

theorem NamesIn.projAgree (hag : LookAgree N f₁ p₁ f₂ p₂) {t : Expr} (h : NamesIn N t) :
    ProjAgree p₁ p₂ t := by
  cases t with
  | proj sn i e => exact (hag.proj sn i h.1).symm
  | _ => trivial

/-- **One case-3 test** for a rule whose constructor and family are in `N`
(`LookAgree.rules`). -/
theorem LookAgree.case3 (hag : LookAgree N f₁ p₁ f₂ p₂) {rl : RecRule} (hc : N rl.ctor)
    (hT : ∀ cvj nP nF, f₁ rl.ctor = some (.ctorInfo cvj nP nF) →
      ∀ T ls, cvj.type.piResult.getAppFn = .const T ls → N T)
    (isK : Bool) (lps : List Name) (us : List Level) :
    ruleCase3 f₁ isK lps us rl = ruleCase3 f₂ isK lps us rl := by
  unfold ruleCase3
  rw [hag.find _ hc]
  split
  · rename_i cvj nP nF hf
    have e : ctorFamily f₁ cvj = ctorFamily f₂ cvj := by
      unfold ctorFamily
      split
      · rename_i T ls hT'
        rw [hag.find T (hT cvj nP nF hf T ls hT')]
      · rfl
    simp only [gCase3, e]
  · rfl

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
    PB.code[oB + 1]! = PA.code[oA + 1]! ∧ NatN N := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | natLit _ h₁ => cases hB with
    | natLit _ h₁' => rw [get!_of_some h₁, get!_of_some h₁']; exact ⟨rfl, hN⟩
  | _ => simp_all

/-- A string literal: one string. -/
theorem TRel.strLit (h : TRel N f₁ p₁ f₂ p₂ PA PB oA oB) (ht : PA.code[oA]! = 6) :
    StrRel PA PB PA.code[oA + 1]! PB.code[oB + 1]! ∧ StrNames N := by
  obtain ⟨t, hN, hA, hB⟩ := h.comp (by rw [ht]; decide)
  have hta := get!_of_some' hA.tag
  cases hA with
  | strLit _ h₁ h₂ => cases hB with
    | strLit _ h₁' h₂' => rw [get!_of_some h₁, get!_of_some h₁']; exact ⟨⟨_, h₂, h₂'⟩, hN⟩
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
theorem FsRel.pushProj {fa fb : Array Nat} (h : FsRel N PA PB fa fb) {a b : Nat} (hp : PiRel PA PB a b) :
    FsRel N PA PB ((fa.push a).push 4) ((fb.push b).push 4) := by
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

/-- **The `Nat` flag where an accelerated operation's entry is read**: its
name in `N` brings the `Nat` basis, so the flags agree. -/
theorem MRel.natOkAt {j : Nat} {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo}
    {p₁ p₂ : Name → Nat → Option ProjEntry} (hag : LookAgree N f₁ p₁ f₂ p₂) {sA sB : MS}
    (hr : MRel j N f₁ p₁ f₂ p₂ sA sB) {kA kB : Nat} (hE : ERel N sA.P sB.P kA kB) :
    ∀ c lps us v, sA.P.kInfo[kA]? = some (.defn c lps us v) → natBin14 c = true →
      sA.P.natOk = sB.P.natOk :=
  fun c _ _ _ hi hb => (hr.natOk (hag.natOp c (hE.2 _ hi) hb)).symm

end ConLeche.Verify.Ground
