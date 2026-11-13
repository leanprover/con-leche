module

public import ConLeche.Verify.Ground.Run
import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step3
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.GroundComplete

public section

/-!
# Mode 1: the literal frames (task #423 soundness, layer (c))

The value in focus meets a literal frame: the `Nat.succ` frame (`7`) packs a
`Nat.succ` reading into a literal, the first literal frame (`5`) reads the
first argument of an accelerated operation and the second (`6`) the
second, which computes the operation (`Red.natOp`, here `ERed.natOp`).  A
value of no literal reading unfolds the operation (δ, a re-dispatch).

The run's flag facts (`RunOK`) are set once, where the run's program is
made: the `Nat` and string flags imply the stored declarations, and the four
entries the run names read back as their constants.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Rules

/-! ## The run's flag facts -/

/-- **The run's flag facts**: what the run's flags and its four named entries
mean, kept by every program extension (`RunOK.ext`). -/
structure RunOK (env : Env) (P : G4Prog) : Prop where
  nat : P.natOk = true → natLitStored env = true
  str : P.strOk = true → strLitStored env = true
  zero : P.kZero < P.kInfo.size ∧ entryTerm P P.kZero = .const natZeroName []
  succ : P.kSucc < P.kInfo.size ∧ entryTerm P P.kSucc = .const natSuccName []
  tru : P.kTrue < P.kInfo.size ∧ entryTerm P P.kTrue = .const boolTrueName []
  fls : P.kFalse < P.kInfo.size ∧ entryTerm P P.kFalse = .const boolFalseName []

theorem ExtR.flagsEq {P P' : G4Prog} (hx : ExtR P P') :
    P'.natOk = P.natOk ∧ P'.strOk = P.strOk := by
  have := hx.flags; simp only [G4Prog.flags, Prod.mk.injEq] at this
  exact this

theorem site_eq {P P' : G4Prog} (hs : P'.site = P.site) :
    P'.kTrue = P.kTrue ∧ P'.kFalse = P.kFalse ∧ P'.kZero = P.kZero ∧ P'.kSucc = P.kSucc := by
  simp only [G4Prog.site, Prod.mk.injEq] at hs
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩

/-- The flag facts under growth that keeps the site's words. -/
theorem RunOK.ext {env : Env} {P P' : G4Prog} (h : RunOK env P) (hx : ExtR P P')
    (hs : P'.site = P.site) : RunOK env P' := by
  obtain ⟨e₁, e₂⟩ := hx.flagsEq
  obtain ⟨e₄, e₅, e₆, e₇⟩ := site_eq hs
  refine ⟨fun h' => h.nat (e₁ ▸ h'), fun h' => h.str (e₂ ▸ h'), ?_, ?_, ?_, ?_⟩
  · rw [e₆]; exact ⟨Nat.lt_of_lt_of_le h.zero.1 hx.kInfoSize, by rw [entryTerm_ext hx h.zero.1]; exact h.zero.2⟩
  · rw [e₇]; exact ⟨Nat.lt_of_lt_of_le h.succ.1 hx.kInfoSize, by rw [entryTerm_ext hx h.succ.1]; exact h.succ.2⟩
  · rw [e₄]; exact ⟨Nat.lt_of_lt_of_le h.tru.1 hx.kInfoSize, by rw [entryTerm_ext hx h.tru.1]; exact h.tru.2⟩
  · rw [e₅]; exact ⟨Nat.lt_of_lt_of_le h.fls.1 hx.kInfoSize, by rw [entryTerm_ext hx h.fls.1]; exact h.fls.2⟩

/-! ## Readings -/

/-- A literal value is its literal. -/
theorem ValDen.inv2 {P : G4Prog} {val ev argA : Array Nat} {oc : Nat → Expr} {v : Nat} {t : Expr}
    (h : ValDen P val ev argA oc v t) (h2 : val[4 * v]! = 2) : t = .lit (.natVal val[4 * v + 1]!) := by
  cases h with
  | natLit _ => rfl
  | other h5 => omega
  | _ => simp_all

/-- A string value is its string. -/
theorem ValDen.inv3 {P : G4Prog} {val ev argA : Array Nat} {oc : Nat → Expr} {v : Nat} {t : Expr}
    (h : ValDen P val ev argA oc v t) (h3 : val[4 * v]! = 3) :
    ∃ s, P.strs[val[4 * v + 1]!]? = some s ∧ t = .lit (.strVal s) := by
  cases h with
  | strLit _ hs => exact ⟨_, hs, rfl⟩
  | other h5 => omega
  | _ => simp_all

theorem span_zero (a : Array Nat) (start : Nat) : span a start 0 = [] := rfl

theorem span_one (a : Array Nat) (start : Nat) : span a start 1 = [a[start]!] := by
  simp [span]

/-! ## The accelerated operations' indices -/

/-- An accelerated operation's index names it in `natBin14Names`. -/
theorem natBin14_idx {c : Name} (h : natBin14 c = true) :
    (natBin14Names.idxOf? c).getD 0 < 14 ∧ natBin14Names[(natBin14Names.idxOf? c).getD 0]! = c ∧
      c ∈ natBinOpNames := by
  simp only [natBin14, Bool.and_eq_true, natBin14Slow, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨-, h⟩ := h
  rcases h with ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h <;>
    subst h <;> decide

/-! ## The literal frames on the stack -/

theorem FS.top_succ {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 7) : ∃ fl', fl = .succ :: fl' ∧ FS fs (fs.size - 1) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | succ _ h' => exact ⟨_, rfl, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | iota h₀ _ | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht
                             rw [h₀] at ht; cases ht
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

theorem FS.top_natA {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 5) :
    ∃ fl', fl = .natA fs[fs.size - 4]! fs[fs.size - 3]! fs[fs.size - 2]! :: fl' ∧ 4 ≤ fs.size ∧
      FS fs (fs.size - 4) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | @natA t' fl' _ h' => exact ⟨fl', by simp, by omega, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | iota h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

theorem FS.top_natB {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 6) :
    ∃ fl', fl = .natB fs[fs.size - 5]! fs[fs.size - 4]! fs[fs.size - 3]! fs[fs.size - 2]! :: fl' ∧
      5 ≤ fs.size ∧ FS fs (fs.size - 5) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | @natB t' fl' _ h' => exact ⟨fl', by simp, by omega, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | iota h₀ _ | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht
                             rw [h₀] at ht; cases ht
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

/-- The frame tags of mode 1 the engine's last branch meets: a literal frame. -/
theorem FS.top_lit {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (h1 : fs[fs.size - 1]! &&& 15 ≠ 1) (h2 : fs[fs.size - 1]! &&& 15 ≠ 2)
    (h3 : fs[fs.size - 1]! &&& 15 ≠ 3) (h4 : fs[fs.size - 1]! &&& 15 ≠ 4)
    (h7 : fs[fs.size - 1]! &&& 15 ≠ 7) :
    fs[fs.size - 1]! &&& 15 = 5 ∨ fs[fs.size - 1]! &&& 15 = 6 := by
  generalize hsz : fs.size = t at h hn h1 h2 h3 h4 h7
  cases h with
  | nil => omega
  | arg h₀ _ => simp only [Nat.add_sub_cancel] at h1; exact absurd h₀ h1
  | upd h₀ _ => simp only [Nat.add_sub_cancel] at h2; exact absurd h₀ h2
  | succ h₀ _ => simp only [Nat.add_sub_cancel] at h7; exact absurd h₀ h7
  | iota h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at h3; exact absurd h₀ h3
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at h4; exact absurd h₀ h4
  | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl]; exact .inl h₀
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl]; exact .inr h₀

theorem FS.pushSucc {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) :
    FS (fs.push 7) (fs.push 7).size (.succ :: fl) := by
  have := FS.succ (fs := fs.push 7) (t := fs.size) (by rw [getElem!_push_eq']; rfl)
    (FS.push _ (Nat.le_refl _) h)
  simpa using this

theorem FS.pushNatB {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (k m a b : Nat) :
    FS (((((fs.push k).push m).push a).push b).push 6) (((((fs.push k).push m).push a).push b).push 6).size
      (.natB k m a b :: fl) := by
  have h5 : (((((fs.push k).push m).push a).push b).push 6).size = fs.size + 5 := by simp
  rw [h5]
  have hp := FS.push 6 (by simp; omega) (FS.push b (by simp; omega) (FS.push a (by simp; omega)
    (FS.push m (by simp only [Array.size_push]; omega) (FS.push k (Nat.le_refl _) h))))
  have e4 : (((((fs.push k).push m).push a).push b).push 6)[fs.size + 4]! = 6 := by
    rw [show fs.size + 4 = ((((fs.push k).push m).push a).push b).size from by simp, getElem!_push_eq']
  have := FS.natB (t := fs.size) (by rw [e4]; rfl) hp
  have e0 : (((((fs.push k).push m).push a).push b).push 6)[fs.size]! = k := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_eq']
  have e1 : (((((fs.push k).push m).push a).push b).push 6)[fs.size + 1]! = m := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), show fs.size + 1 = (fs.push k).size by simp,
      getElem!_push_eq']
  have e2 : (((((fs.push k).push m).push a).push b).push 6)[fs.size + 2]! = a := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show fs.size + 2 = ((fs.push k).push m).size by simp, getElem!_push_eq']
  have e3 : (((((fs.push k).push m).push a).push b).push 6)[fs.size + 3]! = b := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show fs.size + 3 = (((fs.push k).push m).push a).size by simp, getElem!_push_eq']
  rwa [e0, e1, e2, e3] at this

theorem FS.pop1 {fs : Array Nat} {fl : List Fr} (h : FS fs (fs.size - 1) fl) :
    FS fs.pop fs.pop.size fl := by
  show FS (g4PopN fs 1) (g4PopN fs 1).size fl
  rw [g4PopN_size]; exact FS.popN 1 (Nat.le_refl _) h

theorem FS.popK {fs : Array Nat} {fl : List Fr} {k : Nat} (h : FS fs (fs.size - k) fl) :
    FS (g4PopN fs k) (g4PopN fs k).size fl := by
  rw [g4PopN_size]; exact FS.popN k (Nat.le_refl _) h

/-! ## The literal readings of a value (`g4Run`'s `rd` and `m`) -/

/-- The engine's reading of value `v` at a literal frame: `0` a literal,
`1` a `Nat.succ` of a cell, `2` none. -/
@[expose] def litRd (P : G4Prog) (val : Array Nat) (v : Nat) : Nat :=
  if val[g4X4 v]! == 2 then 0
  else if val[g4X4 v]! == 1 && val[g4X4 v + 1]! == P.kZero && val[g4X4 v + 3]! == 0 then 0
  else if val[g4X4 v]! == 1 && val[g4X4 v + 1]! == P.kSucc && val[g4X4 v + 3]! == 1 then 1 else 2

/-- The reading's literal (`litRd = 0`) or cell (`litRd = 1`). -/
@[expose] def litM (P : G4Prog) (val argA : Array Nat) (v : Nat) : Nat :=
  if val[g4X4 v]! == 2 then val[g4X4 v + 1]! else if litRd P val v == 0 then 0
  else if litRd P val v == 1 then argA[val[g4X4 v + 2]!]! else 0

theorem litRead0 {env : Env} {P : G4Prog} (hR : RunOK env P) {val ev argA : Array Nat}
    {oc : Nat → Expr} {v : Nat} {t : Expr} (hv : ValDen P val ev argA oc v t) (hrd : litRd P val v = 0) :
    rawNatLit? t = some (litM P val argA v) := by
  unfold litM; rw [hrd]
  unfold litRd at hrd
  simp only [g4X4_eq] at hrd ⊢
  by_cases h2 : val[4 * v]! = 2
  · simp only [h2, beq_self_eq_true, ite_true]; rw [hv.inv2 h2]; rfl
  · have h2' : (val[4 * v]! == 2) = false := by simpa using h2
    simp only [h2', Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true] at hrd ⊢
    split at hrd
    · rename_i hz
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨⟨h1, hz⟩, hl⟩ := hz
      obtain ⟨-, -, rfl⟩ := hv.inv1 h1
      rw [hl, span_zero, List.map_nil, hz]
      show rawNatLit? (entryTerm P P.kZero) = _
      rw [hR.zero.2]; simp [rawNatLit?]
    · split at hrd <;> cases hrd

theorem litRead1 {env : Env} {P : G4Prog} (hR : RunOK env P) {val ev argA : Array Nat}
    {oc : Nat → Expr} {v : Nat} {t : Expr} (hv : ValDen P val ev argA oc v t) (hrd : litRd P val v = 1) :
    t = .app (.const natSuccName []) (oc (litM P val argA v)) ∧ val[4 * v + 2]! < argA.size ∧
      litM P val argA v = argA[val[4 * v + 2]!]! := by
  unfold litM; rw [hrd]
  unfold litRd at hrd
  simp only [g4X4_eq] at hrd ⊢
  by_cases h2 : val[4 * v]! = 2
  · simp [h2] at hrd
  · have h2' : (val[4 * v]! == 2) = false := by simpa using h2
    simp only [h2', Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true] at hrd ⊢
    simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, ite_false]
    split at hrd
    · cases hrd
    · split at hrd
      · rename_i hs
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨⟨h1, hs⟩, hl⟩ := hs
        obtain ⟨-, hsz, rfl⟩ := hv.inv1 h1
        rw [hl] at hsz ⊢
        rw [span_one, hs, List.map_cons, List.map_nil]
        refine ⟨?_, by omega, trivial⟩
        show Expr.app (entryTerm P P.kSucc) _ = _
        rw [hR.succ.2]
      · cases hrd

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- A new value in focus, over frames `fl'` whose claim holds of its term. -/
theorem MInv.pushVal (h : MInv env t₀ oc s fl) {fs : Array Nat} {fl' : List Fr}
    (hfs : FS fs fs.size fl') (hfl : FlOK s.P s.argA s.N fl') {w0 w1 w2 w3 : Nat} {u : Expr}
    (hv : ValDen s.P ((((s.val.push w0).push w1).push w2).push w3) s.ev s.argA oc (s.val.size / 4) u)
    (hK : K env t₀ s.P s.argA oc fl' u) :
    MInv env t₀ oc { s with
      val := (((s.val.push w0).push w1).push w2).push w3, fs := fs, mode := 1,
      pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  obtain ⟨hsz, -, -, -, hpre⟩ := push4_spec s.val w0 w1 w2 w3 h.store.valSz
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  refine ⟨(h.store.withVal hpre (by rw [hsz]; have := h.store.valSz; omega)).same rfl rfl rfl rfl rfl
    rfl rfl, hfs, hfl, ?_⟩
  show _ < _ ∧ ∃ t, ValDen s.P _ s.ev s.argA oc _ t ∧ _
  rw [hshr, hsz]
  exact ⟨show s.val.size / 4 < (s.val.size + 4) / 4 by omega, u, hv, hK⟩

/-- A literal value in focus. -/
theorem MInv.pushLit (h : MInv env t₀ oc s fl) {fs : Array Nat} {fl' : List Fr}
    (hfs : FS fs fs.size fl') (hfl : FlOK s.P s.argA s.N fl') (n : Nat)
    (hK : K env t₀ s.P s.argA oc fl' (.lit (.natVal n))) :
    MInv env t₀ oc { s with
      val := (((s.val.push 2).push n).push 0).push 0, fs := fs, mode := 1,
      pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  obtain ⟨-, h0, h1, -, -⟩ := push4_spec s.val 2 n 0 0 h.store.valSz
  refine h.pushVal hfs hfl ?_ hK
  have := ValDen.natLit (P := s.P) (ev := s.ev) (argA := s.argA) (oc := oc) h0
  rwa [h1] at this

/-- A constructor value of no argument in focus. -/
theorem MInv.pushCtor0 (h : MInv env t₀ oc s fl) {fs : Array Nat} {fl' : List Fr}
    (hfs : FS fs fs.size fl') (hfl : FlOK s.P s.argA s.N fl') {kc : Nat} (hkc : kc < s.P.kInfo.size)
    (hK : K env t₀ s.P s.argA oc fl' (entryTerm s.P kc)) :
    MInv env t₀ oc { s with
      val := (((s.val.push 1).push kc).push 0).push 0, fs := fs, mode := 1,
      pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  obtain ⟨-, h0, h1, h2, -⟩ := push4_spec s.val 1 kc 0 0 h.store.valSz
  have h3 := push4_get3 s.val 1 kc 0 0 h.store.valSz
  refine h.pushVal hfs hfl (.ctor h0 (by rw [h1]; exact hkc) (by rw [h2, h3]; omega)) ?_
  rw [h1, h2, h3, span_zero]; exact hK

/-- The `Nat.succ` frame pushed over frames whose claim holds of `Nat.succ u`. -/
theorem K.pushSucc {P : G4Prog} {argA : Array Nat} {fl : List Fr} {u : Expr} (hn : natLitStored env = true)
    (hK : K env t₀ P argA oc fl (.app (.const natSuccName []) u)) : K env t₀ P argA oc (.succ :: fl) u :=
  ⟨K.step env t₀ P argA oc fl hK (.forget .refl (.bot _)),
    fun _ _ hw hr => K.step env t₀ P argA oc fl hK (.natSucc hn hw hr)⟩

/-! ## The `Nat.succ` frame -/

/-- **A literal at the `Nat.succ` frame**: its successor. -/
theorem step_succ_lit (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 7) (h2 : s.val[g4X4 s.x]! = 2) :
    ∃ fl', MInv env t₀ oc { s with
      val := (((s.val.push 2).push (s.val[g4X4 s.x + 1]! + 1)).push 0).push 0,
      fs := s.fs.pop, mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  rw [g4X4_eq] at h2 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain rfl := hv.inv2 h2
  obtain ⟨fl', rfl, hfs⟩ := FS.top_succ h.stack hn ht
  exact ⟨fl', h.pushLit hfs.pop1 (fun f hf => h.frames f (List.mem_cons_of_mem _ hf)) _
    (hK.2 _ _ .refl rfl)⟩

/-- **`Nat.zero` at the `Nat.succ` frame**: the literal `1`. -/
theorem step_succ_zero (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 7) (h1 : s.val[g4X4 s.x]! = 1)
    (hz : s.val[g4X4 s.x + 1]! = s.P.kZero) (hl : s.val[g4X4 s.x + 3]! = 0) :
    ∃ fl', MInv env t₀ oc { s with
      val := (((s.val.push 2).push 1).push 0).push 0,
      fs := s.fs.pop, mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  rw [g4X4_eq] at h1 hz hl
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨-, -, rfl⟩ := hv.inv1 h1
  rw [hl, span_zero, List.map_nil, hz] at hK
  change K env t₀ s.P s.argA oc fl (entryTerm s.P s.P.kZero) at hK
  rw [hR.zero.2] at hK
  obtain ⟨fl', rfl, hfs⟩ := FS.top_succ h.stack hn ht
  exact ⟨fl', h.pushLit hfs.pop1 (fun f hf => h.frames f (List.mem_cons_of_mem _ hf)) _
    (hK.2 _ 0 .refl (by simp [rawNatLit?]))⟩

/-- **`Nat.succ c` at the `Nat.succ` frame**: a second frame, and the cell `c`
entered (a stutter). -/
theorem step_succ_succ (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 7) (h1 : s.val[g4X4 s.x]! = 1)
    (hs : s.val[g4X4 s.x + 1]! = s.P.kSucc) (hl : s.val[g4X4 s.x + 3]! = 1) :
    ∃ fl', MInv env t₀ oc { s with
      fs := s.fs.push 7, mode := 2, pc := 0, env := 0, x := s.argA[s.val[g4X4 s.x + 2]!]! } fl' := by
  rw [g4X4_eq] at h1 hs hl ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨-, hsz, rfl⟩ := hv.inv1 h1
  rw [hl, span_one, hs, List.map_cons, List.map_nil] at hK
  change K env t₀ s.P s.argA oc fl (.app (entryTerm s.P s.P.kSucc) _) at hK
  rw [hR.succ.2] at hK
  rw [hl] at hsz
  obtain ⟨fl', rfl, hfs⟩ := FS.top_succ h.stack hn ht
  have hok : s.P.natOk = true := h.frames .succ (List.mem_cons_self ..)
  refine ⟨.succ :: .succ :: fl', h.store.same rfl rfl rfl rfl rfl rfl rfl, FS.pushSucc h.stack, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hok
    · exact h.frames f hf
  · exact ⟨h.store.argRef _ (by omega), K.pushSucc (hR.nat hok) hK⟩

/-- **Any other value at the `Nat.succ` frame**: the frame is popped and
the focus is the neutral. -/
theorem step_succ_pop (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 7) :
    ∃ fl', MInv env t₀ oc { s with fs := s.fs.pop, mode := 1, pc := 0, env := 0, x := 0 } fl' := by
  obtain ⟨-, t, -, hK⟩ := h.val1 hm
  obtain ⟨fl', rfl, hfs⟩ := FS.top_succ h.stack hn ht
  exact ⟨fl', h.neutral hfs.pop1 (fun f hf => List.mem_cons_of_mem _ hf) hK.1⟩

end

/-! ## The literal frames -/

/-- An accelerated operation's entry: its constant, the `Nat` flag, its
operation index. -/
theorem natEntry {env : Env} {P : G4Prog} (hI : Inv env.find? env.findProj? P) {k : Nat}
    (hk : k < P.kInfo.size) (h3 : P.kTag[k]? = some 3) :
    ∃ c, entryTerm P k = .const c [] ∧ P.natOk = true ∧ P.kE[k]! < 14 ∧
      natBin14Names[P.kE[k]!]! = c ∧ c ∈ natBinOpNames := by
  obtain ⟨c, lps, v, hi, hn, hb, he⟩ := (hI.ents k hk).tag3 hk h3
  obtain ⟨h14, hc, hmem⟩ := natBin14_idx hb
  refine ⟨c, by unfold entryTerm; rw [hi]; rfl, hn, ?_⟩
  rw [get!_of_some he]; exact ⟨h14, hc, hmem⟩

theorem g4NatKind_one {op : Nat} (h : g4NatKind op = 1) : op = 4 ∨ op = 5 := by
  unfold g4NatKind at h; split at h <;> simp_all

theorem g4NatKind_zero {op : Nat} (h : g4NatKind op = 0) : op ≠ 4 ∧ op ≠ 5 := by
  unfold g4NatKind at h; split at h <;> simp_all

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- Under a literal frame the `Nat` flag is set. -/
theorem MInv.litOk (h : MInv env t₀ oc s fl) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 5 ∨ s.fs[s.fs.size - 1]! &&& 15 = 6) : s.P.natOk = true := by
  rcases ht with ht | ht
  · obtain ⟨fl', rfl, -, -⟩ := FS.top_natA h.stack hn ht
    obtain ⟨hk, -, -, h3⟩ := h.frames _ (List.mem_cons_self ..)
    obtain ⟨_, -, hok, -⟩ := natEntry h.store.prog hk h3
    exact hok
  · obtain ⟨fl', rfl, -, -⟩ := FS.top_natB h.stack hn ht
    obtain ⟨hk, -, -, h3⟩ := h.frames _ (List.mem_cons_self ..)
    obtain ⟨_, -, hok, -⟩ := natEntry h.store.prog hk h3
    exact hok

/-- **`Nat.succ c` at a literal frame**: the `Nat.succ` frame pushed, the
cell `c` entered (a stutter). -/
theorem step_lit_succ (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 5 ∨ s.fs[s.fs.size - 1]! &&& 15 = 6)
    (hrd : litRd s.P s.val s.x = 1) :
    ∃ fl', MInv env t₀ oc { s with
      fs := s.fs.push 7, mode := 2, pc := 0, env := 0, x := litM s.P s.val s.argA s.x } fl' := by
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨rfl, hlt, he⟩ := litRead1 hR hv hrd
  have hok := h.litOk hn ht
  refine ⟨.succ :: fl, h.store.same rfl rfl rfl rfl rfl rfl rfl, FS.pushSucc h.stack, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hok
    · exact h.frames f hf
  · exact ⟨by rw [he]; exact h.store.argRef _ hlt, K.pushSucc (hR.nat hok) hK⟩

/-- **A literal reading at the first literal frame**: the second frame
pushed, the second argument entered (a stutter). -/
theorem step_natA_lit (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 5) (hrd : litRd s.P s.val s.x = 0) :
    ∃ fl', MInv env t₀ oc { s with
      fs := (((((g4PopN s.fs 4).push s.fs[s.fs.size - 4]!).push (litM s.P s.val s.argA s.x)).push
        s.fs[s.fs.size - 3]!).push s.fs[s.fs.size - 2]!).push 6,
      mode := 2, pc := 0, env := 0, x := s.fs[s.fs.size - 2]! } fl' := by
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  have hr := litRead0 hR hv hrd
  obtain ⟨fl', rfl, -, hfs⟩ := FS.top_natA h.stack hn ht
  obtain ⟨hk, ha, hb, h3⟩ := h.frames _ (List.mem_cons_self ..)
  refine ⟨_, h.store.same rfl rfl rfl rfl rfl rfl rfl, FS.pushNatB hfs.popK _ _ _ _, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨hk, ha, hb, h3⟩
    · exact h.frames f (List.mem_cons_of_mem _ hf)
  · exact ⟨hb, .refl, ⟨t, hK.1, hr⟩, hK.2⟩

/-- The operation unfolded: two argument frames over the entry, a plain
δ dispatch (a stutter). -/
theorem lit_delta (h : MInv env t₀ oc s fl) {k a b d : Nat} {fl' : List Fr}
    (hfs : FS s.fs (s.fs.size - d) fl') (hk : k < s.P.kInfo.size) (ha : a < s.N) (hb : b < s.N)
    (hfl : FlOK s.P s.argA s.N fl') (h3 : s.P.kTag[k]? = some 3)
    (hK : K env t₀ s.P s.argA oc fl' (opTerm s.P oc k a b)) :
    ∃ fl'', MInv env t₀ oc { s with
      fs := ((g4PopN s.fs d).push (g4Tag b 1)).push (g4Tag a 1), mode := 3, pc := 1, env := 0, x := k } fl'' := by
  refine ⟨.arg a :: .arg b :: fl', h.store.same rfl rfl rfl rfl rfl rfl rfl,
    FS.pushArg (FS.pushArg hfs.popK _) _, ?_, hk, fun _ => h3, hK⟩
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact ha
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hb
  · exact hfl f hf

/-- **No literal reading at the first literal frame**: the operation is
unfolded. -/
theorem step_natA_delta (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 5) :
    ∃ fl', MInv env t₀ oc { s with
      fs := ((g4PopN s.fs 4).push (g4Tag s.fs[s.fs.size - 2]! 1)).push (g4Tag s.fs[s.fs.size - 3]! 1),
      mode := 3, pc := 1, env := 0, x := s.fs[s.fs.size - 4]! } fl' := by
  obtain ⟨-, t, -, hK⟩ := h.val1 hm
  obtain ⟨fl', rfl, -, hfs⟩ := FS.top_natA h.stack hn ht
  obtain ⟨hk, ha, hb, h3⟩ := h.frames _ (List.mem_cons_self ..)
  exact lit_delta h hfs hk ha hb (fun f hf => h.frames f (List.mem_cons_of_mem _ hf)) h3 hK.2

/-- **No literal reading at the second literal frame**: the operation is
unfolded. -/
theorem step_natB_delta (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 6) :
    ∃ fl', MInv env t₀ oc { s with
      fs := ((g4PopN s.fs 5).push (g4Tag s.fs[s.fs.size - 2]! 1)).push (g4Tag s.fs[s.fs.size - 3]! 1),
      mode := 3, pc := 1, env := 0, x := s.fs[s.fs.size - 5]! } fl' := by
  obtain ⟨-, t, -, hK⟩ := h.val1 hm
  obtain ⟨fl', rfl, -, hfs⟩ := FS.top_natB h.stack hn ht
  obtain ⟨hk, ha, hb, h3⟩ := h.frames _ (List.mem_cons_self ..)
  exact lit_delta h hfs hk ha hb (fun f hf => h.frames f (List.mem_cons_of_mem _ hf)) h3 hK.2.2

/-- The operation's redex at the second literal frame reduces to the
operation's result on the two readings. -/
theorem natB_red (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 6) (hrd : litRd s.P s.val s.x = 0) :
    ∃ fl' c, FS s.fs (s.fs.size - 5) fl' ∧ FlOK s.P s.argA s.N fl' ∧
      s.P.kE[s.fs[s.fs.size - 5]!]! < 14 ∧ natBin14Names[s.P.kE[s.fs[s.fs.size - 5]!]!]! = c ∧
      ∀ r, natOpResult c s.fs[s.fs.size - 4]! (litM s.P s.val s.argA s.x) = some r →
        K env t₀ s.P s.argA oc fl' r := by
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  have hr := litRead0 hR hv hrd
  obtain ⟨fl', rfl, -, hfs⟩ := FS.top_natB h.stack hn ht
  obtain ⟨hk, -, -, h3⟩ := h.frames _ (List.mem_cons_self ..)
  obtain ⟨c, hc, -, h14, hcn, hmem⟩ := natEntry h.store.prog hk h3
  obtain ⟨hb, ⟨wa, hwa, hra⟩, hK⟩ := hK
  refine ⟨fl', c, hfs, fun f hf => h.frames f (List.mem_cons_of_mem _ hf), h14, hcn, fun r hres => ?_⟩
  unfold opTerm at hK; rw [hc] at hK
  exact K.step env t₀ s.P s.argA oc fl' hK (.natOp hmem hwa hra hb hr hres)

/-- **Two literal readings, a `Nat`-valued operation**: the result literal. -/
theorem step_natB_nat (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 6) (hrd : litRd s.P s.val s.x = 0)
    (hkd : g4NatKind s.P.kE[s.fs[s.fs.size - 5]!]! = 0) :
    ∃ fl', MInv env t₀ oc { s with
      val := (((s.val.push 2).push (g4NatVal s.P.kE[s.fs[s.fs.size - 5]!]! s.fs[s.fs.size - 4]!
        (litM s.P s.val s.argA s.x))).push 0).push 0,
      fs := g4PopN s.fs 5, mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  obtain ⟨fl', c, hfs, hfl, h14, rfl, hK⟩ := natB_red hR h hm hn ht hrd
  exact ⟨fl', h.pushLit hfs.popK hfl _ (hK _ (g4NatVal_natOpResult _ _ _ h14 (g4NatKind_zero hkd)))⟩

/-- **Two literal readings, a `Bool`-valued operation**: the result
constructor. -/
theorem step_natB_bool (hR : RunOK env s.P) (h : MInv env t₀ oc s fl) (hm : s.mode = 1)
    (hn : 0 < s.fs.size) (ht : s.fs[s.fs.size - 1]! &&& 15 = 6) (hrd : litRd s.P s.val s.x = 0)
    (hkd : g4NatKind s.P.kE[s.fs[s.fs.size - 5]!]! = 1) :
    ∃ fl', MInv env t₀ oc { s with
      val := (((s.val.push 1).push (if g4NatVal s.P.kE[s.fs[s.fs.size - 5]!]! s.fs[s.fs.size - 4]!
        (litM s.P s.val s.argA s.x) == 1 then s.P.kTrue else s.P.kFalse)).push 0).push 0,
      fs := g4PopN s.fs 5, mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  obtain ⟨fl', c, hfs, hfl, -, rfl, hK⟩ := natB_red hR h hm hn ht hrd
  have hres := hK _ (g4NatBool_natOpResult _ _ _ (g4NatKind_one hkd))
  refine ⟨fl', h.pushCtor0 hfs.popK hfl ?_ ?_⟩
  · split
    · exact hR.tru.1
    · exact hR.fls.1
  · split
    · rename_i hb; simp only [hb, ite_true] at hres; rw [hR.tru.2]; exact hres
    · rename_i hb; simp only [hb, ite_false, Bool.false_eq_true] at hres; rw [hR.fls.2]; exact hres

end

end ConLeche.Verify.Ground
