module

public import ConLeche.Verify.Ground.Run
import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step4
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.InferLemmas

public section

/-!
# Mode 3: dispatching a constant (task #423 soundness, layer (c))

The entry in focus is applied to the argument frames on top.  A
constructor, a recursor short of its major and an accelerated operation
short of its two arguments collect the arguments into a value (a stutter);
a neutral entry pops them (`forget`); a memo hit enters the recorded cell,
whose origin is the same application (a stutter).
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-! ## Copying argument cells -/

/-- `g4CopyArgs` appends the top argument cells, the first argument first. -/
theorem copyArgs_spec (fs : Array Nat) : ∀ (n j : Nat) (argA : Array Nat),
    (g4CopyArgs fs argA n j).size = argA.size + n ∧ Pre argA (g4CopyArgs fs argA n j) ∧
      ∀ i, i < n → (g4CopyArgs fs argA n j)[argA.size + i]! = g4ArgAt fs (j + i)
  | 0, _, argA => ⟨rfl, Pre.refl argA, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, j, argA => by
    obtain ⟨h₁, h₂, h₃⟩ := copyArgs_spec fs n (j + 1) (argA.push (g4ArgAt fs j))
    refine ⟨by simp only [g4CopyArgs, h₁, Array.size_push]; omega, (Pre.push _ _).trans h₂,
      fun i hi => ?_⟩
    show (g4CopyArgs fs (argA.push (g4ArgAt fs j)) n (j + 1))[argA.size + i]! = _
    cases i with
    | zero =>
      simp only [Nat.add_zero]
      rw [h₂.2 _ (by simp), getElem!_push_eq']
    | succ i =>
      have := h₃ i (by omega)
      simp only [Array.size_push] at this
      rw [show argA.size + (i + 1) = argA.size + 1 + i by omega, this]
      congr 1; omega

/-- The copied span is the top argument frames' cells. -/
theorem copy_span {fs argA : Array Nat} {cs : List Nat}
    (hc : ∀ j, j < cs.length → cs.getD j 0 = fs[fs.size - 1 - j]! >>> 4) :
    span (g4CopyArgs fs argA cs.length 0) argA.size cs.length = cs := by
  obtain ⟨-, -, hget⟩ := copyArgs_spec fs cs.length 0 argA
  have hl := list_eq_range (l := cs) (f := fun i => g4ArgAt fs i) (fun j hj => by
    rw [hc j hj]; rfl)
  unfold span
  conv => rhs; rw [hl]
  apply List.map_congr_left
  intro i hi
  rw [hget i (List.mem_range.mp hi), Nat.zero_add]

/-- A copied prefix of the top argument frames' cells. -/
theorem copy_span_take {fs argA : Array Nat} {cs : List Nat} {n : Nat} (hn : n ≤ cs.length)
    (hc : ∀ j, j < cs.length → cs.getD j 0 = fs[fs.size - 1 - j]! >>> 4) :
    span (g4CopyArgs fs argA n 0) argA.size n = cs.take n := by
  obtain ⟨-, -, hget⟩ := copyArgs_spec fs n 0 argA
  have htl : (cs.take n).length = n := by rw [List.length_take]; omega
  have hl := list_eq_range (l := cs.take n) (f := fun i => g4ArgAt fs i) (fun j hj => by
    rw [htl] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj, ← List.getD_eq_getElem?_getD,
      hc j (by omega)]; rfl)
  rw [hl, htl]
  unfold span
  apply List.map_congr_left
  intro i hi
  rw [hget i (List.mem_range.mp hi), Nat.zero_add]

/-- The top four words of a ι frame. -/
theorem FS.pushIota {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (k start len : Nat) :
    FS ((((fs.push k).push start).push len).push 3) ((((fs.push k).push start).push len).push 3).size
      (.iota k start len :: fl) := by
  have h4 : ((((fs.push k).push start).push len).push 3).size = fs.size + 4 := by simp
  rw [h4]
  have e0 : ((((fs.push k).push start).push len).push 3)[fs.size]! = k := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_eq']
  have e1 : ((((fs.push k).push start).push len).push 3)[fs.size + 1]! = start := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show fs.size + 1 = (fs.push k).size by simp, getElem!_push_eq']
  have e2 : ((((fs.push k).push start).push len).push 3)[fs.size + 2]! = len := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), show fs.size + 2 = ((fs.push k).push start).size by simp,
      getElem!_push_eq']
  have e3 : ((((fs.push k).push start).push len).push 3)[fs.size + 3]! = 3 := by
    rw [show fs.size + 3 = (((fs.push k).push start).push len).size by simp, getElem!_push_eq']
  have hp := FS.push 3 (by simp; omega) (FS.push len (by simp; omega) (FS.push start (by simp only [Array.size_push]; omega)
    (FS.push k (Nat.le_refl _) h)))
  have := FS.iota (by rw [e3]; rfl) hp
  rwa [e0, e1, e2] at this

/-- The top four words of a literal frame (the first argument). -/
theorem FS.pushNatA {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (k a b : Nat) :
    FS ((((fs.push k).push a).push b).push 5) ((((fs.push k).push a).push b).push 5).size
      (.natA k a b :: fl) := by
  have h4 : ((((fs.push k).push a).push b).push 5).size = fs.size + 4 := by simp
  rw [h4]
  have e0 : ((((fs.push k).push a).push b).push 5)[fs.size]! = k := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_eq']
  have e1 : ((((fs.push k).push a).push b).push 5)[fs.size + 1]! = a := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show fs.size + 1 = (fs.push k).size by simp, getElem!_push_eq']
  have e2 : ((((fs.push k).push a).push b).push 5)[fs.size + 2]! = b := by
    rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), show fs.size + 2 = ((fs.push k).push a).size by simp,
      getElem!_push_eq']
  have e3 : ((((fs.push k).push a).push b).push 5)[fs.size + 3]! = 5 := by
    rw [show fs.size + 3 = (((fs.push k).push a).push b).size by simp, getElem!_push_eq']
  have hp := FS.push 5 (by simp; omega) (FS.push b (by simp; omega) (FS.push a (by simp only [Array.size_push]; omega)
    (FS.push k (Nat.le_refl _) h)))
  have := FS.natA (by rw [e3]; rfl) hp
  rwa [e0, e1, e2] at this

/-- The copy names allocated cells. -/
theorem ArgRef.copy {fs argA : Array Nat} {N : Nat} (hr : ArgRef argA N) {n : Nat}
    (hc : ∀ i, i < n → g4ArgAt fs i < N) : ArgRef (g4CopyArgs fs argA n 0) N := by
  obtain ⟨hsz, hpre, hget⟩ := copyArgs_spec fs n 0 argA
  intro j hj
  rcases Nat.lt_or_ge j argA.size with h | h
  · rw [hpre.2 j h]; exact hr j h
  · obtain ⟨i, rfl⟩ : ∃ i, j = argA.size + i := ⟨j - argA.size, by omega⟩
    rw [hget i (by omega), Nat.zero_add]; exact hc i (by omega)

theorem push4_get3 (a : Array Nat) (w0 w1 w2 w3 : Nat) (h : a.size % 4 = 0) :
    ((((a.push w0).push w1).push w2).push w3)[4 * (a.size / 4) + 3]! = w3 := by
  rw [show 4 * (a.size / 4) + 3 = (((a.push w0).push w1).push w2).size by simp; omega,
    getElem!_push_eq']

/-- The store invariant with more value words and a grown argument array. -/
theorem SInv.withValArg {env : Env} {oc : Nat → Expr} {s : MS} (h : SInv env oc s)
    {val' argA' : Array Nat} (hp : Pre s.val val') (h4 : val'.size % 4 = 0) (ha : Pre s.argA argA')
    (hr : ArgRef argA' s.N) : SInv env oc { s with val := val', argA := argA' } :=
  h.grow (s' := { s with val := val', argA := argA' }) h.prog (ExtR.refl _) rfl (Pre.refl _) h.celSz
    hp h4 (Pre.refl _) h.evSz ha rfl rfl (Agree.refl _ _) h.evRef hr
    (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega))

/-! ## The application memo -/

/-- `g4SpanEq` compares a span with the top argument cells. -/
theorem spanEq_spec (fs argA : Array Nat) (start : Nat) : ∀ (n j : Nat),
    g4SpanEq fs argA start n j = true → ∀ i, i < n → argA[start + j + i]! = g4ArgAt fs (j + i)
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, j, h, i, hi => by
    simp only [g4SpanEq, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := spanEq_spec fs argA start n (j + 1) h.2 i (by omega)
      rw [show start + j + (i + 1) = start + (j + 1) + i by omega, this]; congr 1; omega

/-- **A memo hit** is a record whose key is the entry and the top arguments. -/
theorem memoFind_spec (mem mT fs argA : Array Nat) (k n : Nat) (hn : 0 < n) :
    ∀ (f i : Nat), g4MemoFind mem mT fs argA k n f i ≠ 0 →
      ∃ r, 4 * r + 2 < mem.size ∧ mem[4 * r]! = k ∧ mem[4 * r + 2]! = n ∧
        g4SpanEq fs argA mem[4 * r + 1]! n 0 = true ∧ g4MemoFind mem mT fs argA k n f i = mem[4 * r + 3]!
  | 0, _, h => absurd rfl h
  | f + 1, i, h => by
    unfold g4MemoFind at h ⊢
    dsimp only at h ⊢
    by_cases h0 : (mT[i]! == 0) = true
    · simp only [h0, ↓reduceIte] at h; exact absurd rfl h
    · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hc : (mem[g4X4 (mT[i]! - 1)]! == k && mem[g4X4 (mT[i]! - 1) + 2]! == n &&
          g4SpanEq fs argA mem[g4X4 (mT[i]! - 1) + 1]! n 0) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hc
        rw [g4X4_eq] at h₁ h₂ h₃ ⊢
        refine ⟨mT[i]! - 1, ?_, h₁, h₂, h₃, rfl⟩
        rcases Nat.lt_or_ge (4 * (mT[i]! - 1) + 2) mem.size with h' | h'
        · exact h'
        · rw [getElem!_neg mem _ (by omega)] at h₂; exact absurd h₂ (by simp; omega)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
        exact memoFind_spec mem mT fs argA k n hn f _ h

/-- **A new memo record** naming an allocated cell whose origin is its key's
term; the memo's hash table is free. -/
theorem SInv.pushMemo {env : Env} {oc : Nat → Expr} {s : MS} (h : SInv env oc s) {k start len c : Nat}
    (hc : c < s.N) (hk : k < s.P.kInfo.size) (hl : start + len ≤ s.argA.size)
    (ho : oc c = spanTerm s.P s.argA oc k start len) (mH' : Array Nat) :
    SInv env oc { s with mem := (((s.mem.push k).push start).push len).push c, mH := mH' } := by
  obtain ⟨msz, m0, m1, m2, mpre⟩ := push4_spec s.mem k start len c h.memSz
  have m3 := push4_get3 s.mem k start len c h.memSz
  have hms := h.memSz
  refine ⟨h.prog, h.celSz, h.valSz, h.evSz, by show _ % 4 = 0; rw [msz]; omega, h.cell0, h.oc0, h.val0,
    h.closed, h.cells, h.valRef, h.evRef, h.argRef, h.slotsOK, fun r hr => ?_⟩
  change r < ((((s.mem.push k).push start).push len).push c).size / 4 at hr
  rw [msz] at hr
  rcases Nat.lt_or_ge r (s.mem.size / 4) with h' | h'
  · obtain ⟨e₁, e₂, e₃, e₄⟩ := h.memo r h'
    unfold MemoOK
    show _[4 * r + 3]! < s.N ∧ _[4 * r]! < s.P.kInfo.size ∧ _ ∧ _
    rw [mpre.2 _ (by omega), mpre.2 _ (by omega), mpre.2 _ (by omega), mpre.2 _ (by omega)]
    exact ⟨e₁, e₂, e₃, e₄⟩
  · obtain rfl : r = s.mem.size / 4 := by omega
    unfold MemoOK
    show _[4 * (s.mem.size / 4) + 3]! < s.N ∧ _[4 * (s.mem.size / 4)]! < s.P.kInfo.size ∧ _ ∧ _
    rw [m0, m1, m2, m3]
    exact ⟨hc, hk, hl, ho⟩

/-- An entry tagged `0` or `3` is a definition's. -/
theorem EntOK.tag03 {find? : Name → Option ConstantInfo} {P : G4Prog} {k : Nat} (h : EntOK find? P k)
    (hk : k < P.kInfo.size) (ht : P.kTag[k]? = some 0 ∨ P.kTag[k]? = some 3) :
    ∃ c lps us v, P.kInfo[k]? = some (.defn c lps us v) ∧ DefnOK find? P k c lps us v := by
  unfold EntOK at h
  split at h
  · rcases ht with ht | ht <;> rw [ht] at h <;> cases h
  · rename_i heq; exact ⟨_, _, _, _, heq, h⟩
  · obtain ⟨-, h2, -⟩ := h; rcases ht with ht | ht <;> rw [ht] at h2 <;> cases h2
  · obtain ⟨-, -, -, -, -, -, h2, -⟩ := h; rcases ht with ht | ht <;> rw [ht] at h2 <;> cases h2
  · rename_i heq; rw [Array.getElem?_eq_getElem hk] at heq; cases heq

/-- An entry tagged `3` is an accelerated operation's: a definition at no
levels, the `Nat` flag set, its operation index in `kE`. -/
theorem EntOK.tag3 {find? : Name → Option ConstantInfo} {P : G4Prog} {k : Nat} (h : EntOK find? P k)
    (hk : k < P.kInfo.size) (ht : P.kTag[k]? = some 3) :
    ∃ c lps v, P.kInfo[k]? = some (.defn c lps [] v) ∧ P.natOk = true ∧ natBin14 c = true ∧
      P.kE[k]? = some ((natBin14Names.idxOf? c).getD 0) := by
  obtain ⟨c, lps, us, v, hi, -, -, h3, -⟩ := h.tag03 hk (.inr ht)
  rcases h3 with h0 | ⟨-, rfl, hn, hb, he⟩
  · rw [ht] at h0; cases h0
  · exact ⟨c, lps, v, hi, hn, hb, he⟩

theorem Approx.Args.refl : ∀ (l : List Expr), Approx.Args l l
  | [] => .nil
  | a :: l => .cons (Approx.refl a) (Approx.Args.refl l)

/-! ## Collecting the arguments -/

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- The top argument frames in mode 3: the entry applied to their cells. -/
theorem MInv.topArgs (h : MInv env t₀ oc s fl) (hm : s.mode = 3) :
    ∃ (ca : List Nat) (fl' : List Fr), fl = ca.map Fr.arg ++ fl' ∧ g4CountArgs s.fs s.fs.size 0 = ca.length ∧
      s.x < s.P.kInfo.size ∧
      K env t₀ s.P s.argA oc fl' (Expr.mkAppN (entryTerm s.P s.x) (ca.map oc)) ∧
      ca.length ≤ s.fs.size ∧ FS s.fs (s.fs.size - ca.length) fl' ∧
      (∀ j, j < ca.length → ca.getD j 0 = s.fs[s.fs.size - 1 - j]! >>> 4) ∧
      (∀ c ∈ ca, c < s.N) := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hk, hK⟩ := hf
  obtain ⟨ca, fl', rfl, hca⟩ := FS.countArgs h.stack 0
  rw [Nat.zero_add] at hca
  obtain ⟨hle, hfs, hcells⟩ := FS.argsTop ca.length h.stack rfl
  exact ⟨ca, fl', rfl, hca, hk, (K.args env t₀ s.P s.argA oc ca fl' _).mp hK, hle, hfs, hcells,
    fun c hc => h.frames (.arg c) (List.mem_append_left _ (List.mem_map_of_mem hc))⟩

/-- **Collecting the arguments into a value**: a constructor (`w0 = 1`) or a
partial application (`w0 = 4`) of the entry in focus on the top argument
frames' cells (a stutter). -/
theorem step_collect (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {w0 : Nat} (hw : w0 = 1 ∨ w0 = 4) :
    ∃ fl', MInv env t₀ oc { s with
      val := (((s.val.push w0).push s.x).push s.argA.size).push (g4CountArgs s.fs s.fs.size 0),
      fs := g4PopN s.fs (g4CountArgs s.fs s.fs.size 0),
      argA := g4CopyArgs s.fs s.argA (g4CountArgs s.fs s.fs.size 0) 0,
      mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  obtain ⟨ca, fl', rfl, hca, hk, hK, hle, hfs, hcells, hN⟩ := h.topArgs hm
  rw [hca]
  obtain ⟨hsz, hpre, -⟩ := copyArgs_spec s.fs ca.length 0 s.argA
  have href : ArgRef (g4CopyArgs s.fs s.argA ca.length 0) s.N :=
    h.store.argRef.copy (fun i hi => by
      have := hN _ (List.getElem_mem (show i < ca.length from hi))
      have h' := hcells i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h'
      show s.fs[s.fs.size - 1 - i]! >>> 4 < s.N
      rw [← h']; exact this)
  obtain ⟨vsz, v0, v1, v2, vpre⟩ := push4_spec s.val w0 s.x s.argA.size ca.length h.store.valSz
  have v3 := push4_get3 s.val w0 s.x s.argA.size ca.length h.store.valSz
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  have hst := h.store.withValArg vpre (by rw [vsz]; have := h.store.valSz; omega) hpre href
  refine ⟨fl', hst.same rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
  · show FS (g4PopN s.fs ca.length) (g4PopN s.fs ca.length).size fl'
    rw [g4PopN_size]; exact FS.popN _ (Nat.le_refl _) hfs
  · exact fun f hf => (h.frames f (List.mem_append_right _ hf)).grow (ExtR.refl _) hpre (Nat.le_refl _)
  · show _ < _ ∧ ∃ t, ValDen s.P _ s.ev _ oc _ t ∧ _
    rw [hshr, vsz]
    have hK' := K.move h.store.argRef (Agree.refl oc s.N) (ExtR.refl _) hpre
      (fun f hf => h.frames f (List.mem_append_right _ hf)) hK
    have hsp := copy_span (argA := s.argA) hcells
    have e : Expr.mkAppN (entryTerm s.P s.x) (ca.map oc) =
        Expr.mkAppN (entryTerm s.P ((((s.val.push w0).push s.x).push s.argA.size).push
          ca.length)[4 * (s.val.size / 4) + 1]!) ((span (g4CopyArgs s.fs s.argA ca.length 0)
          ((((s.val.push w0).push s.x).push s.argA.size).push ca.length)[4 * (s.val.size / 4) + 2]!
          ((((s.val.push w0).push s.x).push s.argA.size).push ca.length)[4 * (s.val.size / 4) + 3]!).map
          oc) := by rw [v1, v2, v3, hsp]
    refine ⟨show s.val.size / 4 < (s.val.size + 4) / 4 by omega, _, ?_, hK'⟩
    rw [e]
    rcases hw with rfl | rfl
    · exact .ctor v0 (by rw [v1]; exact hk) (by rw [v2, v3, hsz]; exact Nat.le_refl _)
    · exact .pap v0 (by rw [v1]; exact hk) (by rw [v2, v3, hsz]; exact Nat.le_refl _)

/-- **A neutral entry**: the arguments are popped, the value is the neutral
(`forget`). -/
theorem step_neutral_entry (h : MInv env t₀ oc s fl) (hm : s.mode = 3) :
    ∃ fl', MInv env t₀ oc { s with
      fs := g4PopN s.fs (g4CountArgs s.fs s.fs.size 0), mode := 1, pc := 0, env := 0, x := 0 } fl' := by
  obtain ⟨ca, fl', rfl, hca, -, hK, -, hfs, -, -⟩ := h.topArgs hm
  rw [hca]
  refine ⟨fl', h.store.same rfl rfl rfl rfl rfl rfl rfl, ?_,
    fun f hf => h.frames f (List.mem_append_right _ hf), ?_⟩
  · show FS (g4PopN s.fs ca.length) (g4PopN s.fs ca.length).size fl'
    rw [g4PopN_size]; exact FS.popN _ (Nat.le_refl _) hfs
  · show 0 < s.val.size / 4 ∧ ∃ t, ValDen s.P s.val s.ev s.argA oc 0 t ∧ _
    have h0 := h.store.val0
    refine ⟨by omega, bot, .other (by simp only [Nat.mul_zero]; omega), ?_⟩
    exact K.step env t₀ s.P s.argA oc fl' hK (.forget .refl (.bot _))

/-- **A memo hit**: the recorded cell is entered, its origin the entry on the
top `n` argument cells (a stutter). -/
theorem step_memo_hit (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {n f i : Nat} (hn : 0 < n)
    (hle : n ≤ g4CountArgs s.fs s.fs.size 0)
    (h0 : g4MemoFind s.mem s.mH s.fs s.argA s.x n f i ≠ 0) :
    ∃ fl', MInv env t₀ oc { s with
      fs := g4PopN s.fs n, mode := 2, pc := 0, env := 0,
      x := g4MemoFind s.mem s.mH s.fs s.argA s.x n f i } fl' := by
  obtain ⟨r, hr, hk, hn', hsp, heq⟩ := memoFind_spec s.mem s.mH s.fs s.argA s.x n hn f i h0
  rw [heq]
  obtain ⟨hc, -, hlen, ho⟩ := h.store.memo r (by have := h.store.memSz; omega)
  obtain ⟨ca, fl', rfl, hca, -, -, -, -, hcells, hN⟩ := h.topArgs hm
  rw [hca] at hle
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨-, hK⟩ := hf
  have hsplit : ca.map Fr.arg ++ fl' = (ca.take n).map Fr.arg ++ ((ca.drop n).map Fr.arg ++ fl') := by
    rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
  have htl : (ca.take n).length = n := by rw [List.length_take]; omega
  rw [hsplit, K.args] at hK
  obtain ⟨-, hfs, -⟩ := FS.argsTop n (hsplit ▸ h.stack) htl
  -- the record's span is the top `n` cells
  have hspan : span s.argA s.mem[4 * r + 1]! n = ca.take n := by
    have hl := list_eq_range (l := ca.take n) (f := fun i => g4ArgAt s.fs i) (fun j hj => by
      rw [htl] at hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj, ← List.getD_eq_getElem?_getD,
        hcells j (by omega)]; rfl)
    rw [hl, htl]
    unfold span
    apply List.map_congr_left
    intro j hj
    have := spanEq_spec s.fs s.argA _ n 0 hsp j (List.mem_range.mp hj)
    rw [Nat.add_zero, Nat.zero_add] at this; exact this
  refine ⟨(ca.drop n).map Fr.arg ++ fl', h.store.same rfl rfl rfl rfl rfl rfl rfl, ?_,
    fun f hf => h.frames f (by rw [hsplit]; exact List.mem_append_right _ hf), ?_⟩
  · show FS (g4PopN s.fs n) (g4PopN s.fs n).size _
    rw [g4PopN_size]; exact FS.popN n (Nat.le_refl _) hfs
  · show s.mem[4 * r + 3]! < s.N ∧ K env t₀ s.P s.argA oc _ (oc s.mem[4 * r + 3]!)
    refine ⟨hc, ?_⟩
    rw [ho, hk, hn']
    unfold spanTerm
    rw [hspan]; exact hK

/-- **A redex recorded in the memo**: the top `n` argument cells are copied,
a busy cell is allocated for the result, its memo record and update frame
pushed (the claims: the cell's origin is the redex; the frames below see the
redex). -/
theorem memo_core (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {n : Nat}
    (hle : n ≤ g4CountArgs s.fs s.fs.size 0) (mH' : Array Nat) :
    ∃ fl', SInv env (ocExt oc s.N (spanTerm s.P (g4CopyArgs s.fs s.argA n 0) oc s.x s.argA.size n))
      { s with
        cel := (((s.cel.push 1).push 0).push 0).push 0,
        argA := g4CopyArgs s.fs s.argA n 0,
        mem := (((s.mem.push s.x).push s.argA.size).push n).push (s.cel.size >>> 2),
        mH := mH' } ∧
    FS ((g4PopN s.fs n).push (g4Tag (s.cel.size >>> 2) 2))
      ((g4PopN s.fs n).push (g4Tag (s.cel.size >>> 2) 2)).size (.upd s.N :: fl') ∧
    FlOK s.P (g4CopyArgs s.fs s.argA n 0) (s.N + 1) (.upd s.N :: fl') ∧
    K env t₀ s.P (g4CopyArgs s.fs s.argA n 0)
      (ocExt oc s.N (spanTerm s.P (g4CopyArgs s.fs s.argA n 0) oc s.x s.argA.size n))
      (.upd s.N :: fl')
      (spanTerm s.P (g4CopyArgs s.fs s.argA n 0)
        (ocExt oc s.N (spanTerm s.P (g4CopyArgs s.fs s.argA n 0) oc s.x s.argA.size n))
        s.x s.argA.size n) := by
  obtain ⟨ca, fl', rfl, hca, hk, -, -, -, hcells, hN⟩ := h.topArgs hm
  rw [hca] at hle
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨-, hK⟩ := hf
  have hsplit : ca.map Fr.arg ++ fl' =
      (ca.take n).map Fr.arg ++ ((ca.drop n).map Fr.arg ++ fl') := by
    rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
  have htl : (ca.take n).length = n := by rw [List.length_take]; omega
  rw [hsplit, K.args] at hK
  obtain ⟨-, hfs, -⟩ := FS.argsTop n (hsplit ▸ h.stack) htl
  generalize hA : g4CopyArgs s.fs s.argA n 0 = argA'
  obtain ⟨hsz, hpre, -⟩ := copyArgs_spec s.fs n 0 s.argA
  rw [hA] at hsz hpre
  have hsp : span argA' s.argA.size n = ca.take n := by
    rw [← hA]; exact copy_span_take (by omega) hcells
  have hcellN : ∀ c ∈ ca.take n, c < s.N := fun c hc => hN c (List.mem_of_mem_take hc)
  have href : ArgRef argA' s.N := by
    rw [← hA]
    refine h.store.argRef.copy (fun i hi => ?_)
    have h' := hcells i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at h'
    show s.fs[s.fs.size - 1 - i]! >>> 4 < s.N
    rw [← h']; exact hN _ (List.getElem_mem _)
  generalize ht : spanTerm s.P argA' oc s.x s.argA.size n = t
  have hshr : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  rw [hshr]
  -- the store: the copy, the busy cell, the record
  have hs1 := h.store.withValArg (Pre.refl _) h.store.valSz hpre href
  have hclosed : t.looseBVarsBounded 0 = true := by
    rw [← ht]; unfold spanTerm
    refine (mkAppN_bounded _ _).mpr ⟨by unfold entryTerm; split <;> simp [infoTerm_closed, bot,
      Expr.looseBVarsBounded], fun a ha => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    rw [hsp] at hc
    exact h.store.closed c (hcellN c hc)
  have hs2 := hs1.alloc (s' := { s with
      cel := (((s.cel.push 1).push 0).push 0).push 0, argA := argA' }) (w0 := 1) (w1 := 0) (w2 := 0) (t := t) rfl rfl (Pre.refl _) h.store.valSz
    (Pre.refl _) h.store.evSz rfl rfl rfl (h.store.evRef.mono (Nat.le_succ _)) hclosed
    (by unfold CellOK; dsimp only [MS.N]; rw [(push4_spec s.cel 1 0 0 0 h.store.celSz).2.1]; trivial)
    (by omega)
  have hN1 : ({ s with cel := (((s.cel.push 1).push 0).push 0).push 0, argA := argA' } : MS).N =
      s.N + 1 := by
    simp only [MS.N]; rw [(push4_spec s.cel 1 0 0 0 h.store.celSz).1]; have := h.store.celSz; omega
  have hagree := Agree.ext oc s.N t
  have ht' : t = Expr.mkAppN (entryTerm s.P s.x) ((ca.take n).map oc) := by
    rw [← ht]; unfold spanTerm; rw [hsp]
  have hspan' : spanTerm s.P argA' (ocExt oc s.N t) s.x s.argA.size n = t := by
    have e := map_agree hagree hcellN
    unfold spanTerm; rw [hsp, ← e]; exact ht'.symm
  have hs3 := hs2.pushMemo (k := s.x) (start := s.argA.size) (len := n) (c := s.N)
    (by rw [hN1]; omega) hk (by show _ ≤ argA'.size; rw [hsz]; exact Nat.le_refl _)
    (by show ocExt oc s.N t s.N = _; rw [ocExt_self]; exact hspan'.symm) mH'
  refine ⟨(ca.drop n).map Fr.arg ++ fl', hs3.same rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
  · refine FS.pushUpd ?_ s.N
    rw [g4PopN_size]; exact FS.popN _ (Nat.le_refl _) hfs
  · intro f hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · show s.N < s.N + 1; omega
    · exact (h.frames f (by rw [hsplit]; exact List.mem_append_right _ hf')).grow (ExtR.refl _) hpre
        (Nat.le_succ _)
  · rw [hspan']
    refine ⟨by rw [ocExt_self]; exact .refl, ?_⟩
    rw [ocExt_self]
    have := K.move h.store.argRef hagree (ExtR.refl _) hpre
      (fun f hf => h.frames f (by rw [hsplit]; exact List.mem_append_right _ hf)) hK
    rw [← ht'] at this; exact this

/-- **A recursor redex, not in the memo**: `memo_core` on its `mI + 1`
arguments, and the ι frame. -/
theorem rec_core (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {mI : Nat}
    (htag : s.P.kTag[s.x]? = some 2) (hmI : s.P.kArity[s.x]? = some mI)
    (hle : mI + 1 ≤ g4CountArgs s.fs s.fs.size 0) (mH' : Array Nat) :
    ∃ fl', SInv env (ocExt oc s.N (spanTerm s.P (g4CopyArgs s.fs s.argA (mI + 1) 0) oc s.x
        s.argA.size (mI + 1))) { s with
      cel := (((s.cel.push 1).push 0).push 0).push 0,
      fs := (((((g4PopN s.fs (mI + 1)).push (g4Tag (s.cel.size >>> 2) 2)).push s.x).push
        s.argA.size).push (mI + 1)).push 3,
      argA := g4CopyArgs s.fs s.argA (mI + 1) 0,
      mem := (((s.mem.push s.x).push s.argA.size).push (mI + 1)).push (s.cel.size >>> 2),
      mH := mH' } ∧
    FS ((((((g4PopN s.fs (mI + 1)).push (g4Tag (s.cel.size >>> 2) 2)).push s.x).push
        s.argA.size).push (mI + 1)).push 3)
      ((((((g4PopN s.fs (mI + 1)).push (g4Tag (s.cel.size >>> 2) 2)).push s.x).push
        s.argA.size).push (mI + 1)).push 3).size
      (.iota s.x s.argA.size (mI + 1) :: .upd s.N :: fl') ∧
    FlOK s.P (g4CopyArgs s.fs s.argA (mI + 1) 0) (((((s.cel.push 1).push 0).push 0).push 0).size / 4)
      (.iota s.x s.argA.size (mI + 1) :: .upd s.N :: fl') ∧
    K env t₀ s.P (g4CopyArgs s.fs s.argA (mI + 1) 0)
      (ocExt oc s.N (spanTerm s.P (g4CopyArgs s.fs s.argA (mI + 1) 0) oc s.x s.argA.size (mI + 1)))
      (.upd s.N :: fl')
      (spanTerm s.P (g4CopyArgs s.fs s.argA (mI + 1) 0)
        (ocExt oc s.N (spanTerm s.P (g4CopyArgs s.fs s.argA (mI + 1) 0) oc s.x s.argA.size (mI + 1)))
        s.x s.argA.size (mI + 1)) := by
  obtain ⟨fl', hS, hFS, hFl, hK⟩ := memo_core h hm hle mH'
  have hk : s.x < s.P.kInfo.size := by
    have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
  obtain ⟨hsz, -, -⟩ := copyArgs_spec s.fs (mI + 1) 0 s.argA
  have hN1 : (((((s.cel.push 1).push 0).push 0).push 0).size / 4) = s.N + 1 := by
    rw [(push4_spec s.cel 1 0 0 0 h.store.celSz).1]; simp only [MS.N]; have := h.store.celSz; omega
  refine ⟨fl', hS.same rfl rfl rfl rfl rfl rfl rfl, FS.pushIota hFS _ _ _, ?_, hK⟩
  rw [hN1]
  refine FlOK.cons.mpr ⟨?_, hFl⟩
  unfold FrOK
  exact ⟨hk, by omega, by rw [hsz]; exact Nat.le_refl _, htag, by simpa using hmI⟩

/-- **A recursor redex, not in the memo, without the K step**: its major is
entered under the ι frame. -/
theorem step_rec_miss (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {mI : Nat}
    (htag : s.P.kTag[s.x]? = some 2) (hmI : s.P.kArity[s.x]? = some mI)
    (hle : mI + 1 ≤ g4CountArgs s.fs s.fs.size 0) (mH' : Array Nat) :
    ∃ oc' fl', MInv env t₀ oc' { s with
      cel := (((s.cel.push 1).push 0).push 0).push 0,
      fs := (((((g4PopN s.fs (mI + 1)).push (g4Tag (s.cel.size >>> 2) 2)).push s.x).push
        s.argA.size).push (mI + 1)).push 3,
      argA := g4CopyArgs s.fs s.argA (mI + 1) 0,
      mem := (((s.mem.push s.x).push s.argA.size).push (mI + 1)).push (s.cel.size >>> 2),
      mH := mH', mode := 2, pc := 0, env := 0,
      x := (g4CopyArgs s.fs s.argA (mI + 1) 0)[s.argA.size + mI]! } fl' := by
  obtain ⟨fl', hS, hFS, hFl, hK⟩ := rec_core h hm htag hmI hle mH'
  obtain ⟨hsz, -, -⟩ := copyArgs_spec s.fs (mI + 1) 0 s.argA
  refine ⟨_, _, hS.same rfl rfl rfl rfl rfl rfl rfl, hFS, hFl, ?_⟩
  refine ⟨hS.argRef _ (by show _ < (g4CopyArgs s.fs s.argA (mI + 1) 0).size; rw [hsz]; omega),
    .inl ?_, hK⟩
  rw [show s.argA.size + (mI + 1) - 1 = s.argA.size + mI by omega]; exact .refl

/-- **The K step** (`kE ≥ 4`, `Red.iotaK`): the rule's constructor on the
recursor's leading arguments is returned to the ι frame; the major is never
read. -/
theorem step_rec_K (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {mI : Nat}
    (htag : s.P.kTag[s.x]? = some 2) (hmI : s.P.kArity[s.x]? = some mI)
    (hle : mI + 1 ≤ g4CountArgs s.fs s.fs.size 0) (h4 : 4 ≤ s.P.kE[s.x]!) (mH' : Array Nat) :
    ∃ oc' fl', MInv env t₀ oc' { s with
      cel := (((s.cel.push 1).push 0).push 0).push 0,
      val := (((s.val.push 1).push (s.P.kE[s.x]! / 4 - 1)).push s.argA.size).push
        s.P.kArity[s.P.kE[s.x]! / 4 - 1]!,
      fs := (((((g4PopN s.fs (mI + 1)).push (g4Tag (s.cel.size >>> 2) 2)).push s.x).push
        s.argA.size).push (mI + 1)).push 3,
      argA := g4CopyArgs s.fs s.argA (mI + 1) 0,
      mem := (((s.mem.push s.x).push s.argA.size).push (mI + 1)).push (s.cel.size >>> 2),
      mH := mH', mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  have hk : s.x < s.P.kInfo.size := by
    have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
  obtain ⟨c, lps, us, mI₀, rP, base, nr, isK, isEta, hinfo, hrec⟩ :=
    (h.store.prog.ents s.x hk).tag2 hk htag
  obtain ⟨hkc, a, ha, hale⟩ := RecOK.kstep hrec h4
  obtain ⟨-, -, -, -, -, -, -, hmI', -⟩ := hrec
  rw [hmI] at hmI'; obtain rfl := Option.some.inj hmI'
  obtain ⟨fl', hS, hFS, hFl, hK⟩ := rec_core h hm htag hmI hle mH'
  obtain ⟨hsz, -, -⟩ := copyArgs_spec s.fs (mI + 1) 0 s.argA
  generalize s.P.kE[s.x]! / 4 - 1 = kc at hkc ha ⊢
  obtain ⟨vsz, v0, v1, v2, vpre⟩ := push4_spec s.val 1 kc s.argA.size s.P.kArity[kc]! h.store.valSz
  have v3 := push4_get3 s.val 1 kc s.argA.size s.P.kArity[kc]! h.store.valSz
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  have hS' := hS.withVal vpre (by rw [vsz]; have := h.store.valSz; omega)
  refine ⟨_, _, hS'.same rfl rfl rfl rfl rfl rfl rfl, hFS, hFl, ?_⟩
  show _ < _ ∧ ∃ t, ValDen s.P _ s.ev _ _ _ t ∧ _
  rw [hshr, vsz]
  refine ⟨show s.val.size / 4 < (s.val.size + 4) / 4 by omega, _,
    .ctor v0 (by rw [v1]; exact hkc) (by rw [v2, v3, get!_of_some ha, hsz]; omega), .inr h4, hK⟩

/-- **An accelerated operation on two arguments**: the literal frame is
pushed and the first argument entered (a stutter). -/
theorem step_natop_push (h : MInv env t₀ oc s fl) (hm : s.mode = 3)
    (h3 : s.P.kTag[s.x]! = 3) (h2 : g4CountArgs s.fs s.fs.size 0 = 2) :
    ∃ fl', MInv env t₀ oc { s with
      fs := ((((g4PopN s.fs 2).push s.x).push (g4ArgAt s.fs 0)).push (g4ArgAt s.fs 1)).push 5,
      mode := 2, pc := 0, env := 0, x := g4ArgAt s.fs 0 } fl' := by
  obtain ⟨ca, fl', rfl, hca, hk, hK, -, hfs, hcells, hN⟩ := h.topArgs hm
  rw [h2] at hca
  match ca, hca, hK, hcells, hN, hfs with
  | [a, b], _, hK, hcells, hN, hfs =>
    have ha : g4ArgAt s.fs 0 = a := (hcells 0 (by simp)).symm
    have hb : g4ArgAt s.fs 1 = b := (hcells 1 (by simp)).symm
    rw [ha, hb]
    refine ⟨.natA s.x a b :: fl', h.store.same rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
    · refine FS.pushNatA ?_ _ _ _
      rw [g4PopN_size]; exact FS.popN _ (Nat.le_refl _) hfs
    · intro f hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · show FrOK s.P s.argA s.N (.natA s.x a b)
        unfold FrOK
        exact ⟨hk, hN a (by simp), hN b (by simp),
          by rw [some_of_lt (by rw [h.store.prog.sizes]; exact hk), h3]⟩
      · exact h.frames f (List.mem_append_right _ hf')
    · exact ⟨hN a (by simp), .refl, hK⟩

/-- **The δ rule at a compiled definition entry**: the entry's constant on
any arguments reduces, up to erasure, to the compiled body on them; the body
is closed, since the stored value is (`EnvWF`). -/
theorem delta_red (hwf : EnvWF env) {P : G4Prog} (hI : Inv env.find? env.findProj? P) {k : Nat}
    (hk : k < P.kInfo.size) (ht : P.kTag[k]? = some 0 ∨ P.kTag[k]? = some 3) (hc : P.kCode[k]! ≠ 0) :
    ∃ sb, Den P (P.kCode[k]! - 1) sb ∧ sb.looseBVarsBounded 0 = true ∧
      ∀ args : List Expr, ERed env (Expr.mkAppN (entryTerm P k) args) (Expr.mkAppN sb args) := by
  obtain ⟨c, lps, us, v, hinfo, ⟨cv, hh, hfind, rfl⟩, hlen, -, w, hw, hcode⟩ :=
    (hI.ents k hk).tag03 hk ht
  rcases hcode with rfl | ⟨o, sb, rfl, hd, ha⟩
  · rw [get!_of_some hw] at hc; exact absurd rfl hc
  rw [get!_of_some hw, Nat.add_sub_cancel]
  have hvc : v.looseBVarsBounded 0 = true :=
    ((hwf.consts _ (Env.find?_mem hfind)).2.2.2.2.1 cv v hh rfl).2.2.2
  have hsc : sb.looseBVarsBounded 0 = true :=
    Approx.bounded ha (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hvc)
  refine ⟨sb, hd, hsc, fun args => ?_⟩
  have he : entryTerm P k = .const c us := by unfold entryTerm; rw [hinfo]; rfl
  rw [he]
  have hδ : ERed env (Expr.mkAppN (.const c us) args)
      (Expr.mkAppN (v.instantiateLevelParams cv.levelParams us) args) := by
    refine .delta ?_
    unfold unfoldDefinition
    rw [Expr.getAppFn_mkAppN]
    simp only [Expr.getAppFn, hfind, Expr.getAppArgs_mkAppN]
    rw [ite_eq_left hlen]
    simp [Expr.getAppArgs]
  exact .forget hδ (Approx.mkAppN ha (Approx.Args.refl _))

/-- **δ**: a definition entry with its body compiled; the body is evaluated
under the empty environment, the argument frames left in place (`delta`,
then `forget` to the compiled body). -/
theorem step_delta_body (hwf : EnvWF env) (h : MInv env t₀ oc s fl) (hm : s.mode = 3)
    (ht : s.P.kTag[s.x]? = some 0 ∨ s.P.kTag[s.x]? = some 3) (hc : s.P.kCode[s.x]! ≠ 0) :
    MInv env t₀ oc { s with mode := 0, pc := s.P.kCode[s.x]! - 1, env := 0, x := 0 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hk, hK⟩ := hf
  obtain ⟨sb, hd, hsc, hred⟩ := delta_red hwf h.store.prog hk ht hc
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  show ∃ u, NodeTerm s.P s.ev oc _ 0 u ∧ K env t₀ s.P s.argA oc fl u
  refine ⟨sb, ⟨sb, [], hd, .nil, by simpa using hsc, by rw [Expr.instantiateList_eq_self hsc]⟩, ?_⟩
  obtain ⟨ca, fl', rfl, -⟩ := FS.countArgs h.stack 0
  rw [K.args] at hK ⊢
  exact hK.step env t₀ s.P s.argA oc fl' (hred _)

/-- **The δ compile**: a definition entry without its body compiles the
stored value at the entry's levels, stores the node, and dispatches again
(a stutter; the program grows up to the code column). -/
theorem step_delta_compile (h : MInv env t₀ oc s fl) (hm : s.mode = 3) {c : Name} {lps : List Name}
    {us : List Level} {v : Expr} (hi : s.P.kInfo[s.x]! = .defn c lps us v) :
    MInv env t₀ oc { s with P :=
      { (g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us)).2 with
        kCode := (g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us)).2.kCode.set!
          s.x ((g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us)).1 + 1) } }
      fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hk, hK⟩ := hf
  have hi' : s.P.kInfo[s.x]? = some (.defn c lps us v) := by
    rw [Array.getElem?_eq_getElem hk, ← hi, getElem!_pos s.P.kInfo s.x hk]
  have hcomp :=
    (g4Comp_spec env.find? env.findProj? g4CompFuel).1 s.P (v.instantiateLevelParams lps us) h.store.prog
  generalize g4Comp env.find? env.findProj? g4CompFuel s.P (v.instantiateLevelParams lps us) = r at hcomp ⊢
  obtain ⟨o, P1⟩ := r
  obtain ⟨hI1, hx1, sb, hd, ha⟩ := hcomp
  dsimp only at hI1 hx1 hd ⊢
  have hI2 := hI1.setKCode (hx1.kInfo_some hi') hd ha
  have hx : ExtR s.P { P1 with kCode := P1.kCode.set! s.x (o + 1) } :=
    hx1.toExtR.trans (ExtR.codes P1 _ P1.ruleCode)
  refine ⟨h.store.grow (s' := { s with P := _ }) hI2 hx hx.epBase (Pre.refl _) h.store.celSz (Pre.refl _)
    h.store.valSz (Pre.refl _) h.store.evSz (Pre.refl _) rfl rfl (Agree.refl _ _) h.store.evRef
    h.store.argRef (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega)), h.stack,
    h.frames.grow hx (Pre.refl _) (Nat.le_refl _), ?_⟩
  simp only [Focus, hm]
  rw [entryTerm_ext hx hk]
  exact ⟨Nat.lt_of_lt_of_le hk hx.kInfoSize, K.grow env t₀ oc hx (Pre.refl _) fl h.frames hK⟩

/-- Argument frames for a span of cells, the first on top. -/
theorem FS.pushArgs (argA : Array Nat) (start : Nat) : ∀ (len : Nat) {fs : Array Nat} {fl : List Fr},
    FS fs fs.size fl →
    FS (g4PushArgs argA start fs len) (g4PushArgs argA start fs len).size
      ((span argA start len).map Fr.arg ++ fl)
  | 0, _, _, h => by simpa [g4PushArgs, span] using h
  | len + 1, _, fl, h => by
    simp only [g4PushArgs]
    have := FS.pushArgs argA start len (FS.pushArg h argA[start + len]!)
    have e : span argA start (len + 1) = span argA start len ++ [argA[start + len]!] := by
      simp [span, List.range_succ]
    rw [e, List.map_append, List.append_assoc]; exact this

/-- **δ, recorded in the memo**: the arguments are copied, a busy cell
records the redex, its update frame and the arguments' frames are pushed, and
the compiled body is evaluated under them. -/
theorem step_delta_miss (hwf : EnvWF env) (h : MInv env t₀ oc s fl) (hm : s.mode = 3)
    (ht : s.P.kTag[s.x]? = some 0 ∨ s.P.kTag[s.x]? = some 3) (hc : s.P.kCode[s.x]! ≠ 0)
    (mH' : Array Nat) :
    ∃ oc' fl', MInv env t₀ oc' { s with
      cel := (((s.cel.push 1).push 0).push 0).push 0,
      fs := g4PushArgs (g4CopyArgs s.fs s.argA (g4CountArgs s.fs s.fs.size 0) 0) s.argA.size
        ((g4PopN s.fs (g4CountArgs s.fs s.fs.size 0)).push (g4Tag (s.cel.size >>> 2) 2))
        (g4CountArgs s.fs s.fs.size 0),
      argA := g4CopyArgs s.fs s.argA (g4CountArgs s.fs s.fs.size 0) 0,
      mem := (((s.mem.push s.x).push s.argA.size).push (g4CountArgs s.fs s.fs.size 0)).push
        (s.cel.size >>> 2),
      mH := mH', mode := 0, pc := s.P.kCode[s.x]! - 1, env := 0, x := 0 } fl' := by
  have hk : s.x < s.P.kInfo.size := by
    have hf := h.focus; simp only [Focus, hm] at hf; exact hf.1
  obtain ⟨sb, hd, hsc, hred⟩ := delta_red hwf h.store.prog hk ht hc
  generalize hna : g4CountArgs s.fs s.fs.size 0 = na
  obtain ⟨fl', hS, hFS, hFl, hK⟩ := memo_core h hm (Nat.le_of_eq hna.symm) mH'
  generalize hA : g4CopyArgs s.fs s.argA na 0 = argA' at hS hFl hK
  generalize ht' : spanTerm s.P argA' oc s.x s.argA.size na = t at hS hK
  have hN1 : (((((s.cel.push 1).push 0).push 0).push 0).size / 4) = s.N + 1 := by
    rw [(push4_spec s.cel 1 0 0 0 h.store.celSz).1]; simp only [MS.N]; have := h.store.celSz; omega
  have hsz : argA'.size = s.argA.size + na := by rw [← hA]; exact (copyArgs_spec s.fs na 0 s.argA).1
  refine ⟨_, (span argA' s.argA.size na).map Fr.arg ++ .upd s.N :: fl',
    hS.same rfl rfl rfl rfl rfl rfl rfl, FS.pushArgs argA' s.argA.size na hFS, ?_, ?_⟩
  · intro f hf'
    rcases List.mem_append.mp hf' with hf' | hf'
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hf'
      show c < MS.N _
      simp only [MS.N]; rw [hN1]
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc'
      have := hS.argRef (s.argA.size + j) (by
        show s.argA.size + j < argA'.size; rw [List.mem_range] at hj; omega)
      have hcs := h.store.celSz
      simp only [MS.N, Array.size_push] at this ⊢
      omega
    · show FrOK s.P argA' (MS.N _) f
      simp only [MS.N]; rw [hN1]; exact hFl f hf'
  · show ∃ u, NodeTerm s.P s.ev _ _ 0 u ∧ K env t₀ s.P argA' _ _ u
    refine ⟨sb, ⟨sb, [], hd, .nil, by simpa using hsc, by rw [Expr.instantiateList_eq_self hsc]⟩, ?_⟩
    rw [K.args]
    unfold spanTerm at hK
    exact hK.step env t₀ s.P argA' _ _ (hred _)

end

end ConLeche.Verify.Ground
