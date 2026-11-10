module

public import ConLeche.Verify.Ground.Run
import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step3

public section

/-!
# Mode 1: returning a value to a frame (task #423 soundness, layer (c))

The value in focus meets the top frame.  At an argument frame a closure
re-focuses on its λ node (mode 0's known call then binds), a partial
application pushes its arguments back and dispatches its entry again, and
any other value pops the argument frames and becomes the neutral (`forget`).
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-- A closure value is a λ node under its environment. -/
theorem ValDen.inv0 {P : G4Prog} {val ev argA : Array Nat} {oc : Nat → Expr} {v : Nat} {t : Expr}
    (h : ValDen P val ev argA oc v t) (h0 : val[4 * v]! = 0) :
    P.code[val[4 * v + 1]!]! = 2 ∧ NodeTerm P ev oc val[4 * v + 1]! val[4 * v + 2]! t := by
  cases h with
  | closure _ h2 hn => exact ⟨h2, hn⟩
  | other h5 => omega
  | _ => simp_all

/-- A partial application is its entry on its span. -/
theorem ValDen.inv4 {P : G4Prog} {val ev argA : Array Nat} {oc : Nat → Expr} {v : Nat} {t : Expr}
    (h : ValDen P val ev argA oc v t) (h4 : val[4 * v]! = 4) :
    val[4 * v + 1]! < P.kInfo.size ∧ val[4 * v + 2]! + val[4 * v + 3]! ≤ argA.size ∧
      t = Expr.mkAppN (entryTerm P val[4 * v + 1]!) ((span argA val[4 * v + 2]! val[4 * v + 3]!).map oc) := by
  cases h with
  | pap _ hk hs => exact ⟨hk, hs, rfl⟩
  | other h5 => omega
  | _ => simp_all

/-- A constructor value is its entry on its span. -/
theorem ValDen.inv1 {P : G4Prog} {val ev argA : Array Nat} {oc : Nat → Expr} {v : Nat} {t : Expr}
    (h : ValDen P val ev argA oc v t) (h1 : val[4 * v]! = 1) :
    val[4 * v + 1]! < P.kInfo.size ∧ val[4 * v + 2]! + val[4 * v + 3]! ≤ argA.size ∧
      t = Expr.mkAppN (entryTerm P val[4 * v + 1]!) ((span argA val[4 * v + 2]! val[4 * v + 3]!).map oc) := by
  cases h with
  | ctor _ hk hs => exact ⟨hk, hs, rfl⟩
  | other h5 => omega
  | _ => simp_all

/-- `g4CopyFrom` appends a span of the array to it. -/
theorem copyFrom_spec (start : Nat) : ∀ (n j : Nat) (argA : Array Nat), start + j + n ≤ argA.size →
    (g4CopyFrom argA start n j).size = argA.size + n ∧ Pre argA (g4CopyFrom argA start n j) ∧
      ∀ i, i < n → (g4CopyFrom argA start n j)[argA.size + i]! = argA[start + j + i]!
  | 0, _, argA, _ => ⟨rfl, Pre.refl argA, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, j, argA, hle => by
    obtain ⟨h₁, h₂, h₃⟩ := copyFrom_spec start n (j + 1) (argA.push argA[start + j]!)
      (by simp only [Array.size_push]; omega)
    refine ⟨by simp only [g4CopyFrom, h₁, Array.size_push]; omega, (Pre.push _ _).trans h₂, ?_⟩
    intro i hi
    simp only [g4CopyFrom]
    rcases i with _ | i
    · show (g4CopyFrom (argA.push argA[start + j]!) start n (j + 1))[argA.size]! = argA[start + j]!
      rw [h₂.2 argA.size (by simp), getElem!_push_eq']
    · have := h₃ i (by omega)
      rw [Array.size_push] at this
      rw [show argA.size + (i + 1) = argA.size + 1 + i by omega, this,
        getElem!_push_lt' (by omega), show start + (j + 1) + i = start + j + (i + 1) by omega]

theorem span_append (a : Array Nat) (start m n : Nat) :
    span a start (m + n) = span a start m ++ span a (start + m) n := by
  unfold span
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Nat.add_assoc]

theorem span_pre' {a b : Array Nat} (hp : Pre a b) {start len : Nat} (h : start + len ≤ a.size) :
    span b start len = span a start len := by
  unfold span
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact hp.2 _ (by omega)

theorem FS.top_iota {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 3) :
    ∃ k start len fl', fl = .iota k start len :: fl' ∧ 4 ≤ fs.size ∧ FS fs (fs.size - 4) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | iota _ h' => exact ⟨_, _, _, _, rfl, by omega, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

theorem FS.top_proj {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 4) :
    ∃ pi fl', fl = .proj pi :: fl' ∧ 2 ≤ fs.size ∧ FS fs (fs.size - 2) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | proj _ h' => exact ⟨_, _, rfl, by omega, by simpa using h'⟩
  | arg h₀ _ | upd h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | iota h₀ _ | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht
                             rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- The neutral value under frames `fl'` whose claim holds of some term. -/
theorem MInv.neutral (h : MInv env t₀ oc s fl) {fs : Array Nat} {fl' : List Fr}
    (hfs : FS fs fs.size fl') (hfl : ∀ f ∈ fl', f ∈ fl) {u : Expr} (hK : K env t₀ s.P s.argA oc fl' u) :
    MInv env t₀ oc { s with fs := fs, mode := 1, pc := 0, env := 0, x := 0 } fl' := by
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, hfs, fun f hf => h.frames f (hfl f hf), ?_⟩
  show 0 < s.val.size / 4 ∧ ∃ t, ValDen s.P s.val s.ev s.argA oc 0 t ∧ _
  have h0 := h.store.val0
  refine ⟨by omega, bot, .other (by simp only [Nat.mul_zero]; omega), ?_⟩
  exact K.step env t₀ s.P s.argA oc fl' hK (.forget .refl (.bot _))

/-- The value in focus. -/
theorem MInv.val1 (h : MInv env t₀ oc s fl) (hm : s.mode = 1) :
    s.x < s.val.size / 4 ∧ ∃ t, ValDen s.P s.val s.ev s.argA oc s.x t ∧ K env t₀ s.P s.argA oc fl t := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  exact hf

/-- **A closure at an argument frame**: the focus moves to its λ node under
its environment (a stutter; mode 0's known call, `step_lam_call`, binds). -/
theorem step_arg_enter (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (h0 : s.val[g4X4 s.x]! = 0) :
    MInv env t₀ oc { s with mode := 0, pc := s.val[g4X4 s.x + 1]!, env := s.val[g4X4 s.x + 2]!, x := 0 } fl ∧
      s.P.code[s.val[g4X4 s.x + 1]!]! = 2 := by
  rw [g4X4_eq] at h0 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨h2, hn⟩ := hv.inv0 h0
  exact ⟨⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ⟨t, hn, hK⟩⟩, h2⟩

/-- **A partial application at an argument frame**: its arguments are pushed
back as frames and its entry is dispatched again (a stutter). -/
theorem step_arg_pap (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (h4 : s.val[g4X4 s.x]! = 4) :
    ∃ fl', MInv env t₀ oc { s with
      fs := g4PushArgs s.argA s.val[g4X4 s.x + 2]! s.fs s.val[g4X4 s.x + 3]!,
      mode := 3, pc := 0, env := 0, x := s.val[g4X4 s.x + 1]! } fl' := by
  rw [g4X4_eq] at h4 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨hk, hs, rfl⟩ := hv.inv4 h4
  refine ⟨_, h.store.same rfl rfl rfl rfl rfl rfl rfl, FS.pushArgs _ _ _ h.stack, ?_, ?_⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hf
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      rw [List.mem_range] at hj
      exact h.store.argRef _ (by omega)
    · exact h.frames f hf
  · show _ < _ ∧ K env t₀ s.P s.argA oc _ (entryTerm s.P _)
    exact ⟨hk, (K.args env t₀ s.P s.argA oc _ _ _).mpr hK⟩

/-- **Any other value at argument frames** (a neutral, a literal; the
engine's catch-all): the frames are popped and the focus is the neutral
(`forget`). -/
theorem step_arg_pop (h : MInv env t₀ oc s fl) (hm : s.mode = 1) :
    ∃ fl', MInv env t₀ oc { s with
      fs := g4PopN s.fs (g4CountArgs s.fs s.fs.size 0), mode := 1, pc := 0, env := 0, x := 0 } fl' := by
  obtain ⟨-, t, -, hK⟩ := h.val1 hm
  obtain ⟨ca, fl', rfl, hca⟩ := FS.countArgs h.stack 0
  rw [Nat.zero_add] at hca
  obtain ⟨-, hfs, -⟩ := FS.argsTop ca.length h.stack rfl
  rw [K.args] at hK
  rw [hca]
  refine ⟨fl', h.neutral ?_ (fun f hf => List.mem_append_right _ hf) hK⟩
  rw [g4PopN_size]; exact FS.popN _ (Nat.le_refl _) hfs

/-- **A constructor value at argument frames**: its span and the frames'
cells are copied into one new span, the frames popped (a stutter). -/
theorem step_arg_ctor (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (h1 : s.val[g4X4 s.x]! = 1) :
    ∃ fl', MInv env t₀ oc { s with
      val := (((s.val.push 1).push s.val[g4X4 s.x + 1]!).push s.argA.size).push
        (s.val[g4X4 s.x + 3]! + g4CountArgs s.fs s.fs.size 0),
      fs := g4PopN s.fs (g4CountArgs s.fs s.fs.size 0),
      argA := g4CopyArgs s.fs (g4CopyFrom s.argA s.val[g4X4 s.x + 2]! s.val[g4X4 s.x + 3]! 0)
        (g4CountArgs s.fs s.fs.size 0) 0,
      mode := 1, pc := 0, env := 0, x := s.val.size >>> 2 } fl' := by
  rw [g4X4_eq] at h1 ⊢
  obtain ⟨-, t, hv, hK⟩ := h.val1 hm
  obtain ⟨hk, hs, rfl⟩ := hv.inv1 h1
  generalize s.val[4 * s.x + 1]! = kc at hk hK ⊢
  generalize s.val[4 * s.x + 2]! = st at hs hK ⊢
  generalize s.val[4 * s.x + 3]! = len at hs hK ⊢
  obtain ⟨ca, fl', rfl, hca⟩ := FS.countArgs h.stack 0
  rw [Nat.zero_add] at hca
  rw [hca]
  obtain ⟨-, hfs, hcells⟩ := FS.argsTop ca.length h.stack rfl
  have hN : ∀ c ∈ ca, c < s.N := fun c hc => h.frames (.arg c) (List.mem_append_left _ (List.mem_map_of_mem hc))
  obtain ⟨z₁, p₁, g₁⟩ := copyFrom_spec st len 0 s.argA (by omega)
  generalize hA₁ : g4CopyFrom s.argA st len 0 = A₁ at z₁ p₁ g₁
  obtain ⟨z₂, p₂, -⟩ := copyArgs_spec s.fs ca.length 0 A₁
  have hsp₂ : span (g4CopyArgs s.fs A₁ ca.length 0) A₁.size ca.length = ca := by
    rw [copy_span_take (Nat.le_refl _) hcells, List.take_length]
  generalize hA₂ : g4CopyArgs s.fs A₁ ca.length 0 = A₂ at z₂ p₂ hsp₂
  have hsp₁ : span A₁ s.argA.size len = span s.argA st len := by
    unfold span; apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    rw [g₁ i hi, Nat.add_zero]
  have hspan : span A₂ s.argA.size (len + ca.length) = span s.argA st len ++ ca := by
    rw [span_append, span_pre' p₂ (by omega), hsp₁, ← z₁, hsp₂]
  have hpre : Pre s.argA A₂ := p₁.trans p₂
  have href : ArgRef A₂ s.N := by
    rw [← hA₂]
    refine ArgRef.copy (fun j hj => ?_) (fun i hi => ?_)
    · rcases Nat.lt_or_ge j s.argA.size with hj' | hj'
      · rw [p₁.2 j hj']; exact h.store.argRef j hj'
      · obtain ⟨i, rfl⟩ : ∃ i, j = s.argA.size + i := ⟨j - s.argA.size, by omega⟩
        rw [g₁ i (by omega)]; exact h.store.argRef _ (by omega)
    · have h' := hcells i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h'
      show s.fs[s.fs.size - 1 - i]! >>> 4 < s.N
      rw [← h']; exact hN _ (List.getElem_mem _)
  obtain ⟨hvsz, hv0, hv1, hv2, hvp⟩ := push4_spec s.val 1 kc s.argA.size (len + ca.length) h.store.valSz
  have hv3 : ((((s.val.push 1).push kc).push s.argA.size).push (len + ca.length))[4 * (s.val.size / 4) + 3]! =
      len + ca.length := by
    have := h.store.valSz
    rw [show 4 * (s.val.size / 4) + 3 = (((s.val.push 1).push kc).push s.argA.size).size by simp; omega,
      getElem!_push_eq']
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  rw [hshr]
  refine ⟨fl', (h.store.withValArg hvp (by rw [hvsz]; have := h.store.valSz; omega) hpre href).same
    rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
  · show FS (g4PopN s.fs ca.length) (g4PopN s.fs ca.length).size fl'
    rw [g4PopN_size]; exact FS.popN _ (Nat.le_refl _) hfs
  · exact fun f hf => (h.frames f (List.mem_append_right _ hf)).grow (ExtR.refl _) hpre (Nat.le_refl _)
  · show _ < _ ∧ ∃ t, ValDen s.P _ s.ev A₂ oc _ t ∧ K env t₀ s.P A₂ oc fl' t
    dsimp only
    refine ⟨by rw [hvsz]; have := h.store.valSz; omega, _, .ctor hv0 (by rw [hv1]; exact hk)
      (by rw [hv2, hv3, z₂, z₁]; omega), ?_⟩
    rw [hv1, hv2, hv3, hspan, ← K.args, List.map_append, List.append_assoc, K.args]
    refine K.grow env t₀ oc (ExtR.refl _) hpre _ (fun f hf => h.frames f hf) ?_
    rw [K.args] at hK ⊢; exact hK

/-- **A value the ι frame does not reduce on** (a neutral major at a
recursor that needs no rescue, any other value): the frame is popped and the
focus is the neutral (`forget`). -/
theorem step_iota_pop (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 3) :
    ∃ fl', MInv env t₀ oc { s with fs := g4PopN s.fs 4, mode := 1, pc := 0, env := 0, x := 0 } fl' := by
  obtain ⟨-, t, -, hK⟩ := h.val1 hm
  obtain ⟨k, start, len, fl', rfl, h4, hfs⟩ := FS.top_iota h.stack hn ht
  refine ⟨fl', h.neutral ?_ (fun f hf => List.mem_cons_of_mem _ hf) hK.2⟩
  rw [g4PopN_size]; exact FS.popN 4 (Nat.le_refl _) hfs

/-- **A value the projection frame does not reduce on** (no projection
table, any value other than a constructor or a string): the frame is popped
and the focus is the neutral (`forget`). -/
theorem step_proj_pop (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 4) :
    ∃ fl', MInv env t₀ oc { s with fs := s.fs.pop.pop, mode := 1, pc := 0, env := 0, x := 0 } fl' := by
  obtain ⟨-, t, -, hK⟩ := h.val1 hm
  obtain ⟨pi, fl', rfl, h2, hfs⟩ := FS.top_proj h.stack hn ht
  have hfs' : FS s.fs.pop.pop s.fs.pop.pop.size fl' := by
    show FS (g4PopN s.fs 2) (g4PopN s.fs 2).size fl'
    rw [g4PopN_size]; exact FS.popN 2 (Nat.le_refl _) hfs
  have hfl : ∀ f ∈ fl', f ∈ Fr.proj pi :: fl' := fun f hf => List.mem_cons_of_mem _ hf
  simp only [K] at hK
  cases pi with
  | zero => exact ⟨fl', h.neutral hfs' hfl hK⟩
  | succ q =>
    cases hq : s.P.projs[q]? with
    | none => simp only [hq] at hK; exact ⟨fl', h.neutral hfs' hfl hK⟩
    | some pj => simp only [hq] at hK; exact ⟨fl', h.neutral hfs' hfl hK⟩

end

end ConLeche.Verify.Ground
