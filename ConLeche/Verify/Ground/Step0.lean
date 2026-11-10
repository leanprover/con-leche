module

public import ConLeche.Verify.Ground.Run

public section

/-!
# Mode 0, the rest (task #423 soundness, layer (c))

λ (the known call, binding the top argument frames at once, and the
closure value), `let`, the literals, the projection and the shared slot.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-! ## Counting the top argument frames -/

theorem countArgs_ge (fs : Array Nat) : ∀ (t n : Nat), n ≤ g4CountArgs fs t n
  | 0, _ => Nat.le_refl _
  | t + 1, n => by
    simp only [g4CountArgs]
    split
    · exact Nat.le_trans (Nat.le_succ n) (countArgs_ge fs t (n + 1))
    · exact Nat.le_refl _

/-- `g4CountArgs` counts the parse's top argument frames. -/
theorem FS.countArgs {fs : Array Nat} : ∀ {t : Nat} {fl : List Fr}, FS fs t fl → ∀ n,
    ∃ (cs : List Nat) (fl' : List Fr), fl = cs.map Fr.arg ++ fl' ∧ g4CountArgs fs t n = n + cs.length
  | _, _, .nil, _ => ⟨[], [], rfl, rfl⟩
  | _, _, .arg h hr, n => by
    obtain ⟨cs, fl', rfl, hc⟩ := FS.countArgs hr (n + 1)
    refine ⟨_ :: cs, fl', rfl, ?_⟩
    simp only [g4CountArgs, h, beq_self_eq_true, ↓reduceIte, hc, List.length_cons]; omega
  | _, _, .upd h _, _ => ⟨[], _, rfl, by simp [g4CountArgs, h]⟩
  | _, _, .succ h _, _ => ⟨[], _, rfl, by simp [g4CountArgs, h]⟩
  | _, _, .iota h _, _ => ⟨[], _, rfl, by
      rw [show ∀ t, t + 4 = (t + 3) + 1 from fun _ => rfl]; simp [g4CountArgs, h]⟩
  | _, _, .natA h _, _ => ⟨[], _, rfl, by
      rw [show ∀ t, t + 4 = (t + 3) + 1 from fun _ => rfl]; simp [g4CountArgs, h]⟩
  | _, _, .natB h _, _ => ⟨[], _, rfl, by
      rw [show ∀ t, t + 5 = (t + 4) + 1 from fun _ => rfl]; simp [g4CountArgs, h]⟩
  | _, _, .proj h _, _ => ⟨[], _, rfl, by
      rw [show ∀ t, t + 2 = (t + 1) + 1 from fun _ => rfl]; simp [g4CountArgs, h]⟩

/-! ## Environments -/

theorem EnvL.le {ev : Array Nat} : ∀ {e : Nat} {cs : List Nat}, EnvL ev e cs → e ≤ ev.size / 2
  | _, _, .nil => Nat.zero_le _
  | _, _, .cons h _ _ => by omega

/-- Binding frames keeps the references when the frames' cells are allocated. -/
theorem bindFrames_ref (fs : Array Nat) {N : Nat} : ∀ (k j env : Nat) (ev : Array Nat),
    EvRef ev N → ev.size % 2 = 0 → env ≤ ev.size / 2 → (∀ i, i < k → frameCell fs (j + i) < N) →
    EvRef (g4BindFrames fs ev k j env) N
  | 0, _, _, _, hr, _, _, _ => hr
  | k + 1, j, env, ev, hr, h2, hle, hc => by
    simp only [g4BindFrames]
    have hshr : ev.size >>> 1 = ev.size / 2 := Nat.shiftRight_eq_div_pow _ _
    rw [hshr]
    have hsz : ((ev.push (fs[fs.size - 1 - j]! >>> 4)).push env).size = ev.size + 2 := by simp
    refine bindFrames_ref fs k (j + 1) _ _ (hr.push2 h2 (Nat.le_refl _) ?_ hle) (by rw [hsz]; omega)
      (by rw [hsz]; omega) (fun i hi => ?_)
    · have := hc 0 (by omega); simpa [frameCell] using this
    · have := hc (i + 1) (by omega); rwa [show j + (i + 1) = j + 1 + i by omega] at this

/-- **The store invariant with more environment records.** -/
theorem SInv.withEv {env : Env} {oc : Nat → Expr} {s : MS} (h : SInv env oc s) {ev' : Array Nat}
    (hp : Pre s.ev ev') (h2 : ev'.size % 2 = 0) (hr : EvRef ev' s.N) :
    SInv env oc { s with ev := ev' } :=
  h.grow (s' := { s with ev := ev' }) h.prog (ExtR.refl _) rfl (Pre.refl _) h.celSz (Pre.refl _)
    h.valSz hp h2 (Pre.refl _) rfl rfl (Agree.refl _ _) hr h.argRef
    (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega))

/-! ## Lists -/

theorem lams_bounded : ∀ (k : Nat) (b : Expr) (d : Nat),
    (lams k b).looseBVarsBounded d = b.looseBVarsBounded (d + k)
  | 0, _, _ => rfl
  | k + 1, b, d => by
    simp only [lams, Expr.looseBVarsBounded, bot, Bool.true_and]
    rw [lams_bounded k b (d + 1)]; congr 1; omega

theorem list_eq_range {l : List Nat} {f : Nat → Nat} (h : ∀ j, j < l.length → l.getD j 0 = f j) :
    l = (List.range l.length).map f := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  have := h j h₁
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some] at this
  simp [this]


/-! ## Allocation -/

/-- Four words appended. -/
theorem push4_spec (a : Array Nat) (w0 w1 w2 w3 : Nat) (h : a.size % 4 = 0) :
    ((((a.push w0).push w1).push w2).push w3).size = a.size + 4 ∧
    ((((a.push w0).push w1).push w2).push w3)[4 * (a.size / 4)]! = w0 ∧
    ((((a.push w0).push w1).push w2).push w3)[4 * (a.size / 4) + 1]! = w1 ∧
    ((((a.push w0).push w1).push w2).push w3)[4 * (a.size / 4) + 2]! = w2 ∧
    Pre a ((((a.push w0).push w1).push w2).push w3) := by
  have hi : 4 * (a.size / 4) = a.size := by omega
  rw [hi]
  refine ⟨by simp, ?_, ?_, ?_,
    (((Pre.push _ _).trans (Pre.push _ _)).trans (Pre.push _ _)).trans (Pre.push _ _)⟩
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_eq']
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show a.size + 1 = (a.push w0).size by simp, getElem!_push_eq']
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show a.size + 2 = ((a.push w0).push w1).size by simp, getElem!_push_eq']

/-- **One new cell** (`[w0, w1, w2, 0]` at the end) with a closed origin and
its invariant; the other arrays may have grown, the program, the spans, the
slots and the memo not. -/
theorem SInv.alloc {env : Env} {oc : Nat → Expr} {s s' : MS} (h : SInv env oc s) {w0 w1 w2 : Nat}
    {t : Expr} (hP : s'.P = s.P) (hcel : s'.cel = (((s.cel.push w0).push w1).push w2).push 0)
    (hval : Pre s.val s'.val) (hvs : s'.val.size % 4 = 0) (hev : Pre s.ev s'.ev)
    (hes : s'.ev.size % 2 = 0) (harg : s'.argA = s.argA) (hsl : s'.slots = s.slots)
    (hmem : s'.mem = s.mem) (hr : EvRef s'.ev (s.N + 1)) (htc : t.looseBVarsBounded 0 = true)
    (hok : CellOK env s.P s'.val s'.ev s.argA (ocExt oc s.N t) s'.cel s.N)
    (hv : 2 ≤ w0 → w0 - 2 < s'.val.size / 4) : SInv env (ocExt oc s.N t) s' := by
  obtain ⟨hsz, h0, -, -, hpre⟩ := push4_spec s.cel w0 w1 w2 0 h.celSz
  have hN : s'.N = s.N + 1 := by simp only [MS.N]; rw [hcel, hsz]; have := h.celSz; omega
  refine h.grow (by rw [hP]; exact h.prog) (by rw [hP]; exact ExtR.refl _) (by rw [hP])
    (by rw [hcel]; exact hpre) (by rw [hcel, hsz]; have := h.celSz; omega) hval hvs hev hes
    (by rw [harg]; exact Pre.refl _) hsl hmem (Agree.ext oc s.N t) (by rw [hN]; exact hr)
    (by rw [harg, hN]; exact h.argRef.mono (Nat.le_succ _)) (fun c h₁ h₂ => ?_)
  obtain rfl : c = s.N := by omega
  refine ⟨by rw [ocExt_self]; exact htc, by rw [hP, harg]; exact hok, ?_⟩
  rw [hcel, show 4 * s.N = 4 * (s.cel.size / 4) from rfl, h0]; exact hv

/-- The frames' claim under a grown store and an agreeing origin assignment. -/
theorem K.move {env : Env} {t₀ : Expr} {P P' : G4Prog} {argA argA' : Array Nat} {oc oc' : Nat → Expr}
    {N : Nat} {fl : List Fr} {u : Expr} (hg : ArgRef argA N) (ha : Agree oc oc' N) (hx : ExtR P P')
    (hp : Pre argA argA') (hf : FlOK P argA N fl) (hK : K env t₀ P argA oc fl u) :
    K env t₀ P' argA' oc' fl u :=
  K.grow env t₀ oc' hx hp fl hf (K.congr env t₀ P argA hg ha fl hf hK)

/-- The store invariant with more value words. -/
theorem SInv.withVal {env : Env} {oc : Nat → Expr} {s : MS} (h : SInv env oc s) {val' : Array Nat}
    (hp : Pre s.val val') (h4 : val'.size % 4 = 0) : SInv env oc { s with val := val' } :=
  h.grow (s' := { s with val := val' }) h.prog (ExtR.refl _) rfl (Pre.refl _) h.celSz hp h4
    (Pre.refl _) h.evSz (Pre.refl _) rfl rfl (Agree.refl _ _) h.evRef h.argRef
    (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega))

/-- The store invariant with other slots, each naming an allocated cell with
its owner's term. -/
theorem SInv.withSlots {env : Env} {oc : Nat → Expr} {s : MS} (h : SInv env oc s)
    {slots' : Array Nat} (hs : ∀ sl, g4SlotGet slots' s.P.epBase sl ≠ 0 →
      g4SlotGet slots' s.P.epBase sl < s.N ∧ Owns s.P sl (oc (g4SlotGet slots' s.P.epBase sl))) :
    SInv env oc { s with slots := slots' } :=
  ⟨h.prog, h.celSz, h.valSz, h.evSz, h.memSz, h.cell0, h.oc0, h.val0, h.closed, h.cells, h.valRef,
    h.evRef, h.argRef, hs, h.memo⟩

/-! ## Sharing slots -/

theorem growGo_get : ∀ (k : Nat) (a : Array Nat) (i : Nat),
    (g4Grow.g4GrowGo a k).size = a.size + k ∧
      (g4Grow.g4GrowGo a k)[i]! = if i < a.size then a[i]! else 0
  | 0, a, i => by
    simp only [g4Grow.g4GrowGo, Nat.add_zero, true_and]
    split
    · rfl
    · rename_i h; exact getElem!_neg a i h
  | k + 1, a, i => by
    simp only [g4Grow.g4GrowGo]
    obtain ⟨h₁, h₂⟩ := growGo_get k (a.push 0) i
    refine ⟨by rw [h₁]; simp; omega, ?_⟩
    rw [h₂]
    by_cases hi : i < a.size
    · rw [ite_eq_left (by simp; omega), ite_eq_left hi, getElem!_push_lt' hi]
    · rw [ite_eq_right hi]
      split
      · rename_i h'; rw [show i = a.size by simp at h'; omega, getElem!_push_eq']
      · rfl

theorem grow_get (a : Array Nat) (n i : Nat) :
    n ≤ (g4Grow a n).size ∧ (g4Grow a n)[i]! = if i < a.size then a[i]! else 0 := by
  unfold g4Grow
  split
  · obtain ⟨h₁, h₂⟩ := growGo_get (n - a.size) a i
    exact ⟨by omega, h₂⟩
  · refine ⟨by omega, ?_⟩
    split
    · rfl
    · rename_i h; exact getElem!_neg a i h

/-- **Reading a slot after setting one.** -/
theorem slotGet_set (slots : Array Nat) (ep sl w sl' : Nat) :
    g4SlotGet (g4SlotSet slots sl w) ep sl' =
      if sl' = sl then (if w > ep then w - ep else 0) else g4SlotGet slots ep sl' := by
  have key : ∀ (b : Array Nat), sl < b.size → (∀ i, i < slots.size → b[i]! = slots[i]!) →
      (∀ i, slots.size ≤ i → i < b.size → b[i]! = 0) → slots.size ≤ b.size →
      g4SlotGet (b.set! sl w) ep sl' =
        if sl' = sl then (if w > ep then w - ep else 0) else g4SlotGet slots ep sl' := by
    intro b hsl hlo hhi hsz
    have hs : (b.set! sl w).size = b.size := by simp
    by_cases he : sl' = sl
    · subst he
      simp only [g4SlotGet, hs, hsl, ↓reduceIte, set!_get_self hsl]
    · rw [ite_eq_right he]
      simp only [g4SlotGet, hs, set!_get_other he]
      by_cases h₁ : sl' < slots.size
      · simp only [Nat.lt_of_lt_of_le h₁ hsz, h₁, ↓reduceIte, hlo _ h₁]
      · simp only [h₁, ↓reduceIte]
        split
        · rename_i h₂; rw [hhi _ (by omega) h₂]; simp
        · rfl
  unfold g4SlotSet
  split
  · rename_i h; exact key slots h (fun _ _ => rfl) (fun i h₁ h₂ => absurd h₂ (by omega)) (Nat.le_refl _)
  · obtain ⟨h₁, -⟩ := grow_get slots (max (sl + 1) (2 * slots.size)) 0
    refine key _ (by omega) (fun i hi => ?_) (fun i h₂ _ => ?_) (by omega)
    · rw [(grow_get slots _ i).2, ite_eq_left hi]
    · rw [(grow_get slots _ i).2, ite_eq_right (by omega)]

/-- An approximation of a bounded term is bounded. -/
theorem Approx.bounded {s t : Expr} (h : Approx s t) : ∀ {d : Nat}, t.looseBVarsBounded d = true →
    s.looseBVarsBounded d = true := by
  induction h with
  | bot => intro _ _; rfl
  | bvar | fvar | sort | const | lit => intro _ h; exact h
  | app _ _ ih₁ ih₂ | lam _ _ ih₁ ih₂ | forallE _ _ ih₁ ih₂ =>
    intro _ h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢; exact ⟨ih₁ h.1, ih₂ h.2⟩
  | letE _ _ _ ih₁ ih₂ ih₃ =>
    intro _ h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨ih₁ h.1.1, ih₂ h.1.2⟩, ih₃ h.2⟩
  | proj _ ih => intro _ h; simp only [Expr.looseBVarsBounded] at h ⊢; exact ih h

/-- A registered shared node denotes a closed term. -/
theorem Inv.shared_closed {P : G4Prog} {find? : Name → Option ConstantInfo} {findProj? : Name → Nat → Option ProjEntry}
    (hI : Inv find? findProj? P) {a : Expr} {o : Nat} {s : Expr}
    (ho : P.closedNode[a]? = some o) (hd : Den P o s) : s.looseBVarsBounded 0 = true := by
  obtain ⟨s', -, -, hd', ha, hc⟩ := hI.closed a o ho
  rw [Den.unique hd hd']; exact ha.bounded hc

/-! ## Node inversions -/

theorem Den.inv3 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 3) :
    ∃ v b sv sb, P.code[o + 1]? = some v ∧ P.code[o + 2]? = some b ∧ Den P v sv ∧ Den P b sb ∧
      s = .letE bot sv sb := by
  cases h with
  | letE _ h₁ h₂ _ _ hv hb => exact ⟨_, _, _, _, h₁, h₂, hv, hb, rfl⟩
  | _ => simp_all

theorem Den.inv5 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 5) :
    ∃ n, P.code[o + 1]? = some n ∧ s = .lit (.natVal n) := by
  cases h with
  | natLit _ h₁ => exact ⟨_, h₁, rfl⟩
  | _ => simp_all

theorem Den.inv6 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 6) :
    ∃ si str, P.code[o + 1]? = some si ∧ P.strs[si]? = some str ∧ s = .lit (.strVal str) := by
  cases h with
  | strLit _ h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
  | _ => simp_all

theorem Den.inv7 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 7) :
    ∃ q pj e se, P.code[o + 1]? = some (q + 1) ∧ P.projs[q]? = some pj ∧ P.code[o + 2]? = some e ∧
      Den P e se ∧ s = .proj pj.sn pj.idx se := by
  cases h with
  | proj _ h₁ h₂ h₃ _ he => exact ⟨_, _, _, _, h₁, h₂, h₃, he, rfl⟩
  | _ => simp_all

theorem Den.inv9 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 9) :
    ∃ sl a, P.code[o + 1]? = some sl ∧ P.code[o + 2]? = some a ∧ Den P a s ∧
      ∃ a' : Expr, P.closedNode[a']? = some o := by
  cases h with
  | shared _ h₁ h₂ _ ha hc => exact ⟨_, _, h₁, h₂, ha, hc⟩
  | _ => simp_all

/-- A node's tag is one of `g4Comp`'s ten: the run loop's catch-all at mode 0
is the neutral node (tag `8`). -/
theorem Den.tag_le {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) : P.code[o]! ≤ 9 :=
  match h with
  | .bvar h₀ _ | .spine h₀ .. | .lam h₀ .. | .letE h₀ .. | .const h₀ .. | .natLit h₀ _
  | .strLit h₀ .. | .proj h₀ .. | .neutral h₀ | .shared h₀ .. => by rw [get!_of_some h₀]; decide

/-! ## Mode 0 -/

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- **The known call**: a λ with argument frames on top binds as many of
them as the telescope has, at once (`beta` × k). -/
theorem step_lam_call (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 2)
    (hn : 0 < s.fs.size) (htop : s.fs[s.fs.size - 1]! &&& 15 = 1) :
    ∃ fl', MInv env t₀ oc { s with
      ev := g4BindFrames s.fs s.ev
        (if g4CountArgs s.fs s.fs.size 0 < s.P.code[s.pc + 2]! then g4CountArgs s.fs s.fs.size 0
          else s.P.code[s.pc + 2]!) 0 s.env,
      fs := g4PopN s.fs
        (if g4CountArgs s.fs s.fs.size 0 < s.P.code[s.pc + 2]! then g4CountArgs s.fs s.fs.size 0
          else s.P.code[s.pc + 2]!),
      pc := if (if g4CountArgs s.fs s.fs.size 0 < s.P.code[s.pc + 2]! then
            g4CountArgs s.fs s.fs.size 0 else s.P.code[s.pc + 2]!) == s.P.code[s.pc + 2]!
          then s.P.code[s.pc + 3]!
          else g4LamWalk s.P.code
            (if g4CountArgs s.fs s.fs.size 0 < s.P.code[s.pc + 2]! then g4CountArgs s.fs s.fs.size 0
              else s.P.code[s.pc + 2]!) s.pc,
      env := (g4BindFrames s.fs s.ev
        (if g4CountArgs s.fs s.fs.size 0 < s.P.code[s.pc + 2]! then g4CountArgs s.fs s.fs.size 0
          else s.P.code[s.pc + 2]!) 0 s.env).size >>> 1,
      mode := 0, x := 0 } fl' := by
  generalize hna : g4CountArgs s.fs s.fs.size 0 = na
  generalize htn : s.P.code[s.pc + 2]! = tn
  generalize hk : (if na < tn then na else tn) = k
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  have h2 : s.P.code[s.pc]? = some 2 := by rw [some_of_lt hd.lt_size, ht]
  have htn' : s.P.code[s.pc + 2]? = some tn := by
    obtain ⟨_, _, _, _, -, h', -⟩ := hd.lam_inv h2; rw [h', ← htn, get!_of_some h']
  have htn1 : 1 ≤ tn := by
    obtain ⟨_, tn'', _, _, -, h', -, -, -, htel⟩ := hd.lam_inv h2
    rw [htn'] at h'; cases h'
    rcases htel with ⟨-, -, -, h⟩ | ⟨-, h, -⟩ <;> omega
  -- the top argument frames
  obtain ⟨ca, fl', rfl, hca⟩ := FS.countArgs h.stack 0
  rw [hna, Nat.zero_add] at hca
  have hna1 : 1 ≤ na := by
    obtain ⟨t, ht'⟩ : ∃ t, s.fs.size = t + 1 := ⟨s.fs.size - 1, by omega⟩
    have := countArgs_ge s.fs t 1
    rw [← hna, ht']; simp only [g4CountArgs]
    rw [show s.fs[t]! = s.fs[s.fs.size - 1]! by rw [ht']; rfl, htop]; simpa using this
  have hk1 : 1 ≤ k ∧ k ≤ na ∧ k ≤ tn := by rw [← hk]; split <;> omega
  -- the walk
  obtain ⟨sb, hdb, rfl, hin⟩ := Den.lamWalk k hd h2 htn' hk1.2.2
  have hbody : (if k == tn then s.P.code[s.pc + 3]! else g4LamWalk s.P.code k s.pc) =
      g4LamWalk s.P.code k s.pc := by
    split
    · rename_i hkt; rw [get!_of_some (hin (by simpa using hkt))]
    · rfl
  rw [hbody]
  -- split the frames
  have hsplit : ca.map Fr.arg ++ fl' = (ca.take k).map Fr.arg ++ ((ca.drop k).map Fr.arg ++ fl') := by
    rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
  have htl : (ca.take k).length = k := by rw [List.length_take]; omega
  rw [hsplit] at hK
  obtain ⟨hkle, hfs, hcells⟩ := FS.argsTop k (hsplit ▸ h.stack) htl
  have hnew : (List.range k).reverse.map (fun i => frameCell s.fs (0 + i)) = (ca.take k).reverse := by
    have hl := list_eq_range (l := ca.take k) (f := fun i => frameCell s.fs (0 + i)) (fun j hj => by
      rw [hcells j (by omega)]; simp [frameCell])
    rw [htl] at hl
    rw [hl, List.map_reverse]
  obtain ⟨hpre, hsz, hel⟩ := bindFrames_spec s.fs k 0 s.env s.ev cs h.store.evSz he.le he
  simp only [show k ≠ 0 by omega, ↓reduceIte] at hel
  rw [hnew] at hel
  have hN : ∀ c ∈ ca.take k, c < s.N := fun c hc =>
    h.frames (.arg c) (List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_mem_take hc)))
  have hshr : ∀ a : Array Nat, a.size >>> 1 = a.size / 2 := fun _ => Nat.shiftRight_eq_div_pow _ _
  refine ⟨(ca.drop k).map Fr.arg ++ fl', ⟨(h.store.withEv hpre (by rw [hsz]; have := h.store.evSz; omega)
    (bindFrames_ref s.fs k 0 s.env s.ev h.store.evRef h.store.evSz he.le (fun i hi => ?_))).same
      rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩⟩
  · show s.fs[s.fs.size - 1 - (0 + i)]! >>> 4 < s.N
    rw [Nat.zero_add, ← hcells i (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hN _ (List.getElem_mem _)
  · show FS (g4PopN s.fs k) (g4PopN s.fs k).size _
    rw [g4PopN_size]; exact FS.popN k (Nat.le_refl _) hfs
  · intro f hf'
    exact h.frames f (by rw [hsplit]; exact List.mem_append_right _ hf')
  · show ∃ u, NodeTerm s.P _ oc _ _ u ∧ _
    refine ⟨_, ⟨sb, _, hdb, by rw [hshr]; exact hel, ?_, rfl⟩, ?_⟩
    · rw [List.length_append, List.length_reverse, htl, Nat.add_comm]
      rw [← lams_bounded]; exact hb
    · rw [K.args] at hK
      have hβ := betaN_env env ((ca.take k).map oc) sb (cs.map oc)
      rw [List.length_map, htl] at hβ
      have := hK.step env t₀ s.P s.argA oc _ hβ
      rwa [← List.map_reverse, ← List.map_append] at this

/-- **A closure value**: a λ with no argument frame on top is a value. -/
theorem step_lam_value (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 2) :
    MInv env t₀ oc { s with
      val := (((s.val.push 0).push s.pc).push s.env).push 0
      mode := 1
      pc := 0
      env := 0
      x := s.val.size >>> 2 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, hu, hK⟩ := hf
  have hv4 := h.store.valSz
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  have hpre : Pre s.val ((((s.val.push 0).push s.pc).push s.env).push 0) :=
    (((Pre.push _ _).trans (Pre.push _ _)).trans (Pre.push _ _)).trans (Pre.push _ _)
  have hst : SInv env oc { s with val := (((s.val.push 0).push s.pc).push s.env).push 0 } :=
    h.store.grow (s' := { s with val := (((s.val.push 0).push s.pc).push s.env).push 0 }) h.store.prog
      (ExtR.refl _) rfl (Pre.refl _) h.store.celSz hpre (by simp; omega) (Pre.refl _) h.store.evSz
      (Pre.refl _) rfl rfl (Agree.refl _ _) h.store.evRef h.store.argRef
      (fun c h₁ h₂ => absurd h₂ (by simp only [MS.N] at h₁ ⊢; omega))
  have hi : 4 * (s.val.size / 4) = s.val.size := by omega
  refine ⟨hst.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  show _ < _ ∧ ∃ t, ValDen s.P _ s.ev s.argA oc _ t ∧ _
  rw [hshr]
  refine ⟨by simp; omega, u, .closure ?_ ?_ ?_, hK⟩
  · rw [hi, getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_eq']
  · rw [hi, getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show s.val.size + 1 = (s.val.push 0).size by simp, getElem!_push_eq']
    exact ht
  · rw [hi, getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show s.val.size + 1 = (s.val.push 0).size by simp, getElem!_push_eq', getElem!_push_lt' (by simp only [Array.size_push]; omega),
      show s.val.size + 2 = ((s.val.push 0).push s.pc).size by simp, getElem!_push_eq']
    exact hu

/-- **`let`**: the value becomes a thunk cell, the body is evaluated under it (`zeta`). -/
theorem step_let (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 3) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push 0).push s.P.code[s.pc + 1]!).push s.env).push 0
      ev := (s.ev.push (s.cel.size >>> 2)).push s.env
      mode := 0
      pc := s.P.code[s.pc + 2]!
      env := (s.ev.size >>> 1) + 1
      x := 0 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨v, b, sv, sb, h₁, h₂, hv, hdb, rfl⟩ := hd.inv3 (by rw [some_of_lt hd.lt_size, ht])
  simp only [Expr.looseBVarsBounded, bot, Bool.true_and, Bool.and_eq_true] at hb
  have hcl := h.store.allClosed he
  have htc : (sv.instantiateList (cs.map oc)).looseBVarsBounded 0 = true :=
    bounded _ sv 0 hcl (by simpa using hb.1)
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  have hshr1 : s.ev.size >>> 1 = s.ev.size / 2 := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2, hshr1, get!_of_some h₁, get!_of_some h₂]
  have hlt := EnvL.mem_lt h.store.evRef he
  have ha := Agree.ext oc s.N (sv.instantiateList (cs.map oc))
  have hmap : cs.map (ocExt oc s.N (sv.instantiateList (cs.map oc))) = cs.map oc :=
    (map_agree ha hlt).symm
  have hpre2 : Pre s.ev ((s.ev.push s.N).push s.env) := (Pre.push _ _).trans (Pre.push _ _)
  have hrec := EnvL.record h.store.evSz he.le he s.N
  obtain ⟨hcsz, hc0, hc1, hc2, -⟩ := push4_spec s.cel 0 v s.env 0 h.store.celSz
  refine ⟨ocExt oc s.N (sv.instantiateList (cs.map oc)), ⟨?_, h.stack, ?_, ?_⟩⟩
  · refine (h.store.alloc (s' := { s with
      cel := (((s.cel.push 0).push v).push s.env).push 0, ev := (s.ev.push s.N).push s.env })
      rfl rfl (Pre.refl _) h.store.valSz hpre2 (by simp; have := h.store.evSz; omega) rfl rfl rfl
      (h.store.evRef.push2 h.store.evSz (Nat.le_succ _) (Nat.lt_succ_self _) he.le) htc ?_
      (by omega)).same rfl rfl rfl rfl rfl rfl rfl
    show CellOK env s.P s.val _ s.argA _ _ (s.cel.size / 4)
    unfold CellOK; rw [hc0, hc1, hc2]
    exact ⟨sv, cs, hv, he.pre hpre2, hb.1, by rw [show s.cel.size / 4 = s.N from rfl, ocExt_self, hmap]⟩
  · exact FlOK.grow (ExtR.refl _) (Pre.refl _) (by simp only [MS.N]; rw [hcsz]; omega) h.frames
  · show ∃ u, NodeTerm s.P _ _ b _ u ∧ _
    refine ⟨_, ⟨sb, _, hdb, hrec, by simpa using hb.2, rfl⟩, ?_⟩
    have := hK.step env t₀ s.P s.argA oc fl (zeta_env env bot sv sb (cs.map oc))
    rw [List.map_cons, ocExt_self, hmap]
    exact K.move h.store.argRef ha (ExtR.refl _) (Pre.refl _) h.frames this

/-- **A `Nat` literal**: a literal value. -/
theorem step_natLit (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 5) :
    MInv env t₀ oc { s with
      val := (((s.val.push 2).push s.P.code[s.pc + 1]!).push 0).push 0
      mode := 1
      pc := 0
      env := 0
      x := s.val.size >>> 2 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨n, h₁, rfl⟩ := hd.inv5 (by rw [some_of_lt hd.lt_size, ht])
  rw [Expr.instantiateList_eq_self (by simp [Expr.looseBVarsBounded])] at hK
  obtain ⟨hsz, h0, h1, -, hpre⟩ := push4_spec s.val 2 s.P.code[s.pc + 1]! 0 0 h.store.valSz
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  refine ⟨(h.store.withVal hpre (by rw [hsz]; have := h.store.valSz; omega)).same rfl rfl rfl rfl rfl
    rfl rfl, h.stack, h.frames, ?_⟩
  show _ < _ ∧ ∃ t, ValDen s.P _ s.ev s.argA oc _ t ∧ _
  rw [hshr, hsz]
  refine ⟨by show s.val.size / 4 < _; omega, _, .natLit h0, ?_⟩
  rw [h1, get!_of_some h₁]; exact hK

/-- **A string literal**: a literal value. -/
theorem step_strLit (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 6) :
    MInv env t₀ oc { s with
      val := (((s.val.push 3).push s.P.code[s.pc + 1]!).push 0).push 0
      mode := 1
      pc := 0
      env := 0
      x := s.val.size >>> 2 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨si, str, h₁, h₂, rfl⟩ := hd.inv6 (by rw [some_of_lt hd.lt_size, ht])
  rw [Expr.instantiateList_eq_self (by simp [Expr.looseBVarsBounded])] at hK
  obtain ⟨hsz, h0, h1, -, hpre⟩ := push4_spec s.val 3 s.P.code[s.pc + 1]! 0 0 h.store.valSz
  have hshr : s.val.size >>> 2 = s.val.size / 4 := Nat.shiftRight_eq_div_pow _ _
  refine ⟨(h.store.withVal hpre (by rw [hsz]; have := h.store.valSz; omega)).same rfl rfl rfl rfl rfl
    rfl rfl, h.stack, h.frames, ?_⟩
  show _ < _ ∧ ∃ t, ValDen s.P _ s.ev s.argA oc _ t ∧ _
  rw [hshr, hsz]
  refine ⟨by show s.val.size / 4 < _; omega, _, .strLit h0 (by rw [h1, get!_of_some h₁]; exact h₂), hK⟩

/-- **A projection**: its frame is pushed and the structure evaluated
(`projArg`). -/
theorem step_proj (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 7) :
    MInv env t₀ oc { s with
      fs := (s.fs.push s.P.code[s.pc + 1]!).push 4
      mode := 0
      pc := s.P.code[s.pc + 2]!
      x := 0 } (.proj s.P.code[s.pc + 1]! :: fl) := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨q, pj, e, se, h₁, h₂, h₃, hde, rfl⟩ := hd.inv7 (by rw [some_of_lt hd.lt_size, ht])
  rw [get!_of_some h₁, get!_of_some h₃]
  have hq : q < s.P.projs.size := by
    rcases Nat.lt_or_ge q s.P.projs.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at h₂; cases h₂
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, ?_⟩
  · show FS ((s.fs.push (q + 1)).push 4) ((s.fs.push (q + 1)).push 4).size _
    have hst := FS.proj (fs := (s.fs.push (q + 1)).push 4) (t := s.fs.size) (fl := fl)
      (by rw [show s.fs.size + 1 = (s.fs.push (q + 1)).size by simp, getElem!_push_eq']; decide)
      (((h.stack).push _ (Nat.le_refl _)).push _ (by simp))
    rw [getElem!_push_lt' (by simp), getElem!_push_eq'] at hst
    simpa using hst
  · intro f hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · exact .inr (by simpa using hq)
    · exact h.frames f hf'
  · show ∃ u, NodeTerm s.P s.ev oc e s.env u ∧ _
    refine ⟨_, ⟨se, cs, hde, he, by simpa [Expr.looseBVarsBounded] using hb, rfl⟩, ?_⟩
    simp only [K, h₂]
    simpa [Expr.instantiateList] using hK

/-- **A shared node, its slot set**: enter the slot's cell (one closed term,
one origin). -/
theorem step_shared_hit (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 9)
    (hc : g4SlotGet s.slots s.P.epBase s.P.code[s.pc + 1]! ≠ 0) :
    MInv env t₀ oc { s with
      mode := 2, pc := 0, env := 0, x := g4SlotGet s.slots s.P.epBase s.P.code[s.pc + 1]! } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨sl, a, h₁, h₂, hda, a', hcn⟩ := hd.inv9 (by rw [some_of_lt hd.lt_size, ht])
  rw [get!_of_some h₁] at hc ⊢
  obtain ⟨hlt, how⟩ := h.store.slotsOK sl hc
  have heq := h.store.prog.owns_unique how (.inl ⟨a', s.pc, hcn, h₁, hd⟩)
  have hcl := h.store.prog.shared_closed hcn hd
  rw [Expr.instantiateList_eq_self hcl] at hK
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, hlt, ?_⟩
  show K env t₀ s.P s.argA oc fl (oc _)
  rw [heq]; exact hK

/-- **A shared node, its slot empty**: a thunk of the closed term under the
empty environment, registered in the slot, entered. -/
theorem step_shared_miss (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 9)
    (hc : g4SlotGet s.slots s.P.epBase s.P.code[s.pc + 1]! = 0) :
    ∃ oc', MInv env t₀ oc' { s with
      cel := (((s.cel.push 0).push s.P.code[s.pc + 2]!).push 0).push 0
      slots := g4SlotSet s.slots s.P.code[s.pc + 1]! (s.P.epBase + (s.cel.size >>> 2))
      mode := 2
      pc := 0
      env := 0
      x := s.cel.size >>> 2 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨sl, a, h₁, h₂, hda, a', hcn⟩ := hd.inv9 (by rw [some_of_lt hd.lt_size, ht])
  have hcl := h.store.prog.shared_closed hcn hd
  rw [Expr.instantiateList_eq_self hcl] at hK
  have hshr2 : s.cel.size >>> 2 = s.N := Nat.shiftRight_eq_div_pow _ _
  rw [hshr2, get!_of_some h₁, get!_of_some h₂]
  rw [get!_of_some h₁] at hc
  have ha := Agree.ext oc s.N s0
  obtain ⟨hcsz, hc0, hc1, hc2, -⟩ := push4_spec s.cel 0 a 0 0 h.store.celSz
  have hN : s.N + 1 = (s.cel.size + 4) / 4 := by simp only [MS.N]; have := h.store.celSz; omega
  have hst := h.store.alloc (s' := { s with cel := (((s.cel.push 0).push a).push 0).push 0 })
    rfl rfl (Pre.refl _) h.store.valSz (Pre.refl _) h.store.evSz rfl rfl rfl
    (h.store.evRef.mono (Nat.le_succ _)) hcl (by
      show CellOK env s.P s.val s.ev s.argA _ _ (s.cel.size / 4)
      unfold CellOK; rw [hc0, hc1, hc2]
      exact ⟨s0, [], hda, .nil, hcl, by
        rw [show s.cel.size / 4 = s.N from rfl, ocExt_self, List.map_nil, Expr.instantiateList_nil]⟩)
    (by omega)
  have hep : s.P.epBase + s.N > s.P.epBase := by have := h.store.cell0; omega
  refine ⟨ocExt oc s.N s0, ⟨(hst.withSlots (slots' := g4SlotSet s.slots sl (s.P.epBase + s.N))
    (fun sl' hne => ?_)).same rfl rfl rfl rfl rfl rfl rfl, h.stack, ?_, ?_⟩⟩
  · show _ < (((((s.cel.push 0).push a).push 0).push 0).size / 4) ∧ _
    rw [slotGet_set] at hne ⊢
    rw [hcsz, ← hN]
    by_cases he : sl' = sl
    · subst he
      rw [ite_eq_left rfl, ite_eq_left hep, Nat.add_sub_cancel_left, ocExt_self]
      exact ⟨Nat.lt_succ_self _, .inl ⟨a', s.pc, hcn, h₁, hd⟩⟩
    · rw [ite_eq_right he] at hne ⊢
      obtain ⟨hlt, how⟩ := h.store.slotsOK sl' hne
      rw [← ha _ hlt]
      exact ⟨Nat.lt_succ_of_lt hlt, how⟩
  · exact FlOK.grow (ExtR.refl _) (Pre.refl _) (by simp only [MS.N]; rw [hcsz]; omega) h.frames
  · show _ < (((((s.cel.push 0).push a).push 0).push 0).size / 4) ∧ _
    rw [hcsz, ← hN]
    refine ⟨Nat.lt_succ_self _, ?_⟩
    rw [ocExt_self]
    exact K.move h.store.argRef ha (ExtR.refl _) (Pre.refl _) h.frames hK

end

end ConLeche.Verify.Ground
