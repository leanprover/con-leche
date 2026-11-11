module

public import ConLeche.Verify.Ground.Refs

public section

/-!
# The ground machine's invariant and its transitions (task #423 soundness, layer (c))

`MS` bundles `g4Run`'s arguments.  `SInv` is the store invariant: the
program invariant, the array shapes, every allocated cell's invariant
(`CellOK`) with closed origins, the references (`EvRef`, `ArgRef`), the
sharing slots (a slot's cell has its owner's term as origin) and the memo
records (a record's cell has its key's term as origin).  `MInv` adds the
parsed frame stack, its references and the focus (`Focus`, by mode): the
claim `K` holds of the term the machine is working on.

Each transition lemma takes `MInv` of a state to `MInv` of the state
`g4Run` continues with.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-- **The machine's state**: `g4Run`'s arguments. -/
structure MS where
  P : G4Prog
  cel : Array Nat
  val : Array Nat
  ev : Array Nat
  fs : Array Nat
  argA : Array Nat
  slots : Array Nat
  mem : Array Nat
  mH : Array Nat
  mode : Nat
  pc : Nat
  env : Nat
  x : Nat
  st : Nat

section
variable (find? : Name → Option ConstantInfo) (findProj? : Name → Nat → Option ProjEntry)

/-- The machine run from a state. -/
@[expose] def MS.run (n : Nat) (s : MS) : G4Out :=
  g4Run find? findProj? n s.P s.cel s.val s.ev s.fs s.argA s.slots s.mem s.mH s.mode s.pc s.env s.x
    s.st
end

/-- The number of allocated cells. -/
@[expose] def MS.N (s : MS) : Nat := s.cel.size / 4

/-- **A memo record** names an allocated cell whose origin is its key's term. -/
@[expose] def MemoOK (P : G4Prog) (mem argA : Array Nat) (oc : Nat → Expr) (N r : Nat) : Prop :=
  mem[4 * r + 3]! < N ∧ mem[4 * r]! < P.kInfo.size ∧ mem[4 * r + 1]! + mem[4 * r + 2]! ≤ argA.size ∧
    oc mem[4 * r + 3]! = spanTerm P argA oc mem[4 * r]! mem[4 * r + 1]! mem[4 * r + 2]!

/-- **The store invariant.** -/
structure SInv (env : Env) (oc : Nat → Expr) (s : MS) : Prop where
  prog : Inv env.find? env.findProj? s.P
  celSz : s.cel.size % 4 = 0
  valSz : s.val.size % 4 = 0
  evSz : s.ev.size % 2 = 0
  memSz : s.mem.size % 4 = 0
  cell0 : 0 < s.N
  oc0 : oc 0 = bot
  val0 : 4 ≤ s.val.size ∧ s.val[0]! = 5
  closed : ∀ c, c < s.N → (oc c).looseBVarsBounded 0 = true
  cells : ∀ c, c < s.N → CellOK env s.P s.val s.ev s.argA oc s.cel c
  valRef : ∀ c, c < s.N → 2 ≤ s.cel[4 * c]! → s.cel[4 * c]! - 2 < s.val.size / 4
  evRef : EvRef s.ev s.N
  argRef : ArgRef s.argA s.N
  slotsOK : ∀ sl, g4SlotGet s.slots s.P.epBase sl ≠ 0 →
    g4SlotGet s.slots s.P.epBase sl < s.N ∧ Owns s.P sl (oc (g4SlotGet s.slots s.P.epBase sl))
  memo : ∀ r, r < s.mem.size / 4 → MemoOK s.P s.mem s.argA oc s.N r

/-- The store invariant reads only the store. -/
theorem SInv.same {env : Env} {oc : Nat → Expr} {s s' : MS} (h : SInv env oc s) (h1 : s'.P = s.P)
    (h2 : s'.cel = s.cel) (h3 : s'.val = s.val) (h4 : s'.ev = s.ev) (h5 : s'.argA = s.argA)
    (h6 : s'.slots = s.slots) (h7 : s'.mem = s.mem) : SInv env oc s' := by
  obtain ⟨P, cel, val, ev, fs, argA, slots, mem, mH, mode, pc, e, x, st⟩ := s
  obtain ⟨P', cel', val', ev', fs', argA', slots', mem', mH', mode', pc', e', x', st'⟩ := s'
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  exact ⟨h.prog, h.celSz, h.valSz, h.evSz, h.memSz, h.cell0, h.oc0, h.val0, h.closed, h.cells, h.valRef,
    h.evRef, h.argRef, h.slotsOK, h.memo⟩

/-- A spine node `pc` under `env` whose arguments from the `x`-th on are
pushed: the claim `k` holds of the head on the first `x` arguments. -/
@[expose] def SpineAt (P : G4Prog) (ev : Array Nat) (oc : Nat → Expr) (pc env x : Nat)
    (k : Expr → Prop) : Prop :=
  ∃ h n sh ss cs, P.code[pc]? = some 1 ∧ P.code[pc + 1]? = some h ∧ P.code[pc + 2]? = some n ∧
    h < pc ∧ Den P h sh ∧ DenArgs P pc (pc + 3) n ss ∧ EnvL ev env cs ∧
    (Expr.mkAppN sh ss).looseBVarsBounded cs.length = true ∧ x ≤ n ∧
    k ((Expr.mkAppN sh (ss.take x)).instantiateList (cs.map oc))

/-- **The focus**, by mode: the claim holds of the term the machine works on. -/
@[expose] def Focus (env : Env) (t₀ : Expr) (oc : Nat → Expr) (s : MS) (fl : List Fr) : Prop :=
  match s.mode with
  | 0 => ∃ u, NodeTerm s.P s.ev oc s.pc s.env u ∧ K env t₀ s.P s.argA oc fl u
  | 1 => s.x < s.val.size / 4 ∧
      ∃ t, ValDen s.P s.val s.ev s.argA oc s.x t ∧ K env t₀ s.P s.argA oc fl t
  | 2 => s.x < s.N ∧ K env t₀ s.P s.argA oc fl (oc s.x)
  | 3 => s.x < s.P.kInfo.size ∧ (s.pc = 1 → s.P.kTag[s.x]? = some 3) ∧
      K env t₀ s.P s.argA oc fl (entryTerm s.P s.x)
  | 4 => SpineAt s.P s.ev oc s.pc s.env s.x (K env t₀ s.P s.argA oc fl)
  | _ => False

/-- **The machine invariant**: the store, the parsed stack and the focus. -/
structure MInv (env : Env) (t₀ : Expr) (oc : Nat → Expr) (s : MS) (fl : List Fr) : Prop where
  store : SInv env oc s
  stack : FS s.fs s.fs.size fl
  frames : FlOK s.P s.argA s.N fl
  focus : Focus env t₀ oc s fl

/-! ## Stack inversion: the top word's tag names the frame -/

theorem FS.top_upd {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (hn : 0 < fs.size)
    (ht : fs[fs.size - 1]! &&& 15 = 2) :
    ∃ fl', fl = .upd (fs[fs.size - 1]! >>> 4) :: fl' ∧ FS fs (fs.size - 1) fl' := by
  generalize hsz : fs.size = t at h hn ht
  cases h with
  | nil => omega
  | upd _ h' => exact ⟨_, rfl, h'⟩
  | arg h₀ _ | succ h₀ _ => simp only [Nat.add_sub_cancel] at ht; rw [h₀] at ht; cases ht
  | iota h₀ _ | natA h₀ _ => simp only [show ∀ t, t + 4 - 1 = t + 3 from fun _ => rfl] at ht
                             rw [h₀] at ht; cases ht
  | proj h₀ _ => simp only [show ∀ t, t + 2 - 1 = t + 1 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht
  | natB h₀ _ => simp only [show ∀ t, t + 5 - 1 = t + 4 from fun _ => rfl] at ht; rw [h₀] at ht; cases ht

/-! ## Setting a cell's state -/

theorem set!_get_self {a : Array Nat} {i w : Nat} (h : i < a.size) : (a.set! i w)[i]! = w := by
  rw [getElem!_pos _ _ (by simp; omega)]; simp [Array.set!, Array.setIfInBounds, h]

theorem set!_get_other {a : Array Nat} {i j w : Nat} (h : j ≠ i) : (a.set! i w)[j]! = a[j]! := by
  by_cases hl : j < a.size
  · rw [getElem!_pos (a.set! i w) _ (by simpa using hl), getElem!_pos a _ hl]
    simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds_ne (by omega)]
    omega
  · rw [getElem!_neg (a.set! i w) _ (by simpa using hl), getElem!_neg a _ hl]

/-- **Setting a cell's state word** keeps the store invariant when the cell's
own invariant holds afterwards. -/
theorem SInv.setCell {env : Env} {oc : Nat → Expr} {s s' : MS} (h : SInv env oc s) {c w : Nat}
    (hc : c < s.N) (hs' : s' = { s with cel := s.cel.set! (4 * c) w })
    (hok : CellOK env s.P s.val s.ev s.argA oc (s.cel.set! (4 * c) w) c)
    (hv : 2 ≤ w → w - 2 < s.val.size / 4) : SInv env oc s' := by
  subst hs'
  have hN : ({ s with cel := s.cel.set! (4 * c) w } : MS).N = s.N := by simp [MS.N]
  have hread : ∀ c', c' ≠ c → (s.cel.set! (4 * c) w)[4 * c']! = s.cel[4 * c']! :=
    fun c' hne => set!_get_other (by omega)
  refine ⟨h.prog, by simpa using h.celSz, h.valSz, h.evSz, h.memSz, hN ▸ h.cell0, h.oc0, h.val0,
    hN ▸ h.closed, ?_, ?_, hN ▸ h.evRef, hN ▸ h.argRef, hN ▸ h.slotsOK, hN ▸ h.memo⟩
  · intro c' hc'
    rw [hN] at hc'
    by_cases he : c' = c
    · subst he; exact hok
    · exact CellOK.set_other env s.P s.val s.ev s.argA oc he (h.cells c' hc')
  · intro c' hc'
    rw [hN] at hc'
    by_cases he : c' = c
    · subst he
      rw [set!_get_self (by have := h.celSz; simp [MS.N] at hc'; omega)]
      exact hv
    · rw [hread c' he]; exact h.valRef c' hc'

/-! ## Growth: allocation, appended values and records, a grown program -/

/-- A cell's invariant survives growth of the program and the arrays and an
origin assignment that agrees below the cell count. -/
theorem CellOK.grow {env : Env} {P P' : G4Prog} {cel cel' val val' ev ev' argA argA' : Array Nat}
    {oc oc' : Nat → Expr} {N c : Nat} (hx : ExtR P P') (hcel : Pre cel cel') (hval : Pre val val')
    (hev : Pre ev ev') (harg : Pre argA argA') (hr : EvRef ev N) (hg : ArgRef argA N)
    (ha : Agree oc oc' N) (hc : c < N) (hcs : 4 * c + 3 < cel.size)
    (hv : 2 ≤ cel[4 * c]! → 4 * (cel[4 * c]! - 2) + 3 < val.size)
    (h : CellOK env P val ev argA oc cel c) : CellOK env P' val' ev' argA' oc' cel' c := by
  have r0 := hcel.2 (4 * c) (by omega)
  have r1 := hcel.2 (4 * c + 1) (by omega)
  have r2 := hcel.2 (4 * c + 2) (by omega)
  unfold CellOK at h ⊢
  rw [r0, r1, r2, ← ha c hc]
  revert hv h
  generalize cel[4 * c]! = w
  intro hv h
  match w, hv, h with
  | 0, _, h => exact (h.congr hr ha).pre hx hev
  | 1, _, h => exact h
  | v + 2, hv, ⟨t, htv, hred⟩ =>
    exact ⟨t, ((htv.congr hr hg ha).pre hx hval hev harg (by have := hv (by omega); omega)), hred⟩

/-- **The store invariant under growth**: the program extended, the arrays
appended to, new cells with their invariants, and the origin assignment
extended. -/
theorem SInv.grow {env : Env} {oc oc' : Nat → Expr} {s s' : MS} (h : SInv env oc s)
    (hI : Inv env.find? env.findProj? s'.P) (hx : ExtR s.P s'.P) (hep : s'.P.epBase = s.P.epBase)
    (hcel : Pre s.cel s'.cel) (hcs : s'.cel.size % 4 = 0) (hval : Pre s.val s'.val)
    (hvs : s'.val.size % 4 = 0) (hev : Pre s.ev s'.ev) (hes : s'.ev.size % 2 = 0)
    (harg : Pre s.argA s'.argA) (hsl : s'.slots = s.slots) (hmem : s'.mem = s.mem)
    (ha : Agree oc oc' s.N) (hr : EvRef s'.ev s'.N) (hg : ArgRef s'.argA s'.N)
    (hnew : ∀ c, s.N ≤ c → c < s'.N → (oc' c).looseBVarsBounded 0 = true ∧
      CellOK env s'.P s'.val s'.ev s'.argA oc' s'.cel c ∧
      (2 ≤ s'.cel[4 * c]! → s'.cel[4 * c]! - 2 < s'.val.size / 4)) :
    SInv env oc' s' := by
  have hN : s.N ≤ s'.N := by simp only [MS.N]; exact Nat.div_le_div_right hcel.1
  have hvsz : s.val.size / 4 ≤ s'.val.size / 4 := Nat.div_le_div_right hval.1
  have hcs0 := h.celSz
  have hvs0 := h.valSz
  refine ⟨hI, hcs, hvs, hes, by rw [hmem]; exact h.memSz, Nat.lt_of_lt_of_le h.cell0 hN,
    by rw [← ha 0 h.cell0]; exact h.oc0, ⟨Nat.le_trans h.val0.1 hval.1, by
      rw [hval.2 0 (by have := h.val0.1; omega)]; exact h.val0.2⟩, ?_, ?_, ?_, hr, hg, ?_, ?_⟩
  · intro c hc
    rcases Nat.lt_or_ge c s.N with hc' | hc'
    · rw [← ha c hc']; exact h.closed c hc'
    · exact (hnew c hc' hc).1
  · intro c hc
    rcases Nat.lt_or_ge c s.N with hc' | hc'
    · refine (h.cells c hc').grow hx hcel hval hev harg h.evRef h.argRef ha hc'
        (by simp [MS.N] at hc'; omega) (fun h2 => ?_)
      have := h.valRef c hc' h2; omega
    · exact (hnew c hc' hc).2.1
  · intro c hc
    rcases Nat.lt_or_ge c s.N with hc' | hc'
    · rw [hcel.2 (4 * c) (by simp [MS.N] at hc'; omega)]
      intro h2; exact Nat.lt_of_lt_of_le (h.valRef c hc' h2) hvsz
    · exact (hnew c hc' hc).2.2
  · intro sl hne
    rw [hsl, hep] at hne ⊢
    obtain ⟨hlt, how⟩ := h.slotsOK sl hne
    rw [← ha _ hlt]
    exact ⟨Nat.lt_of_lt_of_le hlt hN, how.ext hx⟩
  · intro r hr'
    rw [hmem] at hr' ⊢
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h.memo r hr'
    refine ⟨Nat.lt_of_lt_of_le h₁ hN, Nat.lt_of_lt_of_le h₂ hx.kInfoSize, Nat.le_trans h₃ harg.1, ?_⟩
    rw [← ha _ h₁, h₄]
    unfold spanTerm
    rw [entryTerm_ext hx h₂, span_pre harg h₃, map_agree ha (span_mem_lt h.argRef h₃)]

/-! ## Mode 2: entering a cell -/

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- **Entering a value cell.** -/
theorem step_enter_value (h : MInv env t₀ oc s fl) (hm : s.mode = 2) (hs : 2 ≤ s.cel[g4X4 s.x]!) :
    MInv env t₀ oc { s with mode := 1, pc := 0, env := 0, x := s.cel[g4X4 s.x]! - 2 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hx, hK⟩ := hf
  rw [g4X4_eq] at hs ⊢
  obtain ⟨t, hv, hK'⟩ := enter_value env t₀ s.P s.val s.ev s.argA oc (h.store.cells _ hx)
    (show s.cel[4 * s.x]! = s.cel[4 * s.x]! - 2 + 2 by omega) hK
  exact ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, h.store.valRef _ hx hs, t, hv, hK'⟩

/-- **Entering a thunk**: the cell is busy, its update frame is pushed, and
its node is evaluated under its environment. -/
theorem step_enter_thunk (h : MInv env t₀ oc s fl) (hm : s.mode = 2) (hs : s.cel[g4X4 s.x]! = 0) :
    MInv env t₀ oc { s with
      cel := s.cel.set! (g4X4 s.x) 1, fs := s.fs.push (g4Tag s.x 2), mode := 0,
      pc := s.cel[g4X4 s.x + 1]!, env := s.cel[g4X4 s.x + 2]!, x := 0 } (.upd s.x :: fl) := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hx, hK⟩ := hf
  rw [g4X4_eq] at hs ⊢
  obtain ⟨hn, hK'⟩ := enter_thunk env t₀ s.P s.val s.ev s.argA oc (h.store.cells _ hx) hs hK
  have hst : SInv env oc { s with cel := s.cel.set! (4 * s.x) 1 } :=
    h.store.setCell hx rfl (by unfold CellOK; rw [set!_get_self (by
      have := h.store.celSz; simp [MS.N] at hx; omega)]; trivial) (by omega)
  have hN : ({ s with cel := s.cel.set! (4 * s.x) 1 } : MS).N = s.N := by simp [MS.N]
  refine ⟨hst.same rfl rfl rfl rfl rfl rfl rfl, FS.pushUpd h.stack _, ?_, oc s.x, ?_, hK'⟩
  · intro f hf'
    rcases List.mem_cons.mp hf' with rfl | hf'
    · show s.x < _; simpa [MS.N] using hx
    · simpa [MS.N] using h.frames f hf'
  · show NodeTerm s.P s.ev oc s.cel[4 * s.x + 1]! s.cel[4 * s.x + 2]! (oc s.x)
    exact hn

/-- **Popping an update frame**: the cell gets the value, and the value is
returned to the frames below. -/
theorem step_pop_update (h : MInv env t₀ oc s fl) (hm : s.mode = 1) (hn : 0 < s.fs.size)
    (ht : s.fs[s.fs.size - 1]! &&& 15 = 2) :
    ∃ fl', MInv env t₀ oc { s with
      cel := s.cel.set! (g4X4 (s.fs[s.fs.size - 1]! >>> 4)) (s.x + 2),
      fs := s.fs.pop, mode := 1, pc := 0, env := 0 } fl' := by
  obtain ⟨fl', rfl, hfs⟩ := FS.top_upd h.stack hn ht
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨hxv, t, hv, hK⟩ := hf
  obtain ⟨hcell, hK'⟩ := pop_update env t₀ s.P s.val s.ev s.argA oc hv hK
  have hc : s.fs[s.fs.size - 1]! >>> 4 < s.N := (FlOK.cons.mp h.frames).1
  rw [g4X4_eq]
  have hst : SInv env oc { s with cel := s.cel.set! (4 * (s.fs[s.fs.size - 1]! >>> 4)) (s.x + 2) } :=
    h.store.setCell hc rfl (CellOK.set_value env s.P s.val s.ev s.argA oc (by
      have := h.store.celSz; simp [MS.N] at hc; omega) hcell) (by omega)
  refine ⟨fl', hst.same rfl rfl rfl rfl rfl rfl rfl, ?_, ?_, hxv, t, hv, hK'⟩
  · show FS s.fs.pop s.fs.pop.size fl'
    rw [Array.size_pop]; exact FS.pop (by omega) hfs
  · intro f hf'
    simpa [MS.N] using (FlOK.cons.mp h.frames).2 f hf'

end

/-! ## Node inversions -/

theorem Den.inv0 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 0) :
    ∃ i, P.code[o + 1]? = some i ∧ s = .bvar i := by
  cases h with
  | bvar _ h₁ => exact ⟨_, h₁, rfl⟩
  | _ => simp_all

theorem Den.inv1 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 1) :
    ∃ hd n sh ss, P.code[o + 1]? = some hd ∧ P.code[o + 2]? = some n ∧ hd < o ∧ Den P hd sh ∧
      DenArgs P o (o + 3) n ss ∧ s = Expr.mkAppN sh ss := by
  cases h with
  | spine _ h₁ h₂ hlt hh ha => exact ⟨_, _, _, _, h₁, h₂, hlt, hh, ha, rfl⟩
  | _ => simp_all

theorem Den.inv4 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 4) :
    ∃ k info, P.code[o + 1]? = some k ∧ P.kInfo[k]? = some info ∧ s = infoTerm info := by
  cases h with
  | const _ h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
  | _ => simp_all

theorem Den.inv8 {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h0 : P.code[o]? = some 8) :
    s = bot := by
  cases h with
  | neutral _ => rfl
  | _ => simp_all

theorem DenArgs.length {P : G4Prog} : ∀ {o p n : Nat} {ss : List Expr}, DenArgs P o p n ss →
    ss.length = n
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ _ _ hr => by simp [DenArgs.length hr]

theorem infoTerm_closed : ∀ (info : G4Info), (infoTerm info).looseBVarsBounded 0 = true
  | .defn .. | .ctor .. | .recr .. | .neutral .. => by simp [infoTerm, Expr.looseBVarsBounded]

/-- The cells of an environment have closed origins. -/
theorem SInv.allClosed {env : Env} {oc : Nat → Expr} {s : MS} (h : SInv env oc s) {e : Nat}
    {cs : List Nat} (he : EnvL s.ev e cs) : AllClosed (cs.map oc) := by
  intro v hv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
  exact h.closed c (EnvL.mem_lt h.evRef he c hc)

/-! ## Mode 0: evaluating a node -/

section
variable {env : Env} {t₀ : Expr} {oc : Nat → Expr} {s : MS} {fl : List Fr}

/-- **A variable**: enter its environment cell. -/
theorem step_bvar (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 0) :
    MInv env t₀ oc { s with
      mode := 2, pc := 0, env := 0, x := g4EnvGet s.ev s.env s.P.code[s.pc + 1]! } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨i, hi, rfl⟩ := hd.inv0 (by rw [some_of_lt (hd.lt_size), ht])
  have hil : i < cs.length := by simpa [Expr.looseBVarsBounded] using hb
  rw [get!_of_some hi, EnvL.get he i hil]
  have hgd : cs.getD i 0 = cs[i] := by simp [List.getElem?_eq_getElem hil]
  have hmem : cs.getD i 0 ∈ cs := by rw [hgd]; exact List.getElem_mem hil
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames,
    EnvL.mem_lt h.store.evRef he _ hmem, ?_⟩
  show K env t₀ s.P s.argA oc fl (oc (cs.getD i 0))
  rw [lookup (h.store.allClosed he) (by simpa using hil)] at hK
  rw [hgd]; simpa using hK

/-- **A constant**: dispatch its entry. -/
theorem step_const (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 4) :
    MInv env t₀ oc { s with
      mode := 3, pc := 0, env := 0, x := s.P.code[s.pc + 1]!, st := s.st + 1 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨k, info, hk, hinfo, rfl⟩ := hd.inv4 (by rw [some_of_lt (hd.lt_size), ht])
  rw [Expr.instantiateList_eq_self (infoTerm_closed info)] at hK
  have hkl : k < s.P.kInfo.size := by
    rcases Nat.lt_or_ge k s.P.kInfo.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hinfo; cases hinfo
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  show s.P.code[s.pc + 1]! < s.P.kInfo.size ∧ (0 = 1 → _) ∧
    K env t₀ s.P s.argA oc fl (entryTerm s.P s.P.code[s.pc + 1]!)
  rw [get!_of_some hk]
  exact ⟨hkl, fun h => absurd h (by decide), by unfold entryTerm; rw [hinfo]; exact hK⟩

/-- **A spine**: push its arguments, the last first. -/
theorem step_spine (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 1) :
    MInv env t₀ oc { s with mode := 4, x := s.P.code[s.pc + 2]! } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain ⟨hd', n, sh, ss, h₁, h₂, hlt, hh, ha, rfl⟩ := hd.inv1 (by rw [some_of_lt (hd.lt_size), ht])
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  show SpineAt s.P s.ev oc s.pc s.env s.P.code[s.pc + 2]! (K env t₀ s.P s.argA oc fl)
  rw [get!_of_some h₂]
  refine ⟨hd', n, sh, ss, cs, by rw [some_of_lt (hd.lt_size), ht], h₁, h₂, hlt, hh, ha, he, hb,
    Nat.le_refl _, ?_⟩
  rw [List.take_of_length_le (by rw [ha.length]; exact Nat.le_refl _)]
  exact hK

/-- **The neutral node**: the neutral value. -/
theorem step_neutral (h : MInv env t₀ oc s fl) (hm : s.mode = 0) (ht : s.P.code[s.pc]! = 8) :
    MInv env t₀ oc { s with mode := 1, pc := 0, env := 0, x := 0 } fl := by
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨u, ⟨s0, cs, hd, he, hb, rfl⟩, hK⟩ := hf
  obtain rfl := hd.inv8 (by rw [some_of_lt (hd.lt_size), ht])
  rw [Expr.instantiateList_eq_self (by simp [bot, Expr.looseBVarsBounded])] at hK
  refine ⟨h.store.same rfl rfl rfl rfl rfl rfl rfl, h.stack, h.frames, ?_⟩
  have := h.store.val0
  exact ⟨by show 0 < s.val.size / 4; omega, bot, .other (by simp; omega), hK⟩

end

end ConLeche.Verify.Ground
