module

public import ConLeche.Cached.Ground4
public import ConLeche.Verify.Ground.Erased
import ConLeche.Verify.Ground.Compile

public section

/-!
# The ground machine's state, read as erased terms (task #423 soundness, layer (b))

The machine `g4Run` (`ConLeche/Cached/Ground4.lean`) keeps its state in flat
`Array Nat`s.  This file reads them: an environment record chain as a list of
cells (`EnvL`), a code node under an environment as an erased term
(`NodeTerm`), a value as an erased term (`ValDen`), and the frame stack as a
list of frames (`FS`).  A ghost assignment `oc` gives every cell its origin.

The machine's claim is `K`: for the parsed frames and the term in focus,
every frame's pending reduction holds.  An argument frame and a projection
frame are congruences; an update, ι, literal or packing frame carries the
`ERed` premise its pop discharges; the bottom of the stack is the site's
claim `ERed env t₀ u` for the compiled site term `t₀`.  `K.step`: the claim
is closed under erased reduction of the focus, which is what every
transition of the machine uses (`ERed.forget` included: a neutral focus is
`bot`).

What is not here yet (layer (c)): the invariant's preservation by each
transition of `g4Run` and the induction over the fuel.
-/

namespace ConLeche.Verify.Ground

open ConLeche ConLeche.Cached

/-! ## Environments and node terms -/

/-- **An environment record chain**: environment `0` is empty, `i + 1` is
record `i` (`[cell, next]` at `2 i`), innermost first. -/
inductive EnvL (ev : Array Nat) : Nat → List Nat → Prop where
  | nil : EnvL ev 0 []
  | cons {i : Nat} {cs : List Nat} : 2 * i + 1 < ev.size → ev[2 * i + 1]! ≤ i →
      EnvL ev ev[2 * i + 1]! cs → EnvL ev (i + 1) (ev[2 * i]! :: cs)

/-- An environment's chain is determined by the records. -/
theorem EnvL.unique {ev : Array Nat} : ∀ {e : Nat} {cs cs' : List Nat},
    EnvL ev e cs → EnvL ev e cs' → cs = cs'
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons _ _ h, .cons _ _ h' => by rw [EnvL.unique h h']

/-- An environment chain survives appending records. -/
theorem EnvL.push {ev : Array Nat} (x : Nat) : ∀ {e : Nat} {cs : List Nat},
    EnvL ev e cs → EnvL (ev.push x) e cs
  | _, _, .nil => .nil
  | _, _, @EnvL.cons _ i _ hlt hle h => by
    have h1 : (ev.push x)[2 * i + 1]! = ev[2 * i + 1]! := by
      rw [getElem!_pos (ev.push x) (2 * i + 1) (by simp; omega), getElem!_pos ev (2 * i + 1) hlt,
        Array.getElem_push_lt]
    have h0 : (ev.push x)[2 * i]! = ev[2 * i]! := by
      rw [getElem!_pos (ev.push x) (2 * i) (by simp; omega), getElem!_pos ev (2 * i) (by omega),
        Array.getElem_push_lt]
    rw [← h0]
    refine .cons (by simp; omega) (by rw [h1]; exact hle) ?_
    rw [h1]; exact EnvL.push x h

/-- **A node under an environment** denotes its read-back instantiated at the
environment's cells' origins (`bvar 0` the innermost). -/
def NodeTerm (P : G4Prog) (ev : Array Nat) (oc : Nat → Expr) (pc e : Nat) (u : Expr) : Prop :=
  ∃ s cs, Den P pc s ∧ EnvL ev e cs ∧ u = s.instantiateList (cs.map oc)

/-! ## Values -/

/-- The term of a table entry (`bot` past the table). -/
def entryTerm (P : G4Prog) (k : Nat) : Expr :=
  match P.kInfo[k]? with
  | some info => infoTerm info
  | none => bot

/-- The cells of an argument span. -/
def span (argA : Array Nat) (start len : Nat) : List Nat :=
  (List.range len).map fun j => argA[start + j]!

/-- **A value's term**: a closure is its λ node under its environment; a
constructor or a partial application is its entry's constant on its span's
origins; a literal is itself; anything else (the neutral) is `bot`. -/
inductive ValDen (P : G4Prog) (val ev argA : Array Nat) (oc : Nat → Expr) (v : Nat) : Expr → Prop where
  | closure {u : Expr} : val[4 * v]! = 0 → NodeTerm P ev oc val[4 * v + 1]! val[4 * v + 2]! u →
      ValDen P val ev argA oc v u
  | ctor : val[4 * v]! = 1 → val[4 * v + 2]! + val[4 * v + 3]! ≤ argA.size →
      ValDen P val ev argA oc v
        (Expr.mkAppN (entryTerm P val[4 * v + 1]!) ((span argA val[4 * v + 2]! val[4 * v + 3]!).map oc))
  | natLit : val[4 * v]! = 2 → ValDen P val ev argA oc v (.lit (.natVal val[4 * v + 1]!))
  | strLit {s : String} : val[4 * v]! = 3 → P.strs[val[4 * v + 1]!]? = some s →
      ValDen P val ev argA oc v (.lit (.strVal s))
  | pap : val[4 * v]! = 4 → val[4 * v + 2]! + val[4 * v + 3]! ≤ argA.size →
      ValDen P val ev argA oc v
        (Expr.mkAppN (entryTerm P val[4 * v + 1]!) ((span argA val[4 * v + 2]! val[4 * v + 3]!).map oc))
  | other : val[4 * v]! ≥ 5 → ValDen P val ev argA oc v bot

/-! ## Frames -/

/-- A parsed frame (`g4Run`'s frame stack, top first). -/
inductive Fr where
  | arg (c : Nat)
  | upd (c : Nat)
  | iota (k start len : Nat)
  | proj (pi : Nat)
  | natA (k a b : Nat)
  | natB (k n₁ a b : Nat)
  | succ

/-- **The frame stack** `fs[0, top)` parses as `fl` (top first): each frame
has its tag in the low four bits of its top word. -/
inductive FS (fs : Array Nat) : Nat → List Fr → Prop where
  | nil : FS fs 0 []
  | arg {t : Nat} {fl : List Fr} : fs[t]! &&& 15 = 1 → FS fs t fl →
      FS fs (t + 1) (.arg (fs[t]! >>> 4) :: fl)
  | upd {t : Nat} {fl : List Fr} : fs[t]! &&& 15 = 2 → FS fs t fl →
      FS fs (t + 1) (.upd (fs[t]! >>> 4) :: fl)
  | iota {t : Nat} {fl : List Fr} : fs[t + 3]! &&& 15 = 3 → FS fs t fl →
      FS fs (t + 4) (.iota fs[t]! fs[t + 1]! fs[t + 2]! :: fl)
  | proj {t : Nat} {fl : List Fr} : fs[t + 1]! &&& 15 = 4 → FS fs t fl →
      FS fs (t + 2) (.proj fs[t]! :: fl)
  | natA {t : Nat} {fl : List Fr} : fs[t + 3]! &&& 15 = 5 → FS fs t fl →
      FS fs (t + 4) (.natA fs[t]! fs[t + 1]! fs[t + 2]! :: fl)
  | natB {t : Nat} {fl : List Fr} : fs[t + 4]! &&& 15 = 6 → FS fs t fl →
      FS fs (t + 5) (.natB fs[t]! fs[t + 1]! fs[t + 2]! fs[t + 3]! :: fl)
  | succ {t : Nat} {fl : List Fr} : fs[t]! &&& 15 = 7 → FS fs t fl → FS fs (t + 1) (.succ :: fl)

/-! ## The claim -/

section
variable (env : Env) (t₀ : Expr) (P : G4Prog) (argA : Array Nat) (oc : Nat → Expr)

/-- The term of a literal operation's redex: entry `k` on cells `a`, `b`. -/
def opTerm (k a b : Nat) : Expr := .app (.app (entryTerm P k) (oc a)) (oc b)

/-- The term of a recursor redex: entry `k` on the span. -/
def spanTerm (k start len : Nat) : Expr :=
  Expr.mkAppN (entryTerm P k) ((span argA start len).map oc)

/-- **The machine's claim** for the frames `fl` (top first) and the term in
focus `u`. -/
def K : List Fr → Expr → Prop
  | [], u => ERed env t₀ u
  | .arg c :: fl, u => K fl (.app u (oc c))
  | .upd c :: fl, u => ERed env (oc c) u ∧ K fl (oc c)
  | .iota k start len :: fl, u =>
    ERed env (oc argA[start + len - 1]!) u ∧ K fl (spanTerm P argA oc k start len)
  | .proj pi :: fl, u =>
    match pi with
    | 0 => K fl bot
    | q + 1 =>
      match P.projs[q]? with
      | some pj => K fl (.proj pj.sn pj.idx u)
      | none => K fl bot
  | .natA k a b :: fl, u => ERed env (oc a) u ∧ K fl (opTerm P oc k a b)
  | .natB k n₁ a b :: fl, u =>
    ERed env (oc b) u ∧ (∃ wa, ERed env (oc a) wa ∧ rawNatLit? wa = some n₁) ∧
      K fl (opTerm P oc k a b)
  | .succ :: fl, u => ∀ w n, ERed env u w → rawNatLit? w = some n → K fl (.lit (.natVal (n + 1)))

/-- **The claim is closed under erased reduction of the focus.** -/
theorem K.step : ∀ (fl : List Fr) {u u' : Expr}, K env t₀ P argA oc fl u → ERed env u u' →
    K env t₀ P argA oc fl u'
  | [], _, _, h, hr => h.trans hr
  | .arg _ :: fl, _, _, h, hr => K.step fl h (.appFn hr)
  | .upd _ :: _, _, _, h, hr => ⟨h.1.trans hr, h.2⟩
  | .iota .. :: _, _, _, h, hr => ⟨h.1.trans hr, h.2⟩
  | .proj pi :: fl, _, _, h, hr => by
    cases pi with
    | zero => exact h
    | succ q =>
      simp only [K] at h ⊢
      split at h
      · exact K.step fl h (.projArg hr)
      · exact h
  | .natA .. :: _, _, _, h, hr => ⟨h.1.trans hr, h.2⟩
  | .natB .. :: _, _, _, h, hr => ⟨h.1.trans hr, h.2⟩
  | .succ :: _, _, _, h, hr => fun w n hw hn => h w n (hr.trans hw) hn

/-- The site: the claim at an empty stack is the site's reduction. -/
theorem K.nil {u : Expr} (h : K env t₀ P argA oc [] u) : ERed env t₀ u := h

end

/-! ## Word encodings -/

theorem g4X4_eq (n : Nat) : g4X4 n = 4 * n := by
  show (n + n) + (n + n) = 4 * n; omega

theorem g4Tag_eq (c t : Nat) : g4Tag c t = 16 * c + t := by
  show g4X4 (g4X4 c) + t = 16 * c + t; rw [g4X4_eq, g4X4_eq]; omega

/-- A tagged word's tag. -/
theorem tag_and (c t : Nat) (ht : t < 16) : g4Tag c t &&& 15 = t := by
  rw [g4Tag_eq, show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A tagged word's payload. -/
theorem tag_shr (c t : Nat) (ht : t < 16) : g4Tag c t >>> 4 = c := by
  rw [g4Tag_eq, Nat.shiftRight_eq_div_pow]; omega

/-! ## The frame stack under pushes -/

theorem getElem!_push_lt' {a : Array Nat} {x i : Nat} (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt]

theorem getElem!_push_eq' (a : Array Nat) (x : Nat) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

/-- A parse reads only below its top. -/
theorem FS.push {fs : Array Nat} (x : Nat) : ∀ {t : Nat} {fl : List Fr}, t ≤ fs.size → FS fs t fl →
    FS (fs.push x) t fl
  | _, _, _, .nil => .nil
  | _, _, hle, .arg h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h ⊢
    exact .arg h (FS.push x (by omega) hr)
  | _, _, hle, .upd h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h ⊢
    exact .upd h (FS.push x (by omega) hr)
  | _, _, hle, .iota h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h
    rw [← getElem!_push_lt' (a := fs) (x := x) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 1) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 2) (by omega)]
    exact .iota h (FS.push x (by omega) hr)
  | _, _, hle, .proj h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h
    rw [← getElem!_push_lt' (a := fs) (x := x) (by omega)]
    exact .proj h (FS.push x (by omega) hr)
  | _, _, hle, .natA h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h
    rw [← getElem!_push_lt' (a := fs) (x := x) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 1) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 2) (by omega)]
    exact .natA h (FS.push x (by omega) hr)
  | _, _, hle, .natB h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h
    rw [← getElem!_push_lt' (a := fs) (x := x) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 1) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 2) (by omega),
      ← getElem!_push_lt' (a := fs) (x := x) (i := _ + 3) (by omega)]
    exact .natB h (FS.push x (by omega) hr)
  | _, _, hle, .succ h hr => by
    rw [← getElem!_push_lt' (x := x) (by omega)] at h
    exact .succ h (FS.push x (by omega) hr)

/-- Pushing an update frame. -/
theorem FS.pushUpd {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (c : Nat) :
    FS (fs.push (g4Tag c 2)) (fs.push (g4Tag c 2)).size (.upd c :: fl) := by
  have := FS.upd (fs := fs.push (g4Tag c 2)) (t := fs.size)
    (by rw [getElem!_push_eq']; exact tag_and c 2 (by omega)) (FS.push _ (Nat.le_refl _) h)
  rw [getElem!_push_eq', tag_shr c 2 (by omega)] at this
  simpa using this

/-- Pushing an argument frame. -/
theorem FS.pushArg {fs : Array Nat} {fl : List Fr} (h : FS fs fs.size fl) (c : Nat) :
    FS (fs.push (g4Tag c 1)) (fs.push (g4Tag c 1)).size (.arg c :: fl) := by
  have := FS.arg (fs := fs.push (g4Tag c 1)) (t := fs.size)
    (by rw [getElem!_push_eq']; exact tag_and c 1 (by omega)) (FS.push _ (Nat.le_refl _) h)
  rw [getElem!_push_eq', tag_shr c 1 (by omega)] at this
  simpa using this

/-! ## Cells, and the first transitions -/

section
variable (env : Env) (t₀ : Expr) (P : G4Prog) (val ev argA : Array Nat) (oc : Nat → Expr)

/-- **A cell's invariant** (`[state, code, env, _]` at `4 c`): a thunk is its
node under its environment; a busy cell's claim is on the stack (its update
frame); a value cell's origin reduces to its value's term. -/
def CellOK (cel : Array Nat) (c : Nat) : Prop :=
  match cel[4 * c]! with
  | 0 => NodeTerm P ev oc cel[4 * c + 1]! cel[4 * c + 2]! (oc c)
  | 1 => True
  | v + 2 => ∃ t, ValDen P val ev argA oc v t ∧ ERed env (oc c) t

/-- **Entering a value cell** (mode 2, state `v + 2`): the value is in focus. -/
theorem enter_value {cel : Array Nat} {c v : Nat} {fl : List Fr}
    (hc : CellOK env P val ev argA oc cel c) (hs : cel[4 * c]! = v + 2)
    (hK : K env t₀ P argA oc fl (oc c)) :
    ∃ t, ValDen P val ev argA oc v t ∧ K env t₀ P argA oc fl t := by
  unfold CellOK at hc; rw [hs] at hc
  obtain ⟨t, hv, hr⟩ := hc
  exact ⟨t, hv, hK.step env t₀ P argA oc fl hr⟩

/-- **Entering a thunk** (mode 2, state `0`): the update frame's claim is the
cell's own origin, and its node under its environment is in focus. -/
theorem enter_thunk {cel : Array Nat} {c : Nat} {fl : List Fr}
    (hc : CellOK env P val ev argA oc cel c) (hs : cel[4 * c]! = 0)
    (hK : K env t₀ P argA oc fl (oc c)) :
    NodeTerm P ev oc cel[4 * c + 1]! cel[4 * c + 2]! (oc c) ∧
      K env t₀ P argA oc (.upd c :: fl) (oc c) := by
  unfold CellOK at hc; rw [hs] at hc
  exact ⟨hc, .refl, hK⟩

/-- **Popping an update frame** (mode 1, frame `[c, 2]`): the cell's claim is
discharged by the value, and the frames below see the value. -/
theorem pop_update {c v : Nat} {fl : List Fr} {t : Expr}
    (hv : ValDen P val ev argA oc v t) (hK : K env t₀ P argA oc (.upd c :: fl) t) :
    (∃ t', ValDen P val ev argA oc v t' ∧ ERed env (oc c) t') ∧ K env t₀ P argA oc fl t :=
  ⟨⟨t, hv, hK.1⟩, hK.2.step env t₀ P argA oc fl hK.1⟩

/-- Setting a cell's state word leaves the other cells' invariants. -/
theorem CellOK.set_other {cel : Array Nat} {c c' w : Nat} (hne : c' ≠ c)
    (h : CellOK env P val ev argA oc cel c') : CellOK env P val ev argA oc (cel.set! (4 * c) w) c' := by
  have hget : ∀ j, j < 3 → (cel.set! (4 * c) w)[4 * c' + j]! = cel[4 * c' + j]! := by
    intro j hj
    have hsz : (cel.set! (4 * c) w).size = cel.size := by simp
    by_cases hl : 4 * c' + j < cel.size
    · rw [getElem!_pos (cel.set! (4 * c) w) _ (by simpa using hl), getElem!_pos cel _ hl]
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds_ne (by omega)]
      omega
    · rw [getElem!_neg (cel.set! (4 * c) w) _ (by simpa using hl), getElem!_neg cel _ hl]
  unfold CellOK at h ⊢
  have h0 := hget 0 (by omega); have h1 := hget 1 (by omega); have h2 := hget 2 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2]; exact h

/-- The cell whose state is set to a value is the value's cell. -/
theorem CellOK.set_value {cel : Array Nat} {c v : Nat} (hc : 4 * c < cel.size)
    (h : ∃ t, ValDen P val ev argA oc v t ∧ ERed env (oc c) t) :
    CellOK env P val ev argA oc (cel.set! (4 * c) (v + 2)) c := by
  unfold CellOK
  rw [show (cel.set! (4 * c) (v + 2))[4 * c]! = v + 2 by
    rw [getElem!_pos _ _ (by simp; omega)]; simp [Array.set!, Array.setIfInBounds, hc]]
  exact h

end

end ConLeche.Verify.Ground
