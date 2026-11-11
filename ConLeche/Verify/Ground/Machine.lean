module

public import ConLeche.Verify.Ground.Compile
public import ConLeche.Verify.Ground.Bind

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
environment's cells' origins (`bvar 0` the innermost); the read-back's loose
variables are bound by the environment. -/
@[expose] def NodeTerm (P : G4Prog) (ev : Array Nat) (oc : Nat → Expr) (pc e : Nat) (u : Expr) : Prop :=
  ∃ s cs, Den P pc s ∧ EnvL ev e cs ∧ s.looseBVarsBounded cs.length = true ∧
    u = s.instantiateList (cs.map oc)

/-! ## Values -/

/-- The term of a table entry (`bot` past the table). -/
@[expose] def entryTerm (P : G4Prog) (k : Nat) : Expr :=
  match P.kInfo[k]? with
  | some info => infoTerm info
  | none => bot

/-- The cells of an argument span. -/
@[expose] def span (argA : Array Nat) (start len : Nat) : List Nat :=
  (List.range len).map fun j => argA[start + j]!

/-- **A value's term**: a closure is its λ node under its environment; a
constructor or a partial application is its entry's constant on its span's
origins; a literal is itself; anything else (the neutral) is `bot`. -/
inductive ValDen (P : G4Prog) (val ev argA : Array Nat) (oc : Nat → Expr) (v : Nat) : Expr → Prop where
  | closure {u : Expr} : val[4 * v]! = 0 → P.code[val[4 * v + 1]!]! = 2 →
      NodeTerm P ev oc val[4 * v + 1]! val[4 * v + 2]! u → ValDen P val ev argA oc v u
  | ctor : val[4 * v]! = 1 → val[4 * v + 1]! < P.kInfo.size →
      val[4 * v + 2]! + val[4 * v + 3]! ≤ argA.size →
      ValDen P val ev argA oc v
        (Expr.mkAppN (entryTerm P val[4 * v + 1]!) ((span argA val[4 * v + 2]! val[4 * v + 3]!).map oc))
  | natLit : val[4 * v]! = 2 → ValDen P val ev argA oc v (.lit (.natVal val[4 * v + 1]!))
  | strLit {s : String} : val[4 * v]! = 3 → P.strs[val[4 * v + 1]!]? = some s →
      ValDen P val ev argA oc v (.lit (.strVal s))
  | pap : val[4 * v]! = 4 → val[4 * v + 1]! < P.kInfo.size →
      val[4 * v + 2]! + val[4 * v + 3]! ≤ argA.size →
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
@[expose] def opTerm (k a b : Nat) : Expr := .app (.app (entryTerm P k) (oc a)) (oc b)

/-- The term of a recursor redex: entry `k` on the span. -/
@[expose] def spanTerm (k start len : Nat) : Expr :=
  Expr.mkAppN (entryTerm P k) ((span argA start len).map oc)

/-- **The machine's claim** for the frames `fl` (top first) and the term in
focus `u`. -/
@[expose] def K : List Fr → Expr → Prop
  | [], u => ERed env t₀ u
  | .arg c :: fl, u => K fl (.app u (oc c))
  | .upd c :: fl, u => ERed env (oc c) u ∧ K fl (oc c)
  -- the major reduces to the focus, or the recursor takes the K step
  -- (`kE ≥ 4`: the major is never read)
  | .iota k start len :: fl, u =>
    (ERed env (oc argA[start + len - 1]!) u ∨ 4 ≤ P.kE[k]!) ∧ K fl (spanTerm P argA oc k start len)
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
  -- the frame pops to the neutral on a value of no `Nat` reading
  | .succ :: fl, u =>
    K fl bot ∧ ∀ w n, ERed env u w → rawNatLit? w = some n → K fl (.lit (.natVal (n + 1)))

/-- **The claim is closed under erased reduction of the focus.** -/
theorem K.step : ∀ (fl : List Fr) {u u' : Expr}, K env t₀ P argA oc fl u → ERed env u u' →
    K env t₀ P argA oc fl u'
  | [], _, _, h, hr => h.trans hr
  | .arg _ :: fl, _, _, h, hr => K.step fl h (.appFn hr)
  | .upd _ :: _, _, _, h, hr => ⟨h.1.trans hr, h.2⟩
  | .iota .. :: _, _, _, h, hr => ⟨h.1.imp (fun h => h.trans hr) id, h.2⟩
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
  | .succ :: _, _, _, h, hr => ⟨h.1, fun w n hw hn => h.2 w n (hr.trans hw) hn⟩

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

/-! ## Prefix extension: every reading survives appending -/

/-- `b` extends `a`: what `a` holds, `b` holds at the same index. -/
@[expose] def Pre (a b : Array Nat) : Prop := a.size ≤ b.size ∧ ∀ i, i < a.size → b[i]! = a[i]!

theorem Pre.refl (a : Array Nat) : Pre a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Pre.trans {a b c : Array Nat} (h₁ : Pre a b) (h₂ : Pre b c) : Pre a c :=
  ⟨Nat.le_trans h₁.1 h₂.1, fun i hi => (h₂.2 i (Nat.lt_of_lt_of_le hi h₁.1)).trans (h₁.2 i hi)⟩

theorem Pre.push (a : Array Nat) (x : Nat) : Pre a (a.push x) :=
  ⟨by simp, fun _ hi => getElem!_push_lt' hi⟩

theorem EnvL.pre {ev ev' : Array Nat} (hp : Pre ev ev') : ∀ {e : Nat} {cs : List Nat},
    EnvL ev e cs → EnvL ev' e cs
  | _, _, .nil => .nil
  | _, _, @EnvL.cons _ i _ hlt hle h => by
    have h1 := hp.2 (2 * i + 1) hlt
    have h0 := hp.2 (2 * i) (by omega)
    rw [← h0]
    refine .cons (Nat.lt_of_lt_of_le hlt hp.1) (by rw [h1]; exact hle) ?_
    rw [h1]; exact EnvL.pre hp h

theorem NodeTerm.pre {P P' : G4Prog} {ev ev' : Array Nat} {oc : Nat → Expr} {pc e : Nat} {u : Expr}
    (hx : ExtR P P') (hp : Pre ev ev') (h : NodeTerm P ev oc pc e u) : NodeTerm P' ev' oc pc e u := by
  obtain ⟨s, cs, hd, he, hb, rfl⟩ := h
  exact ⟨s, cs, hd.ext hx, he.pre hp, hb, rfl⟩

theorem entryTerm_ext {P P' : G4Prog} (hx : ExtR P P') {k : Nat} (hk : k < P.kInfo.size) :
    entryTerm P' k = entryTerm P k := by
  unfold entryTerm; rw [hx.kInfo k hk]

theorem span_pre {a a' : Array Nat} (hp : Pre a a') {start len : Nat} (h : start + len ≤ a.size) :
    span a' start len = span a start len := by
  unfold span
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact hp.2 _ (by omega)

theorem get!_congr {a b : Array Nat} {i : Nat} (h : a[i]? = b[i]?) : a[i]! = b[i]! := by
  rw [getElem!_def, getElem!_def, h]

/-- A value keeps its term when the arrays and the program are extended. -/
theorem ValDen.pre {P P' : G4Prog} {val val' ev ev' argA argA' : Array Nat} {oc : Nat → Expr}
    {v : Nat} {t : Expr} (hx : ExtR P P') (hval : Pre val val') (hev : Pre ev ev')
    (harg : Pre argA argA') (hv : 4 * v + 3 < val.size) (h : ValDen P val ev argA oc v t) :
    ValDen P' val' ev' argA' oc v t := by
  have r0 := hval.2 (4 * v) (by omega)
  have r1 := hval.2 (4 * v + 1) (by omega)
  have r2 := hval.2 (4 * v + 2) (by omega)
  have r3 := hval.2 (4 * v + 3) hv
  cases h with
  | closure h0 h2 hn =>
    obtain ⟨_, _, hd, -⟩ := id hn
    exact .closure (by rw [r0]; exact h0) (by rw [r1, get!_congr (hx.code _ hd.lt_size)]; exact h2)
      (by rw [r1, r2]; exact hn.pre hx hev)
  | ctor h0 hk hs =>
    have := ValDen.ctor (P := P') (val := val') (ev := ev') (argA := argA') (oc := oc) (v := v)
      (by rw [r0]; exact h0) (by rw [r1]; exact Nat.lt_of_lt_of_le hk hx.kInfoSize)
      (by rw [r2, r3]; exact Nat.le_trans hs harg.1)
    rwa [r1, r2, r3, entryTerm_ext hx hk, span_pre harg hs] at this
  | natLit h0 => have := ValDen.natLit (P := P') (ev := ev') (argA := argA') (oc := oc)
                   (by rw [r0]; exact h0); rwa [r1] at this
  | strLit h0 hs => exact .strLit (by rw [r0]; exact h0) (by rw [r1]; exact hx.strs_some hs)
  | pap h0 hk hs =>
    have := ValDen.pap (P := P') (val := val') (ev := ev') (argA := argA') (oc := oc) (v := v)
      (by rw [r0]; exact h0) (by rw [r1]; exact Nat.lt_of_lt_of_le hk hx.kInfoSize)
      (by rw [r2, r3]; exact Nat.le_trans hs harg.1)
    rwa [r1, r2, r3, entryTerm_ext hx hk, span_pre harg hs] at this
  | other h0 => exact .other (by rw [r0]; exact h0)

/-! ## λ telescopes -/

/-- A λ node's read-back, inverted. -/
theorem Den.lam_inv {P : G4Prog} {o : Nat} {s : Expr} (h : Den P o s) (h2 : P.code[o]? = some 2) :
    ∃ b tn inner sb, P.code[o + 1]? = some b ∧ P.code[o + 2]? = some tn ∧
      P.code[o + 3]? = some inner ∧ Den P b sb ∧ s = .lam bot sb ∧
      ((P.code[b]? = some 2 ∧ P.code[b + 2]? = some (tn - 1) ∧ P.code[b + 3]? = some inner ∧
          tn ≥ 2) ∨ (P.code[b]? ≠ some 2 ∧ tn = 1 ∧ inner = b)) :=
  match h with
  | .lam _ h₁ h₂ h₃ _ hb htel => ⟨_, _, _, _, h₁, h₂, h₃, hb, rfl, htel⟩
  | .bvar h₀ _ | .spine h₀ .. | .letE h₀ .. | .const h₀ .. | .natLit h₀ _ | .strLit h₀ ..
  | .proj h₀ .. | .neutral h₀ | .shared h₀ .. => by rw [h₀] at h2; cases h2

/-- **The machine's λ walk** (`g4LamWalk`): `k ≤ tn` binders down a λ
telescope node is a node whose read-back is the telescope's body under the
remaining binders; at `k = tn` it is the node's `inner` field. -/
theorem Den.lamWalk {P : G4Prog} : ∀ (k : Nat) {o tn : Nat} {s : Expr}, Den P o s →
    P.code[o]? = some 2 → P.code[o + 2]? = some tn → k ≤ tn →
    ∃ sb, Den P (g4LamWalk P.code k o) sb ∧ s = lams k sb ∧
      (k = tn → P.code[o + 3]? = some (g4LamWalk P.code k o))
  | 0, o, tn, s, h, h2, htn, _ => by
    refine ⟨s, h, rfl, fun hk => ?_⟩
    obtain ⟨b, tn', inner, sb, -, htn', hin, -, -, htel⟩ := h.lam_inv h2
    rw [htn] at htn'; cases htn'
    rcases htel with ⟨-, -, -, h⟩ | ⟨-, h, -⟩ <;> omega
  | k + 1, o, tn, s, h, h2, htn, hk => by
    obtain ⟨b, tn', inner, sb, hb, htn', hin, hdb, rfl, htel⟩ := h.lam_inv h2
    rw [htn] at htn'; cases htn'
    have hwalk : g4LamWalk P.code (k + 1) o = g4LamWalk P.code k b := by
      show g4LamWalk P.code k P.code[o + 1]! = _; rw [get!_of_some hb]
    rw [hwalk]
    rcases htel with ⟨hb2, hbtn, hbin, htn2⟩ | ⟨-, rfl, rfl⟩
    · obtain ⟨sb', hd', rfl, hin'⟩ := Den.lamWalk k hdb hb2 hbtn (by omega)
      refine ⟨sb', hd', rfl, fun hkt => ?_⟩
      rw [hin, ← Option.some.inj (hbin.symm.trans (hin' (by omega)))]
    · obtain rfl : k = 0 := by omega
      exact ⟨sb, hdb, rfl, fun _ => hin⟩

/-! ## Argument frames and the known call -/

/-- Argument frames on top are the focus applied to their origins. -/
theorem K.args (env : Env) (t₀ : Expr) (P : G4Prog) (argA : Array Nat) (oc : Nat → Expr) :
    ∀ (cs : List Nat) (fl : List Fr) (u : Expr),
      K env t₀ P argA oc (cs.map Fr.arg ++ fl) u ↔ K env t₀ P argA oc fl (Expr.mkAppN u (cs.map oc))
  | [], _, _ => Iff.rfl
  | c :: cs, fl, u => K.args env t₀ P argA oc cs fl (.app u (oc c))

theorem getElem!_pop {a : Array Nat} {i : Nat} (h : i < a.size - 1) : a.pop[i]! = a[i]! := by
  rw [getElem!_pos a.pop i (by simp; omega), getElem!_pos a i (by omega), Array.getElem_pop]

/-- A parse reads only below its top: popping above it keeps it. -/
theorem FS.pop {fs : Array Nat} : ∀ {t : Nat} {fl : List Fr}, t ≤ fs.size - 1 → FS fs t fl →
    FS fs.pop t fl
  | _, _, _, .nil => .nil
  | _, _, hle, .arg h hr => by
    rw [← getElem!_pop (by omega)] at h ⊢; exact .arg h (FS.pop (by omega) hr)
  | _, _, hle, .upd h hr => by
    rw [← getElem!_pop (by omega)] at h ⊢; exact .upd h (FS.pop (by omega) hr)
  | _, _, hle, .iota h hr => by
    rw [← getElem!_pop (by omega)] at h
    rw [← getElem!_pop (a := fs) (by omega), ← getElem!_pop (a := fs) (i := _ + 1) (by omega),
      ← getElem!_pop (a := fs) (i := _ + 2) (by omega)]
    exact .iota h (FS.pop (by omega) hr)
  | _, _, hle, .proj h hr => by
    rw [← getElem!_pop (by omega)] at h
    rw [← getElem!_pop (a := fs) (by omega)]
    exact .proj h (FS.pop (by omega) hr)
  | _, _, hle, .natA h hr => by
    rw [← getElem!_pop (by omega)] at h
    rw [← getElem!_pop (a := fs) (by omega), ← getElem!_pop (a := fs) (i := _ + 1) (by omega),
      ← getElem!_pop (a := fs) (i := _ + 2) (by omega)]
    exact .natA h (FS.pop (by omega) hr)
  | _, _, hle, .natB h hr => by
    rw [← getElem!_pop (by omega)] at h
    rw [← getElem!_pop (a := fs) (by omega), ← getElem!_pop (a := fs) (i := _ + 1) (by omega),
      ← getElem!_pop (a := fs) (i := _ + 2) (by omega), ← getElem!_pop (a := fs) (i := _ + 3) (by omega)]
    exact .natB h (FS.pop (by omega) hr)
  | _, _, hle, .succ h hr => by
    rw [← getElem!_pop (by omega)] at h; exact .succ h (FS.pop (by omega) hr)

theorem g4PopN_size : ∀ (fs : Array Nat) (k : Nat), (g4PopN fs k).size = fs.size - k
  | _, 0 => by simp [g4PopN]
  | fs, k + 1 => by simp only [g4PopN]; rw [g4PopN_size]; simp; omega

/-- **Popping `k` words** above a parse keeps it. -/
theorem FS.popN : ∀ (k : Nat) {fs : Array Nat} {t : Nat} {fl : List Fr}, t ≤ fs.size - k → FS fs t fl →
    FS (g4PopN fs k) t fl
  | 0, _, _, _, _, h => h
  | k + 1, fs, _, _, hle, h => by
    simp only [g4PopN]
    exact FS.popN k (by simp; omega) (h.pop (by omega))

/-- The top argument frames of a parse: `n` of them, read off their words. -/
theorem FS.argsTop {fs : Array Nat} : ∀ (n : Nat) {t : Nat} {cs : List Nat} {fl : List Fr},
    FS fs t (cs.map Fr.arg ++ fl) → cs.length = n → n ≤ t ∧ FS fs (t - n) fl ∧
      ∀ j, j < n → cs.getD j 0 = fs[t - 1 - j]! >>> 4
  | 0, t, cs, fl, h, hl => by
    obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero hl
    exact ⟨Nat.zero_le _, by simpa using h, fun j hj => absurd hj (by omega)⟩
  | n + 1, _, c :: cs, fl, h, hl => by
    cases h with
    | @arg t _ ht hr =>
      obtain ⟨hn, hfs, hcs⟩ := FS.argsTop n hr (by simpa using hl)
      refine ⟨by omega, by simpa [show t + 1 - (n + 1) = t - n by omega] using hfs, fun j hj => ?_⟩
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.getD_cons_succ]
        rw [hcs j (by omega)]; congr 2; omega

/-- The cell of the `j`-th argument frame from the top. -/
@[expose] def frameCell (fs : Array Nat) (j : Nat) : Nat := fs[fs.size - 1 - j]! >>> 4

/-- One new environment record over `env`. -/
theorem EnvL.record {ev : Array Nat} {env : Nat} {cs : List Nat} (h2 : ev.size % 2 = 0)
    (hle : env ≤ ev.size / 2) (h : EnvL ev env cs) (c : Nat) :
    EnvL ((ev.push c).push env) (ev.size / 2 + 1) (c :: cs) := by
  have hi : 2 * (ev.size / 2) = ev.size := by omega
  have r1 : ((ev.push c).push env)[2 * (ev.size / 2) + 1]! = env := by
    rw [hi, show ev.size + 1 = (ev.push c).size by simp]; exact getElem!_push_eq' _ _
  have r0 : ((ev.push c).push env)[2 * (ev.size / 2)]! = c := by
    rw [hi, getElem!_push_lt' (by simp), getElem!_push_eq']
  have hsz : ((ev.push c).push env).size = ev.size + 2 := by simp
  have hc := EnvL.cons (ev := (ev.push c).push env) (i := ev.size / 2) (cs := cs) (by rw [hsz]; omega)
    (by rw [r1]; exact hle) (by rw [r1]; exact h.pre ((Pre.push _ _).trans (Pre.push _ _)))
  rwa [r0] at hc

theorem rev_range_succ (f : Nat → Nat) (k : Nat) :
    (List.range (k + 1)).reverse.map f = (List.range k).reverse.map (fun i => f (i + 1)) ++ [f 0] := by
  rw [List.range_succ_eq_map, List.reverse_cons, List.map_append, List.map_reverse, List.map_reverse,
    List.map_map]
  rfl

/-- **Binding the top `k` argument frames** (`g4BindFrames`, from the `j`-th):
the records extend the environment by those cells, the last innermost. -/
theorem bindFrames_spec (fs : Array Nat) : ∀ (k j env : Nat) (ev : Array Nat) (cs : List Nat),
    ev.size % 2 = 0 → env ≤ ev.size / 2 → EnvL ev env cs →
    Pre ev (g4BindFrames fs ev k j env) ∧ (g4BindFrames fs ev k j env).size = ev.size + 2 * k ∧
      EnvL (g4BindFrames fs ev k j env) (if k = 0 then env else (g4BindFrames fs ev k j env).size / 2)
        ((List.range k).reverse.map (fun i => frameCell fs (j + i)) ++ cs)
  | 0, _, _, ev, _, _, _, h => ⟨Pre.refl ev, by show ev.size = _; omega,
      by show EnvL ev _ _; simpa using h⟩
  | k + 1, j, env, ev, cs, h2, hle, h => by
    simp only [g4BindFrames]
    have hrec := EnvL.record h2 hle h (fs[fs.size - 1 - j]! >>> 4)
    have hsz : ((ev.push (fs[fs.size - 1 - j]! >>> 4)).push env).size = ev.size + 2 := by simp
    have hshr : ev.size >>> 1 = ev.size / 2 := Nat.shiftRight_eq_div_pow _ _
    rw [hshr]
    obtain ⟨hp, hs, he⟩ := bindFrames_spec fs k (j + 1) (ev.size / 2 + 1) _ _ (by rw [hsz]; omega)
      (by rw [hsz]; omega) hrec
    refine ⟨((Pre.push _ _).trans (Pre.push _ _)).trans hp, by rw [hs, hsz]; omega, ?_⟩
    have hlist : (List.range k).reverse.map (fun i => frameCell fs (j + 1 + i)) ++
        (fs[fs.size - 1 - j]! >>> 4) :: cs =
        (List.range (k + 1)).reverse.map (fun i => frameCell fs (j + i)) ++ cs := by
      rw [rev_range_succ (fun i => frameCell fs (j + i)) k, List.append_assoc]
      simp only [frameCell, Nat.add_zero, List.singleton_append]
      congr 2
      funext i; congr 3; omega
    rw [← hlist]
    split at he
    · rename_i hk0; subst hk0
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show (g4BindFrames fs ((ev.push (fs[fs.size - 1 - j]! >>> 4)).push env) 0 (j + 1)
          (ev.size / 2 + 1)).size / 2 = ev.size / 2 + 1 by simp [g4BindFrames]; omega]
      exact he
    · simpa using he

/-! ## Cells, and the first transitions -/

section
variable (env : Env) (t₀ : Expr) (P : G4Prog) (val ev argA : Array Nat) (oc : Nat → Expr)

/-- **A cell's invariant** (`[state, code, env, _]` at `4 c`): a thunk is its
node under its environment; a busy cell's claim is on the stack (its update
frame); a value cell's origin reduces to its value's term. -/
@[expose] def CellOK (cel : Array Nat) (c : Nat) : Prop :=
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
