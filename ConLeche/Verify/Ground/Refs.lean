module

public import ConLeche.Verify.Ground.Machine

public section

/-!
# References: every reading names allocated cells (task #423 soundness, layer (b))

The ghost origin assignment `oc` is fixed only on the allocated cells
(`c < N`, `N` the cell count).  A new cell gets its origin by extending `oc`
at `N` (`ocExt`); every reading of the state keeps its meaning because it
names allocated cells only: environment records (`EvRef`), argument spans
(`ArgRef`) and frames (`FrOK`).  This file proves the readings' congruence
under agreement below `N`, and their stability when the arrays and the
program grow (`Pre`, `Ext`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- Every environment record names an allocated cell and an older environment. -/
@[expose] def EvRef (ev : Array Nat) (N : Nat) : Prop :=
  ∀ i, 2 * i + 1 < ev.size → ev[2 * i]! < N ∧ ev[2 * i + 1]! ≤ i

/-- Every argument-span entry is an allocated cell. -/
@[expose] def ArgRef (argA : Array Nat) (N : Nat) : Prop := ∀ j, j < argA.size → argA[j]! < N

/-- Two origin assignments agree on the allocated cells. -/
@[expose] def Agree (oc oc' : Nat → Expr) (N : Nat) : Prop := ∀ c, c < N → oc c = oc' c

/-- The origin assignment extended at the new cell `N`. -/
@[expose] def ocExt (oc : Nat → Expr) (N : Nat) (t : Expr) : Nat → Expr := fun c => if c = N then t else oc c

theorem Agree.ext (oc : Nat → Expr) (N : Nat) (t : Expr) : Agree oc (ocExt oc N t) N :=
  fun c hc => by simp [ocExt, Nat.ne_of_lt hc]

theorem Agree.refl (oc : Nat → Expr) (N : Nat) : Agree oc oc N := fun _ _ => rfl

theorem ocExt_self (oc : Nat → Expr) (N : Nat) (t : Expr) : ocExt oc N t N = t := by simp [ocExt]

/-! ## Environments -/

/-- A chain's cells are allocated. -/
theorem EnvL.mem_lt {ev : Array Nat} {N : Nat} (hr : EvRef ev N) : ∀ {e : Nat} {cs : List Nat},
    EnvL ev e cs → ∀ c ∈ cs, c < N
  | _, _, .nil => by simp
  | _, _, @EnvL.cons _ i _ hlt _ h => by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact (hr i hlt).1
    · exact EnvL.mem_lt hr h c hc

/-- Every environment index up to the record count has its chain. -/
theorem EnvL.of_ref {ev : Array Nat} {N : Nat} (hr : EvRef ev N) :
    ∀ e, e ≤ ev.size / 2 → ∃ cs, EnvL ev e cs := by
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro he
    match e, ih, he with
    | 0, _, _ => exact ⟨[], .nil⟩
    | i + 1, ih, he =>
      have hlt : 2 * i + 1 < ev.size := by omega
      have hle := (hr i hlt).2
      obtain ⟨cs, hcs⟩ := ih ev[2 * i + 1]! (by omega) (by omega)
      exact ⟨_, .cons hlt hle hcs⟩

/-- `g4EnvGet` reads a chain. -/
theorem EnvL.get {ev : Array Nat} : ∀ {e : Nat} {cs : List Nat}, EnvL ev e cs →
    ∀ i, i < cs.length → g4EnvGet ev e i = cs.getD i 0
  | _, _, .nil, i, h => by simp at h
  | _, _, @EnvL.cons _ j _ _ _ h, 0, _ => by
    show ev[j + j]! = _
    rw [show j + j = 2 * j by omega]; rfl
  | _, _, @EnvL.cons _ j _ _ _ h, i + 1, hi => by
    show g4EnvGet ev ev[j + j + 1]! i = _
    rw [show j + j + 1 = 2 * j + 1 by omega, EnvL.get h i (by simpa using hi)]
    rfl

theorem EvRef.push2 {ev : Array Nat} {N N' : Nat} (hr : EvRef ev N) (h2 : ev.size % 2 = 0)
    (hN : N ≤ N') {c e : Nat} (hc : c < N') (he : e ≤ ev.size / 2) :
    EvRef ((ev.push c).push e) N' := by
  intro i hi
  simp only [Array.size_push] at hi
  rcases Nat.lt_or_ge (2 * i + 1) ev.size with h | h
  · rw [getElem!_push_lt' (by simp; omega), getElem!_push_lt' (by omega),
      getElem!_push_lt' (by simp; omega), getElem!_push_lt' (by omega)]
    exact ⟨Nat.lt_of_lt_of_le (hr i h).1 hN, (hr i h).2⟩
  · have hi' : 2 * i = ev.size := by omega
    rw [hi', getElem!_push_lt' (by simp), getElem!_push_eq', show ev.size + 1 = (ev.push c).size by simp,
      getElem!_push_eq']
    exact ⟨hc, by omega⟩

theorem EvRef.mono {ev : Array Nat} {N N' : Nat} (hr : EvRef ev N) (hN : N ≤ N') : EvRef ev N' :=
  fun i hi => ⟨Nat.lt_of_lt_of_le (hr i hi).1 hN, (hr i hi).2⟩

theorem ArgRef.mono {argA : Array Nat} {N N' : Nat} (hr : ArgRef argA N) (hN : N ≤ N') :
    ArgRef argA N' := fun j hj => Nat.lt_of_lt_of_le (hr j hj) hN

theorem ArgRef.push {argA : Array Nat} {N c : Nat} (hr : ArgRef argA N) (hc : c < N) :
    ArgRef (argA.push c) N := by
  intro j hj
  simp only [Array.size_push] at hj
  rcases Nat.lt_or_ge j argA.size with h | h
  · rw [getElem!_push_lt' h]; exact hr j h
  · rw [show j = argA.size by omega, getElem!_push_eq']; exact hc

/-! ## Congruence of the readings -/

theorem map_agree {oc oc' : Nat → Expr} {N : Nat} (ha : Agree oc oc' N) {cs : List Nat}
    (h : ∀ c ∈ cs, c < N) : cs.map oc = cs.map oc' :=
  List.map_congr_left fun c hc => ha c (h c hc)

theorem NodeTerm.congr {P : G4Prog} {ev : Array Nat} {oc oc' : Nat → Expr} {N pc e : Nat} {u : Expr}
    (hr : EvRef ev N) (ha : Agree oc oc' N) (h : NodeTerm P ev oc pc e u) :
    NodeTerm P ev oc' pc e u := by
  obtain ⟨s, cs, hd, he, hb, rfl⟩ := h
  exact ⟨s, cs, hd, he, hb, by rw [map_agree ha (EnvL.mem_lt hr he)]⟩

theorem span_mem_lt {argA : Array Nat} {N : Nat} (hr : ArgRef argA N) {start len : Nat}
    (hs : start + len ≤ argA.size) : ∀ c ∈ span argA start len, c < N := by
  intro c hc
  simp only [span, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  exact hr _ (by omega)

theorem ValDen.congr {P : G4Prog} {val ev argA : Array Nat} {oc oc' : Nat → Expr} {N v : Nat}
    {t : Expr} (hr : EvRef ev N) (hg : ArgRef argA N) (ha : Agree oc oc' N)
    (h : ValDen P val ev argA oc v t) : ValDen P val ev argA oc' v t := by
  cases h with
  | closure h0 h2 hn => exact .closure h0 h2 (hn.congr hr ha)
  | ctor h0 hk hs => rw [map_agree ha (span_mem_lt hg hs)]; exact .ctor h0 hk hs
  | natLit h0 => exact .natLit h0
  | strLit h0 hs => exact .strLit h0 hs
  | pap h0 hk hs => rw [map_agree ha (span_mem_lt hg hs)]; exact .pap h0 hk hs
  | other h0 => exact .other h0

/-- **A frame names allocated cells**, a span inside the argument array, a
table entry and a projection the program has. -/
@[expose] def FrOK (P : G4Prog) (argA : Array Nat) (N : Nat) : Fr → Prop
  | .arg c => c < N
  | .upd c => c < N
  | .iota k start len => k < P.kInfo.size ∧ 0 < len ∧ start + len ≤ argA.size ∧
      P.kTag[k]? = some 2 ∧ P.kArity[k]? = some (len - 1)
  | .proj pi => pi = 0 ∨ pi - 1 < P.projs.size
  | .natA k a b => k < P.kInfo.size ∧ a < N ∧ b < N ∧ P.kTag[k]? = some 3
  | .natB k _ a b => k < P.kInfo.size ∧ a < N ∧ b < N ∧ P.kTag[k]? = some 3
  | .succ => P.natOk = true

@[expose] def FlOK (P : G4Prog) (argA : Array Nat) (N : Nat) (fl : List Fr) : Prop := ∀ f ∈ fl, FrOK P argA N f

theorem FlOK.cons {P : G4Prog} {argA : Array Nat} {N : Nat} {f : Fr} {fl : List Fr} :
    FlOK P argA N (f :: fl) ↔ FrOK P argA N f ∧ FlOK P argA N fl := by
  simp [FlOK]

theorem K.congr (env : Env) (t₀ : Expr) (P : G4Prog) (argA : Array Nat) {oc oc' : Nat → Expr} {N : Nat}
    (hg : ArgRef argA N) (ha : Agree oc oc' N) : ∀ (fl : List Fr) {u : Expr}, FlOK P argA N fl →
    K env t₀ P argA oc fl u → K env t₀ P argA oc' fl u
  | [], _, _, h => h
  | .arg c :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    have := K.congr env t₀ P argA hg ha fl hf.2 h
    simp only [K]; rwa [← ha c hf.1]
  | .upd c :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    simp only [K] at h ⊢; rw [← ha c hf.1]
    exact ⟨h.1, K.congr env t₀ P argA hg ha fl hf.2 h.2⟩
  | .iota k start len :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    obtain ⟨-, hl, hs, -⟩ := hf.1
    simp only [K, spanTerm] at h ⊢
    rw [← ha _ (hg _ (by omega)), ← map_agree ha (span_mem_lt hg hs)]
    have := K.congr env t₀ P argA hg ha fl hf.2 h.2
    exact ⟨h.1, this⟩
  | .proj pi :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    cases pi with
    | zero => exact K.congr env t₀ P argA hg ha fl hf.2 h
    | succ q =>
      simp only [K] at h ⊢
      split at h <;> exact K.congr env t₀ P argA hg ha fl hf.2 h
  | .natA k a b :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    obtain ⟨-, hal, hbl, -⟩ := hf.1
    simp only [K, opTerm] at h ⊢
    have := K.congr env t₀ P argA hg ha fl hf.2 h.2
    rw [← ha a hal, ← ha b hbl]
    exact ⟨h.1, this⟩
  | .natB k n a b :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    obtain ⟨-, hal, hbl, -⟩ := hf.1
    simp only [K, opTerm] at h ⊢
    have := K.congr env t₀ P argA hg ha fl hf.2 h.2.2
    rw [← ha a hal, ← ha b hbl]
    exact ⟨h.1, h.2.1, this⟩
  | .succ :: fl, _, hf, h => by
    rw [FlOK.cons] at hf
    exact ⟨K.congr env t₀ P argA hg ha fl hf.2 h.1,
      fun w n hw hn => K.congr env t₀ P argA hg ha fl hf.2 (h.2 w n hw hn)⟩

/-! ## Growth: the program and the arrays extended -/

theorem FrOK.grow {P P' : G4Prog} {argA argA' : Array Nat} {N N' : Nat} (hx : ExtR P P')
    (hp : Pre argA argA') (hN : N ≤ N') : ∀ {f : Fr}, FrOK P argA N f → FrOK P' argA' N' f
  | .arg _, h => Nat.lt_of_lt_of_le h hN
  | .upd _, h => Nat.lt_of_lt_of_le h hN
  | .iota .., ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨Nat.lt_of_lt_of_le h₁ hx.kInfoSize, h₂, Nat.le_trans h₃ hp.1,
      by rw [(entR_eq (hx.ent _ h₁)).1]; exact h₄, by rw [(entR_eq (hx.ent _ h₁)).2.1]; exact h₅⟩
  | .proj pi, h => by
    rcases h with h | h
    · exact .inl h
    · refine .inr ?_
      have := hx.projs _ h
      rcases Nat.lt_or_ge (pi - 1) P'.projs.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at this; simp [Array.getElem?_eq_getElem h] at this
  | .natA .., ⟨h₁, h₂, h₃, h₄⟩ => ⟨Nat.lt_of_lt_of_le h₁ hx.kInfoSize, Nat.lt_of_lt_of_le h₂ hN,
      Nat.lt_of_lt_of_le h₃ hN, by rw [(entR_eq (hx.ent _ h₁)).1]; exact h₄⟩
  | .natB .., ⟨h₁, h₂, h₃, h₄⟩ => ⟨Nat.lt_of_lt_of_le h₁ hx.kInfoSize, Nat.lt_of_lt_of_le h₂ hN,
      Nat.lt_of_lt_of_le h₃ hN, by rw [(entR_eq (hx.ent _ h₁)).1]; exact h₄⟩
  | .succ, h => by show P'.natOk = true; rw [hx.natOk]; exact h

theorem FlOK.grow {P P' : G4Prog} {argA argA' : Array Nat} {N N' : Nat} (hx : ExtR P P')
    (hp : Pre argA argA') (hN : N ≤ N') {fl : List Fr} (h : FlOK P argA N fl) :
    FlOK P' argA' N' fl := fun f hf => (h f hf).grow hx hp hN

theorem K.grow (env : Env) (t₀ : Expr) {P P' : G4Prog} {argA argA' : Array Nat} (oc : Nat → Expr)
    {N : Nat} (hx : ExtR P P') (hp : Pre argA argA') :
    ∀ (fl : List Fr) {u : Expr}, FlOK P argA N fl →
    K env t₀ P argA oc fl u → K env t₀ P' argA' oc fl u
  | [], _, _, h => h
  | .arg _ :: fl, _, hf, h => K.grow env t₀ oc hx hp fl (FlOK.cons.mp hf).2 h
  | .upd _ :: fl, _, hf, h => ⟨h.1, K.grow env t₀ oc hx hp fl (FlOK.cons.mp hf).2 h.2⟩
  | .iota k start len :: fl, _, hf, h => by
    obtain ⟨⟨hk, hl, hs, -⟩, hf⟩ := FlOK.cons.mp hf
    simp only [K, spanTerm] at h ⊢
    rw [hp.2 _ (by omega), span_pre hp hs, entryTerm_ext hx hk,
      get!_congr (entR_eq (hx.ent k hk)).2.2.2.2.2]
    have := K.grow env t₀ oc hx hp fl hf h.2
    exact ⟨h.1, this⟩
  | .proj pi :: fl, _, hf, h => by
    obtain ⟨hpi, hf'⟩ := FlOK.cons.mp hf
    cases pi with
    | zero => exact K.grow env t₀ oc hx hp fl hf' h
    | succ q =>
      have hq : q < P.projs.size := by rcases hpi with h | h <;> simp_all
      simp only [K] at h ⊢
      rw [hx.projs q hq]
      split at h <;> exact K.grow env t₀ oc hx hp fl hf' h
  | .natA k a b :: fl, _, hf, h => by
    obtain ⟨⟨hk, -, -, -⟩, hf⟩ := FlOK.cons.mp hf
    simp only [K, opTerm] at h ⊢
    have := K.grow env t₀ oc hx hp fl hf h.2
    rw [entryTerm_ext hx hk]
    exact ⟨h.1, this⟩
  | .natB k n a b :: fl, _, hf, h => by
    obtain ⟨⟨hk, -, -, -⟩, hf⟩ := FlOK.cons.mp hf
    simp only [K, opTerm] at h ⊢
    have := K.grow env t₀ oc hx hp fl hf h.2.2
    rw [entryTerm_ext hx hk]
    exact ⟨h.1, h.2.1, this⟩
  | .succ :: fl, _, hf, h => ⟨K.grow env t₀ oc hx hp fl (FlOK.cons.mp hf).2 h.1, fun w n hw hn =>
    K.grow env t₀ oc hx hp fl (FlOK.cons.mp hf).2 (h.2 w n hw hn)⟩

end ConLeche.Verify.Ground
