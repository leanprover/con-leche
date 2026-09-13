module

public import ConLeche.Verify.Inductives.NestedLedger

public section

/-!
# The walk, inverted (task #279 M-B′ step 3m, DESIGN §M.29 finding 5)

`replaceAllNested` is a top-down replace: at every node it first asks
`replaceIfNested` (a nested occurrence `I Ds is` of a stored container
becomes `auxI p⃗ is`, minting `I`'s group on a pin miss), and only when
that declines does it visit the children.  The model's constructor
read needs the walk's INPUT back from its OUTPUT, field by field:

* **W1 — an output that mentions none of the elimination's names is
  its input** (`replaceAllNested_eq_of_unmentioned`): a fire's output
  has a copy's name at its head, and every pin's name is a name of the
  growing type list (`PinsNamed`, kept by every mint); so a
  new-name-free output saw no fire, and the structural arms copy the
  input.

The invariant `ElimState.PinsNamed` is the piece of the ledger this
needs: every pin's `aux` is a type name of the state, kept across
`ElimGrows` (a mint appends the copies and their pins together).
-/

namespace ConLeche

/-! ## Pins are named by types -/

/-- Every pin's copy name is a name of the growing type list. -/
def ElimState.PinsNamed (st : ElimState) : Prop :=
  ∀ q ∈ st.pins, q.aux ∈ st.newNames

/-- The type names only grow. -/
theorem ElimGrows.newNames_mono {st st' : ElimState} (h : ElimGrows st st') :
    ∀ T ∈ st.newNames, T ∈ st'.newNames := by
  obtain ⟨new, -, hnames⟩ := h
  intro T hT
  show T ∈ st'.types.map (·.name)
  rw [hnames]
  exact List.mem_append_left _ hT

/-- `PinsNamed` across a growth: the old pins' names are kept, the new
pins' names are the appended types'. -/
theorem ElimState.PinsNamed.grows {st st' : ElimState} (hpn : st.PinsNamed)
    (h : ElimGrows st st') : st'.PinsNamed := by
  obtain ⟨new, hpins, hnames⟩ := h
  intro q hq
  show q.aux ∈ st'.types.map (·.name)
  rw [hnames, hpins] at *
  rcases List.mem_append.mp hq with hq | hq
  · exact List.mem_append_left _ (hpn q hq)
  · exact List.mem_append_right _ (List.mem_map_of_mem hq)

/-- The initial state has no pins. -/
theorem ElimState.PinsNamed.init (types : List AuxType) (n : Nat) :
    ElimState.PinsNamed ⟨types, [], n⟩ :=
  fun _ hq => nomatch hq

/-! ## Mentions of a spine's head -/

/-- A spine mentions what its head mentions. -/
theorem Expr.mentionsConst_mkAppN_of_head {T : Name} :
    ∀ (as : List Expr) (f : Expr), f.mentionsConst T = true →
      (Expr.mkAppN f as).mentionsConst T = true
  | [], _, h => h
  | a :: as, f, h => by
    show (Expr.mkAppN (.app f a) as).mentionsConst T = true
    refine mentionsConst_mkAppN_of_head as (.app f a) ?_
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact Or.inl h

/-- A fire's output mentions the copy it names. -/
theorem replaceIfNested_mentions {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {e r : Expr}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st')))
    (hpn : st.PinsNamed) :
    ∃ T ∈ st'.newNames, r.mentionsConst T = true := by
  obtain ⟨I, lvls, ci, aux, -, -, -, hr, q, hq, hqa, -⟩ := replaceIfNested_some h
  have hpn' : st'.PinsNamed := hpn.grows (replaceIfNested_grows h r st' rfl)
  refine ⟨aux, by rw [← hqa]; exact hpn' q hq, ?_⟩
  rw [hr]
  refine Expr.mentionsConst_mkAppN_of_head _ _ (Expr.mentionsConst_mkAppN_of_head _ _ ?_)
  simp [Expr.mentionsConst]

/-! ## W1: an unmentioning output is its input -/

/-- **W1.**  An output of the walk mentioning none of the final state's
names is the input: no fire happened at any node (a fire's output
mentions a copy's name, `replaceIfNested_mentions`), and the
structural arms copy the input. -/
theorem replaceAllNested_eq_of_unmentioned {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') → st.PinsNamed →
      (∀ T ∈ st'.newNames, e'.mentionsConst T = false) → e' = e
  | .app f a, st, st', e', h, hpn, hm => by
    rcases replaceAllNested_app h with hfire | ⟨f', a', st₁, hf, ha, rfl⟩
    · obtain ⟨T, hT, hmT⟩ := replaceIfNested_mentions hfire hpn
      rw [hm T hT] at hmT
      exact nomatch hmT
    · have hg₁ := replaceAllNested_grows f hf
      have hg₂ := replaceAllNested_grows a ha
      have hf' : f' = f := replaceAllNested_eq_of_unmentioned f hf hpn fun T hT => by
        have := hm T (hg₂.newNames_mono T hT)
        simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
        exact this.1
      have ha' : a' = a := replaceAllNested_eq_of_unmentioned a ha (hpn.grows hg₁) fun T hT => by
        have := hm T hT
        simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
        exact this.2
      rw [hf', ha']
  | .lam ty b bm, st, st', e', h, hpn, hm => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_lam h
    have hg₁ := replaceAllNested_grows ty hty
    have hg₂ := replaceAllNested_grows b hb
    have hty' : ty' = ty := replaceAllNested_eq_of_unmentioned ty hty hpn fun T hT => by
      have := hm T (hg₂.newNames_mono T hT)
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.1
    have hb' : b' = b := replaceAllNested_eq_of_unmentioned b hb (hpn.grows hg₁) fun T hT => by
      have := hm T hT
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.2
    rw [hty', hb']
  | .forallE ty b bm, st, st', e', h, hpn, hm => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_forallE h
    have hg₁ := replaceAllNested_grows ty hty
    have hg₂ := replaceAllNested_grows b hb
    have hty' : ty' = ty := replaceAllNested_eq_of_unmentioned ty hty hpn fun T hT => by
      have := hm T (hg₂.newNames_mono T hT)
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.1
    have hb' : b' = b := replaceAllNested_eq_of_unmentioned b hb (hpn.grows hg₁) fun T hT => by
      have := hm T hT
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.2
    rw [hty', hb']
  | .letE ty v b, st, st', e', h, hpn, hm => by
    rw [replaceAllNested] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.letE ty v b) = .ok none from rfl] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next ty' st₁ hty =>
        split at h
        · exact nomatch h
        · next v' st₂ hv =>
          split at h
          · exact nomatch h
          · next b' st₃ hb =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hg₁ := replaceAllNested_grows ty hty
            have hg₂ := replaceAllNested_grows v hv
            have hg₃ := replaceAllNested_grows b hb
            have hty' : ty' = ty := replaceAllNested_eq_of_unmentioned ty hty hpn fun T hT => by
              have := hm T (hg₃.newNames_mono T (hg₂.newNames_mono T hT))
              simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
              exact this.1.1
            have hv' : v' = v := replaceAllNested_eq_of_unmentioned v hv (hpn.grows hg₁)
              fun T hT => by
                have := hm T (hg₃.newNames_mono T hT)
                simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
                exact this.1.2
            have hb' : b' = b := replaceAllNested_eq_of_unmentioned b hb
              ((hpn.grows hg₁).grows hg₂) fun T hT => by
                have := hm T hT
                simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
                exact this.2
            rw [hty', hv', hb']
  | .proj s i x, st, st', e', h, hpn, hm => by
    rw [replaceAllNested] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.proj s i x) = .ok none from rfl] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next x' st₁ hx =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hx' : x' = x := replaceAllNested_eq_of_unmentioned x hx hpn fun T hT => by
          have := hm T hT
          simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
          exact this.2
        rw [hx']
  | .bvar i, st, st', e', h, _, _ => by
    unfold replaceAllNested at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.bvar i) = .ok none from rfl] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | .fvar idx ty, st, st', e', h, _, _ => by
    unfold replaceAllNested at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.fvar idx ty) = .ok none from rfl] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | .sort u, st, st', e', h, _, _ => by
    unfold replaceAllNested at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.sort u) = .ok none from rfl] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | .const n us, st, st', e', h, _, _ => by
    unfold replaceAllNested at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.const n us) = .ok none from rfl] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  | .lit l, st, st', e', h, _, _ => by
    unfold replaceAllNested at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · rw [show replaceIfNested env blvls params pbs st (.lit l) = .ok none from rfl] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

end ConLeche
