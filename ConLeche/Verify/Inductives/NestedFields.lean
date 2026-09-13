module

public import ConLeche.Verify.Inductives.NestedWalk
public section

/-!
# The walk, field by field (task #279 M-B′ step 3n, DESIGN §M.31)

The model's constructor read (`Model/Inductives/CopyCtors.lean`'s
record) compares a copy's STORED constructor with the container's,
one field domain at a time.  The walk `replaceAllNested` runs on the
minted constructor as ONE term — the Π-tower over its parameters and
fields — so its inversions (W1/W2, `NestedWalk.lean`) have to be
applied per field.  This module supplies the two pieces:

* **`PinsCopyNamed k st`** and **W1 over the copy names**
  (`replaceAllNested_eq_of_no_copy`): `NestedWalk`'s W1 asks the output
  to mention NONE of the state's type names, the block's own members
  included; a copy field the copy sees as recursive into a BLOCK MEMBER
  (the λ-pin's `(fun _ => PT α) k ↦ PT α`, `ord`'s second arm) mentions
  that member, so W1 as stated does not reach it.  A fire's output
  mentions the COPY it names (the pin's `aux` is a type at index `≥ k`
  of the state — the block's own `k` types come first and every mint
  appends), so it is enough that the output mentions no COPY name.
* **The per-field decomposition** (`replaceAllNested_stripPis`): the
  walk of `Π bs, r` is `Π bs', r'` with every binder's domain and the
  residual walked separately, each from a state the earlier ones left
  and reaching a state the later ones start from (`ElimGrows` both
  ways), the binder data kept.  The walk is a congruence at a Π
  (`replaceAllNested_forallE`); this is that congruence iterated along
  `stripPis`.
-/

namespace ConLeche

/-! ## Pins are named by copies -/

/-- **Every pin's copy name is a type of the state at index `≥ k`** —
the block's own `k` types come first, every mint appends. -/
def ElimState.PinsCopyNamed (k : Nat) (st : ElimState) : Prop :=
  k ≤ st.types.length ∧ ∀ q ∈ st.pins, q.aux ∈ (st.types.map (·.name)).drop k

/-- The copy names only grow. -/
theorem ElimGrows.copyNames_mono {st st' : ElimState} (h : ElimGrows st st') (k : Nat)
    (hk : k ≤ st.types.length) :
    ∀ T ∈ (st.types.map (·.name)).drop k, T ∈ (st'.types.map (·.name)).drop k := by
  obtain ⟨new, -, hnames⟩ := h
  intro T hT
  rw [hnames, List.drop_append_of_le_length (by rw [List.length_map]; exact hk)]
  exact List.mem_append_left _ hT

/-- The type list only grows. -/
theorem ElimGrows.types_length_le {st st' : ElimState} (h : ElimGrows st st') :
    st.types.length ≤ st'.types.length := by
  obtain ⟨new, -, hnames⟩ := h
  have := congrArg List.length hnames
  simp only [List.length_map, List.length_append] at this
  omega

/-- `PinsCopyNamed` across a growth: the old pins' names are kept, the
new pins' names are the appended types', all at index `≥ k`. -/
theorem ElimState.PinsCopyNamed.grows {k : Nat} {st st' : ElimState} (hpn : st.PinsCopyNamed k)
    (h : ElimGrows st st') : st'.PinsCopyNamed k := by
  obtain ⟨hk, hpins⟩ := hpn
  refine ⟨Nat.le_trans hk h.types_length_le, ?_⟩
  obtain ⟨new, hpins', hnames⟩ := h
  intro q hq
  rw [hpins'] at hq
  rw [hnames, List.drop_append_of_le_length (by rw [List.length_map]; exact hk)]
  rcases List.mem_append.mp hq with hq | hq
  · exact List.mem_append_left _ (hpins q hq)
  · exact List.mem_append_right _ (List.mem_map_of_mem hq)

/-- The initial state has no pins. -/
theorem ElimState.PinsCopyNamed.init (types : List AuxType) (n : Nat) :
    ElimState.PinsCopyNamed types.length ⟨types, [], n⟩ :=
  ⟨Nat.le_refl _, fun _ hq => nomatch hq⟩

/-- A fire's output mentions the copy it names, a copy name of the
state it leaves. -/
theorem replaceIfNested_mentions_copy {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {e r : Expr} {k : Nat}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st')))
    (hpn : st.PinsCopyNamed k) :
    ∃ T ∈ (st'.types.map (·.name)).drop k, r.mentionsConst T = true := by
  obtain ⟨I, lvls, ci, aux, -, -, -, hr, q, hq, hqa, -⟩ := replaceIfNested_some h
  have hpn' : st'.PinsCopyNamed k := hpn.grows (replaceIfNested_grows h r st' rfl)
  refine ⟨aux, by rw [← hqa]; exact hpn'.2 q hq, ?_⟩
  rw [hr]
  refine Expr.mentionsConst_mkAppN_of_head _ _ (Expr.mentionsConst_mkAppN_of_head _ _ ?_)
  simp [Expr.mentionsConst]

/-! ## W1 over the copy names -/

/-- **W1, over the copy names.**  An output of the walk mentioning none
of the final state's COPY names is the input: a fire's output mentions
the copy it names (`replaceIfNested_mentions_copy`), and the structural
arms copy the input.  `NestedWalk`'s W1 verbatim, with the block's own
member names allowed in the output. -/
theorem replaceAllNested_eq_of_no_copy {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {k : Nat} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') → st.PinsCopyNamed k →
      (∀ T ∈ (st'.types.map (·.name)).drop k, e'.mentionsConst T = false) → e' = e
  | .app f a, st, st', e', h, hpn, hm => by
    rcases replaceAllNested_app h with hfire | ⟨f', a', st₁, hf, ha, rfl⟩
    · obtain ⟨T, hT, hmT⟩ := replaceIfNested_mentions_copy hfire hpn
      rw [hm T hT] at hmT
      exact nomatch hmT
    · have hg₁ := replaceAllNested_grows f hf
      have hg₂ := replaceAllNested_grows a ha
      have hk₁ : k ≤ st₁.types.length := Nat.le_trans hpn.1 hg₁.types_length_le
      have hf' : f' = f := replaceAllNested_eq_of_no_copy f hf hpn fun T hT => by
        have := hm T (hg₂.copyNames_mono k hk₁ T hT)
        simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
        exact this.1
      have ha' : a' = a := replaceAllNested_eq_of_no_copy a ha (hpn.grows hg₁) fun T hT => by
        have := hm T hT
        simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
        exact this.2
      rw [hf', ha']
  | .lam ty b bm, st, st', e', h, hpn, hm => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_lam h
    have hg₁ := replaceAllNested_grows ty hty
    have hg₂ := replaceAllNested_grows b hb
    have hk₁ : k ≤ st₁.types.length := Nat.le_trans hpn.1 hg₁.types_length_le
    have hty' : ty' = ty := replaceAllNested_eq_of_no_copy ty hty hpn fun T hT => by
      have := hm T (hg₂.copyNames_mono k hk₁ T hT)
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.1
    have hb' : b' = b := replaceAllNested_eq_of_no_copy b hb (hpn.grows hg₁) fun T hT => by
      have := hm T hT
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.2
    rw [hty', hb']
  | .forallE ty b bm, st, st', e', h, hpn, hm => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_forallE h
    have hg₁ := replaceAllNested_grows ty hty
    have hg₂ := replaceAllNested_grows b hb
    have hk₁ : k ≤ st₁.types.length := Nat.le_trans hpn.1 hg₁.types_length_le
    have hty' : ty' = ty := replaceAllNested_eq_of_no_copy ty hty hpn fun T hT => by
      have := hm T (hg₂.copyNames_mono k hk₁ T hT)
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.1
    have hb' : b' = b := replaceAllNested_eq_of_no_copy b hb (hpn.grows hg₁) fun T hT => by
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
            have hk₁ : k ≤ st₁.types.length := Nat.le_trans hpn.1 hg₁.types_length_le
            have hk₂ : k ≤ st₂.types.length := Nat.le_trans hk₁ hg₂.types_length_le
            have hty' : ty' = ty := replaceAllNested_eq_of_no_copy ty hty hpn fun T hT => by
              have := hm T (hg₃.copyNames_mono k hk₂ T (hg₂.copyNames_mono k hk₁ T hT))
              simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
              exact this.1.1
            have hv' : v' = v := replaceAllNested_eq_of_no_copy v hv (hpn.grows hg₁)
              fun T hT => by
                have := hm T (hg₃.copyNames_mono k hk₂ T hT)
                simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
                exact this.1.2
            have hb' : b' = b := replaceAllNested_eq_of_no_copy b hb
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
        have hx' : x' = x := replaceAllNested_eq_of_no_copy x hx hpn fun T hT => by
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

/-! ## The walk over a Π-tower, field by field -/

/-- **The walk of a Π-tower is the tower of the walks**: every binder's
domain and the residual are walked separately, each from a state the
walk of the earlier ones reached and to a state the later ones start
from, the binder data kept. -/
theorem replaceAllNested_stripPis {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} :
    ∀ (n : Nat) (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') →
      ∀ {bs : List (Expr × BinderMeta)} {r : Expr}, e.stripPis n = some (bs, r) →
      ∃ (bs' : List (Expr × BinderMeta)) (r' : Expr),
        e'.stripPis n = some (bs', r') ∧ bs'.length = bs.length ∧
        (∀ (i : Nat) (b b' : Expr × BinderMeta), bs[i]? = some b → bs'[i]? = some b' →
          b'.2 = b.2 ∧ ∃ s₁ s₂ : ElimState, ElimGrows st s₁ ∧
            replaceAllNested env blvls params pbs s₁ b.1 = .ok (b'.1, s₂) ∧ ElimGrows s₂ st') ∧
        ∃ sN : ElimState, ElimGrows st sN ∧ replaceAllNested env blvls params pbs sN r = .ok (r', st')
  | 0, e, st, st', e', h, bs, r, hstrip => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstrip
    obtain ⟨rfl, rfl⟩ := hstrip
    exact ⟨[], e', rfl, rfl, fun _ _ _ hb _ => (nomatch hb), st, ElimGrows.refl st, h⟩
  | n + 1, e, st, st', e', h, bs, r, hstrip => by
    match e, hstrip with
    | .forallE ty b bm, hstrip =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstrip
      obtain ⟨⟨bs₀, r₀⟩, hstrip₀, hbs⟩ := hstrip
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_forallE h
      have hg₁ : ElimGrows st st₁ := replaceAllNested_grows ty hty
      obtain ⟨bs₀', r', hstrip', hlen, hfields, sN, hgN, hr⟩ :=
        replaceAllNested_stripPis n b hb hstrip₀
      refine ⟨(ty', bm) :: bs₀', r', ?_, by simp [hlen], ?_, sN, hg₁.trans hgN, hr⟩
      · simp only [Expr.stripPis, hstrip', Option.map_some]
      · intro i bb bb' hbb hbb'
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
          subst hbb; subst hbb'
          exact ⟨rfl, st, st₁, ElimGrows.refl st, hty, replaceAllNested_grows b hb⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hbb hbb'
          obtain ⟨hbm, s₁, s₂, hg, hw, hg'⟩ := hfields i bb bb' hbb hbb'
          exact ⟨hbm, s₁, s₂, hg₁.trans hg, hw, hg'⟩

end ConLeche
