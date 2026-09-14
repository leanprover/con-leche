module

public import ConLeche.Verify.Inductives.NestedWalk
-- `stripPis_instantiate1_full` (the per-binder form of `instantiate1`
-- through a telescope), used by `instPis_stripPis`
import ConLeche.Verify.Inductives.StructBody
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
@[expose] def ElimState.PinsCopyNamed (k : Nat) (st : ElimState) : Prop :=
  k ≤ st.types.length ∧ ∀ q ∈ st.pins, q.aux ∈ (st.types.map (·.name)).drop k

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

/-- The ledger's `PinsIndexed` (every pin's copy is a type at index
`≥ k`) is the copy-name form. -/
theorem ElimState.PinsIndexed.copyNamed {k : Nat} {st : ElimState} (h : st.PinsIndexed k) :
    st.PinsCopyNamed k := by
  obtain ⟨hk, hall⟩ := h
  refine ⟨hk, fun q hq => ?_⟩
  obtain ⟨j', hj', t, ht, hn⟩ := hall q hq
  have hlt : j' < st.types.length := (List.getElem?_eq_some_iff.mp ht).1
  rw [← hn]
  have hmem : t.name ∈ (st.types.map (·.name)).drop k := by
    rw [List.mem_iff_getElem?]
    refine ⟨j' - k, ?_⟩
    rw [List.getElem?_drop, List.getElem?_map, show k + (j' - k) = j' by omega, ht]
    rfl
  exact hmem

/-- … and it gives `PinsNamed` (every pin's copy is SOME type name). -/
theorem ElimState.PinsIndexed.named {k : Nat} {st : ElimState} (h : st.PinsIndexed k) :
    st.PinsNamed := by
  intro q hq
  obtain ⟨j', -, t, ht, hn⟩ := h.2 q hq
  show q.aux ∈ st.types.map (·.name)
  rw [← hn]
  exact List.mem_map_of_mem (List.mem_of_getElem? ht)

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


/-! ## The opening, binder by binder -/

/-- **A binder's annotation under `openPisAtFvars`** — the per-binder
form of `openPisAtFvars_instSeq`: the `j`-th variable is `fvar (d + j)`
annotated by the `j`-th `stripPis` binder domain instantiated at the
earlier variables (outermost first, at descending cuts).  What the
model's constructor read needs to relate the copy's OPENED field
domains (its datum's `xFvsF`) to the walk's bvar-form output
(`copyCtorFields_of_walk`). -/
theorem openPisAtFvars_binder :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr}
      {bs : List (Expr × BinderMeta)} {body₀ : Expr},
      openPisAtFvars k e d = some (fvs, body) → e.stripPis k = some (bs, body₀) →
      ∀ (j : Nat) (b : Expr × BinderMeta), bs[j]? = some b →
        fvs[j]? = some (.fvar (d + j) (Expr.instSeq (fvs.take j) (j - 1) b.1))
  | 0, e, d, fvs, body, bs, body₀, _, hs, j, b, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    rw [← hs.1] at hb
    exact nomatch hb
  | k + 1, .forallE ty bd m, d, fvs, body, bs, body₀, h, hs, j, b, hb => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs' body' hop =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₀, body₁⟩, hs₀, hbs⟩ := hs
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      -- the instantiated body's binders
      have hsome : ((bd.instantiate1 (.fvar d ty)).stripPis k).isSome :=
        Expr.stripPis_instantiate1_isSome k 0 (by rw [hs₀]; rfl)
      obtain ⟨⟨bs₁, body₂⟩, hs₁⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨-, hbin⟩ := Expr.stripPis_instantiate1_eq k 0 hs₀ hs₁
      have hlen₀ : bs₀.length = k := stripPis_length' k hs₀
      have hlen₁ : bs₁.length = k := stripPis_length' k hs₁
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        simp [Expr.instSeq]
      | succ j =>
        simp only [List.getElem?_cons_succ] at hb
        have hj : j < bs₁.length := by
          rw [hlen₁, ← hlen₀]; exact (List.getElem?_eq_some_iff.mp hb).1
        obtain ⟨b₁, hb₁⟩ : ∃ b₁, bs₁[j]? = some b₁ := ⟨_, List.getElem?_eq_getElem hj⟩
        have hb₁' := hbin j b b₁ hb hb₁
        have ih := openPisAtFvars_binder k hop hs₁ j b₁ hb₁
        simp only [List.getElem?_cons_succ, List.take_succ_cons]
        rw [ih, hb₁', Nat.zero_add]
        show some (Expr.fvar (d + 1 + j) _) = some (Expr.fvar (d + (j + 1)) _)
        rw [Nat.add_right_comm d 1 j, Nat.add_assoc d j 1]
        rfl
    · exact nomatch h
  | k + 1, .bvar _, _, _, _, _, _, h, _, _, _, _ | k + 1, .fvar _ _, _, _, _, _, _, h, _, _, _, _
  | k + 1, .sort _, _, _, _, _, _, h, _, _, _, _ | k + 1, .const _ _, _, _, _, _, _, h, _, _, _, _
  | k + 1, .app _ _, _, _, _, _, _, h, _, _, _, _ | k + 1, .lam _ _ _, _, _, _, _, _, h, _, _, _, _
  | k + 1, .letE _ _ _, _, _, _, _, _, h, _, _, _, _ | k + 1, .lit _, _, _, _, _, _, h, _, _, _, _
  | k + 1, .proj _ _ _, _, _, _, _, _, h, _, _, _, _ => nomatch h

/-! ## A copy constructor's fields: unfired, or a fire at the top -/

/-- A binder domain's mention is the tower's. -/
theorem Expr.stripPis_mentionsConst_binder {T : Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → ∀ b ∈ bs, b.1.mentionsConst T = true →
        e.mentionsConst T = true
  | 0, e, bs, body, h, b, hb, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hb
    exact nomatch hb
  | n + 1, .forallE ty b m, bs, body, h, bb, hbb, hm => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs⟩ := h
    simp only [Prod.mk.injEq] at hbs
    obtain ⟨rfl, rfl⟩ := hbs
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    rcases List.mem_cons.mp hbb with rfl | hbb
    · exact Or.inl hm
    · exact Or.inr (Expr.stripPis_mentionsConst_binder n h₀ bb hbb hm)
  | n + 1, .bvar _, _, _, h, _, _, _ | n + 1, .fvar _ _, _, _, h, _, _, _
  | n + 1, .sort _, _, _, h, _, _, _ | n + 1, .const _ _, _, _, h, _, _, _
  | n + 1, .app _ _, _, _, h, _, _, _ | n + 1, .lam _ _ _, _, _, h, _, _, _
  | n + 1, .letE _ _ _, _, _, h, _, _, _ | n + 1, .lit _, _, _, h, _, _, _
  | n + 1, .proj _ _ _, _, _, h, _, _, _ => nomatch h

/-- **Every field of a walked constructor is unfired or a fire at the
top** (task #279 M-B′ step 3n, DESIGN §M.31 (c)).  The walk of the
instantiated container constructor `cI` (a Π-tower over `nF` field
domains and a residual) is a Π-tower of the same shape
(`replaceAllNested_stripPis`); at each field, and at the residual:

* an output mentioning no COPY name of the final state is its input
  (W1 over the copy names — the copy's ordinary fields and its fields
  into a BLOCK MEMBER);
* an output that is, under its own `n` binders whose domains mention
  no name of the state, a spine headed by a COPY name is a fire at the
  top (W2): the input's binders are the same, its body a stored
  container `I` at `nP` components and index arguments, the output the
  copy at the block's parameters and those arguments, and the pin
  `I lvls Ds` is in the final table.

The state the walk starts from has its pins indexed (`PinsIndexed`,
the ledger's), which is what W1/W2 need at every field's own start
state; the input mentions no copy name (the mint's `MentionInv`). -/
theorem copyCtorFields_of_walk {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {k nF : Nat} {sta stb : ElimState} {cI body' : Expr}
    (hwalk : replaceAllNested env blvls params pbs sta cI = .ok (body', stb))
    (hpi : sta.PinsIndexed k)
    {fs : List (Expr × BinderMeta)} {resid : Expr} (hcI : cI.stripPis nF = some (fs, resid))
    (hin : ∀ T ∈ (stb.types.map (·.name)).drop k, cI.mentionsConst T = false) :
    ∃ (fs' : List (Expr × BinderMeta)) (resid' : Expr),
      body'.stripPis nF = some (fs', resid') ∧ fs'.length = fs.length ∧
      (∀ (i : Nat) (b b' : Expr × BinderMeta), fs[i]? = some b → fs'[i]? = some b' →
        b'.2 = b.2 ∧
        ((∀ T ∈ (stb.types.map (·.name)).drop k, b'.1.mentionsConst T = false) → b'.1 = b.1) ∧
        (∀ (n : Nat) (bs' : List (Expr × BinderMeta)) (aux : Name) (ls : List Level)
            (args : List Expr),
          b'.1.stripPis n = some (bs', Expr.mkAppN (.const aux ls) args) →
          aux ∈ (stb.types.map (·.name)).drop k →
          (∀ bb ∈ bs', ∀ T ∈ stb.newNames, bb.1.mentionsConst T = false) →
          ∃ (body : Expr) (I : Name) (lvls : List Level) (ci : ContainerInfo),
            b.1.stripPis n = some (bs', body) ∧ containerInfo? env I = some ci ∧
            ci.nP ≤ body.getAppArgs.length ∧ body = Expr.mkAppN (.const I lvls) body.getAppArgs ∧
            ls = blvls ∧ args = params ++ body.getAppArgs.drop ci.nP ∧
            ∃ q ∈ stb.pins, q.aux = aux ∧
              q.pin = Expr.mkAppN (.const I lvls) (body.getAppArgs.take ci.nP))) ∧
      ((∀ T ∈ (stb.types.map (·.name)).drop k, resid'.mentionsConst T = false) → resid' = resid) ∧
      (∀ (aux : Name) (ls : List Level) (args : List Expr),
        resid' = Expr.mkAppN (.const aux ls) args → aux ∈ (stb.types.map (·.name)).drop k →
        ∃ (I : Name) (lvls : List Level) (ci : ContainerInfo),
          containerInfo? env I = some ci ∧ ci.nP ≤ resid.getAppArgs.length ∧
          resid = Expr.mkAppN (.const I lvls) resid.getAppArgs ∧ ls = blvls ∧
          args = params ++ resid.getAppArgs.drop ci.nP ∧
          ∃ q ∈ stb.pins, q.aux = aux ∧
            q.pin = Expr.mkAppN (.const I lvls) (resid.getAppArgs.take ci.nP)) := by
  obtain ⟨fs', resid', hstrip', hlen, hfields, sN, hgN, hr⟩ :=
    replaceAllNested_stripPis nF cI hwalk hcI
  have hgAll : ElimGrows sta stb := replaceAllNested_grows cI hwalk
  have hkb : k ≤ stb.types.length := Nat.le_trans hpi.1 hgAll.types_length_le
  -- a copy name of the final state is a copy name at any later state
  refine ⟨fs', resid', hstrip', hlen, ?_, ?_, ?_⟩
  · intro i b b' hb hb'
    obtain ⟨hbm, s₁, s₂, hg₁, hw, hg₂⟩ := hfields i b b' hb hb'
    have hpi₁ : s₁.PinsCopyNamed k := hpi.copyNamed.grows hg₁
    have hpn₁ : s₁.PinsNamed := hpi.named.grows hg₁
    have hk₂ : k ≤ s₂.types.length := Nat.le_trans hpi₁.1 (replaceAllNested_grows _ hw).types_length_le
    refine ⟨hbm, fun hm => ?_, ?_⟩
    · exact replaceAllNested_eq_of_no_copy b.1 hw hpi₁
        (fun T hT => hm T (hg₂.copyNames_mono k hk₂ T hT))
    · intro n bs' aux ls args hstripB haux hbs
      have hnoB : ∀ T ∈ (stb.types.map (·.name)).drop k, b.1.mentionsConst T = false := by
        intro T hT
        refine Bool.eq_false_iff.mpr fun hm => ?_
        have := hin T hT
        rw [Expr.stripPis_mentionsConst_binder nF hcI b (List.mem_of_getElem? hb) hm] at this
        exact nomatch this
      obtain ⟨body, hstripA, I, lvls, ci, hci, hnP, hfe, hls, hargs, q, hq, hqa, hqp⟩ :=
        replaceAllNested_pis_inv ((stb.types.map (·.name)).drop k) n b.1 hw hpn₁ hstripB
          (fun bb hbb T hT => hbs bb hbb T (hg₂.newNames_mono T hT)) rfl haux hnoB
      refine ⟨body, I, lvls, ci, hstripA, hci, hnP, hfe, hls, hargs, q, ?_, hqa, hqp⟩
      obtain ⟨new, hpins, -⟩ := hg₂
      rw [hpins]
      exact List.mem_append_left _ hq
  · intro hm
    have hpiN : sN.PinsCopyNamed k := hpi.copyNamed.grows hgN
    exact replaceAllNested_eq_of_no_copy resid hr hpiN hm
  · intro aux ls args hout haux
    have hpnN : sN.PinsNamed := hpi.named.grows hgN
    have hnoR : ∀ T ∈ (stb.types.map (·.name)).drop k, resid.mentionsConst T = false := by
      intro T hT
      refine Bool.eq_false_iff.mpr fun hm => ?_
      have := hin T hT
      rw [Expr.stripPis_mentionsConst nF hcI hm] at this
      exact nomatch this
    obtain ⟨-, I, lvls, ci, hci, hnP, hfe, hls, hargs, q, hq, hqa, hqp⟩ :=
      replaceAllNested_head_inv ((stb.types.map (·.name)).drop k) resid hr hout haux hnoR
    exact ⟨I, lvls, ci, hci, hnP, hfe, hls, hargs, q, hq, hqa, hqp⟩

/-! ## The instantiated telescope, per field -/

/-- **`instPis` keeps the telescope below the arguments** (task #279
M-B′ step 3p, DESIGN §M.42): instantiating the leading `|args|`
binders of a telescope of `|args| + n` binders leaves a telescope of
`n` binders whose `j`-th domain is the original `|args| + j`-th
instantiated at the arguments in order (`Expr.instSeq` at the
descending indices the peel produces), with the BINDER DATA kept, and
whose residual is the original's instantiated likewise.  This is the
per-field form of the instantiation the elimination performs on a
container's stored constructor at a pin. -/
theorem instPis_stripPis :
    ∀ (args : List Expr) (n : Nat) {T rest : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      Expr.instPis T args = some rest →
      T.stripPis (args.length + n) = some (bs, r) →
      ∃ bs' : List (Expr × BinderMeta),
        rest.stripPis n = some (bs', Expr.instSeq args (args.length + n - 1) r) ∧
        ∀ (j : Nat) (b : Expr × BinderMeta), bs[args.length + j]? = some b →
          bs'[j]? = some (Expr.instSeq args (args.length + j - 1) b.1, b.2)
  | [], n, T, rest, bs, r, hinst, hstrip => by
    simp only [Expr.instPis, Option.some.injEq] at hinst
    subst hinst
    simp only [List.length_nil, Nat.zero_add] at hstrip ⊢
    exact ⟨bs, by simpa [Expr.instSeq] using hstrip, fun j b hb => by
      simpa [Expr.instSeq] using hb⟩
  | a :: as, n, T, rest, bs, r, hinst, hstrip => by
    revert hstrip
    match T, hinst with
    | .forallE ty body mt, hinst =>
      intro hstrip
      simp only [Expr.instPis] at hinst
      rw [show (a :: as).length + n = (as.length + n) + 1 by simp; omega] at hstrip
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstrip
      obtain ⟨⟨bs₁, r₁⟩, hstrip₁, hbs⟩ := hstrip
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨bs₁', hstrip₁', hpt₁⟩ :=
        stripPis_instantiate1_full (v := a) (as.length + n) (e := body) 0 hstrip₁
      rw [Nat.zero_add] at hstrip₁'
      obtain ⟨bs', hrest, hpt⟩ := instPis_stripPis as n hinst hstrip₁'
      refine ⟨bs', ?_, fun j b hb => ?_⟩
      · have hres : Expr.instSeq as (as.length + n - 1) (r₁.instantiate1 a (as.length + n))
            = Expr.instSeq (a :: as) ((a :: as).length + n - 1) r₁ := by
          rw [show Expr.instSeq (a :: as) ((a :: as).length + n - 1) r₁
            = Expr.instSeq as ((a :: as).length + n - 1 - 1)
                (r₁.instantiate1 a ((a :: as).length + n - 1)) from rfl]
          simp only [List.length_cons]
          rw [show as.length + 1 + n - 1 = as.length + n by omega]
        rw [hrest, hres]
      · have hb₁ : bs₁[as.length + j]? = some b := by
          have hb' : ((ty, mt) :: bs₁)[(a :: as).length + j]? = some b := hb
          rw [show (a :: as).length + j = (as.length + j) + 1 by simp; omega] at hb'
          simpa using hb'
        have h2 := hpt j _ (hpt₁ (as.length + j) b hb₁)
        rw [Nat.zero_add] at h2
        rw [h2]
        show some (Expr.instSeq as (as.length + j - 1) (b.1.instantiate1 a (as.length + j)), b.2)
          = some (Expr.instSeq (a :: as) ((a :: as).length + j - 1) b.1, b.2)
        rw [show Expr.instSeq (a :: as) ((a :: as).length + j - 1) b.1
          = Expr.instSeq as ((a :: as).length + j - 1 - 1)
              (b.1.instantiate1 a ((a :: as).length + j - 1)) from rfl]
        simp only [List.length_cons]
        rw [show as.length + 1 + j - 1 = as.length + j by omega]
end ConLeche
