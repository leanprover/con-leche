module

public import ConLeche.Verify.Inductives.NestedLedger
import ConLeche.Verify.Inductives.NestedCtors

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
* **W2 — an output headed by a copy's name that the input does not
  mention is a fire at the top** (`replaceAllNested_head_inv`): the
  input is a stored container `I` at `nP` components and index
  arguments, the output the copy at the block's parameters and those
  index arguments, and the pin `I lvls Ds` is in the final table.  The
  top-down discipline is what makes the fire sit at the TOP: a fire at
  the head of a wider spine would have fired at the wider spine too
  (`replaceIfNested_app_of_fire` — the occurrence test reads only the
  first `nP` arguments).  Under Π binders whose domains mention no new
  name (`replaceAllNested_pis_inv`): the binders are the input's (W1)
  and the body is a fire.
* **The no-aux-mention invariant** (`MentionInv`): every constant a
  pin's components or an UNPROCESSED constructor mention satisfies a
  predicate `ok` — the walk's inputs are the minted constructors (the
  containers' stored constructors at the pins' components, closed over
  the first former's binders) and the block's own; a fire's arguments
  are sub-terms of the input; a mint's new pins and constructors are
  built from them.  Instantiated at `ok := in the pre-block
  environment ∨ a block member's name`, it is W2's premise: the walk
  input mentions no copy's name (fresh at the pre-block environment).

The invariant `ElimState.PinsNamed` is the piece of the ledger this
needs: every pin's `aux` is a type name of the state, kept across
`ElimGrows` (a mint appends the copies and their pins together).
-/

namespace ConLeche

/-! ## Pins are named by types -/

/-- Every pin's copy name is a name of the growing type list. -/
@[expose] def ElimState.PinsNamed (st : ElimState) : Prop :=
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

/-! ## Mentions against resolution -/

/-- **A resolving term mentions only STORED constants** (task #279 M-B′
step 3p): `constsResolve` asks `find?` of every constant node the term
carries, and `mentionsConst` finds one — so a term that resolves at an
environment cannot mention a name that is fresh there.  This is what
refutes an ORDINARY field on the copy's side at a container-recursive
position: the field mentions a copy or a block member, both fresh
before the block, while `mutualFieldsOk`'s ordinary clause demands
resolution at the pre-block environment. -/
theorem Expr.find?_isSome_of_mentionsConst {env : Env} {T : Name} :
    ∀ e : Expr, e.constsResolve env = true → e.mentionsConst T = true →
      (env.find? T).isSome = true
  | .bvar _, _, hm => nomatch hm
  | .sort _, _, hm => nomatch hm
  | .lit _, _, hm => nomatch hm
  | .const n _, hr, hm => by
    simp only [Expr.mentionsConst, beq_iff_eq] at hm
    subst hm
    exact hr
  | .fvar _ ty, hr, hm => find?_isSome_of_mentionsConst ty hr hm
  | .app f a, hr, hm => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact find?_isSome_of_mentionsConst f hr.1 hm
    · exact find?_isSome_of_mentionsConst a hr.2 hm
  | .lam ty b _, hr, hm => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact find?_isSome_of_mentionsConst ty hr.1 hm
    · exact find?_isSome_of_mentionsConst b hr.2 hm
  | .forallE ty b _, hr, hm => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact find?_isSome_of_mentionsConst ty hr.1 hm
    · exact find?_isSome_of_mentionsConst b hr.2 hm
  | .letE ty v b, hr, hm => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with (hm | hm) | hm
    · exact find?_isSome_of_mentionsConst ty hr.1.1 hm
    · exact find?_isSome_of_mentionsConst v hr.1.2 hm
    · exact find?_isSome_of_mentionsConst b hr.2 hm
  | .proj sn _ e, hr, hm => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with rfl | hm
    · exact hr.1
    · exact find?_isSome_of_mentionsConst e hr.2 hm

/-- The contrapositive at a FRESH name: a term resolving at an
environment where `T` is absent does not mention `T`. -/
theorem Expr.not_mentionsConst_of_fresh {env : Env} {T : Name} {e : Expr}
    (hr : e.constsResolve env = true) (hf : env.find? T = none) : e.mentionsConst T = false := by
  refine Bool.eq_false_iff.mpr fun hm => ?_
  have := Expr.find?_isSome_of_mentionsConst e hr hm
  rw [hf] at this
  exact nomatch this

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

/-! ## W2: the fire inversion -/

theorem Expr.mkAppN_append (f : Expr) :
    ∀ (l₁ l₂ : List Expr), Expr.mkAppN f (l₁ ++ l₂) = Expr.mkAppN (Expr.mkAppN f l₁) l₂
  | [], _ => rfl
  | a :: l₁, l₂ => by
    show Expr.mkAppN (.app f a) (l₁ ++ l₂) = Expr.mkAppN (Expr.mkAppN (.app f a) l₁) l₂
    exact Expr.mkAppN_append (.app f a) l₁ l₂

/-- The occurrence test reads only the first `nP` arguments. -/
theorem nestedOccOk_append_one {I : Name} {names : List Name} {nP : Nat} {args : List Expr}
    (a : Expr) (h : nP ≤ args.length) :
    nestedOccOk I names nP (args ++ [a]) = nestedOccOk I names nP args := by
  unfold nestedOccOk
  rw [List.take_append_of_le_length h]

/-- A mention in a telescope's body is a mention in the telescope. -/
theorem Expr.stripPis_mentionsConst {T : Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → body.mentionsConst T = true → e.mentionsConst T = true
  | 0, e, bs, body, h, hm => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]; exact hm
  | n + 1, .forallE ty b m, bs, body, h, hm => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs⟩ := h
    simp only [Prod.mk.injEq] at hbs
    obtain ⟨-, rfl⟩ := hbs
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    exact Or.inr (Expr.stripPis_mentionsConst n h₀ hm)
  | n + 1, .bvar _, _, _, h, _ => nomatch h
  | n + 1, .fvar _ _, _, _, h, _ => nomatch h
  | n + 1, .sort _, _, _, h, _ => nomatch h
  | n + 1, .const _ _, _, _, h, _ => nomatch h
  | n + 1, .app _ _, _, _, h, _ => nomatch h
  | n + 1, .lam _ _ _, _, _, h, _ => nomatch h
  | n + 1, .letE _ _ _, _, _, h, _ => nomatch h
  | n + 1, .lit _, _, _, h, _ => nomatch h
  | n + 1, .proj _ _ _, _, _, h, _ => nomatch h

/-- **A fire at the head of a spine fires at the wider spine**: the
occurrence test reads only the first `nP` arguments, the pin table is
the same, and so is the mint — the state is the same, the index
arguments one longer. -/
theorem replaceIfNested_app_of_fire {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st' : ElimState} {f a r : Expr}
    (h : replaceIfNested env blvls params pbs st f = .ok (some (r, st'))) :
    ∃ r', replaceIfNested env blvls params pbs st (.app f a) = .ok (some (r', st')) := by
  unfold replaceIfNested at h ⊢
  simp only [bind, Except.bind] at h ⊢
  split at h
  · next f₁ a₁ =>
    have hfn : (Expr.app (Expr.app f₁ a₁) a).getAppFn = (Expr.app f₁ a₁).getAppFn := rfl
    have hargs : (Expr.app (Expr.app f₁ a₁) a).getAppArgs = (Expr.app f₁ a₁).getAppArgs ++ [a] := rfl
    rw [hfn, hargs]
    split at h
    · next I lvls hI =>
      split at h
      · next cv caps hfind =>
        split at h
        · exact nomatch h
        · next hq =>
          rw [if_neg hq]
          split at h
          · split at h
            · exact nomatch h
            · exact nomatch h
          · next ci hci =>
            split at h
            · exact nomatch h
            · next hnP =>
              have hle : ci.nP ≤ (Expr.app f₁ a₁).getAppArgs.length := Nat.le_of_not_lt hnP
              rw [if_neg (by rw [List.length_append]; simp only [List.length_singleton]; omega),
                nestedOccOk_append_one a hle]
              split at h
              · exact nomatch h
              · next nested hocc =>
                split at h
                · exact nomatch h
                · next hn =>
                  rw [if_neg hn, List.take_append_of_le_length hle, List.drop_append_of_le_length hle]
                  split at h
                  · next q hq =>
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact ⟨_, rfl⟩
                  · next hq =>
                    split at h
                    · exact nomatch h
                    · next p hmk =>
                      obtain ⟨stq, gotq⟩ := p
                      split at h
                      · exact nomatch h
                      · next auxI hgot =>
                        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨-, rfl⟩ := h
                        exact ⟨_, rfl⟩
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- A constant-headed spine is a constant or an application. -/
theorem Expr.mkAppN_const_shape {n : Name} {ls : List Level} :
    ∀ (args : List Expr), Expr.mkAppN (.const n ls) args = .const n ls ∨
      ∃ f a, Expr.mkAppN (.const n ls) args = .app f a := by
  intro args
  rcases List.eq_nil_or_concat args with rfl | ⟨args₀, a₀, rfl⟩
  · exact Or.inl rfl
  · rw [List.concat_eq_append, Expr.mkAppN_append_one]
    exact Or.inr ⟨_, _, rfl⟩

/-- A constant-headed spine mentions its head. -/
theorem Expr.mentionsConst_mkAppN_const (n : Name) (ls : List Level) (args : List Expr) :
    (Expr.mkAppN (.const n ls) args).mentionsConst n = true :=
  Expr.mentionsConst_mkAppN_of_head args _ (by simp [Expr.mentionsConst])

/-- **The walk at a fire**: when the top node fires the walk's answer is
the fire's. -/
theorem replaceAllNested_of_fire {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} {st st₁ : ElimState} {e r : Expr}
    (hpr : st.newNames.any (fun T => e.mentionsConst T) = true)
    (hfire : replaceIfNested env blvls params pbs st e = .ok (some (r, st₁))) :
    replaceAllNested env blvls params pbs st e = .ok (r, st₁) := by
  unfold replaceAllNested
  rw [if_neg (by rw [hpr]; decide), hfire]

/-- **W2 at the head**: an output that is a spine headed by a name of
`S` — a set the INPUT does not mention — is a FIRE at the top: the input
is a stored container `I` at its components and index arguments, the
output the copy at the block's parameters and those index arguments,
and the pin is in the final table.  (The top-down discipline: a fire
below the top would have fired at the top, `replaceIfNested_app_of_fire`.) -/
theorem replaceAllNested_head_inv {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} (S : List Name) :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') →
      ∀ {aux : Name} {ls : List Level} {args : List Expr},
        e' = Expr.mkAppN (.const aux ls) args → aux ∈ S →
        (∀ T ∈ S, e.mentionsConst T = false) →
        replaceIfNested env blvls params pbs st e = .ok (some (e', st')) ∧
        ∃ (I : Name) (lvls : List Level) (ci : ContainerInfo),
          containerInfo? env I = some ci ∧ ci.nP ≤ e.getAppArgs.length ∧
          e = Expr.mkAppN (.const I lvls) e.getAppArgs ∧ ls = blvls ∧
          args = params ++ e.getAppArgs.drop ci.nP ∧
          ∃ q ∈ st'.pins, q.aux = aux ∧
            q.pin = Expr.mkAppN (.const I lvls) (e.getAppArgs.take ci.nP) := by
  intro e st st' e' h aux ls args hout hS hno
  -- the output mentions `aux`, so the input is not the output: not pruned
  have hmen : e'.mentionsConst aux = true := by rw [hout]; exact Expr.mentionsConst_mkAppN_const _ _ _
  have hne : e' ≠ e := fun heq => by rw [heq, hno aux hS] at hmen; exact nomatch hmen
  have hpr : st.newNames.any (fun T => e.mentionsConst T) = true := by
    refine Classical.byContradiction fun hpr' => ?_
    have := replaceAllNested_prune (env := env) (blvls := blvls) (params := params) (pbs := pbs)
      (Bool.eq_false_iff.mpr hpr')
    rw [this] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact hne h.1.symm
  -- the top node
  cases hri : replaceIfNested env blvls params pbs st e with
  | error err =>
    unfold replaceAllNested at h
    rw [if_neg (by rw [hpr]; decide), hri] at h
    exact nomatch h
  | ok o =>
    cases o with
    | some p =>
      obtain ⟨r, st₁⟩ := p
      have h' := replaceAllNested_of_fire hpr hri
      rw [h'] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      obtain ⟨I, lvls, ci, aux', hci, hnP, hfe, hr, q, hq, hqa, hqp⟩ := replaceIfNested_some hri
      rw [hr, ← Expr.mkAppN_append] at hout
      have hhead := congrArg Expr.getAppFn hout
      rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at hhead
      simp only [Expr.getAppFn, Expr.const.injEq] at hhead
      obtain ⟨rfl, rfl⟩ := hhead
      have hargs := congrArg Expr.getAppArgs hout
      rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at hargs
      simp only [Expr.getAppArgs, List.nil_append] at hargs
      exact ⟨I, lvls, ci, hci, hnP, hfe, rfl, hargs.symm, q, hq, hqa, hqp⟩
    | none =>
      -- the walk descended: the output has the input's top constructor
      exfalso
      cases e with
      | app f a =>
        rcases replaceAllNested_app h with hfire | ⟨f', a', st₁, hf, ha, rfl⟩
        · rw [hri] at hfire; exact nomatch hfire
        · rcases List.eq_nil_or_concat args with rfl | ⟨args₀, a₀, rfl⟩
          · exact nomatch hout
          · rw [List.concat_eq_append, Expr.mkAppN_append_one] at hout
            simp only [Expr.app.injEq] at hout
            obtain ⟨hf', -⟩ := hout
            have hnoF : ∀ T ∈ S, f.mentionsConst T = false := fun T hT => by
              have := hno T hT
              simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
              exact this.1
            obtain ⟨hfireF, -⟩ := replaceAllNested_head_inv S f hf hf' hS hnoF
            obtain ⟨r', hr'⟩ := replaceIfNested_app_of_fire (a := a) hfireF
            rw [hri] at hr'
            exact nomatch hr'
      | lam ty b bm =>
        obtain ⟨ty', b', st₁, -, -, rfl⟩ := replaceAllNested_lam h
        rcases Expr.mkAppN_const_shape (n := aux) (ls := ls) args with hc | ⟨f, a, hc⟩ <;>
          (rw [hc] at hout; exact nomatch hout)
      | forallE ty b bm =>
        obtain ⟨ty', b', st₁, -, -, rfl⟩ := replaceAllNested_forallE h
        rcases Expr.mkAppN_const_shape (n := aux) (ls := ls) args with hc | ⟨f, a, hc⟩ <;>
          (rw [hc] at hout; exact nomatch hout)
      | letE ty v b =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        dsimp only at h
        split at h
        · exact nomatch h
        · split at h
          · exact nomatch h
          · split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              rcases Expr.mkAppN_const_shape (n := aux) (ls := ls) args with hc | ⟨f, a, hc⟩ <;>
                (rw [hc] at hout; exact nomatch hout)
      | proj sn i x =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        dsimp only at h
        split at h
        · exact nomatch h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rcases Expr.mkAppN_const_shape (n := aux) (ls := ls) args with hc | ⟨f, a, hc⟩ <;>
            (rw [hc] at hout; exact nomatch hout)
      | bvar i =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      | fvar i ty =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      | sort u =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      | const n us =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm
      | lit l =>
        unfold replaceAllNested at h
        rw [if_neg (by rw [hpr]; decide), hri] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact hne h.1.symm

/-- **W2 under Π binders**: an output `Π bs', body'` whose binders mention
no name of the final state and whose body is a spine headed by a name
of `S` (unmentioned by the input) is the walk of `Π bs', body` with the
SAME binders (W1 at each domain) and `body ↦ body'` a fire at the top. -/
theorem replaceAllNested_pis_inv {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} (S : List Name) :
    ∀ (n : Nat) (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') → st.PinsNamed →
      ∀ {bs' : List (Expr × BinderMeta)} {body' : Expr}, e'.stripPis n = some (bs', body') →
        (∀ b ∈ bs', ∀ T ∈ st'.newNames, b.1.mentionsConst T = false) →
        ∀ {aux : Name} {ls : List Level} {args : List Expr},
          body' = Expr.mkAppN (.const aux ls) args → aux ∈ S →
          (∀ T ∈ S, e.mentionsConst T = false) →
          ∃ body : Expr, e.stripPis n = some (bs', body) ∧
            ∃ (I : Name) (lvls : List Level) (ci : ContainerInfo),
              containerInfo? env I = some ci ∧ ci.nP ≤ body.getAppArgs.length ∧
              body = Expr.mkAppN (.const I lvls) body.getAppArgs ∧ ls = blvls ∧
              args = params ++ body.getAppArgs.drop ci.nP ∧
              ∃ q ∈ st'.pins, q.aux = aux ∧
                q.pin = Expr.mkAppN (.const I lvls) (body.getAppArgs.take ci.nP)
  | 0, e, st, st', e', h, _, bs', body', hstrip, _, aux, ls, args, hout, hS, hno => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstrip
    obtain ⟨rfl, rfl⟩ := hstrip
    obtain ⟨-, I, lvls, ci, hci, hnP, hfe, hls, hargs, q, hq, hqa, hqp⟩ :=
      replaceAllNested_head_inv S e h hout hS hno
    exact ⟨e, rfl, I, lvls, ci, hci, hnP, hfe, hls, hargs, q, hq, hqa, hqp⟩
  | n + 1, e, st, st', e', h, hpn, bs', body', hstrip, hbs, aux, ls, args, hout, hS, hno => by
    -- the output is a `Π`
    cases e' with
    | forallE ty' b' bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstrip
      obtain ⟨⟨bs₀', body₀'⟩, h₀, hbs'⟩ := hstrip
      simp only [Prod.mk.injEq] at hbs'
      obtain ⟨rfl, rfl⟩ := hbs'
      -- the output mentions `aux`, so it is not the input
      have hmenB : body₀'.mentionsConst aux = true := by
        rw [hout]; exact Expr.mentionsConst_mkAppN_const _ _ _
      have hmen : (Expr.forallE ty' b' bm).mentionsConst aux = true :=
        Expr.stripPis_mentionsConst (n + 1) (e := .forallE ty' b' bm) (bs := (ty', bm) :: bs₀')
          (by simp only [Expr.stripPis, h₀, Option.map_some]) hmenB
      have hne : Expr.forallE ty' b' bm ≠ e := fun heq => by
        rw [heq, hno aux hS] at hmen; exact nomatch hmen
      -- the input is a `Π` too: a fire's output is a spine, the structural arms keep the shape
      cases e with
      | forallE ty b bm₀ =>
        obtain ⟨ty₁, b₁, st₁, hty, hb, heq⟩ := replaceAllNested_forallE h
        simp only [Expr.forallE.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        have hg₁ := replaceAllNested_grows ty hty
        have hg₂ := replaceAllNested_grows b hb
        -- the domain is the input's (W1)
        have hty' : ty' = ty := replaceAllNested_eq_of_unmentioned ty hty hpn fun T hT =>
          hbs (ty', bm) List.mem_cons_self T (hg₂.newNames_mono T hT)
        subst hty'
        have hnoB : ∀ T ∈ S, b.mentionsConst T = false := fun T hT => by
          have := hno T hT
          simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
          exact this.2
        obtain ⟨body, hstripB, rest⟩ := replaceAllNested_pis_inv S n b hb (hpn.grows hg₁) h₀
          (fun x hx T hT => hbs x (List.mem_cons_of_mem _ hx) T hT) hout hS hnoB
        exact ⟨body, by simp only [Expr.stripPis, hstripB, Option.map_some], rest⟩
      | app f a =>
        rcases replaceAllNested_app h with hfire | ⟨f', a', st₁, -, -, heq⟩
        · obtain ⟨I, lvls, ci, aux', -, -, -, hr, -⟩ := replaceIfNested_some hfire
          rw [← Expr.mkAppN_append] at hr
          rcases Expr.mkAppN_const_shape (n := aux') (ls := blvls)
              (params ++ (Expr.app f a).getAppArgs.drop ci.nP) with hc | ⟨f₁, a₁, hc⟩ <;>
            (rw [hc] at hr; exact nomatch hr)
        · exact nomatch heq
      | lam ty b bm₀ =>
        obtain ⟨_, _, _, -, -, heq⟩ := replaceAllNested_lam h
        exact nomatch heq
      | letE ty v b =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.letE ty v b) = .ok none from rfl] at h
          dsimp only at h
          split at h
          · exact nomatch h
          · split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                exact nomatch h.1
      | proj sn i x =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.proj sn i x) = .ok none from rfl] at h
          dsimp only at h
          split at h
          · exact nomatch h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            exact nomatch h.1
      | bvar i =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.bvar i) = .ok none from rfl] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
      | fvar i ty =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.fvar i ty) = .ok none from rfl] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
      | sort u =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.sort u) = .ok none from rfl] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
      | const c us =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.const c us) = .ok none from rfl] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
      | lit l =>
        unfold replaceAllNested at h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
        · rw [show replaceIfNested env blvls params pbs st (.lit l) = .ok none from rfl] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact nomatch h.1
    | bvar _ => exact nomatch hstrip
    | fvar _ _ => exact nomatch hstrip
    | sort _ => exact nomatch hstrip
    | const _ _ => exact nomatch hstrip
    | app _ _ => exact nomatch hstrip
    | lam _ _ _ => exact nomatch hstrip
    | letE _ _ _ => exact nomatch hstrip
    | lit _ => exact nomatch hstrip
    | proj _ _ _ => exact nomatch hstrip

/-! ## The no-aux-mention invariant -/

/-- Every constant `e` mentions satisfies `ok`. -/
@[expose] def Expr.MentionsOnly (ok : Name → Prop) (e : Expr) : Prop :=
  ∀ T, e.mentionsConst T = true → ok T

namespace Expr

variable {ok : Name → Prop}

theorem mentionsOnly_app {f a : Expr} :
    MentionsOnly ok (.app f a) ↔ MentionsOnly ok f ∧ MentionsOnly ok a := by
  simp only [MentionsOnly, mentionsConst, Bool.or_eq_true]
  exact ⟨fun h => ⟨fun T hT => h T (Or.inl hT), fun T hT => h T (Or.inr hT)⟩,
    fun h T hT => hT.elim (h.1 T) (h.2 T)⟩

theorem mentionsOnly_lam {ty b : Expr} {m : BinderMeta} :
    MentionsOnly ok (.lam ty b m) ↔ MentionsOnly ok ty ∧ MentionsOnly ok b := by
  simp only [MentionsOnly, mentionsConst, Bool.or_eq_true]
  exact ⟨fun h => ⟨fun T hT => h T (Or.inl hT), fun T hT => h T (Or.inr hT)⟩,
    fun h T hT => hT.elim (h.1 T) (h.2 T)⟩

theorem mentionsOnly_forallE {ty b : Expr} {m : BinderMeta} :
    MentionsOnly ok (.forallE ty b m) ↔ MentionsOnly ok ty ∧ MentionsOnly ok b := by
  simp only [MentionsOnly, mentionsConst, Bool.or_eq_true]
  exact ⟨fun h => ⟨fun T hT => h T (Or.inl hT), fun T hT => h T (Or.inr hT)⟩,
    fun h T hT => hT.elim (h.1 T) (h.2 T)⟩

theorem mentionsOnly_const {n : Name} {us : List Level} (h : ok n) : MentionsOnly ok (.const n us) := by
  intro T hT
  simp only [mentionsConst, beq_iff_eq] at hT
  rw [← hT]; exact h

theorem MentionsOnly.mkAppN {f : Expr} (hf : MentionsOnly ok f) :
    ∀ (args : List Expr), (∀ a ∈ args, MentionsOnly ok a) → MentionsOnly ok (Expr.mkAppN f args)
  | [], _ => hf
  | a :: as, h =>
    MentionsOnly.mkAppN (mentionsOnly_app.mpr ⟨hf, h a List.mem_cons_self⟩) as
      fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem MentionsOnly.getAppArgs : ∀ {e : Expr}, MentionsOnly ok e → ∀ x ∈ e.getAppArgs, MentionsOnly ok x
  | .app f a, he, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact MentionsOnly.getAppArgs (mentionsOnly_app.mp he).1 x hx
    · exact (mentionsOnly_app.mp he).2
  | .bvar _, _, _, hx => nomatch hx
  | .fvar _ _, _, _, hx => nomatch hx
  | .sort _, _, _, hx => nomatch hx
  | .const _ _, _, _, hx => nomatch hx
  | .lam _ _ _, _, _, hx => nomatch hx
  | .forallE _ _ _, _, _, hx => nomatch hx
  | .letE _ _ _, _, _, hx => nomatch hx
  | .lit _, _, _, hx => nomatch hx
  | .proj _ _ _, _, _, hx => nomatch hx

theorem MentionsOnly.instantiate1 {e v : Expr} (he : MentionsOnly ok e) (hv : MentionsOnly ok v)
    (d : Nat) : MentionsOnly ok (e.instantiate1 v d) := fun T hT =>
  (Expr.mentionsConst_instantiate1 v e d hT).elim (he T) (hv T)

theorem MentionsOnly.instPis :
    ∀ {ty : Expr} {args : List Expr} {r : Expr}, Expr.instPis ty args = some r →
      MentionsOnly ok ty → (∀ a ∈ args, MentionsOnly ok a) → MentionsOnly ok r
  | ty, [], r, h, hty, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h; exact hty
  | .forallE _ body _, a :: as, r, h, hty, hargs =>
    MentionsOnly.instPis (ty := body.instantiate1 a) h
      (((mentionsOnly_forallE).mp hty).2.instantiate1 (hargs a List.mem_cons_self) 0)
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)
  | .bvar _, _ :: _, _, h, _, _ => nomatch h
  | .fvar _ _, _ :: _, _, h, _, _ => nomatch h
  | .sort _, _ :: _, _, h, _, _ => nomatch h
  | .const _ _, _ :: _, _, h, _, _ => nomatch h
  | .app _ _, _ :: _, _, h, _, _ => nomatch h
  | .lam _ _ _, _ :: _, _, h, _, _ => nomatch h
  | .letE _ _ _, _ :: _, _, h, _, _ => nomatch h
  | .lit _, _ :: _, _, h, _, _ => nomatch h
  | .proj _ _ _, _ :: _, _, h, _, _ => nomatch h

/-- Abstracting a variable drops its annotation's mentions and adds none. -/
theorem mentionsConst_abstract1 {T : Name} :
    ∀ (e : Expr) (d k : Nat), (e.abstract1 d k).mentionsConst T = true → e.mentionsConst T = true
  | .bvar _, _, _, h => h
  | .fvar idx ty, d, k, h => by
    simp only [Expr.abstract1] at h
    split at h
    · exact nomatch h
    · exact h
  | .sort _, _, _, h => h
  | .const _ _, _, _, h => h
  | .app f a, d, k, h => by
    simp only [Expr.abstract1, mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.elim (fun h => Or.inl (mentionsConst_abstract1 f d k h))
      (fun h => Or.inr (mentionsConst_abstract1 a d k h))
  | .lam ty b m, d, k, h => by
    simp only [Expr.abstract1, mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.elim (fun h => Or.inl (mentionsConst_abstract1 ty d k h))
      (fun h => Or.inr (mentionsConst_abstract1 b d (k + 1) h))
  | .forallE ty b m, d, k, h => by
    simp only [Expr.abstract1, mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.elim (fun h => Or.inl (mentionsConst_abstract1 ty d k h))
      (fun h => Or.inr (mentionsConst_abstract1 b d (k + 1) h))
  | .letE ty v b, d, k, h => by
    simp only [Expr.abstract1, mentionsConst, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (mentionsConst_abstract1 ty d k h))
    · exact Or.inl (Or.inr (mentionsConst_abstract1 v d k h))
    · exact Or.inr (mentionsConst_abstract1 b d (k + 1) h)
  | .lit _, _, _, h => h
  | .proj s i x, d, k, h => by
    simp only [Expr.abstract1, mentionsConst, Bool.or_eq_true] at h ⊢
    exact h.elim Or.inl (fun h => Or.inr (mentionsConst_abstract1 x d k h))

theorem MentionsOnly.abstract1 {e : Expr} (he : MentionsOnly ok e) (d k : Nat) :
    MentionsOnly ok (e.abstract1 d k) := fun T hT => he T (mentionsConst_abstract1 e d k hT)

/-- Level instantiation keeps every constant's name. -/
theorem mentionsConst_instantiateLevelParams {T : Name} (ks : List Name) (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).mentionsConst T = e.mentionsConst T
  | .bvar _ => rfl
  | .fvar idx ty => by
    simp only [Expr.instantiateLevelParams, mentionsConst]
    exact mentionsConst_instantiateLevelParams ks us ty
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a => by
    simp only [Expr.instantiateLevelParams, mentionsConst]
    rw [mentionsConst_instantiateLevelParams ks us f, mentionsConst_instantiateLevelParams ks us a]
  | .lam ty b _ => by
    simp only [Expr.instantiateLevelParams, mentionsConst]
    rw [mentionsConst_instantiateLevelParams ks us ty, mentionsConst_instantiateLevelParams ks us b]
  | .forallE ty b _ => by
    simp only [Expr.instantiateLevelParams, mentionsConst]
    rw [mentionsConst_instantiateLevelParams ks us ty, mentionsConst_instantiateLevelParams ks us b]
  | .letE ty v b => by
    simp only [Expr.instantiateLevelParams, mentionsConst]
    rw [mentionsConst_instantiateLevelParams ks us ty, mentionsConst_instantiateLevelParams ks us v,
      mentionsConst_instantiateLevelParams ks us b]
  | .lit _ => rfl
  | .proj _ _ x => by
    simp only [Expr.instantiateLevelParams, mentionsConst]
    rw [mentionsConst_instantiateLevelParams ks us x]

theorem MentionsOnly.instantiateLevelParams {e : Expr} (he : MentionsOnly ok e) (ks : List Name)
    (us : List Level) : MentionsOnly ok (e.instantiateLevelParams ks us) := fun T hT =>
  he T (by rw [mentionsConst_instantiateLevelParams] at hT; exact hT)

/-- A term whose constants resolve mentions only stored names. -/
theorem MentionsOnly.of_constsResolve {env : Env} :
    ∀ (e : Expr), e.constsResolve env = true → MentionsOnly (fun T => (env.find? T).isSome = true) e
  | .bvar _, _, _, h => nomatch h
  | .sort _, _, _, h => nomatch h
  | .lit _, _, _, h => nomatch h
  | .const n _, hr, T, h => by
    simp only [mentionsConst, beq_iff_eq] at h
    rw [← h]; exact hr
  | .fvar _ ty, hr, T, h => MentionsOnly.of_constsResolve ty hr T h
  | .app f a, hr, T, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [mentionsConst, Bool.or_eq_true] at h
    exact h.elim (MentionsOnly.of_constsResolve f hr.1 T) (MentionsOnly.of_constsResolve a hr.2 T)
  | .lam ty b _, hr, T, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [mentionsConst, Bool.or_eq_true] at h
    exact h.elim (MentionsOnly.of_constsResolve ty hr.1 T) (MentionsOnly.of_constsResolve b hr.2 T)
  | .forallE ty b _, hr, T, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [mentionsConst, Bool.or_eq_true] at h
    exact h.elim (MentionsOnly.of_constsResolve ty hr.1 T) (MentionsOnly.of_constsResolve b hr.2 T)
  | .letE ty v b, hr, T, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [mentionsConst, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · exact MentionsOnly.of_constsResolve ty hr.1.1 T h
    · exact MentionsOnly.of_constsResolve v hr.1.2 T h
    · exact MentionsOnly.of_constsResolve b hr.2 T h
  | .proj sn _ x, hr, T, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [mentionsConst, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact hr.1
    · exact MentionsOnly.of_constsResolve x hr.2 T h

end Expr

theorem mentionsOnly_closeTelescope {ok : Name → Prop} :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) {body : Expr},
      (∀ b ∈ bs, Expr.MentionsOnly ok b.1) → Expr.MentionsOnly ok body →
      Expr.MentionsOnly ok (ConLeche.closeTelescope bs i body)
  | [], _, _, _, hb => hb
  | (dom, bm) :: bs, i, body, hbs, hb => by
    show Expr.MentionsOnly ok
      (.forallE dom ((ConLeche.closeTelescope bs (i + 1) body).abstract1 i 0) bm)
    refine Expr.mentionsOnly_forallE.mpr ⟨hbs _ List.mem_cons_self, ?_⟩
    exact (mentionsOnly_closeTelescope bs (i + 1) (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
      hb).abstract1 i 0

theorem stripPis_mentionsOnly {ok : Name → Prop} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → Expr.MentionsOnly ok e →
      (∀ b ∈ bs, Expr.MentionsOnly ok b.1) ∧ Expr.MentionsOnly ok body
  | 0, e, bs, body, h, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun _ hb => nomatch hb), he⟩
  | n + 1, .forallE ty b m, bs, body, h, he => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs⟩ := h
    simp only [Prod.mk.injEq] at hbs
    obtain ⟨rfl, rfl⟩ := hbs
    obtain ⟨hty, hb⟩ := Expr.mentionsOnly_forallE.mp he
    obtain ⟨hbs₀, hbody⟩ := stripPis_mentionsOnly n h₀ hb
    refine ⟨fun x hx => ?_, hbody⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hty
    · exact hbs₀ x hx
  | n + 1, .bvar _, _, _, h, _ => nomatch h
  | n + 1, .fvar _ _, _, _, h, _ => nomatch h
  | n + 1, .sort _, _, _, h, _ => nomatch h
  | n + 1, .const _ _, _, _, h, _ => nomatch h
  | n + 1, .app _ _, _, _, h, _ => nomatch h
  | n + 1, .lam _ _ _, _, _, h, _ => nomatch h
  | n + 1, .letE _ _ _, _, _, h, _ => nomatch h
  | n + 1, .lit _, _, _, h, _ => nomatch h
  | n + 1, .proj _ _ _, _, _, h, _ => nomatch h

/-- **The invariant**: every pin's components and every UNPROCESSED
constructor (a type at index `qhead` or later — the worklist processes
the types in order) mention only `ok` constants. -/
structure MentionInv (ok : Name → Prop) (qhead : Nat) (st : ElimState) : Prop where
  pins : ∀ q ∈ st.pins, Expr.MentionsOnly ok q.pin
  ctors : ∀ i, qhead ≤ i → ∀ t, st.types[i]? = some t → ∀ c ∈ t.ctors, Expr.MentionsOnly ok c.2.1

/-- The containers' names and stored constructors are `ok`. -/
@[expose] def ContainersMentionOnly (env : Env) (ok : Name → Prop) : Prop :=
  ∀ (I : Name) (ci : ContainerInfo), containerInfo? env I = some ci →
    ∀ J ∈ ci.members, ok J.name ∧ ∀ c ∈ J.ctors, Expr.MentionsOnly ok c.type

/-- A mint keeps the invariant. -/
theorem mkCopies_mentionInv {env : Env} {ok : Name → Prop} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat} {qhead : Nat}
    (hpbs : ∀ b ∈ pbs, Expr.MentionsOnly ok b.1) (hDs : ∀ D ∈ Ds, Expr.MentionsOnly ok D) :
    ∀ {members : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', got) →
      (∀ J ∈ members, ok J.name ∧ ∀ c ∈ J.ctors, Expr.MentionsOnly ok c.type) →
      MentionInv ok qhead st → MentionInv ok qhead st' := by
  intro members st st' got hmk hok hinv
  obtain ⟨copies, hclen, hty, hpin, hall⟩ := mkCopies_spec hmk
  refine ⟨fun q hq => ?_, fun i hi t ht c hc => ?_⟩
  · rw [hpin] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hinv.pins q hq
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hq
      rw [List.getElem?_zipWith] at hj
      split at hj
      · next c J hc hJ =>
        obtain rfl := Option.some.inj hj
        exact Expr.MentionsOnly.mkAppN (Expr.mentionsOnly_const (hok J (List.mem_of_getElem? hJ)).1)
          Ds hDs
      · exact nomatch hj
  · rw [hty] at ht
    rcases Nat.lt_or_ge i st.types.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at ht
      exact hinv.ctors i hi t ht c hc
    · rw [List.getElem?_append_right hge] at ht
      have hiJ : i - st.types.length < members.length := by
        rw [← hclen]; exact (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨copy, hcopy, hmkc, -⟩ := hall _ _ (List.getElem?_eq_getElem hiJ)
      obtain rfl : t = copy := Option.some.inj (ht.symm.trans hcopy)
      obtain ⟨-, -, -, hctors⟩ := mkCopy_inv hmkc
      obtain ⟨l, hl⟩ := List.getElem?_of_mem hc
      have hlJ : l < members[i - st.types.length].ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hl).1
        rw [(mkCopy_inv hmkc).2.2.1] at this
        exact this
      obtain ⟨cI, hcI, hl'⟩ := hctors l _ (List.getElem?_eq_getElem hlJ)
      obtain rfl := Option.some.inj (hl.symm.trans hl')
      have hJok := (hok _ (List.getElem_mem hiJ)).2
      show Expr.MentionsOnly ok (ConLeche.closeTelescope pbs 0 cI)
      refine mentionsOnly_closeTelescope pbs 0 hpbs (Expr.MentionsOnly.instPis hcI ?_ hDs)
      exact (hJok _ (List.getElem_mem hlJ)).instantiateLevelParams _ _

/-- The openers of a telescope mention only what the telescope does. -/
theorem openPisAtFvars_mentionsOnly {ok : Name → Prop} :
    ∀ (k : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr},
      openPisAtFvars k e d = some (fvs, body) → Expr.MentionsOnly ok e →
      (∀ x ∈ fvs, Expr.MentionsOnly ok x) ∧ Expr.MentionsOnly ok body
  | 0, e, d, fvs, body, h, he => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun _ hx => nomatch hx), he⟩
  | k + 1, .forallE dom b m, d, fvs, body, h, he => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs₀ body₀ h₀ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hdom, hb⟩ := Expr.mentionsOnly_forallE.mp he
      have hfv : Expr.MentionsOnly ok (.fvar d dom) := fun T hT => hdom T hT
      obtain ⟨hfvs, hbody⟩ := openPisAtFvars_mentionsOnly k h₀ (hb.instantiate1 hfv 0)
      refine ⟨fun x hx => ?_, hbody⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfv
      · exact hfvs x hx
    · exact nomatch h
  | k + 1, .bvar _, _, _, _, h, _ => nomatch h
  | k + 1, .fvar _ _, _, _, _, h, _ => nomatch h
  | k + 1, .sort _, _, _, _, h, _ => nomatch h
  | k + 1, .const _ _, _, _, _, h, _ => nomatch h
  | k + 1, .app _ _, _, _, _, h, _ => nomatch h
  | k + 1, .lam _ _ _, _, _, _, h, _ => nomatch h
  | k + 1, .letE _ _ _, _, _, _, h, _ => nomatch h
  | k + 1, .lit _, _, _, _, h, _ => nomatch h
  | k + 1, .proj _ _ _, _, _, _, h, _ => nomatch h

/-- A fire keeps the invariant: the new pins' components and the new
copies' constructors are built from the fired node's arguments. -/
theorem replaceIfNested_mentionInv {env : Env} {ok : Name → Prop} {blvls : List Level}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hcm : ContainersMentionOnly env ok)
    (hpbs : ∀ b ∈ pbs, Expr.MentionsOnly ok b.1) {qhead : Nat} {st st' : ElimState} {e r : Expr}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st')))
    (he : Expr.MentionsOnly ok e) (hinv : MentionInv ok qhead st) : MentionInv ok qhead st' := by
  unfold replaceIfNested at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · next I lvls hfn =>
      split at h
      · split at h
        · exact nomatch h
        · split at h
          · split at h
            · exact nomatch h
            · exact nomatch h
          · next ci hci =>
            split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · next nested hocc =>
                split at h
                · exact nomatch h
                · split at h
                  · next q hq =>
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact hinv
                  · split at h
                    · exact nomatch h
                    · next p hmk =>
                      obtain ⟨stq, gotq⟩ := p
                      split at h
                      · exact nomatch h
                      · next auxI hgot =>
                        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact mkCopies_mentionInv hpbs
                          (fun D hD => he.getAppArgs D (List.mem_of_mem_take hD)) hmk
                          (fun J hJ => hcm I ci hci J hJ) hinv
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- The walk keeps the invariant whenever its input mentions only `ok`
constants (its output may not: that is the point of the walk). -/
theorem replaceAllNested_mentionInv {env : Env} {ok : Name → Prop} {blvls : List Level}
    {params : List Expr} {pbs : List (Expr × BinderMeta)} (hcm : ContainersMentionOnly env ok)
    (hpbs : ∀ b ∈ pbs, Expr.MentionsOnly ok b.1) {qhead : Nat} :
    ∀ (e : Expr) {st : ElimState} {r : Expr × ElimState},
      replaceAllNested env blvls params pbs st e = .ok r → Expr.MentionsOnly ok e →
      MentionInv ok qhead st → MentionInv ok qhead r.2 := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mentionInv hcm hpbs hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := Expr.mentionsOnly_app.mp he
            exact iha (r := (x₂, st₂)) h₂ ha (ihf (r := (x₁, st₁)) h₁ hf hinv)
  | lam ty b bm ihty ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mentionInv hcm hpbs hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := Expr.mentionsOnly_lam.mp he
            exact ihb (r := (x₂, st₂)) h₂ ha (ihty (r := (x₁, st₁)) h₁ hf hinv)
  | forallE ty b bm ihty ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mentionInv hcm hpbs hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := Expr.mentionsOnly_forallE.mp he
            exact ihb (r := (x₂, st₂)) h₂ ha (ihty (r := (x₁, st₁)) h₁ hf hinv)
  | letE ty v b ihty ihv ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mentionInv hcm hpbs hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            split at h
            · contradiction
            · next x₃ st₃ h₃ =>
              obtain rfl := Except.ok.inj h
              have hty : Expr.MentionsOnly ok ty := fun T hT => he T (by
                simp only [Expr.mentionsConst, Bool.or_eq_true]; exact Or.inl (Or.inl hT))
              have hv : Expr.MentionsOnly ok v := fun T hT => he T (by
                simp only [Expr.mentionsConst, Bool.or_eq_true]; exact Or.inl (Or.inr hT))
              have hb : Expr.MentionsOnly ok b := fun T hT => he T (by
                simp only [Expr.mentionsConst, Bool.or_eq_true]; exact Or.inr hT)
              exact ihb (r := (x₃, st₃)) h₃ hb (ihv (r := (x₂, st₂)) h₂ hv (ihty (r := (x₁, st₁)) h₁ hty hinv))
  | proj sn i x ihx =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_mentionInv hcm hpbs hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          obtain rfl := Except.ok.inj h
          have hx : Expr.MentionsOnly ok x := fun T hT => he T (by
            simp only [Expr.mentionsConst, Bool.or_eq_true]; exact Or.inr hT)
          exact ihx (r := (x₁, st₁)) h₁ hx hinv
  | bvar i =>
    intro st r h _ hinv
    unfold replaceAllNested at h
    split at h
    · obtain rfl := Except.ok.inj h; exact hinv
    · rw [show replaceIfNested env blvls params pbs st (.bvar i) = .ok none from rfl] at h
      obtain rfl := Except.ok.inj h; exact hinv
  | fvar i ty =>
    intro st r h _ hinv
    unfold replaceAllNested at h
    split at h
    · obtain rfl := Except.ok.inj h; exact hinv
    · rw [show replaceIfNested env blvls params pbs st (.fvar i ty) = .ok none from rfl] at h
      obtain rfl := Except.ok.inj h; exact hinv
  | sort u =>
    intro st r h _ hinv
    unfold replaceAllNested at h
    split at h
    · obtain rfl := Except.ok.inj h; exact hinv
    · rw [show replaceIfNested env blvls params pbs st (.sort u) = .ok none from rfl] at h
      obtain rfl := Except.ok.inj h; exact hinv
  | const n us =>
    intro st r h _ hinv
    unfold replaceAllNested at h
    split at h
    · obtain rfl := Except.ok.inj h; exact hinv
    · rw [show replaceIfNested env blvls params pbs st (.const n us) = .ok none from rfl] at h
      obtain rfl := Except.ok.inj h; exact hinv
  | lit l =>
    intro st r h _ hinv
    unfold replaceAllNested at h
    split at h
    · obtain rfl := Except.ok.inj h; exact hinv
    · rw [show replaceIfNested env blvls params pbs st (.lit l) = .ok none from rfl] at h
      obtain rfl := Except.ok.inj h; exact hinv

/-- One type's constructors rewritten: the invariant is kept (the
walk's inputs are the constructors opened at the openers). -/
theorem elimCtors_mentionInv {env : Env} {ok : Name → Prop} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} (hcm : ContainersMentionOnly env ok)
    (hpbs : ∀ b ∈ pbs₀, Expr.MentionsOnly ok b.1) (hpar : ∀ p ∈ params, Expr.MentionsOnly ok p)
    {qhead : Nat} :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {r : List (Name × Expr × Nat) × ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok r →
      (∀ c ∈ cs, Expr.MentionsOnly ok c.2.1) → MentionInv ok qhead st → MentionInv ok qhead r.2
  | [], st, r, h, _, hinv => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hinv
  | (c, cty, nF) :: rest, st, r, h, hcs, hinv => by
    simp only [elimCtors, bind, Except.bind] at h
    split at h
    · next pbs rest₀ hstrip =>
      split at h
      · next cbody hinst =>
        split at h
        · contradiction
        · next q st₁ hq =>
          split at h
          · contradiction
          · next rest' st₂ hrest =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hcty : Expr.MentionsOnly ok cty := hcs _ List.mem_cons_self
            have hinv₁ := replaceAllNested_mentionInv hcm hpbs _ hq
              (Expr.MentionsOnly.instPis hinst hcty hpar) hinv
            have hres := elimCtors_mentionInv hcm hpbs hpar hrest
              (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hinv₁
            exact hres
      · contradiction
    · contradiction

/-- The worklist keeps the pins' half of the invariant to the end. -/
theorem elimLoop_mentionInv {env : Env} {ok : Name → Prop} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} (hcm : ContainersMentionOnly env ok)
    (hpbs : ∀ b ∈ pbs₀, Expr.MentionsOnly ok b.1) (hpar : ∀ p ∈ params, Expr.MentionsOnly ok p) :
    ∀ {fuel qhead : Nat} {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      MentionInv ok qhead st → ∀ q ∈ st'.pins, Expr.MentionsOnly ok q.pin
  | 0, _, _, _, h, _ => nomatch h
  | fuel + 1, qhead, st, st', h, hinv => by
    simp only [elimLoop] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv.pins
    · next t ht =>
      split at h
      · exact nomatch h
      · next cs' st₁ hcs =>
        have hinv₁ := elimCtors_mentionInv hcm hpbs hpar hcs (hinv.ctors qhead (Nat.le_refl _) t ht) hinv
        refine elimLoop_mentionInv hcm hpbs hpar h ⟨hinv₁.pins, fun i hi t' ht' c hc => ?_⟩
        rw [List.getElem?_set_ne (by omega)] at ht'
        exact hinv₁.ctors i (by omega) t' ht' c hc

/-- **THE PINS MENTION ONLY `ok` CONSTANTS** at the elimination's end,
given the containers' names and constructors `ok`, the block's own
constructors `ok` and the first former's type `ok`. -/
theorem elimNested_mentionInv {env : Env} {ok : Name → Prop} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState} (hcm : ContainersMentionOnly env ok)
    (h : elimNested env nP lps types = .ok st)
    (hty : ∀ t ∈ types, ∀ c ∈ t.ctors, Expr.MentionsOnly ok c.2.1)
    (ht₀ : ∀ t₀ ∈ types.head?, Expr.MentionsOnly ok t₀.type) :
    ∀ q ∈ st.pins, Expr.MentionsOnly ok q.pin := by
  unfold elimNested at h
  split at h
  · next t₀ hh =>
    split at h
    · next params body hop =>
      split at h
      · next pbs body₀ hstrip =>
        have hok : Expr.MentionsOnly ok t₀.type := ht₀ t₀ (by rw [hh]; exact rfl)
        have hpar : ∀ p ∈ params, Expr.MentionsOnly ok p := (openPisAtFvars_mentionsOnly nP hop hok).1
        have hpbs : ∀ b ∈ pbs, Expr.MentionsOnly ok b.1 := (stripPis_mentionsOnly nP hstrip hok).1
        have hinv₀ : MentionInv ok 0 ⟨types, [], 1⟩ :=
          ⟨(fun q hq => nomatch hq), fun i _ t ht c hc => hty t (List.mem_of_getElem? ht) c hc⟩
        exact elimLoop_mentionInv hcm hpbs hpar h hinv₀
      · contradiction
    · contradiction
  · contradiction

end ConLeche
