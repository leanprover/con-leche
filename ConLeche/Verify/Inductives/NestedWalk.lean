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

end ConLeche
