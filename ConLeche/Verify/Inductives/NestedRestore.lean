module

public import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.Denote.TeleOpen

public section

/-!
# The restore, evaluated (task #279 M-D′ D1, the syntactic half)

`restoreNested R` (`Kernel/Inductives/NestedInstall.lean`) is official's
`restore_nested`: the leading `nP` binders are stripped, the body is
walked TOP-DOWN by `restoreWalk` — a node headed by a copy's name is
replaced by the container at the copy's pin (`auxJ p⃗ is ↦ J Ds is`,
`auxJ.c p⃗ ↦ J.c Ds`, `auxJ.rec ↦ T₁.rec_k`) and its children are NOT
visited; a node mentioning none of the table's names is returned as it
stands (the prune); every other node is rebuilt from its walked
children — and the telescope is put back.  Since K.19 the stored
restored constants ARE `restoreNested R` of the auxiliary ones
(`restoreCtors_id`, `restoreRecTys_id`, `restoreRules_id`), so the
model tier reads a restored constant by evaluating this walk on the
auxiliary constant's shape.

The walk runs on RAW terms (loose bound variables, the pin lifted by
the walk's depth), while every shape the model tier holds is OPENED
(binders instantiated at `fvar`s: `FixOpened`, `openPisAtFvars`).  This
module evaluates the restore at the opened level:

* **`restoreI R`** — the same walk with the pins already in the
  context's own variables (no lift, no depth); **`RestoreTbl.instAt R ps`**
  puts a table's abstracted pins at the parameter variables `ps`.
* **`restoreWalk_instSeq`** (the commutation): the raw walk at depth
  `d`, instantiated at the parameter variables and `d` inner variables,
  is `restoreI` of the instantiated input — on the nose.  The only
  content is at a fire, where `instSeq_liftLooseBVars_prefix` puts the
  lifted pin back at the parameters.
* **`restoreNested_openPis`**: opening a restored constant at
  `fvar`s gives, binder by binder, `restoreI` of the auxiliary
  constant's opened binder (`ErasedEq`: the openers' annotations differ
  between the two sides, and nothing the model reads sees them).
* the EVALUATION lemmas of `restoreI` on the shapes the model holds:
  the identity on a term mentioning none of the table's names outside
  `fvar` annotations (`restoreI_eq_self`), the fire at a copy
  application (`restoreI_fire`), the structural descent through `∀`/`λ`
  binders and a non-table constant's spine.

The fvar-annotation subtlety: `mentionsConst` looks inside `fvar`
annotations, so the prune of an OPENED term can differ from the raw
prune (an opener's annotation is a copy-typed earlier field).  The
walk's result does not: `mentionsConstE` is `mentionsConst` blind to
`fvar` annotations, and a term whose `mentionsConstE` clears every
table name is its own restoration whether or not the prune fires.
-/

namespace ConLeche

/-! ## `mentionsConst`, blind to `fvar` annotations -/

/-- `mentionsConst` outside `fvar` annotations: what the restore's
node step can see. -/
@[expose] def Expr.mentionsConstE (T : Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ | .fvar _ _ => false
  | .const n _ => n == T
  | .app f a => f.mentionsConstE T || a.mentionsConstE T
  | .lam ty b _ | .forallE ty b _ => ty.mentionsConstE T || b.mentionsConstE T
  | .letE ty v b => ty.mentionsConstE T || v.mentionsConstE T || b.mentionsConstE T
  | .proj s _ e => s == T || e.mentionsConstE T

/-- The blind mention is a mention. -/
theorem Expr.mentionsConst_of_mentionsConstE {T : Name} :
    ∀ e : Expr, e.mentionsConstE T = true → e.mentionsConst T = true
  | .const n us, h => by simpa [Expr.mentionsConstE, Expr.mentionsConst] using h
  | .app f a, h => by
    simp only [Expr.mentionsConstE, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (mentionsConst_of_mentionsConstE f h)
    · exact Or.inr (mentionsConst_of_mentionsConstE a h)
  | .lam ty b _, h => by
    simp only [Expr.mentionsConstE, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (mentionsConst_of_mentionsConstE ty h)
    · exact Or.inr (mentionsConst_of_mentionsConstE b h)
  | .forallE ty b _, h => by
    simp only [Expr.mentionsConstE, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (mentionsConst_of_mentionsConstE ty h)
    · exact Or.inr (mentionsConst_of_mentionsConstE b h)
  | .letE ty v b, h => by
    simp only [Expr.mentionsConstE, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (mentionsConst_of_mentionsConstE ty h))
    · exact Or.inl (Or.inr (mentionsConst_of_mentionsConstE v h))
    · exact Or.inr (mentionsConst_of_mentionsConstE b h)
  | .proj s _ e, h => by
    simp only [Expr.mentionsConstE, Bool.or_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (mentionsConst_of_mentionsConstE e h)

/-- On an `fvar`-free term the two agree. -/
theorem Expr.mentionsConstE_eq_of_not_hasFvar {T : Name} :
    ∀ e : Expr, e.hasFvar = false → e.mentionsConstE T = e.mentionsConst T
  | .bvar _, _ | .sort _, _ | .lit _, _ | .const _ _, _ => rfl
  | .fvar _ _, h => nomatch h
  | .app f a, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.mentionsConstE, Expr.mentionsConst,
      mentionsConstE_eq_of_not_hasFvar f h.1, mentionsConstE_eq_of_not_hasFvar a h.2]
  | .lam ty b _, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.mentionsConstE, Expr.mentionsConst,
      mentionsConstE_eq_of_not_hasFvar ty h.1, mentionsConstE_eq_of_not_hasFvar b h.2]
  | .forallE ty b _, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.mentionsConstE, Expr.mentionsConst,
      mentionsConstE_eq_of_not_hasFvar ty h.1, mentionsConstE_eq_of_not_hasFvar b h.2]
  | .letE ty v b, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.mentionsConstE, Expr.mentionsConst,
      mentionsConstE_eq_of_not_hasFvar ty h.1.1, mentionsConstE_eq_of_not_hasFvar v h.1.2,
      mentionsConstE_eq_of_not_hasFvar b h.2]
  | .proj _ _ e, h => by
    simp only [Expr.hasFvar] at h
    simp only [Expr.mentionsConstE, Expr.mentionsConst, mentionsConstE_eq_of_not_hasFvar e h]

/-- The blind mention is invariant under erasure. -/
theorem Expr.mentionsConstE_erasedEq {T : Name} :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ → e₁.mentionsConstE T = e₂.mentionsConstE T
  | .bvar _, .bvar _, _ | .sort _, .sort _, _ | .lit _, .lit _, _ | .fvar _ _, .fvar _ _, _ => rfl
  | .const _ _, .const _ _, h => by
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .app f a, .app g b, h => by
    obtain ⟨h₁, h₂⟩ := h
    simp only [Expr.mentionsConstE, mentionsConstE_erasedEq h₁, mentionsConstE_erasedEq h₂]
  | .lam ty b _, .lam ty' b' _, h => by
    obtain ⟨-, h₁, h₂⟩ := h
    simp only [Expr.mentionsConstE, mentionsConstE_erasedEq h₁, mentionsConstE_erasedEq h₂]
  | .forallE ty b _, .forallE ty' b' _, h => by
    obtain ⟨-, h₁, h₂⟩ := h
    simp only [Expr.mentionsConstE, mentionsConstE_erasedEq h₁, mentionsConstE_erasedEq h₂]
  | .letE ty v b, .letE ty' v' b', h => by
    obtain ⟨h₁, h₂, h₃⟩ := h
    simp only [Expr.mentionsConstE, mentionsConstE_erasedEq h₁, mentionsConstE_erasedEq h₂,
      mentionsConstE_erasedEq h₃]
  | .proj s _ e, .proj s' _ e', h => by
    obtain ⟨rfl, -, h₃⟩ := h
    simp only [Expr.mentionsConstE, mentionsConstE_erasedEq h₃]

/-- Instantiating at `fvar`s adds no blind mention. -/
theorem Expr.mentionsConstE_instantiate1_fvar {T : Name} {k : Nat} {ty : Expr} :
    ∀ (e : Expr) (d : Nat),
      (e.instantiate1 (.fvar k ty) d).mentionsConstE T = e.mentionsConstE T
  | .bvar i, d => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .lit _, _ | .const _ _, _ => rfl
  | .app f a, d => by
    simp only [Expr.instantiate1, Expr.mentionsConstE, mentionsConstE_instantiate1_fvar f,
      mentionsConstE_instantiate1_fvar a]
  | .lam ty' b _, d => by
    simp only [Expr.instantiate1, Expr.mentionsConstE, mentionsConstE_instantiate1_fvar ty',
      mentionsConstE_instantiate1_fvar b]
  | .forallE ty' b _, d => by
    simp only [Expr.instantiate1, Expr.mentionsConstE, mentionsConstE_instantiate1_fvar ty',
      mentionsConstE_instantiate1_fvar b]
  | .letE ty' v b, d => by
    simp only [Expr.instantiate1, Expr.mentionsConstE, mentionsConstE_instantiate1_fvar ty',
      mentionsConstE_instantiate1_fvar v, mentionsConstE_instantiate1_fvar b]
  | .proj _ _ e, d => by
    simp only [Expr.instantiate1, Expr.mentionsConstE, mentionsConstE_instantiate1_fvar e]

/-- A list of `fvar`s. -/
def Expr.AllFvars (xs : List Expr) : Prop := ∀ a ∈ xs, ∃ k ty, a = Expr.fvar k ty

theorem Expr.mentionsConstE_instSeq_fvars {T : Name} :
    ∀ (xs : List Expr), Expr.AllFvars xs → ∀ (t : Nat) (e : Expr),
      (Expr.instSeq xs t e).mentionsConstE T = e.mentionsConstE T
  | [], _, _, _ => rfl
  | a :: xs, hxs, t, e => by
    obtain ⟨k, ty, rfl⟩ := hxs a (List.mem_cons_self ..)
    rw [Expr.instSeq, mentionsConstE_instSeq_fvars xs (fun b hb => hxs b (List.mem_cons_of_mem _ hb)),
      Expr.mentionsConstE_instantiate1_fvar]

/-- A mention survives instantiation at `fvar`s. -/
theorem Expr.mentionsConst_instSeq_fvars_of {T : Name} :
    ∀ (xs : List Expr), Expr.AllFvars xs → ∀ (t : Nat) (e : Expr),
      e.mentionsConst T = true → (Expr.instSeq xs t e).mentionsConst T = true := by
  intro xs hxs t e h
  have h1 : e.mentionsConstE T = true ∨ e.mentionsConst T = true := Or.inr h
  -- go through the blind mention when possible, else by monotonicity of `instantiate1`
  suffices hgen : ∀ (xs : List Expr) (t : Nat) (e : Expr),
      e.mentionsConst T = true → (Expr.instSeq xs t e).mentionsConst T = true from
    hgen xs t e h
  intro xs
  induction xs with
  | nil => intro t e h; exact h
  | cons a xs ih =>
    intro t e h
    rw [Expr.instSeq]
    exact ih _ _ (mentionsConst_instantiate1_mono a e t h)
where
  mentionsConst_instantiate1_mono (v : Expr) :
      ∀ (e : Expr) (d : Nat), e.mentionsConst T = true →
        (e.instantiate1 v d).mentionsConst T = true
    | .bvar _, _, h => nomatch h
    | .fvar _ ty, _, h => h
    | .sort _, _, h => nomatch h
    | .lit _, _, h => nomatch h
    | .const _ _, _, h => h
    | .app f a, d, h => by
      simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (mentionsConst_instantiate1_mono v f d h)
      · exact Or.inr (mentionsConst_instantiate1_mono v a d h)
    | .lam ty b _, d, h => by
      simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (mentionsConst_instantiate1_mono v ty d h)
      · exact Or.inr (mentionsConst_instantiate1_mono v b (d + 1) h)
    | .forallE ty b _, d, h => by
      simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (mentionsConst_instantiate1_mono v ty d h)
      · exact Or.inr (mentionsConst_instantiate1_mono v b (d + 1) h)
    | .letE ty vv b, d, h => by
      simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (mentionsConst_instantiate1_mono v ty d h))
      · exact Or.inl (Or.inr (mentionsConst_instantiate1_mono v vv d h))
      · exact Or.inr (mentionsConst_instantiate1_mono v b (d + 1) h)
    | .proj s _ e, d, h => by
      simp only [Expr.instantiate1, Expr.mentionsConst, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (mentionsConst_instantiate1_mono v e d h)

/-- A blind mention of the head is a blind mention of the spine. -/
theorem Expr.mentionsConstE_mkAppN_of_head {T : Name} :
    ∀ (as : List Expr) (f : Expr), f.mentionsConstE T = true →
      (Expr.mkAppN f as).mentionsConstE T = true
  | [], _, h => h
  | a :: as, f, h =>
    mentionsConstE_mkAppN_of_head as (.app f a) (by simp [Expr.mentionsConstE, h])

/-- A successful `lookup` names a member. -/
theorem List.mem_of_lookup_some {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons q l ih =>
    obtain ⟨k', v'⟩ := q
    rw [List.lookup_cons] at h
    cases hk : (k == k') with
    | true =>
      rw [hk] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at hk
      subst hk
      exact List.mem_cons_self ..
    | false =>
      rw [hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `lookup` through a value-map. -/
theorem List.lookup_map_snd {α β γ : Type} [BEq α] {l : List (α × β)} {k : α} {f : β → γ} :
    (l.map fun q => (q.1, f q.2)).lookup k = (l.lookup k).map f := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨k', v'⟩ := q
    simp only [List.map_cons, List.lookup_cons]
    cases hk : (k == k') <;> simp [ih]

/-! ## The restore at the instantiated level -/

/-- `restoreNode` with the pins in the context's own variables: no
lift.  `none` — descend (or, where the raw step would have thrown, an
answer the commutation never reaches). -/
@[expose] def restoreNodeI (R : RestoreTbl) (e : Expr) : Option Expr :=
  let head : Option Expr :=
    match e.getAppFn with
    | .const n _ =>
      let args := e.getAppArgs
      match R.pins.lookup n with
      | some pin =>
        if args.length < R.nP then none else some (Expr.mkAppN pin (args.drop R.nP))
      | none =>
        match R.ctorPins.find? (fun q => q.1 == n) with
        | some (_, pin, newName) =>
          if args.length < R.nP then none else
            match pin.getAppFn with
            | .const _ ilvls =>
              some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (args.drop R.nP))
            | _ => none
        | none => none
    | _ => none
  match e with
  | .const n us =>
    match R.recMap.lookup n with
    | some n' => some (.const n' us)
    | none => head
  | _ => head

/-- One node of the instantiated walk: the prune, the node step, else
the children's answer `kids`. -/
@[expose] def restoreStepI (R : RestoreTbl) (e kids : Expr) : Expr :=
  if !R.auxNames.any (fun n => e.mentionsConst n) then e else
  match restoreNodeI R e with
  | some e' => e'
  | none => kids

/-- `restoreWalk` at the instantiated level: top-down, prune, node,
children. -/
@[expose] def restoreI (R : RestoreTbl) : Expr → Expr
  | .app f a => restoreStepI R (.app f a) (.app (restoreI R f) (restoreI R a))
  | .lam ty b bm => restoreStepI R (.lam ty b bm) (.lam (restoreI R ty) (restoreI R b) bm)
  | .forallE ty b bm =>
    restoreStepI R (.forallE ty b bm) (.forallE (restoreI R ty) (restoreI R b) bm)
  | .letE ty v b =>
    restoreStepI R (.letE ty v b) (.letE (restoreI R ty) (restoreI R v) (restoreI R b))
  | .proj s i x => restoreStepI R (.proj s i x) (.proj s i (restoreI R x))
  | e => restoreStepI R e e

/-- A table's abstracted pins put at the parameter variables `ps`
(`Expr.instSeq ps (ps.length - 1)`: the outermost parameter first). -/
@[expose] def RestoreTbl.instAt (R : RestoreTbl) (ps : List Expr) : RestoreTbl :=
  { R with
    pins := R.pins.map fun q => (q.1, Expr.instSeq ps (ps.length - 1) q.2)
    ctorPins := R.ctorPins.map fun q => (q.1, Expr.instSeq ps (ps.length - 1) q.2.1, q.2.2) }

/-- The three maps' keys are table names (what the prune sees). -/
structure RestoreTbl.Named (R : RestoreTbl) : Prop where
  pinsNamed : ∀ q ∈ R.pins, q.1 ∈ R.auxNames
  ctorPinsNamed : ∀ q ∈ R.ctorPins, q.1 ∈ R.auxNames
  recMapNamed : ∀ q ∈ R.recMap, q.1 ∈ R.auxNames

/-- **The table's well-formedness** the commutation needs: the keys
are table names, the pins are closed below the parameter count, and
the constructor pins are constant-headed spines. -/
structure RestoreTbl.WF (R : RestoreTbl) : Prop extends RestoreTbl.Named R where
  pinsBounded : ∀ q ∈ R.pins, q.2.looseBVarsBounded R.nP = true
  ctorPinsBounded : ∀ q ∈ R.ctorPins, q.2.1.looseBVarsBounded R.nP = true
  ctorPinsHead : ∀ q ∈ R.ctorPins, ∃ (J : Name) (lvls : List Level) (Ds : List Expr),
    q.2.1 = Expr.mkAppN (.const J lvls) Ds

theorem RestoreTbl.Named.instAt {R : RestoreTbl} (h : R.Named) (ps : List Expr) :
    (R.instAt ps).Named := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, h.recMapNamed⟩
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact h.pinsNamed q' hq'
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact h.ctorPinsNamed q' hq'

/-! ## The raw walk: prune, node, the telescope -/

/-- The prune: a term mentioning none of the table's names is its own
restoration. -/
theorem restoreWalk_prune {R : RestoreTbl} {d : Nat} {e : Expr}
    (h : ∀ n ∈ R.auxNames, e.mentionsConst n = false) :
    restoreWalk R d e = .ok e := by
  unfold restoreWalk
  have : R.auxNames.any (fun n => e.mentionsConst n) = false := by
    rw [List.any_eq_false]
    intro n hn
    simp [h n hn]
  rw [this]
  rfl

/-- `restoreNode` declines at a `∀`. -/
theorem restoreNode_forallE (R : RestoreTbl) (d : Nat) (ty b : Expr) (bm : BinderMeta) :
    restoreNode R d (.forallE ty b bm) = .ok none := rfl

/-- `restoreNode` declines at a `λ`. -/
theorem restoreNode_lam (R : RestoreTbl) (d : Nat) (ty b : Expr) (bm : BinderMeta) :
    restoreNode R d (.lam ty b bm) = .ok none := rfl

/-- The walk through a `∀`: the domain at the same depth, the body one
deeper. -/
theorem restoreWalk_forallE_inv {R : RestoreTbl} {d : Nat} {ty b : Expr} {bm : BinderMeta}
    {e' : Expr} (h : restoreWalk R d (.forallE ty b bm) = .ok e') :
    ∃ ty' b', restoreWalk R d ty = .ok ty' ∧ restoreWalk R (d + 1) b = .ok b' ∧
      e' = .forallE ty' b' bm := by
  unfold restoreWalk at h
  split at h
  · next hprune =>
    simp only [Except.ok.injEq] at h
    subst h
    have hno : ∀ n ∈ R.auxNames, (Expr.forallE ty b bm).mentionsConst n = false := by
      intro n hn
      have := List.any_eq_false.mp (by simpa using hprune) n hn
      simpa using this
    refine ⟨ty, b, restoreWalk_prune ?_, restoreWalk_prune ?_, rfl⟩
    · intro n hn
      have := hno n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.1
    · intro n hn
      have := hno n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.2
  · rw [restoreNode_forallE] at h
    simp only at h
    split at h
    · next hty => exact nomatch h
    · next ty' hty =>
      split at h
      · exact nomatch h
      · next b' hb =>
        simp only [Except.ok.injEq] at h
        exact ⟨ty', b', hty, hb, h.symm⟩

/-- The walk through a `λ`. -/
theorem restoreWalk_lam_inv {R : RestoreTbl} {d : Nat} {ty b : Expr} {bm : BinderMeta}
    {e' : Expr} (h : restoreWalk R d (.lam ty b bm) = .ok e') :
    ∃ ty' b', restoreWalk R d ty = .ok ty' ∧ restoreWalk R (d + 1) b = .ok b' ∧
      e' = .lam ty' b' bm := by
  unfold restoreWalk at h
  split at h
  · next hprune =>
    simp only [Except.ok.injEq] at h
    subst h
    have hno : ∀ n ∈ R.auxNames, (Expr.lam ty b bm).mentionsConst n = false := by
      intro n hn
      have := List.any_eq_false.mp (by simpa using hprune) n hn
      simpa using this
    refine ⟨ty, b, restoreWalk_prune ?_, restoreWalk_prune ?_, rfl⟩
    · intro n hn
      have := hno n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.1
    · intro n hn
      have := hno n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      exact this.2
  · rw [restoreNode_lam] at h
    simp only at h
    split at h
    · exact nomatch h
    · next ty' hty =>
      split at h
      · exact nomatch h
      · next b' hb =>
        simp only [Except.ok.injEq] at h
        exact ⟨ty', b', hty, hb, h.symm⟩

/-- **The walk through a `∀`-telescope**: binder `j` is walked at
depth `d + j`, the residual at `d + n`, the binder data kept. -/
theorem restoreWalk_stripPis {R : RestoreTbl} :
    ∀ (n : Nat) {d : Nat} {e e' : Expr}, restoreWalk R d e = .ok e' →
      ∀ {bs : List (Expr × BinderMeta)} {r : Expr}, e.stripPis n = some (bs, r) →
      ∃ (bs' : List (Expr × BinderMeta)) (r' : Expr),
        e'.stripPis n = some (bs', r') ∧ bs'.length = bs.length ∧
        (∀ (j : Nat) (b b' : Expr × BinderMeta), bs[j]? = some b → bs'[j]? = some b' →
          b'.2 = b.2 ∧ restoreWalk R (d + j) b.1 = .ok b'.1) ∧
        restoreWalk R (d + n) r = .ok r'
  | 0, d, e, e', h, bs, r, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨[], e', rfl, rfl, ?_, by simpa using h⟩
    intro j b b' hb _
    simp at hb
  | n + 1, d, e, e', h, bs, r, hs => by
    match e, hs with
    | .forallE ty b bm, hs =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₁, r₁⟩, hs₁, hbs⟩ := hs
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨ty', b', hty, hb, rfl⟩ := restoreWalk_forallE_inv h
      obtain ⟨bs₂, r₂, hs₂, hlen, hall, hr⟩ := restoreWalk_stripPis n hb hs₁
      refine ⟨(ty', bm) :: bs₂, r₂, ?_, by simp [hlen], ?_, ?_⟩
      · simp only [Expr.stripPis, hs₂, Option.map_some]
      · intro j bb bb' hbb hbb'
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
          subst hbb hbb'
          exact ⟨rfl, by simpa using hty⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hbb hbb'
          obtain ⟨h1, h2⟩ := hall j bb bb' hbb hbb'
          exact ⟨h1, by rw [show d + (j + 1) = d + 1 + j by omega]; exact h2⟩
      · rw [show d + (n + 1) = d + 1 + n by omega]; exact hr
    | .bvar _, hs | .fvar _ _, hs | .sort _, hs | .const _ _, hs | .app _ _, hs
    | .lam _ _ _, hs | .letE _ _ _, hs | .lit _, hs | .proj _ _ _, hs =>
      simp [Expr.stripPis] at hs

/-- **`restoreNested` on a `∀`-telescope**: the leading `nP` binders
are kept, the body walked at depth `0`. -/
theorem restoreNested_stripPis {R : RestoreTbl} {e e' : Expr}
    (h : restoreNested R e = .ok e') {bs : List (Expr × BinderMeta)} {body : Expr}
    (hs : e.stripPis R.nP = some (bs, body)) :
    ∃ body', restoreWalk R 0 body = .ok body' ∧ e'.stripPis R.nP = some (bs, body') := by
  -- `stripPisOrLams` on a `∀`-telescope is `stripPis`, and the rebuild
  -- (`isPi = true` whenever there is a binder) puts the same binders back
  have hsol : ∀ (k : Nat) (e : Expr) (bs : List (Expr × BinderMeta)) (body : Expr),
      e.stripPis k = some (bs, body) → stripPisOrLams k e = some (bs, body) := by
    intro k
    induction k with
    | zero =>
      intro e bs body hs
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rfl
    | succ k ih =>
      intro e bs body hs
      match e, hs with
      | .forallE ty b bm, hs =>
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
        obtain ⟨⟨bs₁, r₁⟩, hs₁, hbs⟩ := hs
        simp only [Prod.mk.injEq] at hbs
        obtain ⟨rfl, rfl⟩ := hbs
        simp only [stripPisOrLams, ih b bs₁ r₁ hs₁, Option.map_some]
      | .bvar _, hs | .fvar _ _, hs | .sort _, hs | .const _ _, hs | .app _ _, hs
      | .lam _ _ _, hs | .letE _ _ _, hs | .lit _, hs | .proj _ _ _, hs =>
        simp [Expr.stripPis] at hs
  have hfold : ∀ (bs : List (Expr × BinderMeta)) (body' : Expr),
      (bs.foldr (fun (b : Expr × BinderMeta) acc => Expr.forallE b.1 acc b.2) body').stripPis
        bs.length = some (bs, body') := by
    intro bs body'
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.foldr_cons, List.length_cons, Expr.stripPis, ih, Option.map_some]
  unfold restoreNested at h
  simp only [hsol R.nP e bs body hs] at h
  split at h
  · exact nomatch h
  · next body' hw =>
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨body', hw, ?_⟩
    have hlen : bs.length = R.nP := stripPis_length' R.nP hs
    -- the rebuild's `isPi` flag: a `∀` at the head whenever `nP ≥ 1`
    cases hR : R.nP with
    | zero =>
      rw [hR] at hlen
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hlen
      subst hbs
      simp only [List.foldr_nil, Expr.stripPis]
    | succ k =>
      rw [hR] at hs hlen
      match e, hs with
      | .forallE ty b bm, hs =>
        simp only [ite_true]
        rw [← hlen]
        exact hfold bs body'
      | .bvar _, hs | .fvar _ _, hs | .sort _, hs | .const _ _, hs | .app _ _, hs
      | .lam _ _ _, hs | .letE _ _ _, hs | .lit _, hs | .proj _ _ _, hs =>
        simp [Expr.stripPis] at hs

/-! ## The raw node step, inverted -/

/-- The head part of `restoreNode` (its `let head`), as a function. -/
@[expose] def restoreHead (R : RestoreTbl) (d : Nat) (e : Expr) : Except CheckError (Option Expr) :=
  match e.getAppFn with
  | .const n _ =>
    match R.pins.lookup n with
    | some pin =>
      if e.getAppArgs.length < R.nP then
        .error (.invalid "failed to restore nested inductive types, auxiliary type is \
          not applied to all parameters")
      else .ok (some (Expr.mkAppN (pin.liftLooseBVars d 0) (e.getAppArgs.drop R.nP)))
    | none =>
      match R.ctorPins.find? (fun q => q.1 == n) with
      | some (_, pin, newName) =>
        if e.getAppArgs.length < R.nP then
          .error (.invalid "failed to restore nested inductive types, auxiliary \
            constructor is not applied to all parameters")
        else
          match (pin.liftLooseBVars d 0).getAppFn with
          | .const _ ilvls =>
            .ok (some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls)
              (pin.liftLooseBVars d 0).getAppArgs) (e.getAppArgs.drop R.nP)))
          | _ =>
            .error (.invalid "failed to restore nested inductive types, nested \
              occurrence is not an inductive type application")
      | none => .ok none
  | _ => .ok none

theorem restoreNode_eq (R : RestoreTbl) (d : Nat) (e : Expr) :
    restoreNode R d e =
      match e with
      | .const n us =>
        match R.recMap.lookup n with
        | some n' => .ok (some (.const n' us))
        | none => restoreHead R d e
      | _ => restoreHead R d e := by
  cases e <;> rfl

/-- `restoreHead`, inverted. -/
theorem restoreHead_ok_inv {R : RestoreTbl} {d : Nat} {e : Expr} {r : Option Expr}
    (h : restoreHead R d e = .ok r) :
    ((∀ (n : Name) (us : List Level), e.getAppFn ≠ .const n us) ∧ r = none) ∨
      ∃ (n : Name) (us : List Level), e.getAppFn = .const n us ∧
        ((∃ pin, R.pins.lookup n = some pin ∧ R.nP ≤ e.getAppArgs.length ∧
            r = some (Expr.mkAppN (pin.liftLooseBVars d 0) (e.getAppArgs.drop R.nP))) ∨
          (R.pins.lookup n = none ∧
            ∃ q : Name × Expr × Name, R.ctorPins.find? (fun q => q.1 == n) = some q ∧
              R.nP ≤ e.getAppArgs.length ∧
              ∃ (J : Name) (ilvls : List Level),
                (q.2.1.liftLooseBVars d 0).getAppFn = .const J ilvls ∧
                r = some (Expr.mkAppN (Expr.mkAppN (.const q.2.2 ilvls)
                  (q.2.1.liftLooseBVars d 0).getAppArgs) (e.getAppArgs.drop R.nP))) ∨
          (R.pins.lookup n = none ∧ R.ctorPins.find? (fun q => q.1 == n) = none ∧ r = none)) := by
  unfold restoreHead at h
  split at h
  · next n us hfn =>
    refine Or.inr ⟨n, us, hfn, ?_⟩
    split at h
    · next pin hpin =>
      split at h
      · exact nomatch h
      · next hlen =>
        simp only [Except.ok.injEq] at h
        exact Or.inl ⟨pin, hpin, by omega, h.symm⟩
    · next hpin =>
      split at h
      · next q _ pin newName hq =>
        split at h
        · exact nomatch h
        · next hlen =>
          split at h
          · next J ilvls hJ =>
            simp only [Except.ok.injEq] at h
            exact Or.inr (Or.inl ⟨hpin, (_, pin, newName), hq, by omega, J, ilvls, hJ, h.symm⟩)
          · exact nomatch h
      · next hq =>
        simp only [Except.ok.injEq] at h
        exact Or.inr (Or.inr ⟨hpin, hq, h.symm⟩)
  · next hfn =>
    simp only [Except.ok.injEq] at h
    exact Or.inl ⟨fun n us hc => hfn n us hc, h.symm⟩

/-- **`restoreNode`, inverted**: a recursor rename, or the head step
with the recursor map out of the way. -/
theorem restoreNode_ok_inv {R : RestoreTbl} {d : Nat} {e : Expr} {r : Option Expr}
    (h : restoreNode R d e = .ok r) :
    (∃ (n : Name) (us : List Level) (n' : Name), e = .const n us ∧ R.recMap.lookup n = some n' ∧
      r = some (.const n' us)) ∨
    ((∀ (n : Name) (us : List Level), e = .const n us → R.recMap.lookup n = none) ∧
      restoreHead R d e = .ok r) := by
  rw [restoreNode_eq] at h
  cases e with
  | const n us =>
    simp only at h
    cases hl : R.recMap.lookup n with
    | some n' =>
      rw [hl] at h
      simp only [Except.ok.injEq] at h
      exact Or.inl ⟨n, us, n', rfl, hl, h.symm⟩
    | none =>
      rw [hl] at h
      exact Or.inr ⟨fun m ms hm => by cases hm; exact hl, h⟩
  | bvar _ | fvar _ _ | sort _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
  | proj _ _ _ =>
    exact Or.inr ⟨fun _ _ hc => (nomatch hc), h⟩

/-! ## The instantiated node step, evaluated -/

/-- The head part of `restoreNodeI`. -/
@[expose] def restoreHeadI (R : RestoreTbl) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const n _ =>
    match R.pins.lookup n with
    | some pin =>
      if e.getAppArgs.length < R.nP then none
      else some (Expr.mkAppN pin (e.getAppArgs.drop R.nP))
    | none =>
      match R.ctorPins.find? (fun q => q.1 == n) with
      | some (_, pin, newName) =>
        if e.getAppArgs.length < R.nP then none else
          match pin.getAppFn with
          | .const _ ilvls =>
            some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs)
              (e.getAppArgs.drop R.nP))
          | _ => none
      | none => none
  | _ => none

theorem restoreNodeI_eq (R : RestoreTbl) (e : Expr) :
    restoreNodeI R e =
      match e with
      | .const n us =>
        match R.recMap.lookup n with
        | some n' => some (.const n' us)
        | none => restoreHeadI R e
      | _ => restoreHeadI R e := by
  cases e <;> rfl

theorem restoreNodeI_rec {R : RestoreTbl} {n n' : Name} {us : List Level}
    (h : R.recMap.lookup n = some n') :
    restoreNodeI R (.const n us) = some (.const n' us) := by
  rw [restoreNodeI_eq]
  simp only [h]

/-- The node step is the head step with the recursor map out of the way. -/
theorem restoreNodeI_eq_head {R : RestoreTbl} {e : Expr}
    (hrec : ∀ (n : Name) (us : List Level), e = .const n us → R.recMap.lookup n = none) :
    restoreNodeI R e = restoreHeadI R e := by
  rw [restoreNodeI_eq]
  cases e with
  | const n us => simp only [hrec n us rfl]
  | bvar _ | fvar _ _ | sort _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
  | proj _ _ _ => rfl

/-- The head step declines wherever the head is not a constant. -/
theorem restoreHeadI_nonconst {R : RestoreTbl} {e : Expr}
    (hfn : ∀ (n : Name) (us : List Level), e.getAppFn ≠ .const n us) :
    restoreHeadI R e = none := by
  unfold restoreHeadI
  split
  · next n us hn => exact absurd hn (hfn n us)
  · rfl

/-- The head step at a constant-headed spine. -/
theorem restoreHeadI_spine (R : RestoreTbl) (n : Name) (us : List Level) (args : List Expr) :
    restoreHeadI R (Expr.mkAppN (.const n us) args) =
      match R.pins.lookup n with
      | some pin => if args.length < R.nP then none else some (Expr.mkAppN pin (args.drop R.nP))
      | none =>
        match R.ctorPins.find? (fun q => q.1 == n) with
        | some (_, pin, newName) =>
          if args.length < R.nP then none else
            match pin.getAppFn with
            | .const _ ilvls =>
              some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (args.drop R.nP))
            | _ => none
        | none => none := by
  have hfn : (Expr.mkAppN (.const n us) args).getAppFn = .const n us := by
    rw [Expr.getAppFn_mkAppN]; rfl
  have hargs : (Expr.mkAppN (.const n us) args).getAppArgs = args := by
    rw [Expr.getAppArgs_mkAppN]; rfl
  unfold restoreHeadI
  rw [hfn, hargs]

/-! ## `restoreI`, unfolded -/

theorem restoreI_app (R : RestoreTbl) (f a : Expr) :
    restoreI R (.app f a) = restoreStepI R (.app f a) (.app (restoreI R f) (restoreI R a)) := rfl
theorem restoreI_lam (R : RestoreTbl) (ty b : Expr) (bm : BinderMeta) :
    restoreI R (.lam ty b bm) = restoreStepI R (.lam ty b bm) (.lam (restoreI R ty) (restoreI R b) bm) :=
  rfl
theorem restoreI_forallE (R : RestoreTbl) (ty b : Expr) (bm : BinderMeta) :
    restoreI R (.forallE ty b bm)
      = restoreStepI R (.forallE ty b bm) (.forallE (restoreI R ty) (restoreI R b) bm) := rfl
theorem restoreI_letE (R : RestoreTbl) (ty v b : Expr) :
    restoreI R (.letE ty v b)
      = restoreStepI R (.letE ty v b) (.letE (restoreI R ty) (restoreI R v) (restoreI R b)) := rfl
theorem restoreI_proj (R : RestoreTbl) (s : Name) (i : Nat) (x : Expr) :
    restoreI R (.proj s i x) = restoreStepI R (.proj s i x) (.proj s i (restoreI R x)) := rfl
theorem restoreI_bvar (R : RestoreTbl) (i : Nat) : restoreI R (.bvar i) = restoreStepI R (.bvar i) (.bvar i) :=
  rfl
theorem restoreI_fvar (R : RestoreTbl) (i : Nat) (ty : Expr) :
    restoreI R (.fvar i ty) = restoreStepI R (.fvar i ty) (.fvar i ty) := rfl
theorem restoreI_sort (R : RestoreTbl) (u : Level) : restoreI R (.sort u) = restoreStepI R (.sort u) (.sort u) :=
  rfl
theorem restoreI_const (R : RestoreTbl) (n : Name) (us : List Level) :
    restoreI R (.const n us) = restoreStepI R (.const n us) (.const n us) := rfl
theorem restoreI_lit (R : RestoreTbl) (l : Literal) : restoreI R (.lit l) = restoreStepI R (.lit l) (.lit l) := by rfl

/-- The step at a pruned node. -/
theorem restoreStepI_prune {R : RestoreTbl} {e kids : Expr}
    (h : ∀ n ∈ R.auxNames, e.mentionsConst n = false) : restoreStepI R e kids = e := by
  unfold restoreStepI
  have : R.auxNames.any (fun n => e.mentionsConst n) = false := by
    rw [List.any_eq_false]
    intro n hn
    simp [h n hn]
  rw [this]
  rfl

/-- The step at an unpruned node. -/
theorem restoreStepI_of_mentions {R : RestoreTbl} {e kids : Expr} {n : Name}
    (hn : n ∈ R.auxNames) (h : e.mentionsConst n = true) :
    restoreStepI R e kids = match restoreNodeI R e with | some e' => e' | none => kids := by
  unfold restoreStepI
  have : R.auxNames.any (fun n => e.mentionsConst n) = true :=
    List.any_eq_true.mpr ⟨n, hn, h⟩
  rw [this]
  rfl

/-- **A term mentioning no table name outside `fvar` annotations is its
own restoration** — whether or not the prune fires. -/
theorem restoreI_eq_self {R : RestoreTbl} (hR : R.Named) :
    ∀ (e : Expr), (∀ n ∈ R.auxNames, e.mentionsConstE n = false) → restoreI R e = e := by
  -- the node step declines on such a term
  have hnode : ∀ (e : Expr), (∀ n ∈ R.auxNames, e.mentionsConstE n = false) →
      restoreNodeI R e = none := by
    intro e he
    by_cases hc : ∃ (n : Name) (us : List Level), e.getAppFn = .const n us
    · obtain ⟨n, us, hfn⟩ := hc
      have hnot : n ∉ R.auxNames := by
        intro hn
        have := he n hn
        rw [← Expr.mkAppN_getApp e, hfn] at this
        have hm : (Expr.mkAppN (.const n us) e.getAppArgs).mentionsConstE n = true :=
          Expr.mentionsConstE_mkAppN_of_head _ _ (by simp [Expr.mentionsConstE])
        rw [hm] at this
        exact nomatch this
      have hpins : R.pins.lookup n = none := by
        cases hl : R.pins.lookup n with
        | none => rfl
        | some pin =>
          exfalso
          exact hnot (hR.pinsNamed (n, pin) (List.mem_of_lookup_some hl))
      have hctor : R.ctorPins.find? (fun q => q.1 == n) = none := by
        cases hl : R.ctorPins.find? (fun q => q.1 == n) with
        | none => rfl
        | some q =>
          exfalso
          have hq := List.find?_some hl
          have hmem := List.mem_of_find?_eq_some hl
          rw [beq_iff_eq] at hq
          exact hnot (hq ▸ hR.ctorPinsNamed q hmem)
      have hrec : R.recMap.lookup n = none := by
        cases hl : R.recMap.lookup n with
        | none => rfl
        | some n' =>
          exfalso
          exact hnot (hR.recMapNamed (n, n') (List.mem_of_lookup_some hl))
      rw [restoreNodeI_eq_head (fun m ms hm => by
          rw [hm] at hfn
          simp only [Expr.getAppFn, Expr.const.injEq] at hfn
          rw [hfn.1]; exact hrec),
        ← Expr.mkAppN_getApp e, hfn, restoreHeadI_spine, hpins, hctor]
    · have hc' : ∀ (n : Name) (us : List Level), e.getAppFn ≠ .const n us :=
        fun n us h => hc ⟨n, us, h⟩
      rw [restoreNodeI_eq_head (fun n us hc'' => absurd (by rw [hc'']; rfl) (hc' n us))]
      exact restoreHeadI_nonconst hc'
  intro e
  induction e with
  | bvar i =>
    intro _
    rw [restoreI_bvar]; unfold restoreStepI; split
    · rfl
    · simp only [hnode (.bvar i) (fun n hn => rfl)]
  | fvar i ty =>
    intro _
    rw [restoreI_fvar]; unfold restoreStepI; split
    · rfl
    · simp only [hnode (.fvar i ty) (fun n hn => rfl)]
  | sort u =>
    intro _
    rw [restoreI_sort]; unfold restoreStepI; split
    · rfl
    · simp only [hnode (.sort u) (fun n hn => rfl)]
  | const n us =>
    intro he
    rw [restoreI_const]; unfold restoreStepI; split
    · rfl
    · simp only [hnode _ he]
  | lit l =>
    intro _
    rw [restoreI_lit]; unfold restoreStepI; split
    · rfl
    · simp only [hnode (.lit l) (fun n hn => rfl)]
  | app f a ihf iha =>
    intro he
    have hf : ∀ n ∈ R.auxNames, f.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.1
    have ha : ∀ n ∈ R.auxNames, a.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.2
    rw [restoreI_app]; unfold restoreStepI; split
    · rfl
    · simp only [hnode _ he, ihf hf, iha ha]
  | lam ty b bm ihty ihb =>
    intro he
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.1
    have hb : ∀ n ∈ R.auxNames, b.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.2
    rw [restoreI_lam]; unfold restoreStepI; split
    · rfl
    · simp only [hnode _ he, ihty hty, ihb hb]
  | forallE ty b bm ihty ihb =>
    intro he
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.1
    have hb : ∀ n ∈ R.auxNames, b.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.2
    rw [restoreI_forallE]; unfold restoreStepI; split
    · rfl
    · simp only [hnode _ he, ihty hty, ihb hb]
  | letE ty v b ihty ihv ihb =>
    intro he
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.1.1
    have hv : ∀ n ∈ R.auxNames, v.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.1.2
    have hb : ∀ n ∈ R.auxNames, b.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.2
    rw [restoreI_letE]; unfold restoreStepI; split
    · rfl
    · simp only [hnode _ he, ihty hty, ihv hv, ihb hb]
  | proj s i x ihx =>
    intro he
    have hx : ∀ n ∈ R.auxNames, x.mentionsConstE n = false := fun n hn => by
      have := he n hn; simp only [Expr.mentionsConstE, Bool.or_eq_false_iff] at this; exact this.2
    rw [restoreI_proj]; unfold restoreStepI; split
    · rfl
    · simp only [hnode _ he, ihx hx]

/-! ## `instSeq` through the remaining shapes -/

theorem instSeq_lam :
    ∀ (args : List Expr) (t : Nat) (d b : Expr) (m : BinderMeta), args.length ≤ t + 1 →
      Expr.instSeq args t (.lam d b m) = .lam (Expr.instSeq args t d) (Expr.instSeq args (t + 1) b) m := by
  intro args
  induction args with
  | nil => intro t d b m _; rfl
  | cons a as ih =>
    intro t d b m hlen
    show Expr.instSeq as (t - 1) (.lam (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m) = _
    rw [ih (t - 1) (d.instantiate1 a t) (b.instantiate1 a (t + 1)) m
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) m =
      Expr.lam (Expr.instSeq as (t - 1) (d.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1))) m
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

theorem instSeq_letE :
    ∀ (args : List Expr) (t : Nat) (ty v b : Expr), args.length ≤ t + 1 →
      Expr.instSeq args t (.letE ty v b)
        = .letE (Expr.instSeq args t ty) (Expr.instSeq args t v) (Expr.instSeq args (t + 1) b) := by
  intro args
  induction args with
  | nil => intro t ty v b _; rfl
  | cons a as ih =>
    intro t ty v b hlen
    show Expr.instSeq as (t - 1)
      (.letE (ty.instantiate1 a t) (v.instantiate1 a t) (b.instantiate1 a (t + 1))) = _
    rw [ih (t - 1) (ty.instantiate1 a t) (v.instantiate1 a t) (b.instantiate1 a (t + 1))
      (by simp only [List.length_cons] at hlen; omega)]
    show Expr.letE (Expr.instSeq as (t - 1) (ty.instantiate1 a t))
        (Expr.instSeq as (t - 1) (v.instantiate1 a t))
        (Expr.instSeq as (t - 1 + 1) (b.instantiate1 a (t + 1))) =
      Expr.letE (Expr.instSeq as (t - 1) (ty.instantiate1 a t))
        (Expr.instSeq as (t - 1) (v.instantiate1 a t))
        (Expr.instSeq as (t + 1 - 1) (b.instantiate1 a (t + 1)))
    cases as with
    | nil => rfl
    | cons a2 as2 =>
      have ht : t - 1 + 1 = t + 1 - 1 := by
        simp only [List.length_cons] at hlen
        omega
      rw [ht]

theorem instSeq_proj :
    ∀ (args : List Expr) (t : Nat) (s : Name) (i : Nat) (x : Expr),
      Expr.instSeq args t (.proj s i x) = .proj s i (Expr.instSeq args t x) := by
  intro args
  induction args with
  | nil => intro t s i x; rfl
  | cons a as ih =>
    intro t s i x
    show Expr.instSeq as (t - 1) (.proj s i (x.instantiate1 a t)) = _
    rw [ih]
    rfl

/-- A term bounded by the argument count, instantiated at closed
arguments from the top index down, is closed. -/
theorem instSeq_closed :
    ∀ (args : List Expr) {e : Expr}, (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      e.looseBVarsBounded args.length = true →
      (Expr.instSeq args (args.length - 1) e).looseBVarsBounded 0 = true
  | [], e, _, he => he
  | a :: as, e, hargs, he => by
    show (Expr.instSeq as (as.length + 1 - 1 - 1) (e.instantiate1 a (as.length + 1 - 1))).looseBVarsBounded 0
      = true
    rw [Nat.add_sub_cancel]
    exact instSeq_closed as (fun b hb => hargs b (List.mem_cons_of_mem _ hb))
      (Expr.looseBVarsBounded_instantiate1_gen (hargs a (List.mem_cons_self ..)) he)

/-- **The lifted pin, instantiated at the parameters and the inner
variables, is the pin at the parameters**: the inner variables miss
it, the parameters hit its `nP` bound variables. -/
theorem instSeq_lifted_pin {ps : List Expr} (xs : List Expr) {nP d t : Nat} {pin : Expr}
    (hps : ps.length = nP) (hpsC : ∀ a ∈ ps, a.looseBVarsBounded 0 = true)
    (ht : t + 1 = nP + d) (hpin : pin.looseBVarsBounded nP = true) :
    Expr.instSeq (ps ++ xs) t (pin.liftLooseBVars d 0) = Expr.instSeq ps (nP - 1) pin := by
  rw [Expr.instSeq_append, Expr.instSeq_liftLooseBVars ps t hpsC (by omega)]
  have hcl : (Expr.instSeq ps (t - d) pin).looseBVarsBounded 0 = true := by
    have : t - d = ps.length - 1 := by omega
    rw [this]
    exact instSeq_closed ps hpsC (by rw [hps]; exact hpin)
  rw [Expr.liftLooseBVars_eq_self hcl, Expr.instSeq_eq_self _ _ hcl]
  congr 1
  omega

/-! ## The head of an instantiated term -/

/-- `getAppFn` through `instantiate1`: the head of the instantiated term
is the head of the instantiated head. -/
theorem Expr.getAppFn_instantiate1' (v : Expr) :
    ∀ (e : Expr) (d : Nat), (e.instantiate1 v d).getAppFn = (e.getAppFn.instantiate1 v d).getAppFn
  | .app f a, d => by
    show (f.instantiate1 v d).getAppFn = _
    rw [getAppFn_instantiate1' v f d]
    rfl
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ | .lam _ _ _, _
  | .forallE _ _ _, _ | .letE _ _ _, _ | .proj _ _ _, _ => rfl

/-- The head of a head is the head. -/
theorem Expr.getAppFn_getAppFn : ∀ (e : Expr), e.getAppFn.getAppFn = e.getAppFn
  | .app f a => by
    show f.getAppFn.getAppFn = f.getAppFn
    exact getAppFn_getAppFn f
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _
  | .proj _ _ _ => rfl

/-- `getAppFn` through `instSeq`: the head of the instantiated term is
the head of the instantiated head. -/
theorem getAppFn_instSeq :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      (Expr.instSeq args t e).getAppFn = (Expr.instSeq args t e.getAppFn).getAppFn
  | [], _, e => (Expr.getAppFn_getAppFn e).symm
  | a :: as, t, e => by
    show (Expr.instSeq as (t - 1) (e.instantiate1 a t)).getAppFn
      = (Expr.instSeq as (t - 1) (e.getAppFn.instantiate1 a t)).getAppFn
    rw [getAppFn_instSeq as, Expr.getAppFn_instantiate1', ← getAppFn_instSeq as]

/-- A bound variable instantiated at `fvar`s is an `fvar` or a bound
variable. -/
theorem instSeq_bvar_fvars :
    ∀ (args : List Expr), Expr.AllFvars args → ∀ (t j : Nat),
      (∃ (k : Nat) (ty : Expr), Expr.instSeq args t (.bvar j) = .fvar k ty) ∨
        ∃ j', Expr.instSeq args t (.bvar j) = .bvar j'
  | [], _, _, j => Or.inr ⟨j, rfl⟩
  | a :: as, hall, t, j => by
    obtain ⟨k, ty, rfl⟩ := hall a (List.mem_cons_self ..)
    have hrest : Expr.AllFvars as := fun b hb => hall b (List.mem_cons_of_mem _ hb)
    show (∃ k' ty', Expr.instSeq as (t - 1) ((Expr.bvar j).instantiate1 (.fvar k ty) t) = .fvar k' ty') ∨
      ∃ j', Expr.instSeq as (t - 1) ((Expr.bvar j).instantiate1 (.fvar k ty) t) = .bvar j'
    simp only [Expr.instantiate1]
    split
    · exact Or.inl ⟨k, ty, Expr.instSeq_eq_self _ _ rfl⟩
    · split
      · exact instSeq_bvar_fvars as hrest (t - 1) (j - 1)
      · exact instSeq_bvar_fvars as hrest (t - 1) j

/-- **A constant head is a constant head, on both sides of an
instantiation at `fvar`s** (an `fvar`-free term, the arguments within
the index). -/
theorem getAppFn_instSeq_const_iff {args : List Expr} (hF : Expr.AllFvars args) {t : Nat}
    (hlen : args.length ≤ t + 1) {e : Expr} {n : Name} {us : List Level} :
    (Expr.instSeq args t e).getAppFn = .const n us ↔ e.getAppFn = .const n us := by
  have hC : ∀ a ∈ args, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨k, ty, rfl⟩ := hF a ha
    rfl
  rw [getAppFn_instSeq]
  constructor
  · intro h
    cases hfn : e.getAppFn with
    | const m ms =>
      rw [hfn, Expr.instSeq_eq_self _ _ rfl] at h
      exact h
    | bvar j =>
      rw [hfn] at h
      rcases instSeq_bvar_fvars args hF t j with ⟨k, ty, hk⟩ | ⟨j', hj'⟩
      · rw [hk] at h; exact nomatch h
      · rw [hj'] at h; exact nomatch h
    | fvar k ty => rw [hfn, Expr.instSeq_eq_self _ _ rfl] at h; exact nomatch h
    | sort u => rw [hfn, Expr.instSeq_eq_self _ _ rfl] at h; exact nomatch h
    | lit l => rw [hfn, Expr.instSeq_eq_self _ _ rfl] at h; exact nomatch h
    | app f a =>
      exfalso
      have := Expr.getAppFn_not_app e
      exact this f a hfn
    | lam ty b bm => rw [hfn, instSeq_lam _ _ _ _ _ hlen] at h; exact nomatch h
    | forallE ty b bm => rw [hfn, Expr.instSeq_forallE _ _ _ _ _ hlen] at h; exact nomatch h
    | letE ty v b => rw [hfn, instSeq_letE _ _ _ _ _ hlen] at h; exact nomatch h
    | proj s i x => rw [hfn, instSeq_proj] at h; exact nomatch h
  · intro h
    rw [h, Expr.instSeq_eq_self _ _ rfl]
    rfl

/-! ## `restoreI` at a leaf, and at a firing node -/

theorem restoreI_leaf_bvar (R : RestoreTbl) (i : Nat) : restoreI R (.bvar i) = .bvar i := by
  rw [restoreI_bvar]; unfold restoreStepI; split
  · rfl
  · rw [restoreNodeI_eq_head (fun _ _ h => by simp at h), restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h)]

theorem restoreI_leaf_fvar (R : RestoreTbl) (i : Nat) (ty : Expr) :
    restoreI R (.fvar i ty) = .fvar i ty := by
  rw [restoreI_fvar]; unfold restoreStepI; split
  · rfl
  · rw [restoreNodeI_eq_head (fun _ _ h => by simp at h), restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h)]

theorem restoreI_leaf_sort (R : RestoreTbl) (u : Level) : restoreI R (.sort u) = .sort u := by
  rw [restoreI_sort]; unfold restoreStepI; split
  · rfl
  · rw [restoreNodeI_eq_head (fun _ _ h => by simp at h), restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h)]

theorem restoreI_leaf_lit (R : RestoreTbl) (l : Literal) : restoreI R (.lit l) = .lit l := by
  rw [restoreI_lit]; unfold restoreStepI; split
  · rfl
  · rw [restoreNodeI_eq_head (fun _ _ h => by simp at h), restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h)]

/-- **A firing node's answer is the fire's**, whatever the term's
shape. -/
theorem restoreI_of_node {R : RestoreTbl} {e e₁ : Expr} {n : Name} (hn : n ∈ R.auxNames)
    (hm : e.mentionsConst n = true) (h : restoreNodeI R e = some e₁) : restoreI R e = e₁ := by
  have hany : R.auxNames.any (fun n => e.mentionsConst n) = true := List.any_eq_true.mpr ⟨n, hn, hm⟩
  cases e <;> simp only [restoreI, restoreStepI, hany, Bool.not_true, Bool.false_eq_true, ite_false, h]

/-- **A declining node's answer is its children's**, per shape. -/
theorem restoreI_of_decline_app {R : RestoreTbl} {f a : Expr} {n : Name} (hn : n ∈ R.auxNames)
    (hm : (Expr.app f a).mentionsConst n = true) (h : restoreNodeI R (.app f a) = none) :
    restoreI R (.app f a) = .app (restoreI R f) (restoreI R a) := by
  have hany : R.auxNames.any (fun n => (Expr.app f a).mentionsConst n) = true :=
    List.any_eq_true.mpr ⟨n, hn, hm⟩
  simp only [restoreI, restoreStepI, hany, Bool.not_true, Bool.false_eq_true, ite_false, h]

theorem restoreI_of_decline_lam {R : RestoreTbl} {ty b : Expr} {bm : BinderMeta} {n : Name}
    (hn : n ∈ R.auxNames) (hm : (Expr.lam ty b bm).mentionsConst n = true)
    (h : restoreNodeI R (.lam ty b bm) = none) :
    restoreI R (.lam ty b bm) = .lam (restoreI R ty) (restoreI R b) bm := by
  have hany : R.auxNames.any (fun n => (Expr.lam ty b bm).mentionsConst n) = true :=
    List.any_eq_true.mpr ⟨n, hn, hm⟩
  simp only [restoreI, restoreStepI, hany, Bool.not_true, Bool.false_eq_true, ite_false, h]

theorem restoreI_of_decline_forallE {R : RestoreTbl} {ty b : Expr} {bm : BinderMeta} {n : Name}
    (hn : n ∈ R.auxNames) (hm : (Expr.forallE ty b bm).mentionsConst n = true)
    (h : restoreNodeI R (.forallE ty b bm) = none) :
    restoreI R (.forallE ty b bm) = .forallE (restoreI R ty) (restoreI R b) bm := by
  have hany : R.auxNames.any (fun n => (Expr.forallE ty b bm).mentionsConst n) = true :=
    List.any_eq_true.mpr ⟨n, hn, hm⟩
  simp only [restoreI, restoreStepI, hany, Bool.not_true, Bool.false_eq_true, ite_false, h]

theorem restoreI_of_decline_letE {R : RestoreTbl} {ty v b : Expr} {n : Name}
    (hn : n ∈ R.auxNames) (hm : (Expr.letE ty v b).mentionsConst n = true)
    (h : restoreNodeI R (.letE ty v b) = none) :
    restoreI R (.letE ty v b) = .letE (restoreI R ty) (restoreI R v) (restoreI R b) := by
  have hany : R.auxNames.any (fun n => (Expr.letE ty v b).mentionsConst n) = true :=
    List.any_eq_true.mpr ⟨n, hn, hm⟩
  simp only [restoreI, restoreStepI, hany, Bool.not_true, Bool.false_eq_true, ite_false, h]

theorem restoreI_of_decline_proj {R : RestoreTbl} {s : Name} {i : Nat} {x : Expr} {n : Name}
    (hn : n ∈ R.auxNames) (hm : (Expr.proj s i x).mentionsConst n = true)
    (h : restoreNodeI R (.proj s i x) = none) :
    restoreI R (.proj s i x) = .proj s i (restoreI R x) := by
  have hany : R.auxNames.any (fun n => (Expr.proj s i x).mentionsConst n) = true :=
    List.any_eq_true.mpr ⟨n, hn, hm⟩
  simp only [restoreI, restoreStepI, hany, Bool.not_true, Bool.false_eq_true, ite_false, h]

/-- A declining constant is its own restoration. -/
theorem restoreI_of_decline_const {R : RestoreTbl} {n : Name} {us : List Level}
    (h : restoreNodeI R (.const n us) = none) : restoreI R (.const n us) = .const n us := by
  rw [restoreI_const]; unfold restoreStepI; split
  · rfl
  · rw [h]

/-- The lift is structural on a spine. -/
theorem Expr.liftLooseBVars_mkAppN (k c : Nat) :
    ∀ (args : List Expr) (f : Expr),
      (Expr.mkAppN f args).liftLooseBVars k c
        = Expr.mkAppN (f.liftLooseBVars k c) (args.map (·.liftLooseBVars k c))
  | [], _ => rfl
  | a :: args, f => by
    show (Expr.mkAppN (.app f a) args).liftLooseBVars k c = _
    rw [liftLooseBVars_mkAppN k c args]
    rfl

/-- The head step of the instantiated table at a constant-headed
spine, in terms of the raw table's lookups. -/
theorem restoreHeadI_instAt_spine (R : RestoreTbl) (ps : List Expr) (n : Name) (us : List Level)
    (args : List Expr) :
    restoreHeadI (R.instAt ps) (Expr.mkAppN (.const n us) args) =
      match R.pins.lookup n with
      | some pin =>
        if args.length < R.nP then none
        else some (Expr.mkAppN (Expr.instSeq ps (ps.length - 1) pin) (args.drop R.nP))
      | none =>
        match R.ctorPins.find? (fun q => q.1 == n) with
        | some (_, pin, newName) =>
          if args.length < R.nP then none else
            match (Expr.instSeq ps (ps.length - 1) pin).getAppFn with
            | .const _ ilvls =>
              some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls)
                (Expr.instSeq ps (ps.length - 1) pin).getAppArgs) (args.drop R.nP))
            | _ => none
        | none => none := by
  rw [restoreHeadI_spine]
  show (match (R.pins.map fun q => (q.1, Expr.instSeq ps (ps.length - 1) q.2)).lookup n with
    | some pin => if args.length < R.nP then none else some (Expr.mkAppN pin (args.drop R.nP))
    | none =>
      match (R.ctorPins.map fun q : Name × Expr × Name =>
          (q.1, Expr.instSeq ps (ps.length - 1) q.2.1, q.2.2)).find?
          (fun q : Name × Expr × Name => q.1 == n) with
      | some (_, pin, newName) =>
        if args.length < R.nP then none else
          match pin.getAppFn with
          | .const _ ilvls =>
            some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (args.drop R.nP))
          | _ => none
      | none => none) = _
  rw [List.lookup_map_snd, List.find?_map]
  cases R.pins.lookup n with
  | some pin => rfl
  | none =>
    simp only [Option.map_none]
    have hcomp : ((fun q : Name × Expr × Name => q.1 == n) ∘
        (fun q : Name × Expr × Name => (q.1, Expr.instSeq ps (ps.length - 1) q.2.1, q.2.2)))
        = fun q => q.1 == n := rfl
    rw [hcomp]
    cases R.ctorPins.find? (fun q => q.1 == n) with
    | some q => rfl
    | none => rfl

/-! ## The commutation: the raw walk, instantiated, is the instantiated walk -/

/-- The lifted pin at the whole context, both when the context is
empty (no parameters, depth `0`) and otherwise. -/
theorem instSeq_lifted_pin' {R : RestoreTbl} {ps xs : List Expr} (hps : ps.length = R.nP)
    (hpsF : Expr.AllFvars ps) (hxs : xs.length ≤ R.nP + xs.length) {d t : Nat}
    (ht : ps ++ xs ≠ [] → t + 1 = R.nP + d) (hxsd : xs.length ≤ d) {pin : Expr}
    (hpin : pin.looseBVarsBounded R.nP = true) :
    Expr.instSeq (ps ++ xs) t (pin.liftLooseBVars d 0) = Expr.instSeq ps (ps.length - 1) pin := by
  have hpsC : ∀ a ∈ ps, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨k, ty, rfl⟩ := hpsF a ha
    rfl
  by_cases hL : ps ++ xs = []
  · have hps0 : ps = [] := by
      cases ps with
      | nil => rfl
      | cons a as => simp at hL
    subst hps0
    have hxs0 : xs = [] := by simpa using hL
    subst hxs0
    have hnP : R.nP = 0 := hps.symm
    rw [hnP] at hpin
    simp only [List.append_nil, Expr.instSeq, Expr.liftLooseBVars_eq_self hpin]
  · rw [instSeq_lifted_pin xs hps hpsC (ht hL) hpin, hps]

/-- **The node step at a fire, instantiated**: the instantiated table's
node step on the instantiated term answers the instantiated fire. -/
theorem restoreNodeI_instAt_of_fire {R : RestoreTbl} (hR : R.WF) {ps : List Expr}
    (hps : ps.length = R.nP) (hpsF : Expr.AllFvars ps) {e e₁ : Expr} {d t : Nat} {xs : List Expr}
    (hnode : restoreNode R d e = .ok (some e₁)) (hfv : e.hasFvar = false)
    (hxs : xs.length ≤ d) (hxsF : Expr.AllFvars xs) (ht : ps ++ xs ≠ [] → t + 1 = R.nP + d) :
    restoreNodeI (R.instAt ps) (Expr.instSeq (ps ++ xs) t e)
      = some (Expr.instSeq (ps ++ xs) t e₁) := by
  have hLF : Expr.AllFvars (ps ++ xs) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpsF a ha
    · exact hxsF a ha
  have hlen : (ps ++ xs).length ≤ t + 1 := by
    by_cases hL : ps ++ xs = []
    · rw [hL]; simp
    · have := ht hL; rw [List.length_append]; omega
  rcases restoreNode_ok_inv hnode with ⟨m, ms, m', rfl, hrec, hr⟩ | ⟨hrecNone, hhead⟩
  · obtain rfl := Option.some.inj hr
    rw [Expr.instSeq_eq_self _ _ rfl, Expr.instSeq_eq_self _ _ rfl]
    exact restoreNodeI_rec hrec
  rcases restoreHead_ok_inv hhead with ⟨-, hr⟩ | ⟨m, ms, hfn, hcases⟩
  · exact nomatch hr
  -- the spine
  have he : e = Expr.mkAppN (.const m ms) e.getAppArgs := by
    rw [← hfn]
    exact (Expr.mkAppN_getApp e).symm
  have hI : Expr.instSeq (ps ++ xs) t e
      = Expr.mkAppN (.const m ms) (e.getAppArgs.map (Expr.instSeq (ps ++ xs) t)) := by
    have h0 : Expr.instSeq (ps ++ xs) t (Expr.mkAppN (.const m ms) e.getAppArgs)
        = Expr.mkAppN (.const m ms) (e.getAppArgs.map (Expr.instSeq (ps ++ xs) t)) := by
      rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl]
    rw [← he] at h0
    exact h0
  have hrecI : ∀ (m'' : Name) (ms'' : List Level),
      Expr.instSeq (ps ++ xs) t e = .const m'' ms'' → (R.instAt ps).recMap.lookup m'' = none := by
    intro m'' ms'' hc
    rw [hI] at hc
    have hnil : e.getAppArgs.map (Expr.instSeq (ps ++ xs) t) = [] := by
      cases hargs : e.getAppArgs.map (Expr.instSeq (ps ++ xs) t) with
      | nil => rfl
      | cons a as =>
        exfalso
        rw [hargs] at hc
        rcases Expr.mkAppN_const_shape (n := m) (ls := ms) (a :: as) with h1 | ⟨f, b, h1⟩
        · have := congrArg Expr.getAppArgs h1
          rw [Expr.getAppArgs_mkAppN] at this
          exact nomatch this
        · rw [h1] at hc; exact nomatch hc
    rw [hnil] at hc
    simp only [Expr.mkAppN, Expr.const.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hargs0 : e.getAppArgs = [] := List.map_eq_nil_iff.mp hnil
    rw [hargs0] at he
    exact hrecNone m ms he
  rw [restoreNodeI_eq_head hrecI, hI, restoreHeadI_instAt_spine]
  have hlenArgs : (e.getAppArgs.map (Expr.instSeq (ps ++ xs) t)).length = e.getAppArgs.length :=
    List.length_map ..
  rcases hcases with ⟨pin, hpin, hle, hr⟩ | ⟨hpinNone, q, hq, hle, J, ilvls, hJ, hr⟩ | ⟨-, -, hr⟩
  · obtain rfl := Option.some.inj hr
    rw [hpin]
    simp only [hlenArgs, show ¬ e.getAppArgs.length < R.nP by omega, ite_false, Option.some.injEq]
    rw [Expr.instSeq_mkAppN, List.map_drop,
      instSeq_lifted_pin' hps hpsF (Nat.le_add_left _ _) ht hxs
        (hR.pinsBounded (m, pin) (List.mem_of_lookup_some hpin))]
  · obtain rfl := Option.some.inj hr
    obtain ⟨J', lvls, Ds, hqpin⟩ := hR.ctorPinsHead q (List.mem_of_find?_eq_some hq)
    obtain ⟨qn, qpin, qnew⟩ := q
    simp only at hqpin hJ ⊢
    subst hqpin
    rw [hpinNone, hq]
    simp only [hlenArgs, show ¬ e.getAppArgs.length < R.nP by omega, ite_false]
    -- the lifted pin's head and arguments
    rw [Expr.liftLooseBVars_mkAppN, Expr.getAppFn_mkAppN] at hJ
    simp only [Expr.liftLooseBVars, Expr.getAppFn, Expr.const.injEq] at hJ
    obtain ⟨rfl, rfl⟩ := hJ
    have hpinI := instSeq_lifted_pin' hps hpsF (Nat.le_add_left _ _) ht hxs
      (hR.ctorPinsBounded (qn, Expr.mkAppN (.const _ _) Ds, qnew) (List.mem_of_find?_eq_some hq))
    simp only at hpinI
    rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl, Expr.getAppFn_mkAppN]
    simp only [Expr.getAppFn, Option.some.injEq]
    rw [Expr.instSeq_mkAppN, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl, List.map_drop,
      Expr.liftLooseBVars_mkAppN, Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN]
    simp only [Expr.liftLooseBVars, Expr.getAppArgs, List.nil_append]
    congr 2
    symm
    have h1 := congrArg Expr.getAppArgs hpinI
    rw [Expr.liftLooseBVars_mkAppN, Expr.instSeq_mkAppN, Expr.instSeq_mkAppN,
      Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN, Expr.instSeq_eq_self _ _ rfl,
      Expr.instSeq_eq_self _ _ rfl] at h1
    simpa [Expr.liftLooseBVars, Expr.getAppArgs] using h1
  · exact nomatch hr

/-- **The node step at a decline, instantiated**: the instantiated
table's node step on the instantiated term declines too. -/
theorem restoreNodeI_instAt_of_decline {R : RestoreTbl} {ps : List Expr}
    (hps : ps.length = R.nP) (hpsF : Expr.AllFvars ps) {e : Expr} {d t : Nat} {xs : List Expr}
    (hnode : restoreNode R d e = .ok none) (_hfv : e.hasFvar = false)
    (hxs : xs.length ≤ d) (hxsF : Expr.AllFvars xs) (ht : ps ++ xs ≠ [] → t + 1 = R.nP + d) :
    restoreNodeI (R.instAt ps) (Expr.instSeq (ps ++ xs) t e) = none := by
  have hLF : Expr.AllFvars (ps ++ xs) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpsF a ha
    · exact hxsF a ha
  have hlen : (ps ++ xs).length ≤ t + 1 := by
    by_cases hL : ps ++ xs = []
    · rw [hL]; simp
    · have := ht hL; rw [List.length_append]; omega
  rcases restoreNode_ok_inv hnode with ⟨_, _, _, _, _, hr⟩ | ⟨hrecNone, hhead⟩
  · exact nomatch hr
  rcases restoreHead_ok_inv hhead with ⟨hfnNot, -⟩ | ⟨m, ms, hfn, hcases⟩
  · have hfnI : ∀ (n : Name) (us : List Level), (Expr.instSeq (ps ++ xs) t e).getAppFn ≠ .const n us :=
      fun n us h => hfnNot n us ((getAppFn_instSeq_const_iff hLF hlen).mp h)
    rw [restoreNodeI_eq_head (fun n us hc => absurd (by rw [hc]; rfl) (hfnI n us))]
    exact restoreHeadI_nonconst hfnI
  have he : e = Expr.mkAppN (.const m ms) e.getAppArgs := by
    rw [← hfn]
    exact (Expr.mkAppN_getApp e).symm
  have hI : Expr.instSeq (ps ++ xs) t e
      = Expr.mkAppN (.const m ms) (e.getAppArgs.map (Expr.instSeq (ps ++ xs) t)) := by
    have h0 : Expr.instSeq (ps ++ xs) t (Expr.mkAppN (.const m ms) e.getAppArgs)
        = Expr.mkAppN (.const m ms) (e.getAppArgs.map (Expr.instSeq (ps ++ xs) t)) := by
      rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl]
    rw [← he] at h0
    exact h0
  have hrecI : ∀ (m'' : Name) (ms'' : List Level),
      Expr.instSeq (ps ++ xs) t e = .const m'' ms'' → (R.instAt ps).recMap.lookup m'' = none := by
    intro m'' ms'' hc
    rw [hI] at hc
    have hnil : e.getAppArgs.map (Expr.instSeq (ps ++ xs) t) = [] := by
      cases hargs : e.getAppArgs.map (Expr.instSeq (ps ++ xs) t) with
      | nil => rfl
      | cons a as =>
        exfalso
        rw [hargs] at hc
        rcases Expr.mkAppN_const_shape (n := m) (ls := ms) (a :: as) with h1 | ⟨f, b, h1⟩
        · have := congrArg Expr.getAppArgs h1
          rw [Expr.getAppArgs_mkAppN] at this
          exact nomatch this
        · rw [h1] at hc; exact nomatch hc
    rw [hnil] at hc
    simp only [Expr.mkAppN, Expr.const.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hargs0 : e.getAppArgs = [] := List.map_eq_nil_iff.mp hnil
    rw [hargs0] at he
    exact hrecNone m ms he
  rw [restoreNodeI_eq_head hrecI, hI, restoreHeadI_instAt_spine]
  rcases hcases with ⟨_, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, hr⟩ | ⟨hpinNone, hctorNone, -⟩
  · exact nomatch hr
  · exact nomatch hr
  · rw [hpinNone, hctorNone]

-- The common prelude of every case of `restoreWalk_instSeq`: the prune
-- and the fire are closed, the decline is left with the node facts in
-- context.
set_option hygiene false in
local macro "restore_prelude" : tactic =>
  `(tactic| (
    intro d t e' hw hfv xs hxs hxsF ht
    have hLF : Expr.AllFvars (ps ++ xs) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hpsF a ha
      · exact hxsF a ha
    have hlen : (ps ++ xs).length ≤ t + 1 := by
      by_cases hL : ps ++ xs = []
      · rw [hL]; simp
      · have := ht hL; rw [List.length_append]; omega
    unfold restoreWalk at hw
    split at hw
    · next hprune =>
      simp only [Except.ok.injEq] at hw
      subst hw
      symm
      apply restoreI_eq_self (hR.toNamed.instAt ps)
      intro n hn
      have hn' : n ∈ R.auxNames := hn
      rw [Expr.mentionsConstE_instSeq_fvars _ hLF, Expr.mentionsConstE_eq_of_not_hasFvar _ hfv]
      have := (List.any_eq_false.mp (by simpa using hprune)) n hn'
      simpa using this
    rename_i hnp
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hnp
    obtain ⟨n, hn, hm⟩ := List.any_eq_true.mp hnp
    have hmI := Expr.mentionsConst_instSeq_fvars_of (ps ++ xs) hLF t _ hm
    split at hw
    · exact nomatch hw
    · next e₁ hnode =>
      simp only [Except.ok.injEq] at hw
      subst hw
      exact (restoreI_of_node (R := R.instAt ps) hn hmI
        (restoreNodeI_instAt_of_fire hR hps hpsF hnode hfv hxs hxsF ht)).symm
    rename_i hnode
    have hnodeI := restoreNodeI_instAt_of_decline hps hpsF hnode hfv hxs hxsF ht))

set_option maxHeartbeats 1600000 in
/-- **THE COMMUTATION** (task #279 M-D′ D1, the syntactic half): the
raw walk at depth `d`, instantiated at the parameter variables `ps`
and at most `d` inner variables `xs` (the outermost first, from index
`t`), is the instantiated walk on the instantiated input — on the
nose.  The only content is at a fire, where the lifted pin lands on
the parameters (`instSeq_lifted_pin`); everywhere else the two walks
prune, decline and descend alike (`mentionsConstE`: the prune of the
opened term may fire later, never with a different answer). -/
theorem restoreWalk_instSeq {R : RestoreTbl} (hR : R.WF) {ps : List Expr} (hps : ps.length = R.nP)
    (hpsF : Expr.AllFvars ps) :
    ∀ (e : Expr) (d t : Nat) {e' : Expr}, restoreWalk R d e = .ok e' → e.hasFvar = false →
      ∀ (xs : List Expr), xs.length ≤ d → Expr.AllFvars xs → (ps ++ xs ≠ [] → t + 1 = R.nP + d) →
        Expr.instSeq (ps ++ xs) t e' = restoreI (R.instAt ps) (Expr.instSeq (ps ++ xs) t e) := by
  intro e
  induction e with
  | app f a ihf iha =>
    restore_prelude
    simp only at hw
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    split at hw
    · exact nomatch hw
    · next f' hf =>
      split at hw
      · exact nomatch hw
      · next a' ha =>
        simp only [Except.ok.injEq] at hw
        subst hw
        rw [Expr.instSeq_app] at hmI hnodeI
        rw [Expr.instSeq_app, Expr.instSeq_app, restoreI_of_decline_app (R := R.instAt ps) hn hmI hnodeI,
          ihf d t hf hfv.1 xs hxs hxsF ht, iha d t ha hfv.2 xs hxs hxsF ht]
  | lam ty b bm ihty ihb =>
    restore_prelude
    simp only at hw
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    split at hw
    · exact nomatch hw
    · next ty' hty =>
      split at hw
      · exact nomatch hw
      · next b' hb =>
        simp only [Except.ok.injEq] at hw
        subst hw
        rw [instSeq_lam _ _ _ _ _ hlen] at hmI hnodeI
        rw [instSeq_lam _ _ _ _ _ hlen, instSeq_lam _ _ _ _ _ hlen,
          restoreI_of_decline_lam (R := R.instAt ps) hn hmI hnodeI, ihty d t hty hfv.1 xs hxs hxsF ht,
          ihb (d + 1) (t + 1) hb hfv.2 xs (by omega) hxsF (fun hne => by have := ht hne; omega)]
  | forallE ty b bm ihty ihb =>
    restore_prelude
    simp only at hw
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    split at hw
    · exact nomatch hw
    · next ty' hty =>
      split at hw
      · exact nomatch hw
      · next b' hb =>
        simp only [Except.ok.injEq] at hw
        subst hw
        rw [Expr.instSeq_forallE _ _ _ _ _ hlen] at hmI hnodeI
        rw [Expr.instSeq_forallE _ _ _ _ _ hlen, Expr.instSeq_forallE _ _ _ _ _ hlen,
          restoreI_of_decline_forallE (R := R.instAt ps) hn hmI hnodeI, ihty d t hty hfv.1 xs hxs hxsF ht,
          ihb (d + 1) (t + 1) hb hfv.2 xs (by omega) hxsF (fun hne => by have := ht hne; omega)]
  | letE ty v b ihty ihv ihb =>
    restore_prelude
    simp only at hw
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    split at hw
    · exact nomatch hw
    · next ty' hty =>
      split at hw
      · exact nomatch hw
      · next v' hv =>
        split at hw
        · exact nomatch hw
        · next b' hb =>
          simp only [Except.ok.injEq] at hw
          subst hw
          rw [instSeq_letE _ _ _ _ _ hlen] at hmI hnodeI
          rw [instSeq_letE _ _ _ _ _ hlen, instSeq_letE _ _ _ _ _ hlen,
            restoreI_of_decline_letE (R := R.instAt ps) hn hmI hnodeI, ihty d t hty hfv.1.1 xs hxs hxsF ht,
            ihv d t hv hfv.1.2 xs hxs hxsF ht,
            ihb (d + 1) (t + 1) hb hfv.2 xs (by omega) hxsF (fun hne => by have := ht hne; omega)]
  | proj s i x ihx =>
    restore_prelude
    simp only at hw
    simp only [Expr.hasFvar] at hfv
    split at hw
    · exact nomatch hw
    · next x' hx =>
      simp only [Except.ok.injEq] at hw
      subst hw
      rw [instSeq_proj] at hmI hnodeI
      rw [instSeq_proj, instSeq_proj, restoreI_of_decline_proj (R := R.instAt ps) hn hmI hnodeI,
        ihx d t hx hfv xs hxs hxsF ht]
  | bvar i =>
    restore_prelude
    simp only at hw
    simp only [Except.ok.injEq] at hw
    subst hw
    rcases instSeq_bvar_fvars (ps ++ xs) hLF t i with ⟨k, ty, hk⟩ | ⟨j', hj'⟩
    · rw [hk, restoreI_leaf_fvar]
    · rw [hj', restoreI_leaf_bvar]
  | fvar i ty _ =>
    intro d t e' _ hfv
    exact nomatch hfv
  | sort u =>
    restore_prelude
    simp only at hw
    simp only [Except.ok.injEq] at hw
    subst hw
    rw [Expr.instSeq_eq_self _ _ rfl, restoreI_leaf_sort]
  | const m ms =>
    restore_prelude
    simp only at hw
    simp only [Except.ok.injEq] at hw
    subst hw
    rw [Expr.instSeq_eq_self _ _ rfl] at hnodeI
    rw [Expr.instSeq_eq_self _ _ rfl, restoreI_of_decline_const hnodeI]
  | lit l =>
    restore_prelude
    simp only at hw
    simp only [Except.ok.injEq] at hw
    subst hw
    rw [Expr.instSeq_eq_self _ _ rfl, restoreI_leaf_lit]

/-! ## `restoreI` is blind to `fvar` annotations -/

/-- Erasure through a spine: the heads and the arguments, pointwise. -/
theorem Expr.ErasedEq.getApp :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
      Expr.ErasedEq e₁.getAppFn e₂.getAppFn ∧ e₁.getAppArgs.length = e₂.getAppArgs.length ∧
      ∀ (k : Nat) (a₁ a₂ : Expr), e₁.getAppArgs[k]? = some a₁ → e₂.getAppArgs[k]? = some a₂ →
        Expr.ErasedEq a₁ a₂
  | .app f a, .app g b, h => by
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨hfn, hlen, hargs⟩ := getApp h₁
    refine ⟨hfn, by simp [Expr.getAppArgs, hlen], fun k a₁ a₂ ha₁ ha₂ => ?_⟩
    simp only [Expr.getAppArgs] at ha₁ ha₂
    by_cases hk : k < f.getAppArgs.length
    · rw [List.getElem?_append_left hk] at ha₁
      rw [List.getElem?_append_left (by rw [← hlen]; exact hk)] at ha₂
      exact hargs k a₁ a₂ ha₁ ha₂
    · rw [List.getElem?_append_right (by omega)] at ha₁
      rw [List.getElem?_append_right (by omega)] at ha₂
      rw [← hlen] at ha₂
      cases hk' : k - f.getAppArgs.length with
      | zero =>
        rw [hk'] at ha₁ ha₂
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha₁ ha₂
        subst ha₁ ha₂
        exact h₂
      | succ j => rw [hk'] at ha₁; simp at ha₁
  | .bvar _, .bvar _, h | .fvar _ _, .fvar _ _, h | .sort _, .sort _, h | .const _ _, .const _ _, h
  | .lit _, .lit _, h | .lam _ _ _, .lam _ _ _, h | .forallE _ _ _, .forallE _ _ _, h
  | .letE _ _ _, .letE _ _ _, h | .proj _ _ _, .proj _ _ _, h =>
    ⟨h, Eq.refl _, fun _ _ _ h₁ _ => by simp [Expr.getAppArgs] at h₁⟩

/-- Erasure of a constant is the constant. -/
theorem Expr.ErasedEq.const_left {n : Name} {us : List Level} :
    ∀ {e : Expr}, Expr.ErasedEq (.const n us) e → e = .const n us
  | .const _ _, h => by obtain ⟨rfl, rfl⟩ := h; rfl

theorem Expr.ErasedEq.const_right {n : Name} {us : List Level} :
    ∀ {e : Expr}, Expr.ErasedEq e (.const n us) → e = .const n us
  | .const _ _, h => by obtain ⟨rfl, rfl⟩ := h; rfl

/-- Erasure is structural on spines. -/
theorem Expr.ErasedEq.mkAppN :
    ∀ (as₁ as₂ : List Expr) {f₁ f₂ : Expr}, Expr.ErasedEq f₁ f₂ → as₁.length = as₂.length →
      (∀ (k : Nat) (a₁ a₂ : Expr), as₁[k]? = some a₁ → as₂[k]? = some a₂ → Expr.ErasedEq a₁ a₂) →
      Expr.ErasedEq (Expr.mkAppN f₁ as₁) (Expr.mkAppN f₂ as₂)
  | [], [], f₁, f₂, hf, _, _ => hf
  | a :: as₁, b :: as₂, f₁, f₂, hf, hlen, hall =>
    mkAppN as₁ as₂ (f₁ := .app f₁ a) (f₂ := .app f₂ b) ⟨hf, hall 0 a b (Eq.refl _) (Eq.refl _)⟩
      (by simpa using hlen)
      (fun k a₁ a₂ h₁ h₂ => hall (k + 1) a₁ a₂ (by simpa using h₁) (by simpa using h₂))

/-- `mentionsConst` is monotone in the blind mention, so an unpruned
node with an erasure-equal partner stays unpruned on both sides only
through the blind mention; the node step itself is blind. -/
theorem restoreNodeI_erasedEq {R : RestoreTbl} {e₁ e₂ : Expr} (h : Expr.ErasedEq e₁ e₂) :
      (restoreNodeI R e₁ = none ↔ restoreNodeI R e₂ = none) ∧
      ∀ (r₁ r₂ : Expr), restoreNodeI R e₁ = some r₁ → restoreNodeI R e₂ = some r₂ →
        Expr.ErasedEq r₁ r₂ := by
  obtain ⟨hfn, hlen, hargs⟩ := h.getApp
  -- the recursor map: a bare constant on one side is the same constant on the other
  have hconst : ∀ (n : Name) (us : List Level), e₁ = .const n us ↔ e₂ = .const n us := by
    intro n us
    constructor
    · intro h1; subst h1; exact h.const_left
    · intro h2; subst h2; exact h.const_right
  by_cases hc : ∃ (n : Name) (us : List Level), e₁.getAppFn = .const n us
  · obtain ⟨n, us, hfn₁⟩ := hc
    have hfn₂ : e₂.getAppFn = .const n us := by
      rw [hfn₁] at hfn
      exact hfn.const_left
    have he₁ : e₁ = Expr.mkAppN (.const n us) e₁.getAppArgs := by
      rw [← hfn₁]; exact (Expr.mkAppN_getApp e₁).symm
    have he₂ : e₂ = Expr.mkAppN (.const n us) e₂.getAppArgs := by
      rw [← hfn₂]; exact (Expr.mkAppN_getApp e₂).symm
    by_cases hrec : ∃ n', R.recMap.lookup n = some n'
    · obtain ⟨n', hn'⟩ := hrec
      by_cases hnil : e₁.getAppArgs = []
      · have hnil₂ : e₂.getAppArgs = [] := by
          rw [← List.length_eq_zero_iff, ← hlen, List.length_eq_zero_iff]; exact hnil
        rw [hnil] at he₁; rw [hnil₂] at he₂
        simp only [Expr.mkAppN] at he₁ he₂
        subst he₁ he₂
        rw [restoreNodeI_rec hn']
        exact ⟨Iff.rfl, fun r₁ r₂ h₁ h₂ => by
          obtain rfl := Option.some.inj h₁; obtain rfl := Option.some.inj h₂; exact Expr.ErasedEq.rfl _⟩
      · have hnil₂ : e₂.getAppArgs ≠ [] := by
          intro h2; apply hnil
          rw [← List.length_eq_zero_iff, hlen, List.length_eq_zero_iff]; exact h2
        have hr₁ : ∀ (m : Name) (ms : List Level), e₁ = .const m ms → R.recMap.lookup m = none := by
          intro m ms hm; exfalso; apply hnil
          rw [hm]; rfl
        have hr₂ : ∀ (m : Name) (ms : List Level), e₂ = .const m ms → R.recMap.lookup m = none := by
          intro m ms hm; exfalso; apply hnil₂
          rw [hm]; rfl
        rw [restoreNodeI_eq_head hr₁, restoreNodeI_eq_head hr₂, he₁, he₂, restoreHeadI_spine,
          restoreHeadI_spine, hlen]
        exact restoreHeadI_spine_erasedEq hlen hargs
    · have hrecNone : R.recMap.lookup n = none := by
        cases hl : R.recMap.lookup n with
        | none => rfl
        | some n' => exact absurd ⟨n', hl⟩ hrec
      have hr₁ : ∀ (m : Name) (ms : List Level), e₁ = .const m ms → R.recMap.lookup m = none := by
        intro m ms hm
        rw [hm] at hfn₁
        simp only [Expr.getAppFn, Expr.const.injEq] at hfn₁
        rw [hfn₁.1]; exact hrecNone
      have hr₂ : ∀ (m : Name) (ms : List Level), e₂ = .const m ms → R.recMap.lookup m = none := by
        intro m ms hm
        rw [hm] at hfn₂
        simp only [Expr.getAppFn, Expr.const.injEq] at hfn₂
        rw [hfn₂.1]; exact hrecNone
      rw [restoreNodeI_eq_head hr₁, restoreNodeI_eq_head hr₂, he₁, he₂, restoreHeadI_spine,
        restoreHeadI_spine, hlen]
      exact restoreHeadI_spine_erasedEq hlen hargs
  · have hc₁ : ∀ (n : Name) (us : List Level), e₁.getAppFn ≠ .const n us :=
      fun n us h' => hc ⟨n, us, h'⟩
    have hc₂ : ∀ (n : Name) (us : List Level), e₂.getAppFn ≠ .const n us := by
      intro n us h'
      rw [h'] at hfn
      exact hc₁ n us hfn.const_right
    rw [restoreNodeI_eq_head (fun n us h' => absurd (by rw [h']; rfl) (hc₁ n us)),
      restoreNodeI_eq_head (fun n us h' => absurd (by rw [h']; rfl) (hc₂ n us)),
      restoreHeadI_nonconst hc₁, restoreHeadI_nonconst hc₂]
    exact ⟨Iff.rfl, fun _ _ h₁ _ => nomatch h₁⟩
where
  /-- the spine's answer, blind to the arguments' annotations -/
  restoreHeadI_spine_erasedEq {n : Name} {as₁ as₂ : List Expr}
      (hlen : as₁.length = as₂.length)
      (hargs : ∀ (k : Nat) (a₁ a₂ : Expr), as₁[k]? = some a₁ → as₂[k]? = some a₂ →
        Expr.ErasedEq a₁ a₂) :
      ((match R.pins.lookup n with
        | some pin => if as₂.length < R.nP then none else some (Expr.mkAppN pin (as₁.drop R.nP))
        | none =>
          match R.ctorPins.find? (fun q => q.1 == n) with
          | some (_, pin, newName) =>
            if as₂.length < R.nP then none else
              match pin.getAppFn with
              | .const _ ilvls =>
                some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (as₁.drop R.nP))
              | _ => none
          | none => none) = none ↔
        (match R.pins.lookup n with
        | some pin => if as₂.length < R.nP then none else some (Expr.mkAppN pin (as₂.drop R.nP))
        | none =>
          match R.ctorPins.find? (fun q => q.1 == n) with
          | some (_, pin, newName) =>
            if as₂.length < R.nP then none else
              match pin.getAppFn with
              | .const _ ilvls =>
                some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (as₂.drop R.nP))
              | _ => none
          | none => none) = none) ∧
      ∀ (r₁ r₂ : Expr),
        (match R.pins.lookup n with
        | some pin => if as₂.length < R.nP then none else some (Expr.mkAppN pin (as₁.drop R.nP))
        | none =>
          match R.ctorPins.find? (fun q => q.1 == n) with
          | some (_, pin, newName) =>
            if as₂.length < R.nP then none else
              match pin.getAppFn with
              | .const _ ilvls =>
                some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (as₁.drop R.nP))
              | _ => none
          | none => none) = some r₁ →
        (match R.pins.lookup n with
        | some pin => if as₂.length < R.nP then none else some (Expr.mkAppN pin (as₂.drop R.nP))
        | none =>
          match R.ctorPins.find? (fun q => q.1 == n) with
          | some (_, pin, newName) =>
            if as₂.length < R.nP then none else
              match pin.getAppFn with
              | .const _ ilvls =>
                some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) pin.getAppArgs) (as₂.drop R.nP))
              | _ => none
          | none => none) = some r₂ →
        Expr.ErasedEq r₁ r₂ := by
    have hdrop : Expr.ErasedEq (Expr.mkAppN (.bvar 0) (as₁.drop R.nP)) (Expr.mkAppN (.bvar 0) (as₂.drop R.nP)) :=
      Expr.ErasedEq.mkAppN _ _ rfl (by simp [hlen]) (fun k a₁ a₂ h₁ h₂ => by
        rw [List.getElem?_drop] at h₁ h₂
        exact hargs _ a₁ a₂ h₁ h₂)
    have hdropE : ∀ (f : Expr), Expr.ErasedEq (Expr.mkAppN f (as₁.drop R.nP)) (Expr.mkAppN f (as₂.drop R.nP)) :=
      fun f => Expr.ErasedEq.mkAppN _ _ (Expr.ErasedEq.rfl f) (by simp [hlen]) (fun k a₁ a₂ h₁ h₂ => by
        rw [List.getElem?_drop] at h₁ h₂
        exact hargs _ a₁ a₂ h₁ h₂)
    cases R.pins.lookup n with
    | some pin =>
      by_cases hlt : as₂.length < R.nP
      · simp only [hlt, ite_true]
        exact ⟨by simp, fun _ _ h₁ _ => nomatch h₁⟩
      · simp only [hlt, ite_false, reduceCtorEq, Option.some.injEq]
        exact ⟨by simp, fun r₁ r₂ h₁ h₂ => by subst h₁ h₂; exact hdropE pin⟩
    | none =>
      cases R.ctorPins.find? (fun q => q.1 == n) with
      | some q =>
        obtain ⟨_, pin, newName⟩ := q
        by_cases hlt : as₂.length < R.nP
        · simp only [hlt, ite_true]
          exact ⟨by simp, fun _ _ h₁ _ => nomatch h₁⟩
        · simp only [hlt, ite_false]
          cases pin.getAppFn with
          | const _ ilvls =>
            simp only [reduceCtorEq, Option.some.injEq]
            exact ⟨by simp, fun r₁ r₂ h₁ h₂ => by subst h₁ h₂; exact hdropE _⟩
          | bvar _ | fvar _ _ | sort _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
          | proj _ _ _ => exact ⟨by simp, fun _ _ h₁ _ => nomatch h₁⟩
      | none => exact ⟨by simp, fun _ _ h₁ _ => nomatch h₁⟩

/-- The node-level half of `restoreI_erasedEq`: a term with no blind
mention is its own restoration on both sides; else both sides are
unpruned, and either both fire (erasure-equal answers) or both decline
(the children's case, `hkids`). -/
theorem restoreI_erasedEq_node {R : RestoreTbl} (hR : R.Named) {e₁ e₂ : Expr}
    (h : Expr.ErasedEq e₁ e₂)
    (hkids : ∀ n ∈ R.auxNames, e₁.mentionsConst n = true → e₂.mentionsConst n = true →
      restoreNodeI R e₁ = none → restoreNodeI R e₂ = none →
      Expr.ErasedEq (restoreI R e₁) (restoreI R e₂)) :
    Expr.ErasedEq (restoreI R e₁) (restoreI R e₂) := by
  by_cases hno : ∀ n ∈ R.auxNames, e₁.mentionsConstE n = false
  · rw [restoreI_eq_self hR e₁ hno, restoreI_eq_self hR e₂ (fun n hn => by
      rw [← Expr.mentionsConstE_erasedEq h]; exact hno n hn)]
    exact h
  have hsome : ∃ n ∈ R.auxNames, e₁.mentionsConstE n = true := by
    refine Classical.byContradiction fun hne => hno fun n hn => ?_
    cases hm : e₁.mentionsConstE n with
    | false => rfl
    | true => exact absurd ⟨n, hn, hm⟩ hne
  obtain ⟨n, hn, hm⟩ := hsome
  have hm₁ := Expr.mentionsConst_of_mentionsConstE _ hm
  have hm₂ : e₂.mentionsConst n = true :=
    Expr.mentionsConst_of_mentionsConstE _ (by rw [← Expr.mentionsConstE_erasedEq h]; exact hm)
  obtain ⟨hnone, hsomeE⟩ := restoreNodeI_erasedEq (R := R) h
  cases hn₁ : restoreNodeI R e₁ with
  | some r₁ =>
    cases hn₂ : restoreNodeI R e₂ with
    | some r₂ =>
      rw [restoreI_of_node hn hm₁ hn₁, restoreI_of_node hn hm₂ hn₂]
      exact hsomeE r₁ r₂ hn₁ hn₂
    | none => exact absurd (hnone.mpr hn₂) (by rw [hn₁]; simp)
  | none => exact hkids n hn hm₁ hm₂ hn₁ (hnone.mp hn₁)

/-- **`restoreI` is blind to `fvar` annotations.** -/
theorem restoreI_erasedEq {R : RestoreTbl} (hR : R.Named) :
    ∀ (e₁ e₂ : Expr), Expr.ErasedEq e₁ e₂ → Expr.ErasedEq (restoreI R e₁) (restoreI R e₂) := by
  intro e₁
  induction e₁ with
  | app f a ihf iha =>
    intro e₂ h
    cases e₂ with
    | app g b =>
      obtain ⟨h₁, h₂⟩ := h
      refine restoreI_erasedEq_node hR ⟨h₁, h₂⟩ fun n hn hm₁ hm₂ hn₁ hn₂ => ?_
      rw [restoreI_of_decline_app hn hm₁ hn₁, restoreI_of_decline_app hn hm₂ hn₂]
      exact ⟨ihf g h₁, iha b h₂⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | lam ty b bm ihty ihb =>
    intro e₂ h
    cases e₂ with
    | lam ty' b' bm' =>
      obtain ⟨rfl, h₁, h₂⟩ := h
      refine restoreI_erasedEq_node hR ⟨rfl, h₁, h₂⟩ fun n hn hm₁ hm₂ hn₁ hn₂ => ?_
      rw [restoreI_of_decline_lam hn hm₁ hn₁, restoreI_of_decline_lam hn hm₂ hn₂]
      exact ⟨rfl, ihty ty' h₁, ihb b' h₂⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | forallE ty b bm ihty ihb =>
    intro e₂ h
    cases e₂ with
    | forallE ty' b' bm' =>
      obtain ⟨rfl, h₁, h₂⟩ := h
      refine restoreI_erasedEq_node hR ⟨rfl, h₁, h₂⟩ fun n hn hm₁ hm₂ hn₁ hn₂ => ?_
      rw [restoreI_of_decline_forallE hn hm₁ hn₁, restoreI_of_decline_forallE hn hm₂ hn₂]
      exact ⟨rfl, ihty ty' h₁, ihb b' h₂⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | letE ty v b ihty ihv ihb =>
    intro e₂ h
    cases e₂ with
    | letE ty' v' b' =>
      obtain ⟨h₁, h₂, h₃⟩ := h
      refine restoreI_erasedEq_node hR ⟨h₁, h₂, h₃⟩ fun n hn hm₁ hm₂ hn₁ hn₂ => ?_
      rw [restoreI_of_decline_letE hn hm₁ hn₁, restoreI_of_decline_letE hn hm₂ hn₂]
      exact ⟨ihty ty' h₁, ihv v' h₂, ihb b' h₃⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | proj s i x ihx =>
    intro e₂ h
    cases e₂ with
    | proj s' i' x' =>
      obtain ⟨rfl, rfl, h₁⟩ := h
      refine restoreI_erasedEq_node hR ⟨rfl, rfl, h₁⟩ fun n hn hm₁ hm₂ hn₁ hn₂ => ?_
      rw [restoreI_of_decline_proj hn hm₁ hn₁, restoreI_of_decline_proj hn hm₂ hn₂]
      exact ⟨rfl, rfl, ihx x' h₁⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _
    | letE _ _ _ => simp [Expr.ErasedEq] at h
  | bvar i =>
    intro e₂ h
    cases e₂ with
    | bvar j =>
      obtain rfl := h
      exact Expr.ErasedEq.rfl _
    | fvar _ _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | fvar i ty _ =>
    intro e₂ h
    cases e₂ with
    | fvar j ty' =>
      obtain rfl := h
      rw [restoreI_leaf_fvar, restoreI_leaf_fvar]
      rfl
    | bvar _ | sort _ | const _ _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | sort u =>
    intro e₂ h
    cases e₂ with
    | sort v =>
      obtain rfl := h
      exact Expr.ErasedEq.rfl _
    | bvar _ | fvar _ _ | const _ _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | const m ms =>
    intro e₂ h
    cases e₂ with
    | const m' ms' =>
      obtain ⟨rfl, rfl⟩ := h
      exact Expr.ErasedEq.rfl _
    | bvar _ | fvar _ _ | sort _ | lit _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h
  | lit l =>
    intro e₂ h
    cases e₂ with
    | lit l' =>
      obtain rfl := h
      exact Expr.ErasedEq.rfl _
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _
    | proj _ _ _ => simp [Expr.ErasedEq] at h

/-! ## The restored constant, opened -/

/-- A `∀`-telescope opens at any depth. -/
theorem openPisAtFvars_of_stripPis' :
    ∀ (n : Nat) {e : Expr} (d : Nat) {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, e, d, bs, body, _ => ⟨[], e, rfl⟩
  | n + 1, e, d, bs, body, hs => by
    match e, hs with
    | .forallE ty b bm, hs =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₁, r₁⟩, hs₁, -⟩ := hs
      have hsome : ((b.instantiate1 (.fvar d ty) 0).stripPis n).isSome :=
        Expr.stripPis_instantiate1_isSome n 0 (by rw [hs₁]; rfl)
      obtain ⟨⟨bs₂, r₂⟩, hs₂⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨fvs, o, hop⟩ := openPisAtFvars_of_stripPis' n (d + 1) hs₂
      refine ⟨.fvar d ty :: fvs, o, ?_⟩
      simp only [openPisAtFvars, hop]
    | .bvar _, hs | .fvar _ _, hs | .sort _, hs | .const _ _, hs | .app _ _, hs
    | .lam _ _ _, hs | .letE _ _ _, hs | .lit _, hs | .proj _ _ _, hs =>
      simp [Expr.stripPis] at hs

/-- A strip splits: `k + m` binders are `k`, then `m` more. -/
theorem stripPis_split :
    ∀ (k : Nat) {m : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      e.stripPis (k + m) = some (bs, r) →
      ∃ mid, e.stripPis k = some (bs.take k, mid) ∧ mid.stripPis m = some (bs.drop k, r)
  | 0, m, e, bs, r, h => ⟨e, rfl, by simpa using h⟩
  | k + 1, m, e, bs, r, h => by
    match e, h with
    | .forallE ty b bm, h =>
      rw [show k + 1 + m = (k + m) + 1 by omega] at h
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₁, r₁⟩, h₁, hbs⟩ := h
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨mid, hk, hm⟩ := stripPis_split k h₁
      refine ⟨mid, ?_, by simpa using hm⟩
      simp only [Expr.stripPis, hk, Option.map_some, List.take_succ_cons]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      rw [show k + 1 + m = (k + m) + 1 by omega] at h
      simp [Expr.stripPis] at h

/-- Two strips join. -/
theorem stripPis_append' :
    ∀ (k : Nat) {m : Nat} {e : Expr} {bs bs' : List (Expr × BinderMeta)} {mid body : Expr},
      e.stripPis k = some (bs, mid) → mid.stripPis m = some (bs', body) →
      e.stripPis (k + m) = some (bs ++ bs', body)
  | 0, m, e, bs, bs', mid, body, h, h' => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | k + 1, m, e, bs, bs', mid, body, h, h' => by
    match e, h with
    | .forallE ty b bm, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₁, r₁⟩, h₁, hbs⟩ := h
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      rw [show k + 1 + m = (k + m) + 1 by omega]
      simp only [Expr.stripPis, stripPis_append' k h₁ h', Option.map_some, List.cons_append]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- The first `i` openers of two openings of the same binders agree. -/
theorem openers_take_eq {ty tyR : Expr} {n : Nat} {fvs fvsR : List Expr} {rest restR : Expr}
    {bs bsR : List (Expr × BinderMeta)} {body bodyR : Expr}
    (hop : openPisAtFvars n ty 0 = some (fvs, rest)) (hopR : openPisAtFvars n tyR 0 = some (fvsR, restR))
    (hs : ty.stripPis n = some (bs, body)) (hsR : tyR.stripPis n = some (bsR, bodyR))
    :
    ∀ i, i ≤ n → (∀ j, j < i → bsR[j]? = bs[j]?) → fvsR.take i = fvs.take i := by
  intro i
  induction i with
  | zero => intro _ _; rfl
  | succ i ih =>
    intro hi hbs
    have hprev := ih (by omega) (fun j hj => hbs j (by omega))
    have hbsLen : bs.length = n := stripPis_length' n hs
    have hbsRLen : bsR.length = n := stripPis_length' n hsR
    obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hbR : bsR[i]? = some b := by rw [hbs i (by omega)]; exact hb
    have hx := openPisAtFvars_binder n hop hs i b hb
    have hxR := openPisAtFvars_binder n hopR hsR i b hbR
    rw [List.take_add_one, List.take_add_one, hx, hxR, hprev]

/-- **The restored constant, opened at `fvar`s** (task #279 M-D′ D1):
opening `restoreNested R ty` at `n ≥ nP` variables gives the same
parameter openers, then at every later position an opener whose
annotation is `restoreI` (at the parameter openers) of the auxiliary
opener's annotation up to erasure, and a residual likewise.  The
`ErasedEq` is exactly the openers' annotations: the restored opening
carries restored annotations, the auxiliary one the auxiliary ones. -/
theorem restoreNested_openPis {R : RestoreTbl} (hR : R.WF) {ty tyR : Expr}
    (h : restoreNested R ty = .ok tyR) (hfv : ty.hasFvar = false)
    {n : Nat} (hn : R.nP ≤ n) {fvs : List Expr} {rest : Expr}
    (hop : openPisAtFvars n ty 0 = some (fvs, rest)) :
    ∃ (fvsR : List Expr) (restR : Expr),
      openPisAtFvars n tyR 0 = some (fvsR, restR) ∧ fvsR.length = n ∧
      fvsR.take R.nP = fvs.take R.nP ∧
      (∀ (i : Nat) (x xR : Expr), R.nP ≤ i → fvs[i]? = some x → fvsR[i]? = some xR →
        ∃ tyX, xR = .fvar i tyX ∧
          Expr.ErasedEq xR.fvarTypeD (restoreI (R.instAt (fvs.take R.nP)) x.fvarTypeD)) ∧
      Expr.ErasedEq restR (restoreI (R.instAt (fvs.take R.nP)) rest) := by
  obtain ⟨bs, body₀, hs, hlen, hshape, hrest⟩ := Verify.openPisAtFvars_stripPis n hop
  -- the strip at the parameters, then at the fields
  obtain ⟨mid, hp, hm⟩ := stripPis_split R.nP (m := n - R.nP)
    (by rw [show R.nP + (n - R.nP) = n by omega]; exact hs)
  obtain ⟨mid', hwalk, hsR⟩ := restoreNested_stripPis h hp
  obtain ⟨bs', body₀', hsR', hlen', hall', hwrest⟩ := restoreWalk_stripPis (n - R.nP) hwalk hm
  have hsRn : tyR.stripPis n = some (bs.take R.nP ++ bs', body₀') := by
    have := stripPis_append' R.nP hsR hsR'
    rwa [show R.nP + (n - R.nP) = n by omega] at this
  obtain ⟨fvsR, restR, hopR⟩ := openPisAtFvars_of_stripPis' n 0 hsRn
  obtain ⟨bsR, bodyR, hsR2, hlenR, hshapeR, hrestR⟩ := Verify.openPisAtFvars_stripPis n hopR
  rw [hsRn] at hsR2
  simp only [Option.some.injEq, Prod.mk.injEq] at hsR2
  obtain ⟨rfl, rfl⟩ := hsR2
  have hplen : (bs.take R.nP).length = R.nP := by rw [List.length_take, stripPis_length' n hs]; omega
  have hbsLen : bs.length = n := stripPis_length' n hs
  -- the binders agree below the parameters
  have hbsEq : ∀ j, j < R.nP → (bs.take R.nP ++ bs')[j]? = bs[j]? := by
    intro j hj
    rw [List.getElem?_append_left (by omega), List.getElem?_take, if_pos hj]
  have htake := openers_take_eq hop hopR hs hsRn R.nP hn hbsEq
  -- the openers are `fvar`s
  have hF : Expr.AllFvars fvs := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨tyX, hx⟩ := hshape j (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hj).1)
    rw [hj] at hx
    exact ⟨_, _, Option.some.inj hx⟩
  have hFR : Expr.AllFvars fvsR := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨tyX, hx⟩ := hshapeR j (by rw [← hlenR]; exact (List.getElem?_eq_some_iff.mp hj).1)
    rw [hj] at hx
    exact ⟨_, _, Option.some.inj hx⟩
  have hpsF : Expr.AllFvars (fvs.take R.nP) := fun a ha => hF a (List.mem_of_mem_take ha)
  have hps : (fvs.take R.nP).length = R.nP := by rw [List.length_take, hlen]; omega
  -- pointwise erasure of the two openings' prefixes
  have hpre : ∀ i, i ≤ n → ∀ (k : Nat) (a₁ a₂ : Expr), (fvsR.take i)[k]? = some a₁ →
      (fvs.take i)[k]? = some a₂ → Expr.ErasedEq a₁ a₂ := by
    intro i hi k a₁ a₂ h₁ h₂
    by_cases hk : k < i
    · rw [List.getElem?_take, if_pos hk] at h₁ h₂
      obtain ⟨t₁, ht₁⟩ := hshapeR k (by omega)
      obtain ⟨t₂, ht₂⟩ := hshape k (by omega)
      rw [ht₁] at h₁; rw [ht₂] at h₂
      obtain rfl := Option.some.inj h₁
      obtain rfl := Option.some.inj h₂
      show 0 + k = 0 + k
      rfl
    · rw [List.getElem?_take, if_neg hk] at h₁
      exact nomatch h₁
  refine ⟨fvsR, restR, hopR, hlenR, htake, ?_, ?_⟩
  · intro i x xR hi hx hxR
    have hiN : i < n := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨b', hb'⟩ : ∃ b', bs'[i - R.nP]? = some b' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen', List.length_drop]; omega)⟩
    have hbR : (bs.take R.nP ++ bs')[i]? = some b' := by
      rw [List.getElem?_append_right (by omega), hplen]; exact hb'
    obtain ⟨hmeta, hwb⟩ := hall' (i - R.nP) b b' (by
      rw [List.getElem?_drop, show R.nP + (i - R.nP) = i by omega]; exact hb) hb'
    have hxE := openPisAtFvars_binder n hop hs i b hb
    have hxRE := openPisAtFvars_binder n hopR hsRn i b' hbR
    rw [hxE] at hx; rw [hxRE] at hxR
    obtain rfl := Option.some.inj hx
    obtain rfl := Option.some.inj hxR
    refine ⟨_, by rw [Nat.zero_add], ?_⟩
    simp only [Expr.fvarTypeD]
    -- the commutation at the field's context
    have hsplit : fvs.take i = fvs.take R.nP ++ (fvs.drop R.nP).take (i - R.nP) := by
      rw [← List.take_add, show R.nP + (i - R.nP) = i by omega]
    have hxsLen : ((fvs.drop R.nP).take (i - R.nP)).length = i - R.nP := by
      rw [List.length_take, List.length_drop, hlen]; omega
    have hbfv : b.1.hasFvar = false :=
      (stripPis_not_hasFvar n hs hfv).1 b (List.mem_of_getElem? hb)
    have hcomm := restoreWalk_instSeq hR hps hpsF b.1 (i - R.nP) (i - 1) (by rw [Nat.zero_add] at hwb; exact hwb)
      hbfv ((fvs.drop R.nP).take (i - R.nP)) (by omega)
      (fun a ha => hF a (List.mem_of_mem_drop (List.mem_of_mem_take ha)))
      (fun hne => by
        rw [← hsplit] at hne
        have := List.length_pos_iff.mpr hne
        rw [List.length_take] at this
        omega)
    rw [← hsplit] at hcomm
    rw [← hcomm]
    exact Expr.instSeq_erasedEq_args _ _ _ (Expr.ErasedEq.rfl _) (hpre i (by omega)) (by
      rw [List.length_take, List.length_take, hlen, hlenR])
  · -- the residual
    have hbfv : body₀.hasFvar = false := (stripPis_not_hasFvar n hs hfv).2
    have hsplit : fvs = fvs.take R.nP ++ fvs.drop R.nP := (List.take_append_drop _ _).symm
    have hcomm := restoreWalk_instSeq hR hps hpsF body₀ (n - R.nP) (n - 1)
      (by rw [Nat.zero_add] at hwrest; exact hwrest) hbfv (fvs.drop R.nP) (by rw [List.length_drop, hlen]; exact Nat.le_refl _)
      (fun a ha => hF a (List.mem_of_mem_drop ha))
      (fun hne => by
        rw [← hsplit] at hne
        have := List.length_pos_iff.mpr hne
        omega)
    rw [← hsplit] at hcomm
    -- `restR ≈ instSeq fvsR body₀' ≈ instSeq fvs body₀' = restoreI (instSeq fvs body₀) ≈ restoreI rest`
    have h1 : Expr.ErasedEq restR (Expr.instSeq fvs (n - 1) body₀') := by
      refine hrestR.trans ?_
      exact Expr.instSeq_erasedEq_args _ _ _ (Expr.ErasedEq.rfl _) (fun k a₁ a₂ h₁ h₂ => by
        have hk : k < n := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp h₂).1
        obtain ⟨t₂, ht₂⟩ := hshape k hk
        rw [ht₂] at h₂
        obtain rfl := Option.some.inj h₂
        rw [Verify.openFvars_getElem? hk] at h₁
        obtain rfl := Option.some.inj h₁
        show 0 + k = 0 + k
        rfl) (by rw [Verify.openFvars_length, hlen])
    refine h1.trans ?_
    rw [hcomm]
    refine restoreI_erasedEq (hR.toNamed.instAt _) _ _ ?_
    refine (Expr.instSeq_erasedEq_args _ _ _ (Expr.ErasedEq.rfl _) (fun k a₁ a₂ h₁ h₂ => ?_)
      (by rw [Verify.openFvars_length, hlen])).trans hrest.symm
    have hk : k < n := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp h₁).1
    obtain ⟨t₁, ht₁⟩ := hshape k hk
    rw [ht₁] at h₁
    obtain rfl := Option.some.inj h₁
    rw [Verify.openFvars_getElem? hk] at h₂
    obtain rfl := Option.some.inj h₂
    show 0 + k = 0 + k
    rfl

/-! ## `restoreI` on the shapes the datum holds -/

/-- **The fire**: a copy application at the block's parameters restores
to the table's pin at the remaining arguments. -/
theorem restoreI_fire {R : RestoreTbl} (hR : R.Named) {aux : Name} {us : List Level}
    {params idx : List Expr} {pin : Expr} (hpin : R.pins.lookup aux = some pin)
    (hlen : params.length = R.nP) (hrec : params ++ idx = [] → R.recMap.lookup aux = none) :
    restoreI R (Expr.mkAppN (.const aux us) (params ++ idx)) = Expr.mkAppN pin idx := by
  have hn : aux ∈ R.auxNames := hR.pinsNamed (aux, pin) (List.mem_of_lookup_some hpin)
  have hm := Expr.mentionsConst_mkAppN_const aux us (params ++ idx)
  refine restoreI_of_node hn hm ?_
  have hrec' : ∀ (m : Name) (ms : List Level),
      Expr.mkAppN (.const aux us) (params ++ idx) = .const m ms → R.recMap.lookup m = none := by
    intro m ms hc
    have hnil : params ++ idx = [] := by
      cases hpi : params ++ idx with
      | nil => rfl
      | cons a as =>
        exfalso
        rw [hpi] at hc
        rcases Expr.mkAppN_const_shape (n := aux) (ls := us) (a :: as) with h1 | ⟨f, b, h1⟩
        · have := congrArg Expr.getAppArgs h1
          rw [Expr.getAppArgs_mkAppN] at this
          exact nomatch this
        · rw [h1] at hc; exact nomatch hc
    rw [hnil] at hc
    simp only [Expr.mkAppN, Expr.const.injEq] at hc
    rw [← hc.1]
    exact hrec hnil
  rw [restoreNodeI_eq_head hrec', restoreHeadI_spine, hpin]
  simp only [List.length_append, show ¬ params.length + idx.length < R.nP by omega, ite_false,
    List.drop_left' hlen]

/-- Descent through a `∀`, unconditionally: a pruned node's children are
their own restorations. -/
theorem restoreI_forallE' {R : RestoreTbl} (hR : R.Named) (ty b : Expr) (bm : BinderMeta) :
    restoreI R (.forallE ty b bm) = .forallE (restoreI R ty) (restoreI R b) bm := by
  by_cases hp : ∀ n ∈ R.auxNames, (Expr.forallE ty b bm).mentionsConst n = false
  · rw [restoreI_forallE, restoreStepI_prune hp]
    have hty : ∀ n ∈ R.auxNames, ty.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : ty.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE ty hE] at this; exact nomatch this.1
    have hb : ∀ n ∈ R.auxNames, b.mentionsConstE n = false := by
      intro n hn
      have := hp n hn
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at this
      cases hE : b.mentionsConstE n with
      | false => rfl
      | true => rw [Expr.mentionsConst_of_mentionsConstE b hE] at this; exact nomatch this.2
    rw [restoreI_eq_self hR ty hty, restoreI_eq_self hR b hb]
  · have hsome : ∃ n ∈ R.auxNames, (Expr.forallE ty b bm).mentionsConst n = true := by
      refine Classical.byContradiction fun hne => hp fun n hn => ?_
      cases hm : (Expr.forallE ty b bm).mentionsConst n with
      | false => rfl
      | true => exact absurd ⟨n, hn, hm⟩ hne
    obtain ⟨n, hn, hm⟩ := hsome
    exact restoreI_of_decline_forallE hn hm (by
      rw [restoreNodeI_eq_head (fun _ _ h => by simp at h)]
      exact restoreHeadI_nonconst (fun _ _ h => by simp [Expr.getAppFn] at h))

/-- Descent through a telescope. -/
theorem restoreI_stripPis {R : RestoreTbl} (hR : R.Named) :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      e.stripPis n = some (bs, r) →
      (restoreI R e).stripPis n = some (bs.map fun b => (restoreI R b.1, b.2), restoreI R r)
  | 0, e, bs, r, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | n + 1, e, bs, r, h => by
    match e, h with
    | .forallE ty b bm, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₁, r₁⟩, h₁, hbs⟩ := h
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      rw [restoreI_forallE' hR]
      simp only [Expr.stripPis, restoreI_stripPis hR n h₁, Option.map_some, List.map_cons]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- **A copy field, restored** (the datum's `FixOpened.recF`/`reflF`
shape): a field that opens at `n` variables to the copy at the block's
parameters and index arguments, whose telescope domains mention no
table name, restores to a field that opens at the SAME variables to
the pin at index arguments erasure-equal to the original's. -/
theorem restoreI_copyField {R : RestoreTbl} (hR : R.Named) {x : Expr} {n dpt : Nat}
    {afvs params idx : List Expr} {aux : Name} {us : List Level} {pin : Expr}
    (hop : openPisAtFvars n x dpt = some (afvs, Expr.mkAppN (.const aux us) (params ++ idx)))
    (hdoms : ∀ a ∈ afvs, ∀ m ∈ R.auxNames, a.fvarTypeD.mentionsConst m = false)
    (hpin : R.pins.lookup aux = some pin) (hpinC : pin.looseBVarsBounded 0 = true)
    (hlen : params.length = R.nP) (hrec : R.recMap.lookup aux = none) :
    ∃ o, openPisAtFvars n (restoreI R x) dpt = some (afvs, o) ∧
      Expr.ErasedEq o (Expr.mkAppN pin idx) := by
  obtain ⟨bs, r, hs, hlenA, hshape, hres⟩ := Verify.openPisAtFvars_stripPis n hop
  have hFo : Expr.AllFvars (Verify.openFvars dpt n) := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    have hjn : j < n := by rw [← Verify.openFvars_length dpt n]; exact (List.getElem?_eq_some_iff.mp hj).1
    rw [Verify.openFvars_getElem? hjn] at hj
    exact ⟨_, _, (Option.some.inj hj).symm⟩
  have hFa : Expr.AllFvars afvs := by
    intro a ha
    obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
    obtain ⟨t, ht⟩ := hshape j (by rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hj).1)
    rw [hj] at ht
    exact ⟨_, _, Option.some.inj ht⟩
  have hlenO : (Verify.openFvars dpt n).length ≤ n - 1 + 1 := by
    rw [Verify.openFvars_length]; omega
  -- the raw residual is the spine
  obtain ⟨hfn, hlenArgs, hargs⟩ := hres.getApp
  have hfnI : (Expr.instSeq (Verify.openFvars dpt n) (n - 1) r).getAppFn = .const aux us := by
    rw [Expr.getAppFn_mkAppN] at hfn
    exact (hfn.const_left).symm ▸ rfl
  have hfnR : r.getAppFn = .const aux us := (getAppFn_instSeq_const_iff hFo hlenO).mp hfnI
  have hr : r = Expr.mkAppN (.const aux us) r.getAppArgs := by
    rw [← hfnR]; exact (Expr.mkAppN_getApp r).symm
  have hrI : Expr.instSeq (Verify.openFvars dpt n) (n - 1) r
      = Expr.mkAppN (.const aux us) (r.getAppArgs.map (Expr.instSeq (Verify.openFvars dpt n) (n - 1))) := by
    have h0 : Expr.instSeq (Verify.openFvars dpt n) (n - 1) (Expr.mkAppN (.const aux us) r.getAppArgs)
        = Expr.mkAppN (.const aux us) (r.getAppArgs.map (Expr.instSeq (Verify.openFvars dpt n) (n - 1))) := by
      rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl]
    rw [← hr] at h0
    exact h0
  have hlenR : r.getAppArgs.length = params.length + idx.length := by
    rw [Expr.getAppArgs_mkAppN] at hlenArgs
    rw [hrI, Expr.getAppArgs_mkAppN] at hlenArgs
    simpa [Expr.getAppArgs] using hlenArgs.symm
  -- the domains are their own restorations
  have hbs : bs.map (fun b => (restoreI R b.1, b.2)) = bs := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map]
    cases hb : bs[j]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some, Option.some.injEq]
      have hx := openPisAtFvars_binder n hop hs j b hb
      have hE : ∀ m ∈ R.auxNames, b.1.mentionsConstE m = false := by
        intro m hm
        have h1 := hdoms _ (List.mem_of_getElem? hx) m hm
        simp only [Expr.fvarTypeD] at h1
        cases hE : b.1.mentionsConstE m with
        | false => rfl
        | true =>
          exfalso
          have := Expr.mentionsConst_of_mentionsConstE _ (by
            rw [← Expr.mentionsConstE_instSeq_fvars (afvs.take j) (fun a ha => hFa a (List.mem_of_mem_take ha)) (j - 1)] at hE
            exact hE)
          rw [this] at h1
          exact nomatch h1
      rw [restoreI_eq_self hR _ hE]
  -- the restored field, stripped and opened
  have hsR := restoreI_stripPis hR n hs
  rw [hbs] at hsR
  have hrest : restoreI R r = Expr.mkAppN pin (r.getAppArgs.drop R.nP) := by
    have h0 := restoreI_fire hR (params := r.getAppArgs.take R.nP) (idx := r.getAppArgs.drop R.nP)
      (us := us) hpin (by rw [List.length_take]; omega) (fun _ => hrec)
    rw [List.take_append_drop, ← hr] at h0
    exact h0
  rw [hrest] at hsR
  obtain ⟨afvs', o, hopR⟩ := openPisAtFvars_of_stripPis' n dpt hsR
  obtain ⟨bsR, rR, hsR', hlenA', hshape', hres'⟩ := Verify.openPisAtFvars_stripPis n hopR
  rw [hsR] at hsR'
  simp only [Option.some.injEq, Prod.mk.injEq] at hsR'
  obtain ⟨rfl, rfl⟩ := hsR'
  -- the openers agree
  have hafvs : afvs' = afvs := by
    have h1 : afvs'.take n = afvs.take n := by
      -- the same binders at every position: `openers_take_eq` at depth `dpt`
      have hgen : ∀ i, i ≤ n → afvs'.take i = afvs.take i := by
        intro i
        induction i with
        | zero => intro _; rfl
        | succ i ih =>
          intro hi
          have hprev := ih (by omega)
          have hbsLen : bs.length = n := stripPis_length' n hs
          obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hx := openPisAtFvars_binder n hop hs i b hb
          have hxR := openPisAtFvars_binder n hopR hsR i b hb
          rw [List.take_add_one, List.take_add_one, hx, hxR, hprev]
      exact hgen n (Nat.le_refl n)
    rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h1
  subst hafvs
  refine ⟨o, hopR, ?_⟩
  -- the residual: `o ≈ instSeq openFvars (pin (args.drop nP))`, and those arguments erase to `idx`
  refine hres'.trans ?_
  rw [Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ hpinC]
  refine Expr.ErasedEq.mkAppN _ _ (Expr.ErasedEq.rfl _) (by rw [List.length_map, List.length_drop, hlenR]; omega)
    (fun k a₁ a₂ h₁ h₂ => ?_)
  rw [List.getElem?_map, List.getElem?_drop] at h₁
  -- `a₁` is the `nP + k`-th argument's instantiation, `a₂` is `idx[k]`
  cases hq : r.getAppArgs[R.nP + k]? with
  | none => rw [hq] at h₁; exact nomatch h₁
  | some q =>
    rw [hq] at h₁
    simp only [Option.map_some, Option.some.injEq] at h₁
    subst h₁
    have hk : (params ++ idx)[R.nP + k]? = some a₂ := by
      rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]; exact h₂
    have := hargs (R.nP + k) a₂ (Expr.instSeq (Verify.openFvars dpt n) (n - 1) q)
      (by rw [Expr.getAppArgs_mkAppN]; simpa [Expr.getAppArgs] using hk)
      (by rw [hrI, Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs, List.getElem?_map, hq])
    exact this.symm

end ConLeche
