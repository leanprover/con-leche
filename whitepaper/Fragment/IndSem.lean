module

public import Fragment.IndCommon
public import Fragment.Access

@[expose] public section

/-!
# The model of an inductive block: the family

What the type former and the constructors of a plain block (`IndSpec`,
`Decl.lean`) denote, and the laws about it that are pure set theory —
no derivation, no environment.  Everything here is at a fixed list of
concrete levels `ls` for the block's parameters (the valuation is
`valOf S.lparams ls`, `IndSpec.ψ`) and at fixed parameter values `ps`.

**The operator.**  A *family* is a function `W : List V → V` from
index values (innermost first) to sets, its fibres.  The block's
operator `famOp` sends a family `W` to the family whose fibre at `is`
is the set of **constructor values** `ctorVal j fs` — the tagged tuple
`tag j (tuple fs)` above a proposition, the point at one — of all
field lists `fs` *fitting* some constructor `j` relative to `W`, with
`is` that constructor's index expressions read under the fields.  A
field list fits (`FitsFields`) when each value is a member of its
field's set at the earlier values (`fieldSet`): an *ordinary* field's
set is its domain's denotation; a *reflexive* field's set is the
product over the field's telescope into the fibres of `W` at the
field's index expressions — with an empty telescope (a *recursive*
field), the fibre itself; a *container* field's set is the **class
at the approximant**: the container's family — its set in the model,
`classSet` — read at the class's arguments with the fibre of `W` at
the nested occurrence's index expressions in the nested position.
The fibre is built as a set with the universe's operations: the
fitting lists of a constructor are a set of tuples (`fitsSet`, by
replacement and union along the fields), and the fibre is the image
of those with the right index values.

**The family** is the least fixed point of the operator inside the
set theory (`lfpFamSet`, `LfpSet.lean`), which exists because the
operator is **monotone** (`famOp_mono`) and has a **closed family in
the universe** — at a proposition outright (`closedFam_zero`), above
one by **accessibility** (`closed_of_acc`, `Access.lean`): every
constructor value depends on a bounded subfamily of its input.
Monotonicity and accessibility are *by positivity*, field kind by
field kind — the two proofs the paper is about, `famOp_mono` and
`famOp_acc`, with the bound `bound`:

* an **ordinary** field is read in `W`-free terms, so it contributes
  nothing to the support and nothing to monotonicity;
* a **recursive** field's value is a member of a fibre of `W`: its
  support is that one occurrence, and the fibre grows with `W`;
* a **reflexive** field's value is a function over its telescope into
  fibres of `W`: its support is one occurrence per fitting argument
  list — a set of tuples, a member of the universe when the
  telescope is — and the product grows with its fibres;
* a **container** field's value is a member of the class at the fibre
  of `W` at the nested occurrence: its support is the value's own
  support in that fibre, coded inside the class's bound, and the
  class grows with the fibre — the two facts the operator asks of
  the container's clause (`ContClause`: monotone, in the universe,
  accessible with the bound `classBound`, and inhabited at the
  one-fibre set when inhabited at all), which the installation of a
  nested block proves from the container's positivity and the
  leastness of its fixed point (`NestSem.lean`); for a plain block
  there is no container and nothing is asked (`contOk_of_plain`).

Because no field reads an earlier recursive or container field
(`NoRecDep`, the block's own positivity condition: con-leche's
`structUsedLater` guard), the telescopes and the ordinary domains met
along an instance are the same at every family, which is what makes
the bound ONE set.
That the bound and the operator's fibres are members of the universe
is the **universe bound on the fields** (`DomsBounded`): the domains
met along an instance of any family in the universe are members of
the result universe — con-leche's `fieldsOk`, recorded at every hole
frame of the tuple space; the installation derives it from the
checker's field-sort check (`Ok`, `Decl.lean`) read in a model in which
the former denotes an arbitrary family (`InstallInd.lean`).

Con-leche: the hole operator of `ConLeche/Model/Annot/BlockLfp.lean`
(`LfpClause.fibre`: a fibre is the set of injections of the spines
fitting a constructor; `fitsMono`: the fit grows with the tuple),
monotonicity and accessibility by inversion of the positivity run
(`ConLeche/Semantics/Inductives/HoleMono.lean`, `HoleAcc.lean`:
`MonoOn.pi`/`AccOn.pi` for a product over a hole-free domain,
`MonoOn.holeApp`/`AccOn.holeApp` for a hole applied to hole-free
arguments — the fragment's reflexive and recursive clauses — and
`ConstOn` for a hole-free reading — the ordinary clause), the tagged
tuples of `ConLeche/SetModel/TaggedSum.lean` and `TupleTower.lean`,
the container clause of `Model/Annot/BlockLfpMono.lean` (a
container's instance through its lfp clause) and
`SetModel/HoleClose.lean`, and the carrier `LfpDatum.carrier` as
`lfpTuple` of the operator.
-/

namespace Fragment
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-! ## Tuples, read back; finite unions -/

open Classical in
/-- The list a tuple is the tuple of (`[]` off the tuples). -/
noncomputable def untuple (t : V) : List V :=
  if h : ∃ vs, (tuple vs : V) = t then Classical.choose h else []

theorem untuple_tuple (vs : List V) : untuple (tuple vs : V) = vs := by
  unfold untuple
  have h : ∃ ws, (tuple ws : V) = tuple vs := ⟨vs, rfl⟩
  rw [dif_pos h]
  exact tuple_inj (Classical.choose_spec h)

/-- The union of a list of sets. -/
noncomputable def listUnion : List V → V
  | [] => empty
  | A :: As => binUnion A (listUnion As)

theorem mem_listUnion {x : V} : ∀ {As : List V}, x ∈ˢ listUnion As ↔ ∃ A ∈ As, x ∈ˢ A
  | [] => by simp [listUnion, not_mem_empty]
  | A :: _ => by
    simp only [listUnion, mem_binUnion, List.mem_cons, exists_eq_or_imp]
    rw [mem_listUnion]

theorem listUnion_mem_univ {n : Nat} (hn : n ≠ 0) :
    ∀ {As : List V}, (∀ A ∈ As, A ∈ˢ (univ n : V)) → listUnion As ∈ˢ (univ n : V)
  | [], _ => empty_mem_univ n
  | A :: _, h =>
    binUnion_mem_univ hn (h A List.mem_cons_self)
      (listUnion_mem_univ hn fun B hB => h B (List.mem_cons_of_mem A hB))

/-- The set of tuples of value lists fitting a context (innermost
first): replacement and union along the context. -/
noncomputable def ctxSet (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) : List Expr → V
  | [] => sing (tuple [])
  | A :: Γ => famUnion (ctxSet M φ ρ Γ) fun t =>
      famUnion (interp M φ (consList (untuple t) ρ) A) fun y => sing (tuple (y :: untuple t))

theorem mem_ctxSet (M : Name → List Nat → V) (φ : Name → Nat) (ρ : Nat → V) :
    ∀ {Γ : List Expr} {x : V}, x ∈ˢ ctxSet M φ ρ Γ ↔ ∃ ys, FitsVals M φ ρ Γ ys ∧ x = tuple ys
  | [], x => by
    simp only [ctxSet, mem_sing]
    constructor
    · rintro rfl; exact ⟨[], trivial, rfl⟩
    · rintro ⟨ys, hys, rfl⟩
      cases ys with
      | nil => rfl
      | cons _ _ => exact hys.elim
  | A :: Γ, x => by
    simp only [ctxSet, mem_famUnion, mem_sing]
    constructor
    · rintro ⟨t, ht, y, hy, rfl⟩
      obtain ⟨ys, hys, rfl⟩ := (mem_ctxSet M φ ρ).mp ht
      rw [untuple_tuple] at hy ⊢
      exact ⟨y :: ys, ⟨hys, hy⟩, rfl⟩
    · rintro ⟨ys, hys, rfl⟩
      cases ys with
      | nil => exact hys.elim
      | cons y ys =>
        refine ⟨tuple ys, (mem_ctxSet M φ ρ).mpr ⟨ys, hys.1, rfl⟩, y, ?_, ?_⟩
        · rw [untuple_tuple]; exact hys.2
        · rw [untuple_tuple]

/-- The tuples of a context whose domains are members of a positive
universe are members of it. -/
theorem ctxSet_mem_univ (M : Name → List Nat → V) (φ : Name → Nat) {n : Nat} (hn : n ≠ 0) :
    ∀ {Γ : List Expr} {ρ : Nat → V},
      (∀ i A, Γ[i]? = some A → ∀ vs, FitsVals M φ ρ (Γ.drop (i + 1)) vs →
        interp M φ (consList vs ρ) A ∈ˢ (univ n : V)) →
      ctxSet M φ ρ Γ ∈ˢ (univ n : V) ∧
        ∀ ys, FitsVals M φ ρ Γ ys → ∀ y ∈ ys, y ∈ˢ (univ n : V)
  | [], ρ, _ => by
    refine ⟨sing_mem_univ hn (tuple_mem_univ hn fun _ h => absurd h List.not_mem_nil), ?_⟩
    intro ys hys y hy
    cases ys with
    | nil => exact absurd hy List.not_mem_nil
    | cons _ _ => exact hys.elim
  | A :: Γ, ρ, hdom => by
    obtain ⟨ih, ihv⟩ := ctxSet_mem_univ M φ hn (Γ := Γ) (ρ := ρ)
      fun i B hB vs hvs => hdom (i + 1) B hB vs hvs
    have hval : ∀ ys, FitsVals M φ ρ (A :: Γ) ys → ∀ y ∈ ys, y ∈ˢ (univ n : V) := by
      intro ys hys y hy
      cases ys with
      | nil => exact absurd hy List.not_mem_nil
      | cons y' ys =>
        rcases List.mem_cons.mp hy with rfl | hy
        · exact univ_trans hn (hdom 0 A rfl ys hys.1) hys.2
        · exact ihv ys hys.1 y hy
    refine ⟨?_, hval⟩
    simp only [ctxSet]
    refine famUnion_mem_univ hn ih fun t ht => ?_
    obtain ⟨ys, hys, rfl⟩ := (mem_ctxSet M φ ρ).mp ht
    rw [untuple_tuple]
    refine famUnion_mem_univ hn (hdom 0 A rfl ys hys) fun y hy => ?_
    refine sing_mem_univ hn (tuple_mem_univ hn fun v hv => ?_)
    exact hval (y :: ys) ⟨hys, hy⟩ v hv

/-- Two environments under which a context's domains read alike at
fitting prefixes have the same fits and the same tuples. -/
theorem ctxSet_congr (M : Name → List Nat → V) (φ : Name → Nat) :
    ∀ {Γ : List Expr} {ρ ρ' : Nat → V},
      (∀ i A, Γ[i]? = some A → ∀ vs, FitsVals M φ ρ (Γ.drop (i + 1)) vs →
        interp M φ (consList vs ρ) A = interp M φ (consList vs ρ') A) →
      (∀ ys, FitsVals M φ ρ Γ ys ↔ FitsVals M φ ρ' Γ ys) ∧ ctxSet M φ ρ Γ = ctxSet M φ ρ' Γ
  | [], _, _, _ => ⟨fun ys => by cases ys <;> exact Iff.rfl, rfl⟩
  | A :: Γ, ρ, ρ', h => by
    obtain ⟨ihf, ihs⟩ := ctxSet_congr M φ (Γ := Γ) (ρ := ρ) (ρ' := ρ')
      fun i B hB vs hvs => h (i + 1) B hB vs hvs
    refine ⟨fun ys => ?_, ?_⟩
    · cases ys with
      | nil => exact Iff.rfl
      | cons y ys =>
        simp only [FitsVals_cons]
        rw [ihf ys]
        constructor
        · rintro ⟨hys, hy⟩
          exact ⟨hys, by rwa [← h 0 A rfl ys (by simpa using (ihf ys).mpr hys)]⟩
        · rintro ⟨hys, hy⟩
          exact ⟨hys, by rwa [h 0 A rfl ys (by simpa using (ihf ys).mpr hys)]⟩
    · simp only [ctxSet]
      rw [ihs]
      refine famUnion_congr fun t ht => ?_
      obtain ⟨ys, hys, rfl⟩ := (mem_ctxSet M φ ρ').mp ht
      rw [untuple_tuple, h 0 A rfl ys (by simpa using (ihf ys).mpr hys)]

/-! ## Numerals -/

theorem nat_mem_univ {n : Nat} (hn : n ≠ 0) (k : Nat) : (nat k : V) ∈ˢ univ n :=
  univ_trans hn (omega_mem_univ hn) (mem_omega.mpr ⟨k, rfl⟩)

/-! ## η over a context, and re-typing a member of a product -/

/-- A member of a product over a context is the abstraction of its
applications (η, iterated). -/
theorem lamCtx_eta (M : Name → List Nat → V) (φ : Name → Nat) {p : Bool} {ρ : Nat → V} :
    ∀ {Γ : List Expr} {G : (Nat → V) → V} {f : V}, f ∈ˢ piCtx M φ p ρ Γ G →
      lamCtx M φ p ρ Γ (fun ρ' => appList f (readEnv Γ.length ρ').reverse) = f
  | [], _, f, _ => rfl
  | A :: Γ, G, f, hf => by
    rw [piCtx_cons] at hf
    rw [lamCtx_cons]
    refine Eq.trans ?_ (lamCtx_eta M φ hf)
    refine lamCtx_congr M φ fun ys hys => ?_
    have hl := FitsVals_length M φ hys
    rw [readEnv_consList hl]
    have hmem := appList_mem_of_piCtx M φ hf hys
    rw [← lamR_eta hmem]
    refine lamR_congr fun x _ => ?_
    rw [show cons x (consList ys ρ) = consList (x :: ys) ρ from rfl, List.length_cons,
      readEnv_consList (by simp [hl]), List.reverse_cons, appList_append, appList_cons, appList_nil]

/-- **Re-typing**: a member of a product over a context whose
applications at every fitting argument list land in other fibres is a
member of the product into those fibres (at a proposition they must
be truth values). -/
theorem piCtx_retype (M : Name → List Nat → V) (φ : Name → Nat) {p : Bool} {ρ : Nat → V}
    {Γ : List Expr} {G G' : (Nat → V) → V} {f : V} (hf : f ∈ˢ piCtx M φ p ρ Γ G)
    (h : ∀ ys, FitsVals M φ ρ Γ ys → appList f ys.reverse ∈ˢ G' (consList ys ρ))
    (hG' : p = true → ∀ ys, FitsVals M φ ρ Γ ys → G' (consList ys ρ) ∈ˢ (univ 0 : V)) :
    f ∈ˢ piCtx M φ p ρ Γ G' := by
  rw [← lamCtx_eta M φ hf]
  refine lamCtx_mem_piCtx M φ (fun ys hys => ?_) hG'
  rw [readEnv_consList (FitsVals_length M φ hys)]
  exact h ys hys

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-! ## Fields over a family -/

/-- **The set a field ranges over**, relative to a family `W` (index
values to sets), at parameters `ps` and the earlier field values `fs`
(innermost first): an ordinary field's domain; for a reflexive field
the product over its telescope into the fibres of `W` at the field's
index expressions read under the telescope's values — the fibre
itself when the telescope is empty; for a container field the class
at the fibre of `W` at the nested occurrence's index expressions
(`classSet`: the container's family, read at the class's arguments
with that fibre in the nested position; a plain block has no
container field, and the clause is empty).  Con-leche: a field's
reading with holes, `LfpDatum.fields`, read at the hole frame of the
tuple (`HFits`, `BlockLfp.lean`); the container clause `contApp`
through the container's lfp clause (`BlockLfpMono.lean`). -/
def fieldSet (W : List V → V) (ps fs : List V) : Field → V
  | .ordinary A => interp M (S.ψ ls) (consList fs (envP ps)) A
  | .reflexive tele es =>
    piCtx M (S.ψ ls) (S.z ls) (consList fs (envP ps)) tele fun ρ' => W (S.idxVals M ls ρ' es)
  | .container =>
    match S.nest with
    | some N => S.classSet M ls N ps (W (S.memberIdx M ls N ps))
    | none => empty

/-- The container clause, when the block has a class. -/
theorem fieldSet_container {N : NestInfo} (hN : S.nest = some N) (W : List V → V) (ps fs : List V) :
    S.fieldSet M ls W ps fs .container = S.classSet M ls N ps (W (S.memberIdx M ls N ps)) := by
  simp [fieldSet, hN]

/-- No container clause without a class. -/
theorem fieldSet_container_none (hpl : S.nest = none) (W : List V → V) (ps fs : List V) :
    S.fieldSet M ls W ps fs .container = empty := by
  simp [fieldSet, hpl]

/-- **Field values fitting a constructor's fields** (both innermost
first) relative to a family: each value a member of its field's set
at the earlier values.  Con-leche: `SpineFit` at the hole frame. -/
def FitsFields (W : List V → V) (ps : List V) : List Field → List V → Prop
  | [], [] => True
  | f :: fs, v :: vs => FitsFields W ps fs vs ∧ v ∈ˢ S.fieldSet M ls W ps vs f
  | _, _ => False

theorem FitsFields_length {W : List V → V} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.FitsFields M ls W ps fields fs → fs.length = fields.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [FitsFields_length h.1]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Each field of a fitting list is a member of its set at the
earlier fields. -/
theorem FitsFields_get {W : List V → V} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.FitsFields M ls W ps fields fs →
      ∀ {k : Nat} {f : Field}, fields[fields.length - 1 - k]? = some f → k < fields.length →
        fieldVal fs k ∈ˢ S.fieldSet M ls W ps (earlier fs k) f
  | [], [], _, k, _, _, hk => by simp at hk
  | f' :: fields, v :: fs, hf, k, f, h, hk => by
    have hlen := S.FitsFields_length M ls hf.1
    by_cases hkl : k = fields.length
    · subst hkl
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at h
      subst h
      simp only [fieldVal, earlier, List.length_cons, hlen, Nat.add_sub_cancel, Nat.sub_self,
        List.getD_cons_zero]
      rw [show fields.length + 1 - fields.length = 1 by omega, List.drop_succ_cons, List.drop_zero]
      exact hf.2
    · have hk' : k < fields.length := by simp at hk; omega
      have : fields.length + 1 - 1 - k = (fields.length - 1 - k) + 1 := by omega
      simp only [List.length_cons, this, List.getElem?_cons_succ] at h
      rw [fieldVal_cons (by omega), earlier_cons (by omega)]
      exact FitsFields_get hf.1 h hk'
  | [], _ :: _, hf, _, _, _, _ => hf.elim
  | _ :: _, [], hf, _, _, _, _ => hf.elim

/-- The earlier fields of a fitting list fit the earlier fields. -/
theorem FitsFields_earlier {W : List V → V} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.FitsFields M ls W ps fields fs →
      ∀ k, k ≤ fields.length →
        S.FitsFields M ls W ps (fields.drop (fields.length - k)) (earlier fs k)
  | [], [], _, _, _ => by simp [earlier, FitsFields]
  | f' :: fields, v :: fs, hf, k, hk => by
    have hlen := S.FitsFields_length M ls hf.1
    by_cases hkl : k = fields.length + 1
    · subst hkl
      simp only [earlier, List.length_cons, hlen, Nat.sub_self, List.drop_zero]
      exact hf
    · have hk' : k ≤ fields.length := by simp at hk; omega
      rw [earlier_cons (by omega), List.length_cons,
        show fields.length + 1 - k = (fields.length - k) + 1 by omega, List.drop_succ_cons]
      exact FitsFields_earlier hf.1 k hk'
  | [], _ :: _, hf, _, _ => hf.elim
  | _ :: _, [], hf, _, _ => hf.elim

/-! ## What the operator asks of the container's clause

A container field reads the class at the approximant's fibre at the
nested occurrence.  For the operator to be monotone and accessible,
the class must be, in the parameter set: it grows with it, stays in the
result universe, and every member of the class at `X` has a support
in `X` — occurrences in `X`, coded inside one set fixed by the
specification (`classBound`: the finite paths over the container's
field positions, the bound of the container's own accessibility in
the parameter, `Access.lean`'s `lfpP_acc`) — such that the member is
in the class at every parameter set of the universe holding the
support.  And for the block's bound to be one set the class at the
one-fibre set must be inhabited when the class is inhabited at all
(a container value's stand-in when the fields are read off the
family, `toOne`).  These are the facts `ContClause` lists; the
installation of a nested block proves them from the container's
positivity and the leastness of its fixed point (`NestSem.lean`,
`contClause_of`), and nothing is asked of a plain block
(`contOk_of_plain`).  Con-leche: the container case of
`Model/Annot/BlockLfpMono.lean` (monotone through the container's lfp
clause), `Model/Inductives/ContAcc.lean` (accessible). -/

/-- The numerals below `n`: `{nat 0, …, nat (n - 1)}`. -/
noncomputable def natsBelow (n : Nat) : V := sep omega fun z => idx z < n

theorem mem_natsBelow {n : Nat} {z : V} : z ∈ˢ natsBelow n ↔ ∃ k, k < n ∧ z = nat k := by
  unfold natsBelow
  rw [mem_sep, mem_omega]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    rw [idx_nat] at hk
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, rfl⟩, by rw [idx_nat]; exact hk⟩

theorem natsBelow_mem_univ {n : Nat} (hn : n ≠ 0) (m : Nat) : (natsBelow m : V) ∈ˢ univ n :=
  sep_mem_univ (omega_mem_univ hn)

/-- Some member of a set, if it has one; the point if not. -/
noncomputable def pickMem (A : V) : V :=
  open Classical in if h : ∃ v, v ∈ˢ A then Classical.choose h else pt

theorem pickMem_mem {A : V} (h : ∃ v, v ∈ˢ A) : pickMem A ∈ˢ A := by
  unfold pickMem; rw [dif_pos h]; exact Classical.choose_spec h

/-- The length of the longest field list of the container's
constructors: the field positions its support codes range over. -/
def _root_.Fragment.NestInfo.maxFields (N : NestInfo) : Nat :=
  N.K.ctors.foldr (fun c m => max c.fields.length m) 0

omit [IndLib V] in
theorem length_le_foldr_max {c : CtorSpec} :
    ∀ {cs : List CtorSpec}, c ∈ cs → c.fields.length ≤ cs.foldr (fun c m => max c.fields.length m) 0
  | [], hc => by simp at hc
  | c' :: cs, hc => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (length_le_foldr_max hc) (Nat.le_max_right _ _)

omit [IndLib V] in
theorem _root_.Fragment.NestInfo.length_le_maxFields (N : NestInfo) {c : CtorSpec}
    (hc : c ∈ N.K.ctors) : c.fields.length ≤ N.maxFields :=
  length_le_foldr_max hc

/-- **The class's bound**: the finite paths over the container's field
positions — the bound of the container's family's accessibility in
the parameter set (`lfpP_acc`, the paths over the container's joint
bound, which is one code per field position).  Empty for a plain
block. -/
noncomputable def classBound : V :=
  match S.nest with
  | some N => accPaths (natsBelow N.maxFields)
  | none => empty

theorem classBound_mem_univ {n : Nat} (hn : n ≠ 0) : S.classBound ∈ˢ (univ n : V) := by
  unfold classBound
  split
  · exact accPaths_mem_univ hn (natsBelow_mem_univ hn _)
  · exact empty_mem_univ n

theorem pt_mem_classBound {N : NestInfo} (hN : S.nest = some N) : (pt : V) ∈ˢ S.classBound := by
  unfold classBound
  rw [hN]
  exact pt_mem_accPaths _

/-- **The container's clause, as the operator needs it** at the
parameters `ps` (see the section heading): the class is monotone in
the parameter set, in the result universe, accessible with the class's
bound, and inhabited at the one-fibre set when inhabited at all. -/
structure ContClause (N : NestInfo) (ps : List V) : Prop where
  /-- The class grows with the parameter set. -/
  mono : ∀ X Y, X ⊆ˢ Y → X ∈ˢ (univ (S.u₀ ls) : V) → Y ∈ˢ (univ (S.u₀ ls) : V) →
    S.classSet M ls N ps X ⊆ˢ S.classSet M ls N ps Y
  /-- The class at a parameter set of the universe is in the universe. -/
  mem_univ : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.classSet M ls N ps X ∈ˢ (univ (S.u₀ ls) : V)
  /-- Every member of the class at `X` has a support in `X`, coded in
  the class's bound, carrying it to the class at every parameter set
  holding the support. -/
  acc : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → ∀ v, v ∈ˢ S.classSet M ls N ps X →
    ∃ (B : V) (g : V → V), B ⊆ˢ S.classBound ∧ (∀ b, b ∈ˢ B → g b ∈ˢ X) ∧
      ∀ X', X' ∈ˢ (univ (S.u₀ ls) : V) → (∀ b, b ∈ˢ B → g b ∈ˢ X') → v ∈ˢ S.classSet M ls N ps X'
  /-- The class at the one-fibre set is inhabited when the class at
  some parameter set of the universe is. -/
  inhab_one : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → (∃ v, v ∈ˢ S.classSet M ls N ps X) →
    ∃ v, v ∈ˢ S.classSet M ls N ps one

/-- **The container's clause holds**, when the block has a class
(vacuous for a plain block). -/
def ContOk (ps : List V) : Prop := ∀ N, S.nest = some N → S.ContClause M ls N ps

theorem contOk_of_plain (hpl : S.nest = none) (ps : List V) : S.ContOk M ls ps := by
  intro N hN
  rw [hpl] at hN
  cases hN

/-! ## The operator -/

/-- **The fitting lists of a field list, as a set of tuples**:
replacement and union along the fields (innermost first).
Con-leche builds the fibre the same way, by replacement over the
spines (`BlockLfp.lean`, `fibre`). -/
noncomputable def fitsSet (W : List V → V) (ps : List V) : List Field → V
  | [] => sing (tuple [])
  | f :: fs => famUnion (fitsSet W ps fs) fun t =>
      famUnion (S.fieldSet M ls W ps (untuple t) f) fun v => sing (tuple (v :: untuple t))

theorem mem_fitsSet {W : List V → V} {ps : List V} :
    ∀ {fields : List Field} {x : V},
      x ∈ˢ S.fitsSet M ls W ps fields ↔ ∃ fs, S.FitsFields M ls W ps fields fs ∧ x = tuple fs
  | [], x => by
    simp only [fitsSet, mem_sing]
    constructor
    · rintro rfl; exact ⟨[], trivial, rfl⟩
    · rintro ⟨fs, hfs, rfl⟩
      cases fs with
      | nil => rfl
      | cons _ _ => exact hfs.elim
  | f :: fields, x => by
    simp only [fitsSet, mem_famUnion, mem_sing]
    constructor
    · rintro ⟨t, ht, v, hv, rfl⟩
      obtain ⟨fs, hfs, rfl⟩ := mem_fitsSet.mp ht
      rw [untuple_tuple] at hv ⊢
      exact ⟨v :: fs, ⟨hfs, hv⟩, rfl⟩
    · rintro ⟨fs, hfs, rfl⟩
      cases fs with
      | nil => exact hfs.elim
      | cons v fs =>
        refine ⟨tuple fs, mem_fitsSet.mpr ⟨fs, hfs.1, rfl⟩, v, ?_, ?_⟩
        · rw [untuple_tuple]; exact hfs.2
        · rw [untuple_tuple]

/-- **The fibre of constructor `j`** at the family `W` and the index
values `is`: the constructor values of the fitting lists whose index
expressions read as `is`. -/
noncomputable def ctorFibre (W : List V → V) (ps is : List V) (j : Nat) (c : CtorSpec) : V :=
  open Classical in
  image (fun t => S.ctorVal ls j (untuple t))
    (sep (S.fitsSet M ls W ps c.fields) fun t =>
      is = S.idxVals M ls (consList (untuple t) (envP ps)) c.idx)

/-- **The block's operator** on families: the fibre at `is` is the
union over the constructors of their fibres.  Con-leche: the hole
operator `holeOp` (`BlockDatum.lean`), the operator of
`LfpClause.functor`. -/
noncomputable def famOp (ps : List V) (W : List V → V) (is : List V) : V :=
  listUnion ((List.range S.n).map fun j => S.ctorFibre M ls W ps is j (S.ctors.getD j ⟨"", [], []⟩))

/-- **A constructor instance over a family** at `is`: `x` is the
constructor value of fields fitting some constructor at `W`, with
`is` that constructor's index expressions read under the fields.
Con-leche: `HFits` with the injection, the right-hand side of
`LfpClause.fibre`. -/
def Inst (W : List V → V) (ps is : List V) (x : V) : Prop :=
  ∃ j c fs, S.ctors[j]? = some c ∧ S.FitsFields M ls W ps c.fields fs ∧
    is = S.idxVals M ls (consList fs (envP ps)) c.idx ∧ x = S.ctorVal ls j fs

/-- **What the operator is**: the members of its fibre at `is` are the
constructor instances over the input family at `is`.  Con-leche:
`LfpClause.fibre`. -/
theorem mem_famOp {ps : List V} {W : List V → V} {is : List V} {x : V} :
    x ∈ˢ S.famOp M ls ps W is ↔ S.Inst M ls W ps is x := by
  unfold famOp Inst
  rw [mem_listUnion]
  constructor
  · rintro ⟨A, hA, hx⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
    have hj' : j < S.n := List.mem_range.mp hj
    unfold ctorFibre at hx
    rw [mem_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rw [mem_sep] at ht
    obtain ⟨ht, his⟩ := ht
    obtain ⟨fs, hfs, rfl⟩ := (S.mem_fitsSet M ls).mp ht
    rw [untuple_tuple] at his ⊢
    refine ⟨j, S.ctors.getD j ⟨"", [], []⟩, fs, ?_, hfs, his, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rfl
  · rintro ⟨j, c, fs, hc, hfs, his, rfl⟩
    have hj : j < S.n := (List.getElem?_eq_some_iff.mp hc).1
    have hcd : S.ctors.getD j ⟨"", [], []⟩ = c := by
      rw [List.getD_eq_getElem?_getD, hc]; rfl
    refine ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
    unfold ctorFibre
    rw [hcd, mem_image]
    refine ⟨tuple fs, ?_, by rw [untuple_tuple]⟩
    rw [mem_sep, untuple_tuple]
    exact ⟨(S.mem_fitsSet M ls).mpr ⟨fs, hfs, rfl⟩, his⟩

/-! ## Monotonicity, by positivity

The fit grows with the family, field kind by field kind: an ordinary
field's set does not read the family; a reflexive field's set is a
product into fibres of the family, monotone in them (`piCtx_sub`) —
at a proposition the larger fibres must be truth values, which is
where the universe of the larger family enters; a container field's
set is the class at a fibre of the family, monotone in it by the
container's clause (`ContClause.mono`), which is where the universe
of both families enters.  Con-leche: `ConstOn.monoOn`, `MonoOn.pi`,
`MonoOn.holeApp` (`HoleMono.lean`), the container case of
`BlockLfpMono.lean`, and `LfpClause.fitsMono`. -/

/-- A fibre of a family in the universe at a proposition is a truth
value. -/
theorem fibre_mem_univ_zero {W : List V → V} (hW : InUniv (S.u₀ ls) W) (hz : S.z ls = true) (is : List V) :
    W is ∈ˢ (univ 0 : V) := by
  have := hW is
  rwa [(S.z_iff ls).mp hz] at this

/-- **A field's set grows with the family.** -/
theorem fieldSet_mono {ps : List V} (hc : S.ContOk M ls ps) {W W' : List V → V}
    (hW : InUniv (S.u₀ ls) W) (hW' : InUniv (S.u₀ ls) W') (hle : FamLe W W') (fs : List V) :
    ∀ f : Field, S.fieldSet M ls W ps fs f ⊆ˢ S.fieldSet M ls W' ps fs f
  | .ordinary _ => Sub.refl _
  | .reflexive tele es => by
    simp only [fieldSet]
    exact piCtx_sub M _ (fun _ _ => hle _) fun hz _ _ => S.fibre_mem_univ_zero ls hW' hz _
  | .container => by
    cases hN : S.nest with
    | none => rw [S.fieldSet_container_none M ls hN]; exact empty_sub _
    | some N =>
      rw [S.fieldSet_container M ls hN, S.fieldSet_container M ls hN]
      exact (hc N hN).mono _ _ (hle _) (hW _) (hW' _)

/-- **A fitting list fits at every larger family.** -/
theorem FitsFields_mono {ps : List V} (hc : S.ContOk M ls ps) {W W' : List V → V}
    (hW : InUniv (S.u₀ ls) W) (hW' : InUniv (S.u₀ ls) W') (hle : FamLe W W') :
    ∀ {fields : List Field} {fs : List V},
      S.FitsFields M ls W ps fields fs → S.FitsFields M ls W' ps fields fs
  | [], [], _ => trivial
  | _ :: _, _ :: fs, hf =>
    ⟨FitsFields_mono hc hW hW' hle hf.1, S.fieldSet_mono M ls hc hW hW' hle fs _ _ hf.2⟩
  | [], _ :: _, hf => hf.elim
  | _ :: _, [], hf => hf.elim

/-- **The operator is monotone**, on families in the result universe,
under the container's clause.  Con-leche: `LfpClause.functor`'s first
conjunct, from `fitsMono`. -/
theorem famOp_mono {ps : List V} (hc : S.ContOk M ls ps) : MonoFam (S.u₀ ls) (S.famOp M ls ps) := by
  intro W W' hW hW' hle is x hx
  obtain ⟨j, c, fs, hc', hfs, his, rfl⟩ := (S.mem_famOp M ls).mp hx
  exact (S.mem_famOp M ls).mpr ⟨j, c, fs, hc', S.FitsFields_mono M ls hc hW hW' hle hfs, his, rfl⟩

/-! ## The universe bound on the fields -/

/-- **The universe bound on the fields, at every family in the
universe**: above a proposition, along any list fitting the fields
before a position relative to a family of members of the result
universe, an ordinary field's domain is a member of the result
universe, and so is every entry of a reflexive field's telescope at
every fitting prefix of the telescope.  Con-leche: the constructors'
fields are small at every hole frame of the tuple space
(`LfpClause.fieldsOk`, `ConLeche/Model/Annot/BlockLfp.lean`, the
install's `FieldsOkB`); the installation derives it from the checker's
field-sort check read in a model in which the former denotes an
arbitrary family of the universe (`domsBounded_of`,
`InstallInd.lean`). -/
def DomsBounded (ps : List V) : Prop :=
  S.z ls = false → ∀ W, InUniv (S.u₀ ls) W → ∀ c ∈ S.ctors, ∀ k f,
    c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
    ∀ fs, S.FitsFields M ls W ps (c.fields.drop (c.fields.length - k)) fs →
      match f with
      | .ordinary A => interp M (S.ψ ls) (consList fs (envP ps)) A ∈ˢ (univ (S.u₀ ls) : V)
      | .reflexive tele _ => ∀ t T, tele[t]? = some T → ∀ ys,
          FitsVals M (S.ψ ls) (consList fs (envP ps)) (tele.drop (t + 1)) ys →
          interp M (S.ψ ls) (consList ys (consList fs (envP ps))) T ∈ˢ (univ (S.u₀ ls) : V)
      | .container => True

theorem u₀_ne_zero (hz : S.z ls = false) : S.u₀ ls ≠ 0 := fun h0 => by
  have := (S.z_iff ls).mpr h0
  rw [hz] at this
  exact Bool.false_ne_true this


/-! ### The bound reads the levels through the valuation only -/

theorem fieldSet_congr_ls {ls' : List Nat} (h : S.ψ ls = S.ψ ls') (W : List V → V) (ps fs : List V) :
    ∀ f : Field, S.fieldSet M ls W ps fs f = S.fieldSet M ls' W ps fs f
  | .ordinary _ => by simp only [fieldSet, h]
  | .reflexive _ _ => by simp only [fieldSet, idxVals, z, h]
  | .container => by simp only [fieldSet, classSet, classArgsV, lsK, memberIdx, idxVals, h]

theorem classSet_congr_ls {ls' : List Nat} (h : S.ψ ls = S.ψ ls') (N : NestInfo) :
    S.classSet M ls N = S.classSet M ls' N := by
  funext ps X
  simp only [classSet, classArgsV, lsK, h]

/-- The container's clause depends on the levels only through the
block's valuation. -/
theorem ContOk_congr_ls {ls' : List Nat} (h : S.ψ ls = S.ψ ls') {ps : List V}
    (hc : S.ContOk M ls ps) : S.ContOk M ls' ps := by
  intro N hN
  have hu : S.u₀ ls = S.u₀ ls' := by unfold u₀; rw [h]
  obtain ⟨h1, h2, h3, h4⟩ := hc N hN
  rw [S.classSet_congr_ls M ls h N] at h1 h2 h3 h4
  rw [hu] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem FitsFields_congr_ls {ls' : List Nat} (h : S.ψ ls = S.ψ ls') {W : List V → V} {ps : List V} :
    ∀ {fields : List Field} {fs : List V},
      S.FitsFields M ls W ps fields fs ↔ S.FitsFields M ls' W ps fields fs
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | f :: fields, v :: fs => by
    show (_ ∧ _) ↔ (_ ∧ _)
    rw [FitsFields_congr_ls h (fields := fields) (fs := fs), S.fieldSet_congr_ls M ls h W ps fs f]

/-- The universe bound on the fields depends on the levels only
through the block's valuation. -/
theorem DomsBounded_congr_ls {ls' : List Nat} (h : S.ψ ls = S.ψ ls') {ps : List V}
    (hd : S.DomsBounded M ls ps) : S.DomsBounded M ls' ps := by
  intro hz W hW c hc k f hf hk fs hfs
  have hz' : S.z ls = false := by unfold z; rw [h]; exact hz
  have hW' : InUniv (S.u₀ ls) W := by
    show InUniv (S.sort.eval (S.ψ ls)) W
    rw [h]; exact hW
  have := hd hz' W hW' c hc k f hf hk fs ((S.FitsFields_congr_ls M ls h).mpr hfs)
  cases f with
  | ordinary A =>
    unfold u₀ at this ⊢
    rw [h] at this
    exact this
  | reflexive tele es =>
    intro t T hT ys hys
    rw [← h] at hys
    have := this t T hT ys hys
    unfold u₀ at this ⊢
    rw [h] at this
    exact this
  | container => trivial

/-- A field's set at fitting earlier values is a member of the result
universe (above a proposition). -/
theorem fieldSet_mem_univ {ps : List V} (hz : S.z ls = false) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps)
    {W : List V → V} (hW : InUniv (S.u₀ ls) W) {c : CtorSpec} (hc : c ∈ S.ctors) {k : Nat}
    {f : Field} (hf : c.fields[c.fields.length - 1 - k]? = some f) (hk : k < c.fields.length)
    {fs : List V} (hfs : S.FitsFields M ls W ps (c.fields.drop (c.fields.length - k)) fs) :
    S.fieldSet M ls W ps fs f ∈ˢ (univ (S.u₀ ls) : V) := by
  have hb' := hb hz W hW c hc k f hf hk fs hfs
  cases f with
  | ordinary A => exact hb'
  | reflexive tele es =>
    simp only [fieldSet]
    exact piCtx_mem_univ M _ (S.u₀_ne_zero ls hz) hb' fun _ _ => hW _
  | container =>
    cases hN : S.nest with
    | none => rw [S.fieldSet_container_none M ls hN]; exact empty_mem_univ _
    | some N => rw [S.fieldSet_container M ls hN]; exact (hco N hN).mem_univ _ (hW _)

/-- The fitting lists of the fields before a position are a set of
the result universe, with members of it as entries (above a
proposition). -/
theorem fitsSet_mem_univ {ps : List V} (hz : S.z ls = false) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps)
    {W : List V → V} (hW : InUniv (S.u₀ ls) W) {c : CtorSpec} (hc : c ∈ S.ctors) :
    ∀ k, k ≤ c.fields.length →
      S.fitsSet M ls W ps (c.fields.drop (c.fields.length - k)) ∈ˢ (univ (S.u₀ ls) : V) ∧
      ∀ fs, S.FitsFields M ls W ps (c.fields.drop (c.fields.length - k)) fs →
        ∀ v ∈ fs, v ∈ˢ (univ (S.u₀ ls) : V)
  | 0, _ => by
    have hn := S.u₀_ne_zero ls hz
    rw [Nat.sub_zero, List.drop_length]
    refine ⟨sing_mem_univ hn (tuple_mem_univ hn fun _ h => absurd h List.not_mem_nil), ?_⟩
    intro fs hfs v hv
    cases fs with
    | nil => exact absurd hv List.not_mem_nil
    | cons _ _ => exact hfs.elim
  | k + 1, hk => by
    have hn := S.u₀_ne_zero ls hz
    obtain ⟨ih, ihv⟩ := fitsSet_mem_univ hz hb hco hW hc k (by omega)
    have hi : c.fields.length - (k + 1) < c.fields.length := by omega
    have hd := List.drop_eq_getElem_cons hi
    rw [show c.fields.length - (k + 1) + 1 = c.fields.length - k by omega] at hd
    have hf : c.fields[c.fields.length - 1 - k]? = some c.fields[c.fields.length - (k + 1)] := by
      rw [show c.fields.length - 1 - k = c.fields.length - (k + 1) by omega]
      exact List.getElem?_eq_getElem hi
    rw [hd]
    have hval : ∀ fs, S.FitsFields M ls W ps (c.fields[c.fields.length - (k + 1)] ::
        c.fields.drop (c.fields.length - k)) fs → ∀ v ∈ fs, v ∈ˢ (univ (S.u₀ ls) : V) := by
      intro fs hfs v hv
      cases fs with
      | nil => exact absurd hv List.not_mem_nil
      | cons v' fs =>
        rcases List.mem_cons.mp hv with rfl | hv
        · exact univ_trans hn (S.fieldSet_mem_univ M ls hz hb hco hW hc hf (by omega) hfs.1) hfs.2
        · exact ihv fs hfs.1 v hv
    refine ⟨?_, hval⟩
    simp only [fitsSet]
    refine famUnion_mem_univ hn ih fun t ht => ?_
    obtain ⟨fs, hfs, rfl⟩ := (S.mem_fitsSet M ls).mp ht
    rw [untuple_tuple]
    refine famUnion_mem_univ hn (S.fieldSet_mem_univ M ls hz hb hco hW hc hf (by omega) hfs) fun v hv => ?_
    exact sing_mem_univ hn (tuple_mem_univ hn fun w hw => hval (v :: fs) ⟨hfs, hv⟩ w hw)

/-- A constructor by number. -/
theorem getD_mem {j : Nat} (hj : j < S.n) : S.ctors.getD j ⟨"", [], []⟩ ∈ S.ctors := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem _

/-- **The operator maps families in the universe to families in the
universe**: at a proposition its fibres are truth values; above one
they are sets of tagged tuples of members, built by replacement and
union from sets of the universe (the class's membership in the
universe from the container's clause).  Con-leche: `LfpClause.functor`'s
second conjunct, from `fieldsOk`. -/
theorem famOp_maps {ps : List V} (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps) :
    MapsFam (S.u₀ ls) (S.famOp M ls ps) := by
  intro W hW is
  cases hz : S.z ls with
  | true =>
    rw [(S.z_iff ls).mp hz]
    refine mem_univ_zero.mpr fun x hx => ?_
    obtain ⟨j, c, fs, -, -, -, rfl⟩ := (S.mem_famOp M ls).mp hx
    simp [ctorVal, hz]
  | false =>
    have hn := S.u₀_ne_zero ls hz
    unfold famOp
    refine listUnion_mem_univ hn fun A hA => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
    have hc := S.getD_mem (List.mem_range.mp hj)
    obtain ⟨hset, hval⟩ := S.fitsSet_mem_univ M ls hz hb hco hW hc _ (Nat.le_refl _)
    rw [Nat.sub_self, List.drop_zero] at hset hval
    unfold ctorFibre
    refine image_mem_univ hn (sep_mem_univ hset) fun t ht => ?_
    obtain ⟨fs, hfs, rfl⟩ := (S.mem_fitsSet M ls).mp (mem_sep.mp ht).1
    rw [untuple_tuple]
    simp only [ctorVal, hz, Bool.false_eq_true, if_false]
    exact tag_mem_univ hn (tuple_mem_univ hn fun v hv => hval fs hfs v (List.mem_reverse.mp hv))

/-! ## The one-fibre family: reading the fields off the family

No field reads an earlier recursive or container field (`NoRecDep`),
so the ordinary domains and the telescopes met along an instance of
any family are those met along an instance of the **one-fibre
family** (every fibre `{pt}`, a member of every universe) at the same
ordinary values — the recursive values replaced by that family's
canonical member of the field's set, the point abstracted over the
telescope, and the container values by a member of the class at the
one-fibre set, which the container's clause supplies
(`ContClause.inhab_one`; `toOne`).  That is how the support bound is
ONE set, independent of the family.  Con-leche: the frame walk at
arbitrary recursive slots (`structUsedLater`, `Positivity.lean`;
`InvOn`, `HoleAcc.lean`). -/

/-- The one-fibre family. -/
def oneFam : List V → V := fun _ => one

theorem oneFam_inUniv (n : Nat) : InUniv n (oneFam : List V → V) := fun _ => one_mem_univ n

/-- A container value's stand-in at the one-fibre family: a member of
the class at the one-fibre set, if any. -/
noncomputable def contOne (ps : List V) : V :=
  match S.nest with
  | some N => pickMem (S.classSet M ls N ps one)
  | none => pt

/-- An instance's values with every recursive value replaced by the
one-fibre family's canonical member of its field's set, and every
container value by its stand-in. -/
noncomputable def toOne (ps : List V) : List Field → List V → List V
  | f :: fields, v :: vs =>
    (match f with
      | .reflexive tele _ =>
        lamCtx M (S.ψ ls) (S.z ls) (consList (toOne ps fields vs) (envP ps)) tele fun _ => pt
      | .container => S.contOne M ls ps
      | _ => v) :: toOne ps fields vs
  | _, vs => vs

/-- The replaced values agree with the values at every non-recursive
position. -/
theorem consList_toOne_eq (ps : List V) (ρ : Nat → V) :
    ∀ (fields : List Field) (fs : List V) (i : Nat),
      (∀ f, fields[i]? = some f → f.isRec = false) →
      consList (S.toOne M ls ps fields fs) ρ i = consList fs ρ i
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | f :: _, _ :: _, 0, h => by
    have := h f rfl
    cases f with
    | ordinary _ => rfl
    | reflexive _ _ => simp [Field.isRec] at this
    | container => simp [Field.isRec] at this
  | _ :: fields, _ :: fs, i + 1, h => by
    simp only [toOne, consList_cons, cons_succ]
    exact consList_toOne_eq ps ρ fields fs i fun f' hf' => h f' hf'

/-- An expression that reads no recursive earlier field reads alike
under the values and under the replaced values (`d` own binders on
top). -/
theorem interp_toOne (ps : List V) {fields : List Field} {fs ys : List V} {d : Nat} (ρ : Nat → V)
    (e : Expr) (hy : ys.length = d)
    (h : ∀ i f, fields[i]? = some f → f.isRec = true → e.usesVar (d + i) = false) :
    interp M (S.ψ ls) (consList ys (consList (S.toOne M ls ps fields fs) ρ)) e
      = interp M (S.ψ ls) (consList ys (consList fs ρ)) e := by
  apply interp_usesVar
  intro j hj
  by_cases hjd : j < d
  · rw [consList_lt (by omega), consList_lt (by omega)]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + d := ⟨j - d, by omega⟩
    rw [← hy, consList_ge, consList_ge]
    apply S.consList_toOne_eq
    intro f hf
    cases hr : f.isRec with
    | false => rfl
    | true =>
      exfalso
      have := h i f hf hr
      rw [Nat.add_comm] at hj
      simp [this] at hj

/-- No field of a list reads an earlier recursive field of the list:
`NoRecDep` restricted to a suffix of a constructor's fields. -/
def ListNoRecDep (L : List Field) : Prop :=
  ∀ i f, L[i]? = some f → fieldNoRecDep (L.drop (i + 1)) f

theorem ListNoRecDep.tail {f : Field} {L : List Field} (h : ListNoRecDep (f :: L)) : ListNoRecDep L :=
  fun i f' hf' => by
    have := h (i + 1) f' (by simpa using hf')
    simpa using this

theorem ListNoRecDep.head {f : Field} {L : List Field} (h : ListNoRecDep (f :: L)) :
    fieldNoRecDep L f := by
  have := h 0 f rfl
  simpa using this

/-- A suffix of a constructor's fields, in a block without such
dependencies. -/
theorem noRecDep_drop (hnr : S.NoRecDep) {c : CtorSpec} (hc : c ∈ S.ctors) (m : Nat) :
    ListNoRecDep (c.fields.drop m) := by
  intro i f hf
  rw [List.getElem?_drop] at hf
  have := hnr c hc (m + i) f hf
  rw [List.drop_drop]
  rwa [← Nat.add_assoc]

/-- **A fitting list fits the one-fibre family once its recursive
and container values are replaced.** -/
theorem FitsFields_toOne {ps : List V} (hco : S.ContOk M ls ps) {W : List V → V}
    (hW : InUniv (S.u₀ ls) W) :
    ∀ {L : List Field} {fs : List V}, ListNoRecDep L → S.FitsFields M ls W ps L fs →
      S.FitsFields M ls oneFam ps L (S.toOne M ls ps L fs)
  | [], [], _, _ => trivial
  | f :: L, v :: fs, hnr, hf => by
    refine ⟨FitsFields_toOne hco hW hnr.tail hf.1, ?_⟩
    have hhead := hnr.head
    cases f with
    | ordinary A =>
      show v ∈ˢ interp M (S.ψ ls) (consList (S.toOne M ls ps L fs) (envP ps)) A
      have := S.interp_toOne M ls ps (fs := fs) (ys := []) (d := 0) (envP ps) A rfl
        fun i f' hf' hr => by simpa using hhead i f' hf' hr
      simp only [consList_nil] at this
      rw [this]
      exact hf.2
    | reflexive tele es =>
      show lamCtx M (S.ψ ls) (S.z ls) _ tele (fun _ => pt) ∈ˢ piCtx M (S.ψ ls) (S.z ls) _ tele _
      exact lamCtx_mem_piCtx M _ (fun _ _ => mem_one.mpr rfl) fun _ _ _ => one_mem_univ_zero
    | container =>
      have hv := hf.2
      cases hN : S.nest with
      | none => rw [S.fieldSet_container_none M ls hN] at hv; exact absurd hv (not_mem_empty v)
      | some N =>
        rw [S.fieldSet_container M ls hN] at hv
        show S.contOne M ls ps ∈ˢ S.fieldSet M ls oneFam ps _ .container
        rw [S.fieldSet_container M ls hN]
        unfold contOne
        rw [hN]
        exact pickMem_mem ((hco N hN).inhab_one _ (hW _) ⟨v, hv⟩)
  | [], _ :: _, _, hf => hf.elim
  | _ :: _, [], _, hf => hf.elim

/-- A reflexive field's telescope has the same tuples at the values
and at the replaced values. -/
theorem ctxSet_toOne (ps : List V) {L : List Field} {tele es : List Expr} {fs : List V}
    (hnr : fieldNoRecDep L (.reflexive tele es)) :
    ctxSet M (S.ψ ls) (consList fs (envP ps)) tele
      = ctxSet M (S.ψ ls) (consList (S.toOne M ls ps L fs) (envP ps)) tele := by
  refine (ctxSet_congr M (S.ψ ls) fun t T hT ys hys => ?_).2
  have hl := FitsVals_length M _ hys
  have hd : ys.length = tele.length - 1 - t := by
    rw [hl, List.length_drop]; omega
  rw [S.interp_toOne M ls ps (envP ps) T hd fun i f hf hr => (hnr i f hf hr).1 t T hT]

/-! ## The support bound -/

/-- **A constructor's support bound**: for each reflexive field, the
tuples of its telescope at every list fitting the fields before it
relative to the one-fibre family, each coded by the field's position
(a numeral in a path step, `pcons`); for each container field, the
class's bound, coded likewise.  An ordinary field contributes
nothing; a recursive field, whose telescope is empty, contributes the
one tuple `tuple []` per prefix.  Con-leche: `piBound` glued along the
telescope (`HoleAcc.lean`), made uniform along the fields
(`TeleAcc.lean`); the container's bound `accPaths` of
`ContAccFrame.lean`. -/
noncomputable def ctorBound (ps : List V) (c : CtorSpec) : V :=
  listUnion ((List.range c.fields.length).map fun k =>
    match c.fields[c.fields.length - 1 - k]? with
    | some (.reflexive tele _) =>
      famUnion (S.fitsSet M ls oneFam ps (c.fields.drop (c.fields.length - k))) fun t =>
        image (pcons (nat k)) (ctxSet M (S.ψ ls) (consList (untuple t) (envP ps)) tele)
    | some .container => image (pcons (nat k)) S.classBound
    | _ => empty)

/-- **The bound**: the union of the constructors' support bounds.
Con-leche: the block's accessibility bound of `blockAcc_of_run`. -/
noncomputable def bound (ps : List V) : V :=
  listUnion ((List.range S.n).map fun j => S.ctorBound M ls ps (S.ctors.getD j ⟨"", [], []⟩))

/-- **The bound is a member of the result universe** (above a
proposition), by the universe bound on the fields at the one-fibre
family. -/
theorem bound_mem_univ {ps : List V} (hz : S.z ls = false) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) : S.bound M ls ps ∈ˢ (univ (S.u₀ ls) : V) := by
  have hn := S.u₀_ne_zero ls hz
  unfold bound
  refine listUnion_mem_univ hn fun A hA => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hA
  have hc := S.getD_mem (List.mem_range.mp hj)
  unfold ctorBound
  refine listUnion_mem_univ hn fun B hB => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hB
  have hk' := List.mem_range.mp hk
  split
  · rename_i tele es hf
    have hW := oneFam_inUniv (V := V) (S.u₀ ls)
    refine famUnion_mem_univ hn (S.fitsSet_mem_univ M ls hz hb hco hW hc k (by omega)).1 fun t ht => ?_
    obtain ⟨fs, hfs, rfl⟩ := (S.mem_fitsSet M ls).mp ht
    rw [untuple_tuple]
    have hdom := hb hz oneFam hW _ hc k _ hf hk' fs hfs
    have hset := (ctxSet_mem_univ M (S.ψ ls) hn hdom).1
    exact image_mem_univ hn hset fun y hy =>
      pcons_mem_univ hn (nat_mem_univ hn k) (univ_trans hn hset hy)
  · exact image_mem_univ hn (S.classBound_mem_univ hn) fun y hy =>
      pcons_mem_univ hn (nat_mem_univ hn k) (univ_trans hn (S.classBound_mem_univ hn) hy)
  · exact empty_mem_univ _

/-! ## Accessibility, by positivity

A constructor value's **support** in the input family: for each
reflexive field, the occurrences `(the field's index expressions at
`ys`, the field applied to `ys`)` for every argument list `ys` fitting
its telescope — a recursive field's being the one occurrence of its
value at its index expressions; for each container field, the
occurrences at the nested occurrence's index expressions of the
container value's own support in the fibre there, which the
container's clause supplies (`ContClause.acc`); an ordinary field has
none.  The support is coded by the field's position and the argument
tuple (resp. the container value's own code), so it is a subset of
the bound; and a constructor value with its support in a family `W'`
of the universe is a constructor instance over `W'`: its ordinary
fields are read without the family, each reflexive field's value, a
function whose applications lie in `W'`'s fibres, is a member of the
product into them (`piCtx_retype`), and each container field's value
is in the class at `W'`'s fibre by the container's clause.
Con-leche: `ConstOn.accOn` (an ordinary field), `AccOn.holeApp` (a
recursive field: the bound `{pt}`), `AccOn.pi` (a reflexive field:
the bound glued over the domain) in `HoleAcc.lean`, the container
instance's accessibility in `ContAcc.lean` (`accConcl_of_frameAccOut`),
assembled along the fields by `TeleAcc.lean` and into `AccTuple` by
`blockAcc_of_run`. -/

/-- The codes of an instance's support, given the container values'
own supports `Bk` (by position). -/
noncomputable def instSupp (ps : List V) (c : CtorSpec) (fs : List V) (Bk : Nat → V) : V :=
  listUnion ((List.range c.fields.length).map fun k =>
    match c.fields[c.fields.length - 1 - k]? with
    | some (.reflexive tele _) =>
      image (pcons (nat k)) (ctxSet M (S.ψ ls) (consList (earlier fs k) (envP ps)) tele)
    | some .container => image (pcons (nat k)) (Bk k)
    | _ => empty)

/-- The occurrence a code stands for: at a reflexive field, the field
at the code's position applied to the code's argument tuple, at the
field's index expressions there; at a container field, the container
value's own occurrence `gk` at the code, at the nested occurrence's
index expressions. -/
noncomputable def instOcc (ps : List V) (c : CtorSpec) (fs : List V) (gk : Nat → V → V) (b : V) :
    List V × V :=
  match c.fields[c.fields.length - 1 - idx (pfst b)]? with
  | some (.reflexive _ es) =>
    (S.idxVals M ls (consList (untuple (psnd b)) (consList (earlier fs (idx (pfst b))) (envP ps))) es,
      appList (fieldVal fs (idx (pfst b))) (untuple (psnd b)).reverse)
  | some .container =>
    match S.nest with
    | some N => (S.memberIdx M ls N ps, gk (idx (pfst b)) (psnd b))
    | none => ([], pt)
  | _ => ([], pt)

/-- The members of the support's codes. -/
theorem mem_instSupp' {ps : List V} {c : CtorSpec} {fs : List V} {Bk : Nat → V} {b : V} :
    b ∈ˢ S.instSupp M ls ps c fs Bk ↔
      (∃ k tele es ys, c.fields[c.fields.length - 1 - k]? = some (.reflexive tele es) ∧
        k < c.fields.length ∧
        FitsVals M (S.ψ ls) (consList (earlier fs k) (envP ps)) tele ys ∧
        b = pcons (nat k) (tuple ys)) ∨
      (∃ k b', c.fields[c.fields.length - 1 - k]? = some .container ∧ k < c.fields.length ∧
        b' ∈ˢ Bk k ∧ b = pcons (nat k) b') := by
  unfold instSupp
  rw [mem_listUnion]
  constructor
  · rintro ⟨A, hA, hb⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hA
    have hk' := List.mem_range.mp hk
    revert hb
    split
    · rename_i tele es hf
      intro hb
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hb
      obtain ⟨ys, hys, rfl⟩ := (mem_ctxSet M (S.ψ ls) _).mp ht
      exact Or.inl ⟨k, tele, es, ys, hf, hk', hys, rfl⟩
    · rename_i hf
      intro hb
      obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
      exact Or.inr ⟨k, b', hf, hk', hb', rfl⟩
    · intro hb; exact absurd hb (not_mem_empty _)
  · rintro (⟨k, tele, es, ys, hf, hk, hys, rfl⟩ | ⟨k, b', hf, hk, hb', rfl⟩)
    · refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ?_⟩
      simp only [hf]
      exact mem_image.mpr ⟨tuple ys, (mem_ctxSet M (S.ψ ls) _).mpr ⟨ys, hys, rfl⟩, rfl⟩
    · refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ?_⟩
      simp only [hf]
      exact mem_image.mpr ⟨b', hb', rfl⟩

/-- The occurrence at a reflexive field's code. -/
theorem instOcc_code {ps : List V} {c : CtorSpec} {fs : List V} {gk : Nat → V → V} {k : Nat}
    {tele es : List Expr}
    (hf : c.fields[c.fields.length - 1 - k]? = some (.reflexive tele es)) (ys : List V) :
    S.instOcc M ls ps c fs gk (pcons (nat k) (tuple ys)) =
      (S.idxVals M ls (consList ys (consList (earlier fs k) (envP ps))) es,
        appList (fieldVal fs k) ys.reverse) := by
  unfold instOcc
  simp only [pfst_pcons, psnd_pcons, idx_nat, untuple_tuple, hf]

/-- The occurrence at a container field's code. -/
theorem instOcc_code_cont {ps : List V} {c : CtorSpec} {fs : List V} {gk : Nat → V → V} {k : Nat}
    (hf : c.fields[c.fields.length - 1 - k]? = some .container) {N : NestInfo}
    (hN : S.nest = some N) (b' : V) :
    S.instOcc M ls ps c fs gk (pcons (nat k) b') = (S.memberIdx M ls N ps, gk k b') := by
  unfold instOcc
  simp only [pfst_pcons, psnd_pcons, idx_nat, hf, hN]

/-- **A fitting list fits every family holding its support** — the
re-typing of each reflexive field's value, and the container's clause
at each container value. -/
theorem FitsFields_retype {ps : List V} (hco : S.ContOk M ls ps) {W W' : List V → V}
    (hW' : InUniv (S.u₀ ls) W') :
    ∀ {fields : List Field} {fs : List V}, S.FitsFields M ls W ps fields fs →
      (∀ k tele es, fields[fields.length - 1 - k]? = some (.reflexive tele es) → k < fields.length →
        ∀ ys, FitsVals M (S.ψ ls) (consList (earlier fs k) (envP ps)) tele ys →
          appList (fieldVal fs k) ys.reverse ∈ˢ
            W' (S.idxVals M ls (consList ys (consList (earlier fs k) (envP ps))) es)) →
      (∀ k, fields[fields.length - 1 - k]? = some .container → k < fields.length →
        ∀ N, S.nest = some N →
          fieldVal fs k ∈ˢ S.classSet M ls N ps (W' (S.memberIdx M ls N ps))) →
      S.FitsFields M ls W' ps fields fs
  | [], [], _, _, _ => trivial
  | f :: fields, v :: fs, hf, h, h' => by
    have hlen := S.FitsFields_length M ls hf.1
    refine ⟨FitsFields_retype hco hW' hf.1 (fun k tele es hk hkl ys hys => ?_)
      (fun k hk hkl N hN => ?_), ?_⟩
    · have := h k tele es (by
          rw [show (f :: fields).length - 1 - k = (fields.length - 1 - k) + 1 by simp; omega]
          simpa using hk) (by simp; omega) ys (by rwa [earlier_cons (by omega)])
      rwa [fieldVal_cons (by omega), earlier_cons (by omega)] at this
    · have := h' k (by
          rw [show (f :: fields).length - 1 - k = (fields.length - 1 - k) + 1 by simp; omega]
          simpa using hk) (by simp; omega) N hN
      rwa [fieldVal_cons (by omega)] at this
    · cases f with
      | ordinary _ => exact hf.2
      | container =>
        cases hN : S.nest with
        | none =>
          have hv := hf.2
          rw [S.fieldSet_container_none M ls hN] at hv
          exact absurd hv (not_mem_empty v)
        | some N =>
          have hk := h' fields.length (by simp) (by simp) N hN
          have hfv : fieldVal (v :: fs) fields.length = v := by
            simp [fieldVal, hlen]
          rw [hfv] at hk
          rw [S.fieldSet_container M ls hN]
          exact hk
      | reflexive tele es =>
        have hk := h fields.length tele es (by simp) (by simp)
        have hfv : fieldVal (v :: fs) fields.length = v := by
          simp [fieldVal, hlen]
        have hea : earlier (v :: fs) fields.length = fs := by
          simp only [earlier, List.length_cons, hlen]
          rw [show fields.length + 1 - fields.length = 1 by omega]; rfl
        rw [hfv, hea] at hk
        simp only [fieldSet] at hf ⊢
        exact piCtx_retype M _ hf.2 hk fun hz _ _ => S.fibre_mem_univ_zero ls hW' hz _
  | [], _ :: _, hf, _, _ => hf.elim
  | _ :: _, [], hf, _, _ => hf.elim

omit [IndLib V] in
/-- Supports chosen for every position (skolemisation over the
field positions). -/
theorem skolem_pos {Q : Nat → V → (V → V) → Prop} (h : ∀ k, ∃ B g, Q k B g) :
    ∃ (Bk : Nat → V) (gk : Nat → V → V), ∀ k, Q k (Bk k) (gk k) :=
  ⟨fun k => Classical.choose (h k), fun k => Classical.choose (Classical.choose_spec (h k)),
    fun k => Classical.choose_spec (Classical.choose_spec (h k))⟩

/-- **The operator is accessible with the bound** — by positivity:
every constructor value's support is coded inside the bound, lies in
the input family, and carries the value to every family of the
universe holding it; at a container field by the container's clause.
Con-leche: `blockAcc_of_run`, the `AccTuple` `closed_of_acc`
consumes. -/
theorem famOp_acc {ps : List V} (hnr : S.NoRecDep) (hco : S.ContOk M ls ps) :
    AccFam (S.u₀ ls) (S.famOp M ls ps) (S.bound M ls ps) := by
  intro W hW is x hx
  obtain ⟨j, c, fs, hc, hfs, his, rfl⟩ := (S.mem_famOp M ls).mp hx
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hj : j < S.n := (List.getElem?_eq_some_iff.mp hc).1
  have hcd : S.ctors.getD j ⟨"", [], []⟩ = c := by rw [List.getD_eq_getElem?_getD, hc]; rfl
  -- the container values' own supports, one per container position
  obtain ⟨Bk, gk, hk⟩ := skolem_pos (Q := fun k B g =>
    ∀ N, S.nest = some N → c.fields[c.fields.length - 1 - k]? = some .container →
      k < c.fields.length →
      B ⊆ˢ S.classBound ∧ (∀ b, b ∈ˢ B → g b ∈ˢ W (S.memberIdx M ls N ps)) ∧
        ∀ X', X' ∈ˢ (univ (S.u₀ ls) : V) → (∀ b, b ∈ˢ B → g b ∈ˢ X') →
          fieldVal fs k ∈ˢ S.classSet M ls N ps X')
    (by
      intro k
      classical
      by_cases hcase : ∃ N, S.nest = some N ∧ c.fields[c.fields.length - 1 - k]? = some .container ∧
        k < c.fields.length
      · obtain ⟨N, hN, hf, hkl⟩ := hcase
        have hget := S.FitsFields_get M ls hfs hf hkl
        rw [S.fieldSet_container M ls hN] at hget
        obtain ⟨B, g, hB, hg, hs⟩ := (hco N hN).acc _ (hW _) _ hget
        refine ⟨B, g, fun N' hN' _ _ => ?_⟩
        rw [hN] at hN'
        cases hN'
        exact ⟨hB, hg, hs⟩
      · exact ⟨empty, fun _ => pt, fun N hN hf hkl => absurd ⟨N, hN, hf, hkl⟩ hcase⟩)
  refine ⟨S.instSupp M ls ps c fs Bk, S.instOcc M ls ps c fs gk, ?_, ?_, ?_⟩
  · -- the codes lie in the bound: the prefix transferred to the one-fibre family
    intro b hb
    rcases (S.mem_instSupp' M ls).mp hb with ⟨k, tele, es, ys, hf, hk', hys, rfl⟩ |
      ⟨k, b', hf, hk', hb', rfl⟩
    · unfold bound
      refine mem_listUnion.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
      rw [hcd]
      unfold ctorBound
      refine mem_listUnion.mpr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩, ?_⟩
      simp only [hf]
      have hnrL := S.noRecDep_drop hnr hcm (c.fields.length - k)
      have hpre := S.FitsFields_earlier M ls hfs k (Nat.le_of_lt hk')
      refine mem_famUnion.mpr ⟨tuple (S.toOne M ls ps _ (earlier fs k)),
        (S.mem_fitsSet M ls).mpr ⟨_, S.FitsFields_toOne M ls hco hW hnrL hpre, rfl⟩, ?_⟩
      rw [untuple_tuple]
      have hnrf : fieldNoRecDep (c.fields.drop (c.fields.length - k)) (.reflexive tele es) := by
        have := hnr c hcm _ _ hf
        rwa [show c.fields.length - 1 - k + 1 = c.fields.length - k by omega] at this
      rw [← S.ctxSet_toOne M ls ps hnrf]
      exact mem_image.mpr ⟨tuple ys, (mem_ctxSet M (S.ψ ls) _).mpr ⟨ys, hys, rfl⟩, rfl⟩
    · obtain ⟨N, hN⟩ : ∃ N, S.nest = some N := by
        cases hN : S.nest with
        | none =>
          have hget := S.FitsFields_get M ls hfs hf hk'
          rw [S.fieldSet_container_none M ls hN] at hget
          exact absurd hget (not_mem_empty _)
        | some N => exact ⟨N, rfl⟩
      unfold bound
      refine mem_listUnion.mpr ⟨_, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_⟩
      rw [hcd]
      unfold ctorBound
      refine mem_listUnion.mpr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr hk', rfl⟩, ?_⟩
      simp only [hf]
      exact mem_image.mpr ⟨b', (hk k N hN hf hk').1 b' hb', rfl⟩
  · -- the support lies in the input family
    intro b hb
    rcases (S.mem_instSupp' M ls).mp hb with ⟨k, tele, es, ys, hf, hk', hys, rfl⟩ |
      ⟨k, b', hf, hk', hb', rfl⟩
    · unfold InFam
      rw [S.instOcc_code M ls hf]
      have hget := S.FitsFields_get M ls hfs hf hk'
      simp only [fieldSet] at hget
      exact appList_mem_of_piCtx M _ hget hys
    · obtain ⟨N, hN⟩ : ∃ N, S.nest = some N := by
        cases hN : S.nest with
        | none =>
          have hget := S.FitsFields_get M ls hfs hf hk'
          rw [S.fieldSet_container_none M ls hN] at hget
          exact absurd hget (not_mem_empty _)
        | some N => exact ⟨N, rfl⟩
      unfold InFam
      rw [S.instOcc_code_cont M ls hf hN]
      exact (hk k N hN hf hk').2.1 b' hb'
  · -- a family holding the support holds the value
    intro W' hW' hsupp
    refine (S.mem_famOp M ls).mpr ⟨j, c, fs, hc, ?_, his, rfl⟩
    refine S.FitsFields_retype M ls hco hW' hfs (fun k tele es hf hk' ys hys => ?_)
      (fun k hf hk' N hN => ?_)
    · have := hsupp _ ((S.mem_instSupp' M ls).mpr (Or.inl ⟨k, tele, es, ys, hf, hk', hys, rfl⟩))
      unfold InFam at this
      rwa [S.instOcc_code M ls hf] at this
    · refine (hk k N hN hf hk').2.2 _ (hW' _) fun b' hb' => ?_
      have := hsupp _ ((S.mem_instSupp' M ls).mpr (Or.inr ⟨k, b', hf, hk', hb', rfl⟩))
      unfold InFam at this
      rwa [S.instOcc_code_cont M ls hf hN] at this

/-! ## The family -/

/-- **A closed family in the universe**: at a proposition the family
of truth values `{pt}` (`closedFam_zero`); above one, from
accessibility (`closed_of_acc`).  Con-leche: `LfpClause.functor`'s
third conjunct, `closedTuple_zero` and `closed_of_acc`. -/
theorem closedFam {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) : ∃ L, IsClosedFam (S.u₀ ls) (S.famOp M ls ps) L := by
  cases hz : S.z ls with
  | true =>
    have hm := S.famOp_maps M ls hb hco
    rw [(S.z_iff ls).mp hz] at hm ⊢
    exact closedFam_zero hm
  | false =>
    exact closed_of_acc (S.u₀_ne_zero ls hz) (S.bound_mem_univ M ls hz hb hco)
      (S.famOp_maps M ls hb hco) (S.famOp_acc M ls hnr hco)

/-- **The family**: the fibre at the index values `is` is the least
fixed point of the block's operator inside the set theory.
Con-leche: `LfpDatum.carrier`, `lfpTuple` of the hole operator. -/
noncomputable def Fam (ps is : List V) : V := lfpFamSet (S.u₀ ls) (S.famOp M ls ps) is

/-- **The fibre is a member of the result universe** — unconditionally,
by the definition of the least fixed point inside the set theory.
Con-leche: `lfpTuple_mem`. -/
theorem Fam_mem_univ (ps is : List V) : S.Fam M ls ps is ∈ˢ (univ (S.u₀ ls) : V) :=
  lfpFamSet_mem _ _ is

theorem Fam_inUniv (ps : List V) : InUniv (S.u₀ ls) (S.Fam M ls ps) := lfpFamSet_mem _ _

/-- **The fixed-point equation**: the operator at the family is the
family.  Con-leche: `LfpClause.carrier_eq`. -/
theorem famOp_Fam {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) (is : List V) :
    S.famOp M ls ps (S.Fam M ls ps) is = S.Fam M ls ps is :=
  lfpFamSet_eq (S.closedFam M ls hnr hb hco) (S.famOp_mono M ls hco) (S.famOp_maps M ls hb hco) is

/-- **The family's case analysis**: a member of the fibre at `is` is
a constructor instance over the family at `is`, and conversely.
Con-leche: `LfpClause.carrier_case`. -/
theorem mem_Fam {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) {is : List V} {t : V} :
    t ∈ˢ S.Fam M ls ps is ↔ S.Inst M ls (S.Fam M ls ps) ps is t := by
  rw [← S.famOp_Fam M ls hnr hb hco]
  exact S.mem_famOp M ls

/-- **A constructor's value is in the fibre** at its index expressions
when its fields fit the family.  Con-leche: `LfpClause.ctor` with the
carrier's closure. -/
theorem ctorVal_mem_Fam {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) {j : Nat}
    {c : CtorSpec} (hc : S.ctors[j]? = some c) {fs : List V}
    (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs) :
    S.ctorVal ls j fs ∈ˢ S.Fam M ls ps (S.idxVals M ls (consList fs (envP ps)) c.idx) :=
  (S.mem_Fam M ls hnr hb hco).mpr ⟨j, c, fs, hc, hfit, rfl, rfl⟩

/-- **Induction over the family**: a property that holds of every
constructor instance over the family's separation by it holds on the
family.  Con-leche: `lfpTuple_induction`, the block's induction the
recursor's graph is built with. -/
theorem Fam_induction {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) (P : List V → V → Prop)
    (h : ∀ is x, S.Inst M ls (fun is' => sep (S.Fam M ls ps is') (P is')) ps is x → P is x) :
    ∀ is x, x ∈ˢ S.Fam M ls ps is → P is x :=
  lfpFamSet_induction (S.closedFam M ls hnr hb hco) (S.famOp_mono M ls hco) P fun is x hx =>
    h is x ((S.mem_famOp M ls).mp hx)

/-- The family's separation by a property is in the universe. -/
theorem sepFam_inUniv (ps : List V) (P : List V → V → Prop) :
    InUniv (S.u₀ ls) fun is' => sep (S.Fam M ls ps is') (P is') :=
  fun is => sep_mem_univ (S.Fam_mem_univ M ls ps is)

/-- A fitting list at the family's separation fits the family. -/
theorem FitsFields_of_sep {ps : List V} (hco : S.ContOk M ls ps) (P : List V → V → Prop)
    {fields : List Field} {fs : List V}
    (hfit : S.FitsFields M ls (fun is' => sep (S.Fam M ls ps is') (P is')) ps fields fs) :
    S.FitsFields M ls (S.Fam M ls ps) ps fields fs :=
  S.FitsFields_mono M ls hco (S.sepFam_inUniv M ls ps P) (S.Fam_inUniv M ls ps) (fun _ => sep_sub)
    hfit

/-! ### The two regimes, and the decoding of a member

Above a proposition a member of the fibre is the tagged tuple of its
fields, which decode it uniquely (tags and tuples are injective); at
a proposition it is the point, and a fibre is `{pt}` exactly when some
instance exists.  The recursor (`IndRec.lean`) reads a member through
its decodings (`Mem`), one at a type, any at a proposition — where the
subsingleton criterion makes them agree (`Uniq`, `Uniq.lean`). -/

/-- **A decoding** of a member: a tagged tuple of fields fitting a
constructor at the family, with its index expressions reading as
`is` — what a member of a type-valued fibre is, and what the point of
a propositional fibre stands for.  Con-leche: `Dec`, the major's
decoding as a datum (`GraphRecKit`, `ConLeche/SetModel/GraphRec.lean`). -/
def Mem (ps is : List V) (x : V) : Prop :=
  ∃ j c fs, S.ctors[j]? = some c ∧ S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs ∧
    is = S.idxVals M ls (consList fs (envP ps)) c.idx ∧ x = tag (S.tagOf j) (tuple fs.reverse)

/-- At a proposition a member of the fibre is the point and some
decoding exists. -/
theorem mem_Fam_true {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) (hz : S.z ls = true) {is : List V} {t : V} :
    t ∈ˢ S.Fam M ls ps is ↔ t = pt ∧ ∃ x, S.Mem M ls ps is x := by
  rw [S.mem_Fam M ls hnr hb hco]
  unfold Inst Mem ctorVal
  simp only [hz, if_true]
  constructor
  · rintro ⟨j, c, fs, hc, hfit, his, rfl⟩
    exact ⟨rfl, _, j, c, fs, hc, hfit, his, rfl⟩
  · rintro ⟨rfl, -, j, c, fs, hc, hfit, his, -⟩
    exact ⟨j, c, fs, hc, hfit, his, rfl⟩

/-- Above a proposition a member of the fibre is its own decoding. -/
theorem mem_Fam_false {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps) (hz : S.z ls = false) {is : List V} {t : V} :
    t ∈ˢ S.Fam M ls ps is ↔ S.Mem M ls ps is t := by
  rw [S.mem_Fam M ls hnr hb hco]
  unfold Inst Mem ctorVal
  simp only [hz, Bool.false_eq_true, if_false]

/-! ## The sets of the former and the constructors

The former and the constructors as sets: graphs over the generated
contexts (`Decl.lean`), read in the model as it grows — the
constructors' contexts mention the former. -/

/-- **A former's set over any family** `F` (levels, parameters, index
values to sets): the graph over the index and parameter contexts
whose value is `F`'s fibre.  The block's former is the graph of its
family (`famSet`); a reader of the block (`Read.lean`) may assign the
former the graph of any family in the universe, which is how the
universe bound on the fields is read off the checker's sort facts at
every family (`InstallInd.lean`). -/
noncomputable def famSetF (F : List Nat → List V → List V → V) : V :=
  lamCtx M (S.ψ ls) false base (S.indices ++ S.params) fun ρ' =>
    F ls (readEnv S.nP (shiftE S.nI 0 ρ')) (readEnv S.nI ρ')

/-- **The type former's set** at `ls`: the graph over the index and
parameter contexts whose value is the fibre. -/
noncomputable def famSet : V := S.famSetF M ls (S.Fam M)

theorem famSet_eq_famSetF : S.famSet M ls = S.famSetF M ls (S.Fam M) := rfl

/-- The model with the former assigned the graph of a family `F`. -/
noncomputable def M₁F (F : List Nat → List V → List V → V) : Name → List Nat → V :=
  fun n ls' => if n = S.name then S.famSetF M ls' F else M n ls'

/-- The model with the type former added. -/
noncomputable def M₁ : Name → List Nat → V := S.M₁F M (S.Fam M)

theorem M₁_eq_M₁F : S.M₁ M = S.M₁F M (S.Fam M) := rfl

/-- **A constructor's set**: the abstraction over the parameters and
fields (read in the model with the former) of the constructor's
value. -/
noncomputable def ctorSet (j : Nat) (c : CtorSpec) : V :=
  lamCtx (S.M₁ M) (S.ψ ls) (S.z ls) base (S.fieldCtx c.fields ++ S.params) fun ρ' =>
    S.ctorVal ls j (readEnv c.fields.length ρ')

/-- The model with the former and the constructors added. -/
noncomputable def M₂ : Name → List Nat → V :=
  fun n ls' =>
    match S.ctorOf? n with
    | some (j, c) => S.ctorSet M ls' j c
    | none => S.M₁ M n ls'

end IndSpec

end Fragment
