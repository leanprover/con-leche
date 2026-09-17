module

public import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.ExceptBind

public section

/-!
# The provenance of a copy's constructors (task #315 L-B)

Where a MINTED type's stored constructors come from.  The elimination
(`ConLeche/Kernel/Inductives/NestedElim.lean`) appends a copy with
`mkCopy`'s constructors and later — when the worklist reaches it —
replaces each of them by `elimCtors`' rewrite of `mkCopy`'s.  This file
reads that history off a successful `elimNested`: every type behind the
block's own members is a copy of a container member at a pin, and every
constructor it carries is `closeTelescope` of a `replaceAllNested` of
`mkCopy`'s constructor, at states whose pins and type names are
sandwiched in the elimination's.

The architecture is `NestedElimInv.lean`'s and `NestedRestoreTbl.lean`'s:
an invariant on states (`CopyInv`), preserved by each function of the
elimination, established at the end.
-/

namespace ConLeche

/-! ## Closing the branches the run cannot have taken -/

/-- An `.error` never succeeds. -/
private theorem cpErr_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (Except.error e : CheckM α) = .ok a) : False := by
  simp at h

/-- A declining step never returns a replacement. -/
private theorem cpNone_ne_some {α : Type} {a : α}
    (h : (pure none : CheckM (Option α)) = .ok (some a)) : False := by
  simp [pure, Except.pure] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact cpErr_ne_ok (by assumption))
        | (exfalso; exact cpNone_ne_some (by assumption)))

/-! ## List odds and ends -/

/-- An index into a list is an index into any extension of it. -/
private theorem cpGetElem?_append {α : Type} {l l' : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : (l ++ l')[i]? = some a := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

/-- Positions at or after the length of the first summand are the
second's — here, the single appended element. -/
private theorem cpGetElem?_append_one {α : Type} {l : List α} {i : Nat} {a t : α}
    (hi : l.length ≤ i) (h : (l ++ [a])[i]? = some t) : i = l.length ∧ t = a := by
  rw [List.getElem?_append_right hi] at h
  have hi0 : i - l.length = 0 := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simp only [List.length_cons, List.length_nil] at this
    omega
  rw [hi0] at h
  simp only [List.getElem?_cons_zero, Option.some.injEq] at h
  exact ⟨by omega, h.symm⟩

/-- A list that carries every entry of another at the same position is
at least as long. -/
private theorem cpLen_of_keep {α : Type} {l l' : List α}
    (h : ∀ (i : Nat) (t : α), l[i]? = some t → l'[i]? = some t) :
    l.length ≤ l'.length := by
  rcases Nat.lt_or_ge l'.length l.length with hlt | hge
  · exfalso
    obtain ⟨t, ht⟩ : ∃ t, l[l'.length]? = some t :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have := h _ t ht
    rw [List.getElem?_eq_none (Nat.le_refl _)] at this
    simp at this
  · exact hge

/-- Rewriting one entry's constructors leaves the name list alone. -/
private theorem cpMap_name_set {l : List AuxType} {i : Nat} {t : AuxType}
    {cs : List (Name × Expr × Nat)} (h : l[i]? = some t) :
    (l.set i { t with ctors := cs }).map (·.name) = l.map (·.name) := by
  refine List.ext_getElem? (fun j => ?_)
  by_cases hij : i = j
  · subst hij
    have hlt : i < l.length := (List.getElem?_eq_some_iff.mp h).1
    simp only [List.getElem?_map, List.getElem?_set_self hlt, h, Option.map_some]
  · simp only [List.getElem?_map, List.getElem?_set_ne hij]

/-! ## The copy record, as an invariant

Three predicates carry the history.  `CopyHead` is what the MINT wrote:
the container and the member, the source record, and `mkCopy`'s output
`c` — the type is that output's and the constructor count is too, but
the constructors THEMSELVES are rewritten later, so only their number
survives here.  `CtorsDone` is what the worklist wrote: each stored
constructor is `mkCopy`'s at the same position, opened at the block's
parameters, replaced, and closed again.  `CopyStep` is what a function
of the elimination does to a state: it appends, and everything it
appends is a mint.
-/

/-- **The mint's record at one type**: the type at this position is the
copy of the container member `J` of `I`'s group at the pin `J Ds`, with
`c` the `mkCopy` output the mint appended.  The occurrence test's two
verdicts are carried along: some `D` mentions a type of the growing
list (`names`), and no `D` has a loose bound variable. -/
private def CopyHead (env : Env) (pbs₀ : List (Expr × BinderMeta)) (names : List Name)
    (t c : AuxType) : Prop :=
  ∃ (I : Name) (ci : ContainerInfo) (m : Nat) (J : ContainerMember) (lvls : List Level)
    (Ds : List Expr),
    containerInfo? env I = some ci ∧ ci.members[m]? = some J ∧
    t.src = some (J.name, lvls, Ds) ∧ mkCopy pbs₀ lvls Ds t.name J = .ok c ∧
    t.type = c.type ∧ t.ctors.length = c.ctors.length ∧
    (Ds.any fun a => names.any fun T => a.mentionsConst T) = true ∧
    (∀ a ∈ Ds, a.looseBVarsBounded 0 = true)

/-- **The worklist's record at one type**: every stored constructor is
the `mkCopy` constructor at the same position, its parameter prefix
opened at the block's parameters, its residual replaced at states whose
pins and type names sit inside `stF`'s.

The last clause is the one the copies' reading needs (task #315 L-B):
the occurrence test's mint verdict holds already **at the state the
constructor's own rewrite starts from** — the copy was minted before
the worklist reached it, so its components mention a type of the
growing list already there, and `replaceAllNested_occurrence` may be
applied to the run this record hands over.  It is keyed on `t.src`,
which no step of the worklist changes, so no two mint records have to
be matched up. -/
private def CtorsDone (env : Env) (blvls : List Level) (nP : Nat) (params : List Expr)
    (pbs₀ : List (Expr × BinderMeta)) (stF : ElimState) (t c : AuxType) : Prop :=
  ∀ (j : Nat) (cj : Name × Expr × Nat), t.ctors[j]? = some cj →
    ∃ (c₀ : Name × Expr × Nat) (pbs : List (Expr × BinderMeta)) (rest cbody cbody' : Expr)
      (st₁ st₂ : ElimState),
      c.ctors[j]? = some c₀ ∧ c₀.2.1.stripPis nP = some (pbs, rest) ∧
      Expr.instPis c₀.2.1 params = some cbody ∧
      replaceAllNested env blvls params pbs₀ st₁ cbody = .ok (cbody', st₂) ∧
      cj = (c₀.1, closeTelescope pbs 0 cbody', c₀.2.2) ∧
      st₁.pins <+: st₂.pins ∧ st₂.pins <+: stF.pins ∧
      st₁.types.map (·.name) <+: stF.types.map (·.name) ∧
      ∀ (Jn : Name) (lvls : List Level) (Ds : List Expr), t.src = some (Jn, lvls, Ds) →
        (Ds.any fun a => st₁.newNames.any fun T => a.mentionsConst T) = true

/-- **What a step of the elimination does to the state**: the pins and
the type names only grow, every type stays where it was, and everything
appended is a mint whose constructors are still `mkCopy`'s. -/
private def CopyStep (env : Env) (pbs₀ : List (Expr × BinderMeta)) (st st' : ElimState) :
    Prop :=
  st.pins <+: st'.pins ∧
  st.types.map (·.name) <+: st'.types.map (·.name) ∧
  (∀ (i : Nat) (t : AuxType), st.types[i]? = some t → st'.types[i]? = some t) ∧
  (∀ (i : Nat) (t : AuxType), st.types.length ≤ i → st'.types[i]? = some t →
    ∃ c, CopyHead env pbs₀ st'.newNames t c ∧ t.ctors = c.ctors)

/-- The mint's record only needs MORE names: the occurrence test's
witness is still in the extension. -/
private theorem cpHead_mono {env : Env} {pbs₀ : List (Expr × BinderMeta)}
    {names names' : List Name} {t c : AuxType} (hn : names <+: names')
    (h : CopyHead env pbs₀ names t c) : CopyHead env pbs₀ names' t c := by
  obtain ⟨I, ci, m, J, lvls, Ds, hci, hJ, hsrc, hmk, hty, hlen, hany, hloose⟩ := h
  refine ⟨I, ci, m, J, lvls, Ds, hci, hJ, hsrc, hmk, hty, hlen, ?_, hloose⟩
  obtain ⟨a, ha, hT⟩ := List.any_eq_true.mp hany
  obtain ⟨T, hTm, hTc⟩ := List.any_eq_true.mp hT
  exact List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨T, hn.subset hTm, hTc⟩⟩

/-- The worklist's record travels to any later state. -/
private theorem cpDone_mono {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {stF stF' : ElimState} {t c : AuxType}
    (hp : stF.pins <+: stF'.pins)
    (hn : stF.types.map (·.name) <+: stF'.types.map (·.name))
    (h : CtorsDone env blvls nP params pbs₀ stF t c) :
    CtorsDone env blvls nP params pbs₀ stF' t c := by
  intro j cj hj
  obtain ⟨c₀, pbs, rest, cbody, cbody', st₁, st₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
    h j cj hj
  exact ⟨c₀, pbs, rest, cbody, cbody', st₁, st₂, h₁, h₂, h₃, h₄, h₅, h₆,
    h₇.trans hp, h₈.trans hn, h₉⟩

/-- A state is a step of itself. -/
private theorem cpStep_refl {env : Env} {pbs₀ : List (Expr × BinderMeta)} (st : ElimState) :
    CopyStep env pbs₀ st st := by
  refine ⟨List.prefix_refl _, List.prefix_refl _, fun _ _ h => h, ?_⟩
  intro i t hi hti
  rw [List.getElem?_eq_none hi] at hti
  simp at hti

/-- Steps compose: a type appended by the first is still a mint after
the second, since the second keeps it and only grows the names. -/
private theorem cpStep_trans {env : Env} {pbs₀ : List (Expr × BinderMeta)}
    {st stM st' : ElimState} (h₁ : CopyStep env pbs₀ st stM)
    (h₂ : CopyStep env pbs₀ stM st') : CopyStep env pbs₀ st st' := by
  obtain ⟨hp₁, hn₁, hk₁, hnew₁⟩ := h₁
  obtain ⟨hp₂, hn₂, hk₂, hnew₂⟩ := h₂
  refine ⟨hp₁.trans hp₂, hn₁.trans hn₂, fun i t hi => hk₂ i t (hk₁ i t hi), ?_⟩
  intro i t hi hti
  rcases Nat.lt_or_ge i stM.types.length with hlt | hge
  · obtain ⟨t', ht'⟩ : ∃ t', stM.types[i]? = some t' := ⟨_, List.getElem?_eq_getElem hlt⟩
    have het : t' = t := Option.some.inj ((hk₂ i t' ht').symm.trans hti)
    subst het
    obtain ⟨c, hc, hcc⟩ := hnew₁ i _ hi ht'
    exact ⟨c, cpHead_mono hn₂ hc, hcc⟩
  · exact hnew₂ i t hge hti

/-! ## The occurrence test, inverted -/

/-- The occurrence witness survives a longer name list. -/
private theorem cpAny_mono {Ds : List Expr} {names names' : List Name}
    (hn : names <+: names')
    (h : (Ds.any fun a => names.any fun T => a.mentionsConst T) = true) :
    (Ds.any fun a => names'.any fun T => a.mentionsConst T) = true := by
  obtain ⟨a, ha, hT⟩ := List.any_eq_true.mp h
  obtain ⟨T, hTm, hTc⟩ := List.any_eq_true.mp hT
  exact List.any_eq_true.mpr ⟨a, ha, List.any_eq_true.mpr ⟨T, hn.subset hTm, hTc⟩⟩

/-- **THE OCCURRENCE TEST'S TWO VERDICTS** (task #315): a `true` says
some parameter argument mentions a type of the growing list, and the
`.ok` says none of them has a loose bound variable. -/
private theorem cpOccOk_inv {I : Name} {names : List Name} {nPI : Nat} {args : List Expr}
    (h : nestedOccOk I names nPI args = .ok true) :
    ((args.take nPI).any fun a => names.any fun T => a.mentionsConst T) = true ∧
    (∀ a ∈ args.take nPI, a.looseBVarsBounded 0 = true) := by
  unfold nestedOccOk at h
  dsimp only at h
  split at h
  · close_throw
  · rename_i hcond
    simp only [Except.ok.injEq] at h
    refine ⟨h, ?_⟩
    rw [h, Bool.true_and] at hcond
    have hl : ((args.take nPI).any fun a => !a.looseBVarsBounded 0) = false := by
      simpa using hcond
    intro a ha
    have := List.any_eq_false.mp hl a ha
    simpa using this

/-! ## One mint group -/

/-- **ONE APPENDED COPY IS A STEP**: the state that carries one more
type — `mkCopy`'s output, with its own pin — is a `CopyStep` of the one
before it. -/
private theorem cpStep_append {env : Env} {pbs₀ : List (Expr × BinderMeta)} {st : ElimState}
    {copy : AuxType} {pin : NestedPin} {nextIdx : Nat} {Ic : Name} {ci : ContainerInfo}
    {m : Nat} {J : ContainerMember} {lvls : List Level} {Ds : List Expr}
    (hci : containerInfo? env Ic = some ci) (hm : ci.members[m]? = some J)
    (hsrc : copy.src = some (J.name, lvls, Ds))
    (hmk : mkCopy pbs₀ lvls Ds copy.name J = .ok copy)
    (hany : (Ds.any fun a => st.newNames.any fun T => a.mentionsConst T) = true)
    (hloose : ∀ a ∈ Ds, a.looseBVarsBounded 0 = true) :
    CopyStep env pbs₀ st
      { types := st.types ++ [copy], pins := st.pins ++ [pin], nextIdx := nextIdx } := by
  have hnpre : st.types.map (·.name) <+: (st.types ++ [copy]).map (·.name) := by
    rw [List.map_append]; exact List.prefix_append _ _
  refine ⟨List.prefix_append _ _, hnpre, fun i t hi => cpGetElem?_append hi, ?_⟩
  intro i t hi hti
  obtain ⟨-, rfl⟩ := cpGetElem?_append_one hi hti
  exact ⟨t, ⟨Ic, ci, m, J, lvls, Ds, hci, hm, hsrc, hmk, rfl, rfl,
    cpAny_mono hnpre hany, hloose⟩, rfl⟩

/-- **EVERY TYPE A MINT APPENDS IS A COPY** (task #315): `mkCopies`
appends one `mkCopy` per member of the container's group, under the
name the counter minted, and touches nothing else. -/
private theorem cpMkCopies_step {env : Env} {pbs₀ : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I Ic : Name} {base size : Nat}
    {ci : ContainerInfo} (hci : containerInfo? env Ic = some ci)
    (hloose : ∀ a ∈ Ds, a.looseBVarsBounded 0 = true) :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {got : Option Name},
      (∀ J ∈ Js, J ∈ ci.members) →
      (Ds.any fun a => st.newNames.any fun T => a.mentionsConst T) = true →
      mkCopies env pbs₀ lvls Ds I base size Js st = .ok (st', got) →
      CopyStep env pbs₀ st st'
  | [], st, st', got, _, _, h => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact cpStep_refl st
  | J :: rest, st, st', got, hJs, hany, h => by
    rw [mkCopies] at h
    split at h
    rename_i auxName nextIdx heq
    obtain ⟨copy, hcopy, h⟩ := exceptBind_ok h
    obtain ⟨r, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, -, hname, hsrc, -, -⟩ := mkCopy_inv hcopy
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp (hJs J (List.mem_cons_self ..))
    have hmid : CopyStep env pbs₀ st
        { types := st.types ++ [copy]
          pins := st.pins ++
            [⟨auxName, J.name, Expr.mkAppN (.const J.name lvls) Ds, base, size, st.curType⟩]
          nextIdx := nextIdx } :=
      cpStep_append hci hm hsrc (by rw [hname]; exact hcopy) hany hloose
    exact cpStep_trans hmid (cpMkCopies_step hci hloose
      (fun J' hJ' => hJs J' (List.mem_cons_of_mem _ hJ')) (cpAny_mono hmid.2.1 hany) hrec)

/-! ## One occurrence -/

/-- **A MINT IS THE ONLY THING ONE OCCURRENCE DOES TO THE STATE**
(task #315): `replaceIfNested` either returns the state it was given
(no occurrence, or the pin already minted) or mints the container's
whole group, and the occurrence test's verdicts travel with it. -/
private theorem cpReplaceIfNested_step {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {st st' : ElimState} {e e' : Expr}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    CopyStep env pbs₀ st st' := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · rename_i ci hci
            dsimp only at h
            split at h
            · close_throw
            · obtain ⟨nested, hocc, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · rename_i hn
                split at h
                · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  exact cpStep_refl _
                · obtain ⟨q, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := q
                  split at h
                  · close_throw
                  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    have hnt : nested = true := by simpa using hn
                    rw [hnt] at hocc
                    obtain ⟨hany, hloose⟩ := cpOccOk_inv hocc
                    exact cpMkCopies_step hci hloose (fun _ hJ => hJ) hany hcop
      · close_throw
    · close_throw
  · close_throw

/-! ## The top-down replace -/

/-- The walk returned the state it was given. -/
private theorem cpStepSame {env : Env} {pbs₀ : List (Expr × BinderMeta)}
    {st st' : ElimState} {e e' : Expr}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) :
    CopyStep env pbs₀ st st' := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact cpStep_refl _

/-- **THE TOP-DOWN REPLACE ONLY MINTS** (task #315): every state it
threads is a `CopyStep` of the one before — the prune and the
already-minted pin return the state, an occurrence mints, and the
children compose. -/
private theorem cpReplaceAllNested_step {env : Env} {blvls : List Level}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      CopyStep env pbs₀ st st' := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact cpStepSame h
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact cpReplaceIfNested_step heq
        · exact cpStepSame h
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact cpStepSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact cpReplaceIfNested_step heq
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact cpStep_trans (ihf heq1) (iha heq2)
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact cpStepSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact cpReplaceIfNested_step heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact cpStep_trans (ihty heq1) (ihb heq2)
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact cpStepSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact cpReplaceIfNested_step heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact cpStep_trans (ihty heq1) (ihb heq2)
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact cpStepSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact cpReplaceIfNested_step heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i v' st2 heq2
            split at h
            · close_throw
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact cpStep_trans (ihty heq1) (cpStep_trans (ihv heq2) (ihb heq3))
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact cpStepSame h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact cpReplaceIfNested_step heq
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihx heq1

/-! ## One type's constructors -/

/-- **`elimCtors` ONLY MINTS**: the states it threads are `CopyStep`s. -/
private theorem cpElimCtors_step {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      CopyStep env pbs₀ st st'
  | [], st, st', cs', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact cpStep_refl _
  | (c, cty, nF) :: rest, st, st', cs', h => by
    rw [elimCtors] at h
    split at h
    · split at h
      · obtain ⟨q₁, h₁, h⟩ := exceptBind_ok h
        obtain ⟨cbody', st₁⟩ := q₁
        obtain ⟨q₂, h₂, h⟩ := exceptBind_ok h
        obtain ⟨rest', st₂⟩ := q₂
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact cpStep_trans (cpReplaceAllNested_step _ h₁) (cpElimCtors_step h₂)
      · close_throw
    · close_throw

/-- **WHERE ONE REWRITTEN CONSTRUCTOR COMES FROM** (task #315):
`elimCtors` returns, at every position, the input constructor's name
and field count with the type `closeTelescope pbs 0 cbody'` — `pbs` its
own parameter binders, `cbody'` the replace of its residual at a state
sandwiched in the call's. -/
private theorem cpElimCtors_ctor {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      ∀ (j : Nat) (cj : Name × Expr × Nat), cs'[j]? = some cj →
        ∃ (c₀ : Name × Expr × Nat) (pbs : List (Expr × BinderMeta))
          (rest cbody cbody' : Expr) (stA stB : ElimState),
          cs[j]? = some c₀ ∧ c₀.2.1.stripPis nP = some (pbs, rest) ∧
          Expr.instPis c₀.2.1 params = some cbody ∧
          replaceAllNested env blvls params pbs₀ stA cbody = .ok (cbody', stB) ∧
          cj = (c₀.1, closeTelescope pbs 0 cbody', c₀.2.2) ∧
          stA.pins <+: stB.pins ∧ stB.pins <+: st'.pins ∧
          stA.types.map (·.name) <+: st'.types.map (·.name) ∧
          st.types.map (·.name) <+: stA.types.map (·.name)
  | [], st, st', cs', h, j, cj, hj => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp at hj
  | (c, cty, nF) :: rest, st, st', cs', h, j, cj, hj => by
    rw [elimCtors] at h
    split at h
    · rename_i pbs restT hstrip
      split at h
      · rename_i cbody hinst
        obtain ⟨q₁, h₁, h⟩ := exceptBind_ok h
        obtain ⟨cbody', st₁⟩ := q₁
        obtain ⟨q₂, h₂, h⟩ := exceptBind_ok h
        obtain ⟨rest', st₂⟩ := q₂
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          refine ⟨(c, cty, nF), pbs, restT, cbody, cbody', st, st₁, rfl, hstrip, hinst,
            h₁, rfl, (cpReplaceAllNested_step _ h₁).1, (cpElimCtors_step h₂).1,
            ((cpReplaceAllNested_step _ h₁).2.1).trans (cpElimCtors_step h₂).2.1,
            List.prefix_refl _⟩
        | succ j' =>
          simp only [List.getElem?_cons_succ] at hj
          obtain ⟨c₀, pbs', rest', cbody₂, cbody₂', stA, stB, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈,
            e₉⟩ := cpElimCtors_ctor h₂ j' cj hj
          exact ⟨c₀, pbs', rest', cbody₂, cbody₂', stA, stB, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈,
            ((cpReplaceAllNested_step _ h₁).2.1).trans e₉⟩
      · close_throw
    · close_throw

/-! ## The worklist's invariant -/

/-- **THE ELIMINATION'S COPY INVARIANT**: every type behind the block's
own `k` members is a mint, and it is PROCESSED (its constructors are
the rewrite of `mkCopy`'s) exactly at the positions the worklist has
already passed. -/
private def CopyInv (env : Env) (blvls : List Level) (nP : Nat) (params : List Expr)
    (pbs₀ : List (Expr × BinderMeta)) (k qhead : Nat) (st : ElimState) : Prop :=
  ∀ (q : Nat) (t : AuxType), st.types[k + q]? = some t →
    ∃ c, CopyHead env pbs₀ st.newNames t c ∧
      (k + q < qhead → CtorsDone env blvls nP params pbs₀ st t c) ∧
      (qhead ≤ k + q → t.ctors = c.ctors)

/-- Rewriting a type's constructors, without changing their number,
leaves the mint's record standing. -/
private theorem cpHead_ctors {env : Env} {pbs₀ : List (Expr × BinderMeta)}
    {names : List Name} {t c : AuxType} {cs : List (Name × Expr × Nat)}
    (hlen : cs.length = t.ctors.length) (h : CopyHead env pbs₀ names t c) :
    CopyHead env pbs₀ names { t with ctors := cs } c := by
  obtain ⟨I, ci, m, J, lvls, Ds, hci, hJ, hsrc, hmk, hty, hclen, hany, hloose⟩ := h
  exact ⟨I, ci, m, J, lvls, Ds, hci, hJ, hsrc, hmk, hty, hlen.trans hclen, hany, hloose⟩

/-- The invariant travels through a step of the elimination: the types
the step kept keep their record, and the ones it appended are mints the
worklist has not reached. -/
private theorem cpInv_step {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {k qhead : Nat} {st st' : ElimState}
    (hq : qhead ≤ st.types.length) (hs : CopyStep env pbs₀ st st')
    (hinv : CopyInv env blvls nP params pbs₀ k qhead st) :
    CopyInv env blvls nP params pbs₀ k qhead st' := by
  obtain ⟨hp, hn, hk, hnew⟩ := hs
  intro q t hqt
  rcases Nat.lt_or_ge (k + q) st.types.length with hlt | hge
  · obtain ⟨t₀, ht₀⟩ : ∃ t₀, st.types[k + q]? = some t₀ := ⟨_, List.getElem?_eq_getElem hlt⟩
    have het : t₀ = t := Option.some.inj ((hk _ t₀ ht₀).symm.trans hqt)
    subst het
    obtain ⟨c, hc, hdone, hunp⟩ := hinv q _ ht₀
    exact ⟨c, cpHead_mono hn hc, fun hlt' => cpDone_mono hp hn (hdone hlt'), hunp⟩
  · obtain ⟨c, hc, hcc⟩ := hnew _ t hge hqt
    exact ⟨c, hc, fun hlt' => absurd hlt' (by omega), fun _ => hcc⟩

/-- **THE WORKLIST PROCESSES EVERY COPY** (task #315): started with the
invariant at `qhead`, `elimLoop` returns a state in which every type
behind the block's own members is a mint whose constructors are the
rewrite of `mkCopy`'s. -/
private theorem cpElimLoop_inv {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ (fuel qhead : Nat) {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      qhead ≤ st.types.length →
      CopyInv env blvls nP params pbs₀ k qhead st →
      ∀ (q : Nat) (t : AuxType), st'.types[k + q]? = some t →
        ∃ c, CopyHead env pbs₀ st'.newNames t c ∧
          CtorsDone env blvls nP params pbs₀ st' t c := by
  intro fuel
  induction fuel with
  | zero =>
    intro qhead st st' h
    rw [elimLoop] at h
    close_throw
  | succ fuel ih =>
    intro qhead st st' h hq hinv
    rw [elimLoop] at h
    cases htq : st.types[qhead]? with
    | none =>
      simp only [htq, Except.ok.injEq] at h
      obtain rfl := h
      intro q t hqt
      obtain ⟨c, hc, hdone, -⟩ := hinv q t hqt
      have hlen : st.types.length ≤ qhead := by
        rcases Nat.lt_or_ge qhead st.types.length with hlt | hge
        · rw [List.getElem?_eq_getElem hlt] at htq
          simp at htq
        · exact hge
      have hlt2 : k + q < st.types.length := (List.getElem?_eq_some_iff.mp hqt).1
      exact ⟨c, hc, hdone (by omega)⟩
    | some tq =>
      simp only [htq] at h
      split at h
      · close_throw
      · rename_i cs' st₁ heq
        have hqlt : qhead < st.types.length := (List.getElem?_eq_some_iff.mp htq).1
        have hinv₁ : CopyInv env blvls nP params pbs₀ k qhead st₁ :=
          cpInv_step (by omega) (cpElimCtors_step heq) hinv
        have htq₁ : st₁.types[qhead]? = some tq := elimCtors_types_prefix heq qhead tq htq
        have hq₁ : qhead < st₁.types.length := (List.getElem?_eq_some_iff.mp htq₁).1
        have hnames : (st₁.types.set qhead { tq with ctors := cs' }).map (·.name)
            = st₁.types.map (·.name) := cpMap_name_set htq₁
        have hclen : cs'.length = tq.ctors.length := by
          have := elimCtors_names heq
          have := congrArg List.length this
          simpa using this
        refine ih (qhead + 1) h (by simp only [List.length_set]; omega) ?_
        intro q t hqt
        simp only at hqt
        by_cases hqe : k + q = qhead
        · rw [hqe, List.getElem?_set_self hq₁, Option.some.injEq] at hqt
          subst hqt
          obtain ⟨c, hc, -, hunp⟩ := hinv₁ q tq (by rw [hqe]; exact htq₁)
          have hcc : tq.ctors = c.ctors := hunp (by omega)
          refine ⟨c, ?_, ?_, fun hle => absurd hle (by omega)⟩
          · refine cpHead_ctors hclen ?_
            simp only [ElimState.newNames, hnames]
            exact hc
          · intro _hlt j cj hj
            obtain ⟨c₀, pbs, rest, cbody, cbody', stA, stB, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
              h₉⟩ := cpElimCtors_ctor heq j cj hj
            -- the mint verdict at the state the rewrite STARTS from: the
            -- copy was minted before the worklist reached it
            obtain ⟨c', hc', -, -⟩ := hinv q tq (by rw [hqe]; exact htq)
            obtain ⟨I', ci', m', J', lvls', Ds', -, -, hsrc', -, -, -, hany', -⟩ := hc'
            refine ⟨c₀, pbs, rest, cbody, cbody', stA, stB, ?_, h₂, h₃, h₄, h₅, h₆, h₇, ?_, ?_⟩
            · rw [← hcc]; exact h₁
            · simp only [ElimState.newNames, hnames] at *
              exact h₈
            · intro Jn lvls Ds hsrc
              have : (J'.name, lvls', Ds') = (Jn, lvls, Ds) :=
                Option.some.inj (hsrc'.symm.trans hsrc)
              obtain ⟨-, -, rfl⟩ : J'.name = Jn ∧ lvls' = lvls ∧ Ds' = Ds := by
                simpa using this
              exact cpAny_mono h₉ hany'
        · rw [List.getElem?_set_ne (fun hc => hqe hc.symm)] at hqt
          obtain ⟨c, hc, hdone, hunp⟩ := hinv₁ q t hqt
          refine ⟨c, ?_, ?_, fun hle => hunp (by omega)⟩
          · simp only [ElimState.newNames, hnames]
            exact hc
          · intro hlt'
            refine cpDone_mono (stF := st₁) (List.prefix_refl _) ?_ (hdone (by omega))
            show st₁.types.map (·.name) <+:
              (st₁.types.set qhead { tq with ctors := cs' }).map (·.name)
            rw [hnames]
            exact List.prefix_refl _

/-! ## The elimination -/

/-- **The mint verdict survives a longer name list** — the public twin
of `cpAny_mono`, for a consumer that carries `elimNested_copyCtors`'
mint condition to a later state of the same rewrite (the states a
telescope's per-domain runs start at, `replaceAllNested_mkPisB`). -/
theorem elimMint_mono {Ds : List Expr} {names names' : List Name}
    (hn : names <+: names')
    (h : (Ds.any fun a => names.any fun T => a.mentionsConst T) = true) :
    (Ds.any fun a => names'.any fun T => a.mentionsConst T) = true :=
  cpAny_mono hn h


/-- **THE PROVENANCE OF A COPY'S STORED CONSTRUCTORS** (task #315):
every type the elimination appended behind the block's own members is
the copy of a container member `J` of `I`'s group at the pin `J D⃗` —
the source record says so, `mkCopy` at the block's first former's
parameter binders `pbs₀` produces it, and the occurrence test's two
verdicts hold of `D⃗` at the FINAL name list.  Its stored type is
`mkCopy`'s; its stored constructors are `mkCopy`'s, one for one,
rewritten: the parameter prefix stripped (`pbs`), the residual opened
at the block's parameters (`instPis … params`), replaced
(`replaceAllNested`) at a state whose pins and type names sit inside
the elimination's, and closed again with the constructor's OWN binder
data.  The run's own state satisfies the mint verdict too (the copy is
minted before the worklist reaches it), which is what lets a consumer
apply `replaceAllNested_occurrence` to the run. -/
theorem elimNested_copyCtors {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (h : elimNested env nP lps types = .ok st) :
    ∃ (t₀ : AuxType) (params : List Expr) (o : Expr) (pbs₀ : List (Expr × BinderMeta))
      (o' : Expr),
      types.head? = some t₀ ∧ openPisAtFvars nP t₀.type 0 = some (params, o) ∧
      t₀.type.stripPis nP = some (pbs₀, o') ∧
      ∀ (q : Nat) (t : AuxType), st.types[types.length + q]? = some t →
        ∃ (I : Name) (ci : ContainerInfo) (m : Nat) (J : ContainerMember) (lvls : List Level)
          (Ds : List Expr) (c : AuxType),
          containerInfo? env I = some ci ∧ ci.members[m]? = some J ∧
          t.src = some (J.name, lvls, Ds) ∧ mkCopy pbs₀ lvls Ds t.name J = .ok c ∧
          t.type = c.type ∧ t.ctors.length = c.ctors.length ∧
          (Ds.any fun a => st.newNames.any fun T => a.mentionsConst T) = true ∧
          (∀ a ∈ Ds, a.looseBVarsBounded 0 = true) ∧
          ∀ (j : Nat) (cj : Name × Expr × Nat), t.ctors[j]? = some cj →
            ∃ (c₀ : Name × Expr × Nat) (pbs : List (Expr × BinderMeta))
              (rest cbody cbody' : Expr) (st₁ st₂ : ElimState),
              c.ctors[j]? = some c₀ ∧ c₀.2.1.stripPis nP = some (pbs, rest) ∧
              Expr.instPis c₀.2.1 params = some cbody ∧
              replaceAllNested env (lps.map Level.param) params pbs₀ st₁ cbody
                = .ok (cbody', st₂) ∧
              cj = (c₀.1, closeTelescope pbs 0 cbody', c₀.2.2) ∧
              st₁.pins <+: st₂.pins ∧ st₂.pins <+: st.pins ∧
              st₁.types.map (·.name) <+: st.types.map (·.name) ∧
              (Ds.any fun a => st₁.newNames.any fun T => a.mentionsConst T) = true := by
  unfold elimNested at h
  split at h
  · rename_i t₀ hhead
    split at h
    · rename_i params o hopen
      split at h
      · rename_i pbs₀ o' hstrip
        refine ⟨t₀, params, o, pbs₀, o', hhead, hopen, hstrip, ?_⟩
        intro q t hqt
        have hinit : CopyInv env (lps.map Level.param) nP params pbs₀ types.length 0
            ⟨types, [], 1, 0⟩ := by
          intro q' t' hq'
          exfalso
          have hlt : types.length + q' < types.length := (List.getElem?_eq_some_iff.mp hq').1
          omega
        obtain ⟨c, hhd, hdone⟩ :=
          cpElimLoop_inv (k := types.length) nestedElimFuel 0 h (Nat.zero_le _) hinit q t hqt
        obtain ⟨I, ci, m, J, lvls, Ds, hci, hJ, hsrc, hmk, hty, hlen, hany, hloose⟩ := hhd
        refine ⟨I, ci, m, J, lvls, Ds, c, hci, hJ, hsrc, hmk, hty, hlen, hany, hloose, ?_⟩
        intro j cj hj
        obtain ⟨c₀, pbs, rest, cbody, cbody', st₁, st₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
          hdone j cj hj
        exact ⟨c₀, pbs, rest, cbody, cbody', st₁, st₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
          h₉ J.name lvls Ds hsrc⟩
      · close_throw
    · close_throw
  · close_throw

end ConLeche
