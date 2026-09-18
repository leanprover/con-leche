module

public import ConLeche.Kernel.Inductives.NestedInstall
import ConLeche.Verify.Inductives.NestedElimInv
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.FrontDoor
import ConLeche.Verify.EnvWF
-- **THE DECIMAL RENDERING** (task #315, the mirror assemblies' Blocker 2):
-- the restored recursors' names are pairwise distinct SYNTACTICALLY, and
-- the mimics' `T₁.rec_j` are separated by `j` — which needs `toString`
-- injective on `Nat`.  `Verify/Frontend/Digits.lean` characterises
-- `Nat.repr` once, for the file-level statement; this is its second
-- consumer.
import ConLeche.Verify.Frontend.Digits

public section

/-!
# The nested block's recursor names (task #315)

`MutualCoreModeled`'s `hrecNames` at the NESTED route's scratch
install (DESIGN §U.18 (d) 6): every recursor name the auxiliary block
will mint is FREE at the environment the recursor stage runs at, and is
neither a reserved basis name nor shaped like a projection function's.

The auxiliary block's members split in two, and so does the argument.

* A **member** of the stream's own block (`t < p.k`) carries its
  declared name, and the RESTORE checks `T_t.rec` through the
  pre-annotated front door (`restoreRecTys`) — whose guards are exactly
  the three facts, at the restored environment.  Freshness travels down
  the restore's cons chain to the pre-block environment.
* A **copy** (`p.k ≤ t`) carries a minted name.  `copiesFresh` is the
  run's own check that every minted name — the copy's, its recursor's
  and its constructors' — is free at the pre-block environment, and the
  mint's SHAPE (`mkUniqueName` over the `_nested` prefix) is what keeps
  a copy's recursor out of the reserved list.

From the pre-block environment the three facts travel UP the scratch
install's two cons stages, since `b.blockNames.Nodup` keeps a recursor
name off every member and every constructor of the block.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The cons chains, downward -/

/-- A cons chain finds everything the base finds: the restore's
formers. -/
theorem consNestedFormers_find?_none :
    ∀ {as : List AuxStored} {env : Env} {n : Name},
      (consNestedFormers as env).find? n = none → env.find? n = none
  | [], _, _, h => h
  | a :: rest, env, n, h => by
    have h' : (Env.mk (.indInfo a.cvTa a.caps :: env.consts)).find? n = none :=
      consNestedFormers_find?_none h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- A cons chain finds everything the base finds: the restore's
constructors. -/
theorem consNestedCtors_find?_none :
    ∀ {cs : List (ConstantVal × Nat × Nat)} {env : Env} {n : Name},
      (consNestedCtors cs env).find? n = none → env.find? n = none
  | [], _, _, h => h
  | (cv, nP, nF) :: rest, env, n, h => by
    have h' : (Env.mk (.ctorInfo cv nP nF :: env.consts)).find? n = none :=
      consNestedCtors_find?_none h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- A lookup past the constructors' conses of other names
(`consMutualFormers_find?_of_ne`'s twin). -/
theorem consMutualCtors_find?_of_ne {nP : Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {env : Env} {n : Name},
      (∀ c ∈ cs, c.1.name ≠ n) →
      (consMutualCtors nP cs env).find? n = env.find? n
  | [], _, _, _ => rfl
  | c :: cs, env, n, hne => by
    show (consMutualCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩).find? n = _
    rw [consMutualCtors_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      Env.find?_cons]
    exact if_neg (hne c List.mem_cons_self)

/-- A recursor name is never shaped like a projection function's. -/
theorem isProjFnShape_str_rec (n : Name) : (n.str "rec").isProjFnShape = false := rfl

/-! ## The restore's front door at a recursor name -/

/-- **THE RESTORED RECURSOR TYPES' FRONT DOOR**, positionally: the
constant stored at position `i` carries the name the caller asked for,
and the door's three name guards hold of it. -/
theorem restoreRecTys_door {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat} :
    ∀ {names : List Name} {as : List AuxStored} {out : List ConstantVal},
      restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out →
      ∀ (i : Nat) (nm : Name) (o : ConstantVal), names[i]? = some nm → out[i]? = some o →
        o.name = nm ∧ env.find? nm = none ∧
          reservedBasisNames.contains nm = false ∧ nm.isProjFnShape = false := by
  intro names as
  induction as generalizing names with
  | nil =>
    intro out h i nm o _ ho
    simp only [restoreRecTys, pure, Except.pure, Except.ok.injEq] at h
    rw [← h] at ho
    exact absurd ho (by simp)
  | cons a rest ih =>
    intro out h i nm o hnm ho
    unfold restoreRecTys at h
    obtain ⟨ty, -, h⟩ := exceptBind_ok h
    obtain ⟨cvA, hpre, h⟩ := exceptBind_ok h
    obtain ⟨rest', hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hnm ho
      obtain rfl := ho
      have hhd : names.headD a.cvRa.name = nm := by
        cases names with
        | nil => exact absurd hnm (by simp)
        | cons x xs =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hnm
          simp [hnm]
      rw [hhd] at hpre
      have hd := FrontDoorFacts.ofPre hpre
      exact ⟨hd.name, hd.fresh, hd.nres, hd.pshape⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at ho
      refine ih hrest k nm o ?_ ho
      rw [List.getElem?_drop, Nat.add_comm]
      exact hnm

/-- **THE RESTORED RECURSORS' NAMES ARE THE NAMES ASKED FOR**, as a
membership (task #315 M7-3 session 21): `restoreRecTys_door` reads the
name off position `i`, and a restored constant is AT some position, so
a name list at least as long as the output pins down every restored
name.  The length side condition is not idle — `restoreRecTys` walks
the AUXILIARY records and falls back to the auxiliary recursor's own
name once the caller's list runs out (`names.headD a.cvRa.name`), so
nothing is known past `names.length`; both real calls hand it a list of
exactly the output's length.

The consumer is the nested route's `nestedMimN`
(`Model/Inductives/EnvModelBStages.lean`): a MIMIC-shaped recursor name
the install conses is one of the mimics', which is what tells the
own-pin crossing that a mimic under an OLD container is never new. -/
theorem restoreRecTys_names_of_mem {env : Env} {R : RestoreTbl} {lps : List Name} {F : Nat}
    {names : List Name} {as : List AuxStored} {out : List ConstantVal}
    (h : restoreRecTys (m := CheckM) (fueledOps mode F) env R lps names as = .ok out)
    (hlen : out.length ≤ names.length) : ∀ o ∈ out, o.name ∈ names := by
  intro o ho
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
  have hlt : i < names.length := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hi).1 hlen
  obtain ⟨hname, -, -, -⟩ := restoreRecTys_door h i names[i] o (List.getElem?_eq_getElem hlt) hi
  rw [hname]
  exact List.getElem_mem hlt

/-! ## The minted names' shape -/

/-- The shape of every name the elimination mints: the `_nested`
prefix in front of the container member's name, with `mkUniqueName`'s
running counter appended (`Name.appendIndexAfter`). -/
def NestedCopyName (n : Name) : Prop :=
  ∃ (base : Name) (i : Nat), n = Name.appendIndexAfter (Name.appendName nestedPrefixName base) i

/-- A non-anonymous prefix is never appended away. -/
theorem appendName_ne_anonymous {pre : Name} (hpre : pre ≠ .anonymous) :
    ∀ base : Name, Name.appendName pre base ≠ .anonymous
  | .anonymous => hpre
  | .str _ _ => by simp [Name.appendName]
  | .num _ _ => by simp [Name.appendName]

/-- A minted name is never a bare root name of five characters or
fewer — the `_nested` prefix alone is seven. -/
theorem nestedCopyName_ne_root {n : Name} (h : NestedCopyName n) {s : String}
    (hlen : s.length ≤ 5) : n ≠ Name.anonymous.str s := by
  obtain ⟨base, i, rfl⟩ := h
  have hpre : nestedPrefixName ≠ Name.anonymous := by simp [nestedPrefixName]
  cases base with
  | anonymous =>
    simp only [Name.appendName, nestedPrefixName, Name.appendIndexAfter,
      ne_eq, Name.str.injEq, not_and]
    intro _ hs
    have := congrArg String.length hs
    rw [String.length_append, String.length_append] at this
    have h1 : "_nested".length = 7 := by rfl
    have h2 : "_".length = 1 := by rfl
    omega
  | str p s' =>
    simp only [Name.appendName, Name.appendIndexAfter, ne_eq, Name.str.injEq, not_and]
    intro hc
    exact absurd hc (appendName_ne_anonymous hpre p)
  | num p k =>
    simp [Name.appendName, Name.appendIndexAfter]

/-- **A MINTED RECURSOR NAME IS NOT A RESERVED ONE**: the reserved
names are five roots and their members, and a minted name is neither a
root of at most five characters nor a member under a name other than
`rec`. -/
theorem nestedCopyName_nres {n : Name} (h : NestedCopyName n) :
    reservedBasisNames.contains (n.str "rec") = false := by
  have hroot : ∀ s : String, s.length ≤ 5 → n ≠ Name.anonymous.str s :=
    fun s hs => nestedCopyName_ne_root h hs
  have hmem : (n.str "rec") ∉ reservedBasisNames := by
    simp only [reservedBasisNames, eqName, eqReflName, natName, natZeroName, natSuccName,
      punitName, punitUnitName, emptyName, falseName, quotName, quotMkName, quotLiftName,
      quotIndName, quotSoundName, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
      h1 | h1 | h1) <;>
      simp only [Name.str.injEq] at h1 <;>
      first
        | exact absurd h1.2 (by decide)
        | exact hroot _ (by decide) h1.1
  simp [hmem]

/-! ## The mint's shape, threaded through the elimination -/

/-- **`mkUniqueName` only ever returns an INDEXED base**: the loop
skips a taken candidate, and every candidate is the base with a
counter appended. -/
theorem mkUniqueName_shape (env : Env) (base : Name) :
    ∀ (fuel idx : Nat), ∃ j, (mkUniqueName env base fuel idx).1 = Name.appendIndexAfter base j
  | 0, idx => ⟨idx, rfl⟩
  | fuel + 1, idx => by
    rw [mkUniqueName]
    split
    · exact ⟨idx, rfl⟩
    · exact mkUniqueName_shape env base fuel (idx + 1)

/-- The elimination's invariant: every type past the block's own `k`
members carries a name the elimination MINTED. -/
def CopiesNamed (k : Nat) (st : ElimState) : Prop :=
  ∀ (i : Nat) (t : AuxType), k ≤ i → st.types[i]? = some t → NestedCopyName t.name

/-- One appended copy keeps the invariant. -/
private theorem copiesNamed_append {k : Nat} {st : ElimState} {c : AuxType}
    {pins : List NestedPin} {idx cur : Nat} (h : CopiesNamed k st) (hc : NestedCopyName c.name) :
    CopiesNamed k ⟨st.types ++ [c], pins, idx, cur⟩ := by
  intro i t hk hi
  by_cases hlt : i < st.types.length
  · exact h i t hk (by rwa [List.getElem?_append_left hlt] at hi)
  · rw [List.getElem?_append_right (by omega)] at hi
    have hi0 : i - st.types.length = 0 := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_cons, List.length_nil] at this
      omega
    rw [hi0] at hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    rw [← hi]
    exact hc

/-- **One mint group** keeps the invariant: every appended copy carries
`mkUniqueName`'s indexed `_nested` name. -/
theorem mkCopies_named {env : Env} {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {I : Name} {base size k : Nat} :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size Js st = .ok (st', got) →
      CopiesNamed k st → CopiesNamed k st'
  | [], st, st', got, h, hst => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hst
  | J :: rest, st, st', got, h, hst => by
    rw [mkCopies] at h
    split at h
    rename_i auxName nextIdx heq
    obtain ⟨copy, hcopy, h⟩ := exceptBind_ok h
    obtain ⟨q, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := q
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, -, hname, -, -, -⟩ := mkCopy_inv hcopy
    obtain ⟨j, hj⟩ := mkUniqueName_shape env (Name.appendName nestedPrefixName J.name)
      1024 st.nextIdx
    refine mkCopies_named hrec (copiesNamed_append hst ?_)
    refine ⟨J.name, j, ?_⟩
    rw [hname, ← hj, heq]

/-- An `.error` never succeeds. -/
private theorem elimErr_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (Except.error e : CheckM α) = .ok a) : False := by
  simp at h

/-- A declining step never returns a replacement. -/
private theorem elimNone_ne_some {α : Type} {a : α}
    (h : (pure none : CheckM (Option α)) = .ok (some a)) : False := by
  simp [pure, Except.pure] at h

/-- Close a branch the run cannot have taken (`NestedElimInv.lean`'s
tactic: the elimination is a plain `Except`, so its refusals are
`.error`s rather than `throw`s). -/
local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact elimErr_ne_ok (by assumption))
        | (exfalso; exact elimNone_ne_some (by assumption)))

/-- **One occurrence** keeps the invariant: `replaceIfNested` either
passes the state through or mints. -/
theorem replaceIfNested_named {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {st st' : ElimState} {e e' : Expr} {k : Nat}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    CopiesNamed k st → CopiesNamed k st' := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_throw
        · split at h
          · split at h <;> close_throw
          · dsimp only at h
            split at h
            · close_throw
            · obtain ⟨nested, -, h⟩ := exceptBind_ok h
              split at h
              · close_throw
              · split at h
                · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  exact id
                · obtain ⟨q, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := q
                  split at h
                  · close_throw
                  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact mkCopies_named hcop
      · close_throw
    · close_throw
  · close_throw

/-- The walk returned the state it was given. -/
private theorem elimSameN {st st' : ElimState} {e e' : Expr} {k : Nat}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) :
    CopiesNamed k st → CopiesNamed k st' := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact id

/-- **The top-down replace only threads the state**, so the invariant
travels through it. -/
theorem replaceAllNested_named {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      CopiesNamed k st → CopiesNamed k st' := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact elimSameN h
      · split at h
        · close_throw
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact replaceIfNested_named heq
        · exact elimSameN h
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameN h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_named heq
      · split at h
        · close_throw
        · rename_i f' st1 heq1
          split at h
          · close_throw
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun hs => iha heq2 (ihf heq1 hs)
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameN h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_named heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun hs => ihb heq2 (ihty heq1 hs)
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameN h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_named heq
      · split at h
        · close_throw
        · rename_i ty' st1 heq1
          split at h
          · close_throw
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun hs => ihb heq2 (ihty heq1 hs)
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameN h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_named heq
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
              exact fun hs => ihb heq3 (ihv heq2 (ihty heq1 hs))
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameN h
    · split at h
      · close_throw
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_named heq
      · split at h
        · close_throw
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihx heq1


/-- **One type's constructors** keep the invariant: `elimCtors` only
threads the state. -/
theorem elimCtors_named {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      CopiesNamed k st → CopiesNamed k st'
  | [], st, st', cs', h => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact id
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
        exact fun hs => elimCtors_named h₂ (replaceAllNested_named _ h₁ hs)
      · close_throw
    · close_throw

/-- **The worklist** keeps the invariant: `elimLoop` `set`s the type it
is at, with the same name, and the constructors' elimination only
threads the state. -/
private theorem elimLoop_named {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ (fuel qhead : Nat) {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      CopiesNamed k st → CopiesNamed k st' := by
  intro fuel
  induction fuel with
  | zero =>
    intro qhead st st' h
    rw [elimLoop] at h
    close_throw
  | succ fuel ih =>
    intro qhead st st' h
    rw [elimLoop] at h
    cases htq : st.types[qhead]? with
    | none =>
      simp only [htq, Except.ok.injEq] at h
      obtain rfl := h
      exact id
    | some tq =>
      simp only [htq] at h
      split at h
      · close_throw
      · rename_i cs' st₁ heq
        intro hst
        have h₁ : CopiesNamed k st₁ := elimCtors_named heq hst
        refine ih (qhead + 1) h ?_
        intro i t hk hi
        by_cases hiq : i = qhead
        · subst hiq
          have hlt : i < st₁.types.length := by
            have := (List.getElem?_eq_some_iff.mp hi).1
            simpa using this
          rw [List.getElem?_set_self hlt] at hi
          simp only [Option.some.injEq] at hi
          rw [← hi]
          exact hst i tq hk htq
        · rw [List.getElem?_set_ne (Ne.symm hiq)] at hi
          exact h₁ i t hk hi

/-- **THE ELIMINATION'S COPIES CARRY MINTED NAMES** (task #315): every
type past the block's own members is a copy, and every copy's name is
`mkUniqueName`'s — the `_nested` prefix in front of the container
member's name, with a counter appended. -/
theorem elimNested_named {env : Env} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState} {k : Nat} (hk : types.length ≤ k)
    (h : elimNested env nP lps types = .ok st) : CopiesNamed k st := by
  unfold elimNested at h
  split at h
  · split at h
    · split at h
      · refine elimLoop_named _ _ h ?_
        intro i t hi hit
        have hit' : types[i]? = some t := hit
        rw [List.getElem?_eq_none (by omega)] at hit'
        exact nomatch hit'
      · close_throw
    · close_throw
  · close_throw

/-! ## The mimic recursors' indices (task #315, the mirror assemblies)

`K.39` records the restored recursors' distinctness as a
CERTIFICATION-ONLY Bool, which is `true` in trusted mode and therefore
useless to the cached mirror's push chain: that chain must hold in
EVERY mode.  The ruling was to prove the distinctness syntactically
instead of making the check unconditional, and the one thing it needs
that core does not carry is `Nat.repr`'s injectivity —
`Verify/Frontend/Digits.lean` has it, as `digitsVal ∘ lit ∘ toString`.
-/

/-- Left cancellation for `String.append`, through the character list. -/
theorem string_append_cancel {s x y : String} (h : s ++ x = s ++ y) : x = y := by
  have h2 := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_left h2)

/-- **`toString` IS INJECTIVE ON `Nat`**: the rendering's digit run
values back to the number (`Frontend.repr_isDec`), so two numbers with
one rendering are one number. -/
theorem toString_nat_inj {a b : Nat} (h : toString a = toString b) : a = b := by
  have ha := (Frontend.repr_isDec a).val
  have hb := (Frontend.repr_isDec b).val
  rw [h] at ha
  rw [← ha, hb]

/-- **THE INDEX APPENDED TO A NAME DETERMINES THE INDEX.** -/
theorem appendIndexAfter_inj : ∀ {n : Name} {i j : Nat},
    Name.appendIndexAfter n i = Name.appendIndexAfter n j → i = j
  | .str q s, i, j, h => by
    simp only [Name.appendIndexAfter, Name.str.injEq] at h
    exact toString_nat_inj (string_append_cancel h.2)
  | .anonymous, i, j, h => by
    simp only [Name.appendIndexAfter, Name.str.injEq] at h
    exact toString_nat_inj (string_append_cancel h.2)
  | .num q k, i, j, h => by
    simp only [Name.appendIndexAfter, Name.str.injEq] at h
    exact toString_nat_inj (string_append_cancel h.2)

/-- **A MEMBER'S RECURSOR NAME IS NOT A MIMIC'S**: the last string
component is `rec` on one side and `rec_j` on the other. -/
theorem recName_ne_mimicName {b b' : Name} {i : Nat} :
    (Name.str b "rec") ≠ Name.appendIndexAfter (Name.str b' "rec") i := by
  simp only [Name.appendIndexAfter, ne_eq, Name.str.injEq, not_and]
  intro _ hs
  have hlen := congrArg String.length hs
  simp only [String.length_append] at hlen
  rw [show "rec".length = 3 from rfl, show "_".length = 1 from rfl] at hlen
  omega

/-- **THE MIMIC RECURSOR NAMES ARE PAIRWISE DISTINCT**, syntactically:
`T₁.rec_1, T₁.rec_2, …` differ in their index. -/
theorem mimicRecNames_nodup (p : NestedParts) (n : Nat) :
    ((List.range n).map p.mimicRecName).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  refine List.pairwise_lt_range.imp ?_
  intro i j hij heq
  have := appendIndexAfter_inj (n := (p.formers.headD default).1.name.str "rec") heq
  omega

/-- **THE MEMBERS' RECURSOR NAMES ARE PAIRWISE DISTINCT** when the
members' own names are: `·.str "rec"` is injective. -/
theorem memberRecNames_nodup {p : NestedParts} {k : Nat}
    (h : ∀ i j, i < k → j < k →
      (p.formers.getD i default).1.name = (p.formers.getD j default).1.name → i = j) :
    ((List.range k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec")).Nodup := by
  rw [List.Nodup, List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  rw [List.length_range] at hi hj
  rw [List.getElem_range, List.getElem_range] at heq
  exact absurd (h i j hi hj (Name.str.inj heq).1) (by omega)

/-- **AND THE TWO LISTS ARE DISJOINT**, so the whole restored-recursor
name list is `Nodup` — K.39's content, proved rather than recorded. -/
theorem restoredRecNames_nodup {p : NestedParts} {k n : Nat}
    (h : ∀ i j, i < k → j < k →
      (p.formers.getD i default).1.name = (p.formers.getD j default).1.name → i = j) :
    (((List.range k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
      ++ ((List.range n).map p.mimicRecName)).Nodup := by
  refine List.nodup_append.mpr ⟨memberRecNames_nodup h, mimicRecNames_nodup p n, ?_⟩
  intro x hx y hx'
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, -, hj⟩ := List.mem_map.mp hx'
  rw [← hj]
  exact recName_ne_mimicName

/-- **THE RESTORED RECURSORS' NAME LIST IS `Nodup`**, from the block's
own members being distinct — which the SCRATCH install's shape check
establishes (`b.blockNames.Nodup`, through `auxBlock_memberNames`).
This is K.39's content as a THEOREM: the cached mirror's push chain
must hold in EVERY mode, and a `certOnly` Bool is `true` in trusted
mode, so the check cannot serve it. -/
theorem restoredRecNames_nodup_of {p : NestedParts} (hnd : p.memberNames.Nodup) (n : Nat) :
    (((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
      ++ ((List.range n).map p.mimicRecName)).Nodup := by
  refine restoredRecNames_nodup (fun i j hi hj heq => ?_)
  have hlen : p.memberNames.length = p.k := by
    simp only [NestedParts.memberNames, List.length_map, NestedParts.k]
  have hget : ∀ m, m < p.k → p.memberNames[m]? = some (p.formers.getD m default).1.name := by
    intro m hm
    simp only [NestedParts.memberNames, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show m < p.formers.length from hm)]
    rfl
  have hi' := hget i hi
  have hj' := hget j hj
  rw [heq] at hi'
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  obtain ⟨hil, hiv⟩ := List.getElem?_eq_some_iff.mp hi'
  obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp hj'
  rcases Nat.lt_trichotomy i j with hlt | hlt | hlt
  · exact absurd (hiv.trans hjv.symm) (hnd i j hil hjl hlt)
  · exact hlt
  · exact absurd (hjv.trans hiv.symm) (hnd j i hjl hil hlt)

/-! ## The recursor names, at the scratch install -/

/-- **THE NESTED BLOCK'S RECURSOR NAMES ARE FREE, RESERVED-FREE AND
NOT PROJECTION-SHAPED** (task #315, `MutualCoreModeled`'s `hrecNames`
at the nested route): at the environment the auxiliary block's recursor
stage runs at — the block's formers and constructors consed onto the
stream's own environment — no recursor name of the auxiliary block is
taken, none is a reserved basis name, and none is shaped like an
installed projection function's.

The block's own members answer through the RESTORE's front door
(`restoreRecTys` checks `T_t.rec` with `checkConstantValPre`, whose
guards are the three facts), the copies through `copiesFresh` (the
run's own check that every minted name is free) and the mint's shape
(`elimNested_named`). -/
theorem nestedRecNames_of {env : Env} {p : NestedParts} {F : Nat} {fmsA ctorsA₀ : List ConstantVal}
    {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms : List ConstantVal}
    (hfA : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (helim : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA₀) = .ok st)
    (hfresh : copiesFresh env p.k st = true)
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    (hstored : auxStoredAll envAux b b.k = some stored)
    (hrm : restoreRecTys (m := CheckM) (fueledOps mode F)
      (consNestedCtors ctorsR.flatten (consNestedFormers (stored.take p.k) env))
      (restoreTbl p st) p.lps
      ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
      (stored.take p.k) = .ok cvRms)
    {fms : List MutualFormerA}
    (hformers : mutualFormers (fueledOps mode F) b.nP b.formers env true
      = .ok (consMutualFormers fms env, fms))
    {isProp : Bool} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hctors : checkMutualCtors (fueledOps mode F) (consMutualFormers fms env) b fms isProp true
      b.ctors = .ok (ctorsA, sortss)) :
    ∀ t, t < b.k →
      (consMutualCtors b.nP ctorsA (consMutualFormers fms env)).find? (b.recName t) = none ∧
      reservedBasisNames.contains (b.recName t) = false ∧
      (b.recName t).isProjFnShape = false := by
  -- the block's shape
  have hnd : b.blockNames.Nodup := (checkMutualCore_inv haux).1
  rw [MutualBlock.blockNames] at hnd
  have hkc : b.k = p.k + st.pins.length := auxBlock_k_count hfA helim hb
  have hkt : b.k = st.types.length := auxBlock_k hb
  have hlenS : stored.length = b.k := (auxStoredAll_get hstored).1
  have hpk : p.k ≤ b.k := by omega
  -- the two consed name lists
  have hfnames : fms.map (·.cvTa.name) = b.memberNames :=
    mutualFormerChecksG_names (mutualFormers_inv hformers).1
  have hctorName : ∀ c ∈ ctorsA, c.1.name ∈ b.ctors.map (·.cv.name) := by
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨hlen, -, hall⟩ := checkMutualCtors_inv hctors
    have hjlt : j < b.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨c', hc'⟩ : ∃ c', b.ctors[j]? = some c' := ⟨_, List.getElem?_eq_getElem hjlt⟩
    obtain ⟨-, sorts, -, hrun⟩ := hall j c' c hc' hj
    obtain ⟨⟨ty', hdoor⟩, -⟩ := checkMutualCtorG_shape hrun
    exact List.mem_map.mpr ⟨c', List.mem_of_getElem? hc', hdoor.name.symm⟩
  intro t ht
  -- the recursor name is none of the block's other names
  have hrecMem : b.recName t ∈ (List.range b.k).map b.recName :=
    List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩
  have hother : ∀ x ∈ b.memberNames ++ b.ctors.map (·.cv.name), x ≠ b.recName t := by
    intro x hx hxe
    subst hxe
    exact (List.nodup_append.mp hnd).2.2 _ hx _ hrecMem rfl
  -- the three facts at the PRE-BLOCK environment
  have key : env.find? (b.recName t) = none ∧
      reservedBasisNames.contains (b.recName t) = false := by
    by_cases htp : t < p.k
    · -- a member: the restore's front door
      have hmn : (b.formers.getD t default).1.name = (p.formers.getD t default).1.name := by
        obtain ⟨x, hx⟩ : ∃ x, b.formers[t]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [← MutualBlock.k]; omega)⟩
        obtain ⟨y, hy⟩ : ∃ y, p.formers[t]? = some y :=
          ⟨_, List.getElem?_eq_getElem (by rw [← NestedParts.k]; omega)⟩
        have h1 : b.memberNames[t]? = some x.1.name := by
          simp only [MutualBlock.memberNames, List.getElem?_map, hx, Option.map_some]
        have h2 : p.memberNames[t]? = some y.1.name := by
          simp only [NestedParts.memberNames, List.getElem?_map, hy, Option.map_some]
        have h3 : b.memberNames[t]? = p.memberNames[t]? := by
          rw [← auxBlock_memberNames hfA helim hb, List.getElem?_take, if_pos htp]
        rw [h1, h2] at h3
        simp only [List.getD_eq_getElem?_getD, hx, hy, Option.getD_some]
        exact Option.some.inj h3
      have hnames : ((List.range p.k).map fun mIdx =>
          ((p.formers.getD mIdx default).1.name.str "rec"))[t]? = some (b.recName t) := by
        rw [List.getElem?_map, List.getElem?_range htp]
        simp only [Option.map_some, Option.some.injEq]
        rw [MutualBlock.recName, hmn]
      obtain ⟨hlenR, -⟩ := restoreRecTys_id hrm
      obtain ⟨o, ho⟩ : ∃ o, cvRms[t]? = some o := by
        refine ⟨_, List.getElem?_eq_getElem ?_⟩
        rw [hlenR, List.length_take]
        omega
      obtain ⟨-, hfr, hnres, -⟩ := restoreRecTys_door hrm t (b.recName t) o hnames ho
      exact ⟨consNestedFormers_find?_none (consNestedCtors_find?_none hfr), hnres⟩
    · -- a copy: the run's freshness check and the mint's shape
      obtain ⟨tt, htt⟩ : ∃ tt, st.types[t]? = some tt :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨-, hform⟩ := auxBlock_former hb
      obtain ⟨nIdx, hbf, -⟩ := hform t tt htt
      have hrec : b.recName t = tt.name.str "rec" := by
        simp only [MutualBlock.recName, List.getD_eq_getElem?_getD, hbf, Option.getD_some]
      have hdrop : tt ∈ st.types.drop p.k := by
        refine List.mem_of_getElem? (i := t - p.k) ?_
        rw [List.getElem?_drop, show p.k + (t - p.k) = t by omega]
        exact htt
      have hmem : tt.name.str "rec" ∈ nestedCopyNames p.k st := by
        refine List.mem_flatMap.mpr ⟨tt, hdrop, ?_⟩
        simp
      have hfr : env.find? (tt.name.str "rec") = none := by
        simp only [copiesFresh] at hfresh
        have := List.all_eq_true.mp hfresh _ hmem
        simpa using this
      have hlen0 : (nestedTypes0 p fmsA ctorsA₀).length ≤ p.k := by
        rw [nestedTypes0_length, nestedAnnotFormers_length hfA]
        exact Nat.le_refl _
      have hcopy : NestedCopyName tt.name :=
        elimNested_named hlen0 helim t tt (by omega) htt
      exact ⟨hrec ▸ hfr, hrec ▸ nestedCopyName_nres hcopy⟩
  refine ⟨?_, key.2, isProjFnShape_str_rec _⟩
  rw [consMutualCtors_find?_of_ne
      (fun c hc => hother _ (List.mem_append_right _ (hctorName c hc))),
    consMutualFormers_find?_of_ne
      (fun g hg => hother _ (List.mem_append_left _ (hfnames ▸ List.mem_map_of_mem hg)))]
  exact key.1

end ConLeche
