module

public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedElimInv

public section

/-!
# The restore table's keys (task #315)

`restoreTbl` (`ConLeche/Kernel/Inductives/NestedInstall.lean`) is the
elimination's table: the mimics' pins, their constructors' pins and
restored names, the mimic recursors' names, and — as the walk's prune
reads it — the list of every name the replace can fire on.

This file proves the table's own facts, hypothesis-free where the
structure gives them: the prune's side condition
(`RestoreTbl.KeysInAux`) holds of EVERY `restoreTbl`, since each map's
keys are literally the names `auxNames` lists; and each map answers at
a pin's auxiliary name exactly as the mint wrote it.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## Association lists -/

/-- A `lookup` hit is a member of the list, at that key. -/
private theorem restoreLookupMem {β : Type} {n : Name} {v : β} :
    ∀ {l : List (Name × β)}, l.lookup n = some v → ∃ p ∈ l, p.1 = n
  | [], h => by exact absurd h (by simp)
  | (a, b) :: rest, h => by
    rw [List.lookup_cons] at h
    split at h
    · rename_i he
      exact ⟨(a, b), List.mem_cons_self .., (beq_iff_eq.mp he).symm⟩
    · obtain ⟨p, hp, hpn⟩ := restoreLookupMem h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpn⟩

/-- A key no entry carries is a `lookup` miss. -/
private theorem restoreLookupNone {β : Type} {n : Name} :
    ∀ {l : List (Name × β)}, (∀ p ∈ l, p.1 ≠ n) → l.lookup n = none
  | [], _ => rfl
  | (a, b) :: rest, h => by
    rw [List.lookup_cons]
    split
    · rename_i he
      exact absurd (beq_iff_eq.mp he).symm (h (a, b) (List.mem_cons_self ..))
    · exact restoreLookupNone (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- With the keys pairwise distinct, an entry IS the `lookup`. -/
private theorem restoreLookupOfMem {β : Type} {n : Name} {v : β} :
    ∀ {l : List (Name × β)}, (l.map (·.1)).Nodup → (n, v) ∈ l → l.lookup n = some v
  | [], _, h => by exact absurd h (by simp)
  | (a, b) :: rest, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    split
    · rename_i he
      have ha : a = n := (beq_iff_eq.mp he).symm
      subst ha
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        rw [h.2]
      · exact absurd (List.mem_map.mpr ⟨(a, v), h, rfl⟩) hnd.1
    · rename_i he
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1 (by simpa using he)
      · exact restoreLookupOfMem hnd.2 h

/-! ## The table's shape -/

/-- The table copies the block's parameter count. -/
theorem restoreTbl_nP (p : NestedParts) (st : ElimState) :
    (restoreTbl p st).nP = p.nP := rfl

/-- **THE PRUNE'S SIDE CONDITION HOLDS OF EVERY RESTORE TABLE**
(task #315): a hit in any of the three maps is a name `auxNames`
lists — the pins' auxiliary names are its first summand, the copies'
constructor names its second (`ctorPins` lists the constructors of the
copies with a pin, a subset), and the mimic recursors' names its
third. -/
theorem restoreTbl_keysInAux (p : NestedParts) (st : ElimState) :
    (restoreTbl p st).KeysInAux := by
  refine ⟨?_, ?_, ?_⟩
  · -- the pins
    intro n pin hl
    obtain ⟨q, hq, hqn⟩ := restoreLookupMem hl
    simp only [restoreTbl] at hq ⊢
    obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.mp hq
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨q₀, hq₀, hqn⟩))
  · -- the copies' constructors
    intro n q hf
    have hmem : q ∈ (restoreTbl p st).ctorPins := List.mem_of_find?_eq_some hf
    have hkey : q.1 = n := by
      have := List.find?_some hf
      simpa using this
    simp only [restoreTbl] at hmem ⊢
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp hmem
    obtain ⟨tj, htj, rfl⟩ := List.mem_map.mp hl
    obtain ⟨t, j⟩ := tj
    have ht : t ∈ st.types.drop p.k := List.fst_mem_of_mem_zipIdx htj
    simp only at hql
    split at hql
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hql
      exact List.mem_flatMap.mpr ⟨t, ht, List.mem_map.mpr ⟨c, hc, hkey⟩⟩
    · simp only [List.not_mem_nil] at hql
  · -- the mimic recursors
    intro n n' hl
    obtain ⟨q, hq, hqn⟩ := restoreLookupMem hl
    simp only [restoreTbl] at hq ⊢
    obtain ⟨qj, hqj, rfl⟩ := List.mem_map.mp hq
    obtain ⟨q₀, j⟩ := qj
    exact List.mem_append_right _ (List.mem_map.mpr ⟨q₀, List.fst_mem_of_mem_zipIdx hqj, hqn⟩)

/-- A pin's auxiliary name is one of the table's `auxNames`. -/
theorem restoreTbl_aux_mem {p : NestedParts} {st : ElimState} {q : Nat} {qn : NestedPin}
    (hq : st.pins[q]? = some qn) : qn.aux ∈ (restoreTbl p st).auxNames := by
  simp only [restoreTbl]
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨qn, List.mem_of_getElem? hq, rfl⟩))

/-- **THE PIN MAP ANSWERS AT A PIN'S AUXILIARY NAME** (task #315):
with the auxiliary names pairwise distinct, `restoreTbl`'s `pins`
returns the pin the mint recorded, abstracted at the block's
parameters. -/
theorem restoreTbl_pins_lookup {p : NestedParts} {st : ElimState} {q : Nat} {qn : NestedPin}
    (hnd : (st.pins.map (·.aux)).Nodup) (hq : st.pins[q]? = some qn) :
    (restoreTbl p st).pins.lookup qn.aux = some (Expr.abstractRange qn.pin 0 p.nP 0) := by
  simp only [restoreTbl]
  refine restoreLookupOfMem ?_ (List.mem_map.mpr ⟨qn, List.mem_of_getElem? hq, rfl⟩)
  rw [List.map_map]
  exact hnd

/-- **THE RECURSOR MAP DECLINES AT A PIN'S AUXILIARY NAME**
(task #315): its keys are the auxiliary names with `rec` appended, so a
pin's own name is a miss — provided no auxiliary name IS another's
recursor name.  The pin's position (`_hq`) is carried for the caller's
convenience; the shape hypothesis alone settles the lookup. -/
theorem restoreTbl_recMap_lookup_aux {p : NestedParts} {st : ElimState}
    {q : Nat} {qn : NestedPin} (_hq : st.pins[q]? = some qn)
    (hshape : ∀ q' ∈ st.pins, qn.aux ≠ q'.aux.str "rec") :
    (restoreTbl p st).recMap.lookup qn.aux = none := by
  simp only [restoreTbl]
  refine restoreLookupNone ?_
  intro pr hpr
  obtain ⟨qj, hqj, rfl⟩ := List.mem_map.mp hpr
  obtain ⟨q₀, j⟩ := qj
  exact fun hc => hshape q₀ (List.fst_mem_of_mem_zipIdx hqj) hc.symm

/-! ## The pins and the types, aligned

The elimination's mint appends one type and one pin in the same breath,
under the same minted name, and no other step touches either list's
names: `elimLoop` `set`s the type it is at, with its own name, and the
constructors' rewrite only threads the state.  So the pin at `q` is the
type at `k + q`, and the two carry the SAME name — which is what turns
the auxiliary block's `blockNames.Nodup` into a fact about the PINS.
-/

/-- **The elimination's alignment invariant**: the type list is the
given `k` members plus one type per pin, and the pin at `q` is the type
at `k + q`, under the name the mint gave both. -/
def PinsAligned (k : Nat) (st : ElimState) : Prop :=
  st.types.length = k + st.pins.length ∧
  ∀ (q : Nat) (qn : NestedPin), st.pins[q]? = some qn →
    ∃ t, st.types[k + q]? = some t ∧ t.name = qn.aux

/-- An `.error` never succeeds. -/
private theorem alignErrNeOk {α : Type} {e : CheckError} {a : α}
    (h : (Except.error e : CheckM α) = .ok a) : False := by
  simp at h

/-- A declining step never returns a replacement. -/
private theorem alignNoneNeSome {α : Type} {a : α}
    (h : (pure none : CheckM (Option α)) = .ok (some a)) : False := by
  simp [pure, Except.pure] at h

/-- Close a branch the run cannot have taken. -/
local syntax "close_align" : tactic
local macro_rules
  | `(tactic| close_align) =>
    `(tactic| first
        | (exfalso; exact alignErrNeOk (by assumption))
        | (exfalso; exact alignNoneNeSome (by assumption)))

/-- **One mint group** keeps the alignment: `mkCopies` appends the copy
and its pin together, and `mkCopy` names the copy with the pin's own
auxiliary name. -/
theorem mkCopies_aligned {env : Env} {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {I : Name} {base size k : Nat} :
    ∀ {Js : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size Js st = .ok (st', got) →
      PinsAligned k st → PinsAligned k st'
  | [], st, st', got, h, hst => by
    simp only [mkCopies, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hst
  | J :: rest, st, st', got, h, hst => by
    rw [mkCopies] at h
    split at h
    rename_i auxName nextIdx heq
    obtain ⟨copy, hcopy, h⟩ := exceptBind_ok h
    obtain ⟨r, hrec, h⟩ := exceptBind_ok h
    obtain ⟨stM, gotM⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨-, -, hname, -, -, -⟩ := mkCopy_inv hcopy
    obtain ⟨hlen, hpin⟩ := hst
    refine mkCopies_aligned hrec ⟨?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · intro q qn hq
      by_cases hlt : q < st.pins.length
      · rw [List.getElem?_append_left hlt] at hq
        obtain ⟨t, ht, htn⟩ := hpin q qn hq
        refine ⟨t, ?_, htn⟩
        rw [List.getElem?_append_left (by omega)]
        exact ht
      · rw [List.getElem?_append_right (by omega)] at hq
        have hq0 : q - st.pins.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hq).1
          simp only [List.length_cons, List.length_nil] at this
          omega
        have hqe : q = st.pins.length := by omega
        rw [hq0] at hq
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        refine ⟨copy, ?_, ?_⟩
        · rw [List.getElem?_append_right (by omega),
            show k + q - st.types.length = 0 by omega]
          rfl
        · rw [hname, ← hq]

/-- **One occurrence** keeps the alignment: `replaceIfNested` either
passes the state through or mints. -/
theorem replaceIfNested_aligned {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {st st' : ElimState} {e e' : Expr} {k : Nat}
    (h : replaceIfNested env blvls params pbs₀ st e = .ok (some (e', st'))) :
    PinsAligned k st → PinsAligned k st' := by
  unfold replaceIfNested at h
  split at h
  · split at h
    · split at h
      · split at h
        · close_align
        · split at h
          · split at h <;> close_align
          · dsimp only at h
            split at h
            · close_align
            · obtain ⟨nested, -, h⟩ := exceptBind_ok h
              split at h
              · close_align
              · split at h
                · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                    Prod.mk.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  exact id
                · obtain ⟨r, hcop, h⟩ := exceptBind_ok h
                  obtain ⟨stM, gotM⟩ := r
                  split at h
                  · close_align
                  · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨-, rfl⟩ := h
                    exact mkCopies_aligned hcop
      · close_align
    · close_align
  · close_align

/-- The walk returned the state it was given. -/
private theorem elimSameA {st st' : ElimState} {e e' : Expr} {k : Nat}
    (h : (Except.ok (e, st) : CheckM (Expr × ElimState)) = .ok (e', st')) :
    PinsAligned k st → PinsAligned k st' := by
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact id

/-- **The top-down replace only threads the state**, so the alignment
travels through it. -/
theorem replaceAllNested_aligned {env : Env} {blvls : List Level} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs₀ st e = .ok (e', st') →
      PinsAligned k st → PinsAligned k st' := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ | fvar _ _ =>
    intro st st' e' h
    rw [replaceAllNested] at h
    · split at h
      · exact elimSameA h
      · split at h
        · close_align
        · rename_i r heq
          obtain ⟨re, rst⟩ := r
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact replaceIfNested_aligned heq
        · exact elimSameA h
    all_goals (intros; exact Expr.noConfusion ‹_›)
  | app f a ihf iha =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameA h
    · split at h
      · close_align
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_aligned heq
      · split at h
        · close_align
        · rename_i f' st1 heq1
          split at h
          · close_align
          · rename_i a' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun hs => iha heq2 (ihf heq1 hs)
  | lam ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameA h
    · split at h
      · close_align
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_aligned heq
      · split at h
        · close_align
        · rename_i ty' st1 heq1
          split at h
          · close_align
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun hs => ihb heq2 (ihty heq1 hs)
  | forallE ty b m ihty ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameA h
    · split at h
      · close_align
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_aligned heq
      · split at h
        · close_align
        · rename_i ty' st1 heq1
          split at h
          · close_align
          · rename_i b' st2 heq2
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            exact fun hs => ihb heq2 (ihty heq1 hs)
  | letE ty v b ihty ihv ihb =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameA h
    · split at h
      · close_align
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_aligned heq
      · split at h
        · close_align
        · rename_i ty' st1 heq1
          split at h
          · close_align
          · rename_i v' st2 heq2
            split at h
            · close_align
            · rename_i b' st3 heq3
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact fun hs => ihb heq3 (ihv heq2 (ihty heq1 hs))
  | proj s i x ihx =>
    intro st st' e' h
    rw [replaceAllNested] at h
    split at h
    · exact elimSameA h
    · split at h
      · close_align
      · rename_i r heq
        obtain ⟨re, rst⟩ := r
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact replaceIfNested_aligned heq
      · split at h
        · close_align
        · rename_i x' st1 heq1
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact ihx heq1

/-- **One type's constructors** keep the alignment: `elimCtors` only
threads the state. -/
theorem elimCtors_aligned {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ {cs : List (Name × Expr × Nat)} {st st' : ElimState}
      {cs' : List (Name × Expr × Nat)},
      elimCtors env blvls nP params pbs₀ cs st = .ok (cs', st') →
      PinsAligned k st → PinsAligned k st'
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
        exact fun hs => elimCtors_aligned h₂ (replaceAllNested_aligned _ h₁ hs)
      · close_align
    · close_align

/-- **The worklist** keeps the alignment: `elimLoop` `set`s the type it
is at, with the name it already had (`elimCtors` leaves the list's
entries in place), and the constructors' rewrite only threads the
state. -/
private theorem elimLoop_aligned {env : Env} {blvls : List Level} {nP : Nat}
    {params : List Expr} {pbs₀ : List (Expr × BinderMeta)} {k : Nat} :
    ∀ (fuel qhead : Nat) {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      PinsAligned k st → PinsAligned k st' := by
  intro fuel
  induction fuel with
  | zero =>
    intro qhead st st' h
    rw [elimLoop] at h
    close_align
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
      · close_align
      · rename_i cs' st₁ heq
        intro hst
        obtain ⟨hlen, hpin⟩ := elimCtors_aligned heq hst
        have htq₁ : st₁.types[qhead]? = some tq := elimCtors_types_prefix heq qhead tq htq
        refine ih (qhead + 1) h ⟨?_, ?_⟩
        · simp only [List.length_set]
          exact hlen
        · intro q qn hq
          obtain ⟨t, ht, htn⟩ := hpin q qn hq
          by_cases hqe : k + q = qhead
          · refine ⟨{ tq with ctors := cs' }, ?_, ?_⟩
            · rw [hqe, List.getElem?_set_self
                ((List.getElem?_eq_some_iff.mp htq₁).1)]
            · rw [hqe] at ht
              obtain rfl : t = tq := Option.some.inj (ht.symm.trans htq₁)
              exact htn
          · exact ⟨t, by rw [List.getElem?_set_ne (Ne.symm hqe)]; exact ht, htn⟩

/-- **THE ELIMINATION'S PINS ARE ITS COPIES** (task #315): the pin at
`q` is the type at `k + q` of the elimination's list, under the same
minted name — the mint writes both at once, and nothing renames
either. -/
theorem elimNested_aligned {env : Env} {nP : Nat} {lps : List Name}
    {types : List AuxType} {st : ElimState} {k : Nat} (hk : types.length = k)
    (h : elimNested env nP lps types = .ok st) : PinsAligned k st := by
  unfold elimNested at h
  split at h
  · split at h
    · split at h
      · refine elimLoop_aligned _ _ h ⟨by simpa using hk, ?_⟩
        intro q qn hq
        exact absurd hq (by simp)
      · close_align
    · close_align
  · close_align

/-! ## The auxiliary block's names, read at the pins

The auxiliary mutual block is checked by `checkMutualCore`, whose first
guard is `b.blockNames.Nodup` — the members, the constructors and the
recursors of the block are pairwise distinct names.  With the alignment
above, `b.memberNames` IS the elimination's type-name list, so the
block's own guard answers the two questions the restore table asks
about the pins: their auxiliary names are distinct, and none of them is
another's recursor name.
-/

/-- Two equal entries of a `Nodup` list sit at the same index. -/
private theorem nodupIdxEq {L : List Name} (hL : L.Nodup) {u w : Nat} {v : Name}
    (hu : L[u]? = some v) (hw : L[w]? = some v) : u = w := by
  obtain ⟨hu', hu''⟩ := List.getElem?_eq_some_iff.mp hu
  obtain ⟨hw', hw''⟩ := List.getElem?_eq_some_iff.mp hw
  have e1 : List.idxOf v L = u := by rw [← hu'']; exact hL.idxOf_getElem u hu'
  have e2 : List.idxOf v L = w := by rw [← hw'']; exact hL.idxOf_getElem w hw'
  omega

/-- **The auxiliary block's member names are the elimination's type
names** (task #315): `auxBlock` reads one former per type, under the
type's own name. -/
theorem auxBlock_memberNames_eq {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (hb : auxBlock p st = some b) : b.memberNames = st.types.map (·.name) := by
  obtain ⟨-, hform⟩ := auxBlock_former hb
  have hk : b.k = st.types.length := auxBlock_k hb
  refine List.ext_getElem? (fun i => ?_)
  by_cases hlt : i < st.types.length
  · obtain ⟨t, ht⟩ : ∃ t, st.types[i]? = some t := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨nIdx, hfo, -⟩ := hform i t ht
    simp only [MutualBlock.memberNames, List.getElem?_map, hfo, ht, Option.map_some]
  · have h1 : b.memberNames[i]? = none := by
      refine List.getElem?_eq_none ?_
      simp only [MutualBlock.memberNames, List.length_map]
      rw [← MutualBlock.k, hk]
      omega
    have h2 : (st.types.map (·.name))[i]? = none :=
      List.getElem?_eq_none (by simp only [List.length_map]; omega)
    rw [h1, h2]

/-- **THE PINS' AUXILIARY NAMES ARE PAIRWISE DISTINCT** (task #315):
the mint names the copy and its pin together, and the auxiliary block's
own guard (`checkMutualCore`'s `blockNames.Nodup`) says the copies'
names are distinct. -/
theorem nestedPinAux_nodup {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA₀ : List ConstantVal} {st : ElimState} {b : MutualBlock} {envAux : Env}
    (hfA : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (helim : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA₀) = .ok st)
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux) :
    (st.pins.map (·.aux)).Nodup := by
  have hlen0 : (nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [nestedTypes0_length, nestedAnnotFormers_length hfA, NestedParts.k]
  have hal := elimNested_aligned hlen0 helim
  have hnd : b.blockNames.Nodup := (checkMutualCore_inv haux).1
  rw [MutualBlock.blockNames] at hnd
  have hmn : (st.types.map (·.name)).Nodup := by
    rw [← auxBlock_memberNames_eq hb]
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij hc
  have hi' : i < st.pins.length := by simpa using hi
  have hj' : j < st.pins.length := by simpa using hj
  obtain ⟨qi, hqi⟩ : ∃ q, st.pins[i]? = some q := ⟨_, List.getElem?_eq_getElem hi'⟩
  obtain ⟨qj, hqj⟩ : ∃ q, st.pins[j]? = some q := ⟨_, List.getElem?_eq_getElem hj'⟩
  have v1 : (st.pins.map (·.aux))[i] = qi.aux :=
    Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans
      (by simp only [List.getElem?_map, hqi, Option.map_some]))
  have v2 : (st.pins.map (·.aux))[j] = qj.aux :=
    Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans
      (by simp only [List.getElem?_map, hqj, Option.map_some]))
  have hA : qi.aux = qj.aux := by rw [← v1, ← v2]; exact hc
  obtain ⟨ti, hti, htin⟩ := hal.2 i qi hqi
  obtain ⟨tj, htj, htjn⟩ := hal.2 j qj hqj
  have k1 : (st.types.map (·.name))[p.k + i]? = some qi.aux := by
    simp only [List.getElem?_map, hti, Option.map_some, htin]
  have k2 : (st.types.map (·.name))[p.k + j]? = some qi.aux := by
    rw [hA]
    simp only [List.getElem?_map, htj, Option.map_some, htjn]
  exact absurd (nodupIdxEq hmn k1 k2) (by omega)

/-- **NO PIN'S AUXILIARY NAME IS ANOTHER PIN'S RECURSOR NAME**
(task #315): both are names of the auxiliary block — a member's and a
recursor's — and `blockNames.Nodup` keeps the two lists apart. -/
theorem nestedPinAux_ne_rec {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA₀ : List ConstantVal} {st : ElimState} {b : MutualBlock} {envAux : Env}
    (hfA : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (helim : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA₀) = .ok st)
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn) :
    ∀ q' ∈ st.pins, qn.aux ≠ q'.aux.str "rec" := by
  have hlen0 : (nestedTypes0 p fmsA ctorsA₀).length = p.k := by
    rw [nestedTypes0_length, nestedAnnotFormers_length hfA, NestedParts.k]
  have hal := elimNested_aligned hlen0 helim
  have hnd : b.blockNames.Nodup := (checkMutualCore_inv haux).1
  rw [MutualBlock.blockNames] at hnd
  obtain ⟨-, hform⟩ := auxBlock_former hb
  have hk : b.k = st.types.length := auxBlock_k hb
  obtain ⟨t, ht, htn⟩ := hal.2 q qn hq
  obtain ⟨nIdx, hfo, -⟩ := hform (p.k + q) t ht
  have hmem : qn.aux ∈ b.memberNames := by
    refine List.mem_of_getElem? (i := p.k + q) ?_
    simp only [MutualBlock.memberNames, List.getElem?_map, hfo, Option.map_some, htn]
  intro q' hq' hce
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq'
  have hj' : j < st.pins.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨t', ht', htn'⟩ := hal.2 j q' hj
  obtain ⟨nIdx', hfo', -⟩ := hform (p.k + j) t' ht'
  have hrecMem : q'.aux.str "rec" ∈ (List.range b.k).map b.recName := by
    refine List.mem_map.mpr ⟨p.k + j, List.mem_range.mpr ?_, ?_⟩
    · rw [hk, hal.1]
      omega
    · simp only [MutualBlock.recName, List.getD_eq_getElem?_getD, hfo', Option.getD_some, htn']
  exact (List.nodup_append.mp hnd).2.2 _ (List.mem_append_left _ hmem) _ hrecMem hce

/-! ## The table's lookups at a pin, off the run -/

/-- **THE PIN MAP ANSWERS AT A PIN'S AUXILIARY NAME, OFF THE RUN**
(task #315): the distinctness hypothesis of `restoreTbl_pins_lookup` is
a fact of the elimination and its block check. -/
theorem restoreTbl_pins_lookup_run {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA₀ : List ConstantVal} {st : ElimState} {b : MutualBlock} {envAux : Env}
    (hfA : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (helim : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA₀) = .ok st)
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn) :
    (restoreTbl p st).pins.lookup qn.aux = some (Expr.abstractRange qn.pin 0 p.nP 0) :=
  restoreTbl_pins_lookup (nestedPinAux_nodup hfA helim hb haux) hq

/-- **THE RECURSOR MAP DECLINES AT A PIN'S AUXILIARY NAME, OFF THE
RUN** (task #315): the shape hypothesis of
`restoreTbl_recMap_lookup_aux` is a fact of the elimination and its
block check. -/
theorem restoreTbl_recMap_lookup_aux' {env : Env} {p : NestedParts} {F : Nat}
    {fmsA ctorsA₀ : List ConstantVal} {st : ElimState} {b : MutualBlock} {envAux : Env}
    (hfA : nestedAnnotFormers (m := CheckM) (fueledOps mode F) env p.nP p.formers = .ok fmsA)
    (helim : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA₀) = .ok st)
    (hb : auxBlock p st = some b)
    (haux : checkMutualCore (fueledOps mode F) env b none true = .ok envAux)
    {q : Nat} {qn : NestedPin} (hq : st.pins[q]? = some qn) :
    (restoreTbl p st).recMap.lookup qn.aux = none :=
  restoreTbl_recMap_lookup_aux hq (nestedPinAux_ne_rec hfA helim hb haux hq)

end ConLeche
