module

public import ConLeche.Verify.Inductives.NestedElimInv
public import ConLeche.Verify.Abstract
import ConLeche.Verify.AbstractRange
public import ConLeche.Verify.Subst
public import ConLeche.Verify.Inductives.MutualGrouped
-- the auxiliary block's own-constructor count (task #315 M8)
import ConLeche.Verify.Inductives.NestedAuxFormers

public section

/-!
# Glue for the copies' reading (task #315)

Three syntactic facts the nested route's model tier consumes when it
reads a minted copy off the auxiliary block.

* **`mentionsConst_of_constsResolve`** — the resolution guard is a
  superset of the occurrence walk: `Expr.constsResolve` demands every
  `const` node (and every `proj`'s structure name) to be in the
  environment, and `Expr.mentionsConst` finds `n` only at such a node,
  both walks descending into `fvar` annotations alike.  So a resolving
  term that mentions `n` witnesses `n` in the environment.

* **`instSeq_abstractRange_fvs`** — the EXACT open/close roundtrip.
  `Expr.instSeq_abstractRange_erased` (`Verify/EraseAnnots.lean`) only
  gets the roundtrip up to annotations, because the openers' annotations
  need not be the ones the term carries.  Here they are: the hypothesis
  that every `fvar` leaf of the term occurs in the opener list pins each
  leaf's annotation to the opener's own (`fvarConsistent_of_leaves`),
  which is exactly `abstract1_instantiate1`'s side condition.

* **`auxBlock_ownCtors_getElem?`** — a member's own constructor run,
  positionally.  `auxBlock` flattens the elimination's type list into
  `b.ctors`, tagging each constructor with its type's index, so the
  `ownCtors` selection at `mIdx` is the `mIdx`-th type's constructor
  list, in order; under the grouping guard the global index of its
  `j`-th entry is `b.ownOffset mIdx + j`
  (`auxBlock_ctors_getElem?`, the corollary in `b.ctors`).
-/

namespace ConLeche

open Expr

/-! ## (A) The resolution guard sees every mentioned constant -/

/-- **A RESOLVING TERM'S CONSTANTS ARE IN THE ENVIRONMENT** (task
#315): `Expr.constsResolve` and `Expr.mentionsConst` are the same walk
— both descend into `fvar` type annotations, both stop at the same
leaves — and `mentionsConst n` is true only at a node `constsResolve`
requires to be found (`.const n _`, or a `.proj n _ _`'s structure). -/
theorem mentionsConst_of_constsResolve {env : Env} {n : Name} :
    ∀ (e : Expr), e.constsResolve env = true → e.mentionsConst n = true →
      (env.find? n).isSome = true := by
  intro e
  induction e with
  | bvar i => intro _ h; simp [Expr.mentionsConst] at h
  | sort u => intro _ h; simp [Expr.mentionsConst] at h
  | lit l => intro _ h; cases l <;> simp [Expr.mentionsConst] at h
  | const m us =>
    intro hr h
    simp only [Expr.mentionsConst, beq_iff_eq] at h
    subst h
    simpa [Expr.constsResolve] using hr
  | fvar idx ty ih =>
    intro hr h
    exact ih (by simpa [Expr.constsResolve] using hr) (by simpa [Expr.mentionsConst] using h)
  | app f a ihf iha =>
    intro hr h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    exact h.elim (fun h => ihf hr.1 h) (fun h => iha hr.2 h)
  | lam ty b m ihty ihb =>
    intro hr h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    exact h.elim (fun h => ihty hr.1 h) (fun h => ihb hr.2 h)
  | forallE ty b m ihty ihb =>
    intro hr h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    exact h.elim (fun h => ihty hr.1 h) (fun h => ihb hr.2 h)
  | letE ty v b ihty ihv ihb =>
    intro hr h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true] at h
    exact h.elim (fun h => h.elim (fun h => ihty hr.1.1 h) (fun h => ihv hr.1.2 h))
      (fun h => ihb hr.2 h)
  | proj s i sub ih =>
    intro hr h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.mentionsConst, Bool.or_eq_true, beq_iff_eq] at h
    refine h.elim (fun h => ?_) (fun h => ih hr.2 h)
    subst h
    exact hr.1

/-! ## (B) The exact open/close roundtrip -/

/-- Leafwise consistency is `fvarConsistent`: `Expr.fvarLeaves` lists
every reachable `fvar` node, and `Expr.fvarConsistent d ty` asks of
exactly those with index `d` that they carry `ty`. -/
theorem fvarConsistent_of_leaves {d : Nat} {ty : Expr} :
    ∀ (e : Expr), (∀ l ∈ e.fvarLeaves, l.1 = d → l.2 = ty) →
      Expr.fvarConsistent d ty e := by
  intro e
  induction e with
  | bvar i => intro _; trivial
  | sort u => intro _; trivial
  | const m us => intro _; trivial
  | lit l => intro _; trivial
  | fvar idx ty' ih =>
    intro h
    exact fun hidx => h (idx, ty') (by rw [Expr.fvarLeaves]; exact List.mem_cons_self) hidx
  | app f a ihf iha =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨ihf (fun l hl => h l (List.mem_append_left _ hl)),
      iha (fun l hl => h l (List.mem_append_right _ hl))⟩
  | lam t b m iht ihb =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨iht (fun l hl => h l (List.mem_append_left _ hl)),
      ihb (fun l hl => h l (List.mem_append_right _ hl))⟩
  | forallE t b m iht ihb =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ⟨iht (fun l hl => h l (List.mem_append_left _ hl)),
      ihb (fun l hl => h l (List.mem_append_right _ hl))⟩
  | letE t v b iht ihv ihb =>
    intro h
    rw [Expr.fvarLeaves] at h
    refine ⟨?_, ?_, ?_⟩
    · exact iht (fun l hl => h l (List.mem_append_left _ (List.mem_append_left _ hl)))
    · exact ihv (fun l hl => h l (List.mem_append_left _ (List.mem_append_right _ hl)))
    · exact ihb (fun l hl => h l (List.mem_append_right _ hl))
  | proj s i sub ih =>
    intro h
    rw [Expr.fvarLeaves] at h
    exact ih h

/-- The roundtrip, with the openers' annotations pinned by a
consistency hypothesis at every opener. -/
private theorem instSeq_abstractRange_consistent :
    ∀ (k : Nat) (fvs : List Expr) (e : Expr) (c : Nat), fvs.length = k →
      (∀ j, j < k → ∃ ty, fvs[j]? = some (Expr.fvar j ty)) →
      (∀ (j : Nat) (ty : Expr), fvs[j]? = some (Expr.fvar j ty) →
        Expr.fvarConsistent j ty e) →
      e.looseBVarsBounded c = true →
      Expr.instSeq fvs (k + c - 1) (e.abstractRange 0 k c) = e := by
  intro k
  induction k with
  | zero =>
    intro fvs e c hlen _ _ _
    obtain rfl : fvs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [ConLeche.abstractRange_zero]
    rfl
  | succ k ih =>
    intro fvs e c hlen hidx hcons hb
    obtain ⟨fvs', x, rfl⟩ : ∃ fvs' x, fvs = fvs' ++ [x] := by
      rcases List.eq_nil_or_concat fvs with rfl | ⟨l', b, rfl⟩
      · simp at hlen
      · exact ⟨l', b, by simp⟩
    have hlen' : fvs'.length = k := by simpa using hlen
    have hbound : ∀ (j : Nat) (v : Expr), fvs'[j]? = some v → j < k := by
      intro j v hj
      rcases Nat.lt_or_ge j fvs'.length with h | h
      · omega
      · rw [List.getElem?_eq_none h] at hj; exact nomatch hj
    have hsub : ∀ (j : Nat) (v : Expr), fvs'[j]? = some v → (fvs' ++ [x])[j]? = some v := by
      intro j v hj
      rw [List.getElem?_append_left (by have := hbound j v hj; omega)]
      exact hj
    have hlast : (fvs' ++ [x])[k]? = some x := by
      rw [List.getElem?_append_right (by omega), hlen']
      simp
    obtain ⟨tyk, htyk⟩ := hidx k (by omega)
    obtain rfl : x = Expr.fvar k tyk := by
      rw [hlast] at htyk; exact Option.some.inj htyk
    -- the abstraction peels the outermost opener first
    rw [ConLeche.abstractRange_succ, Expr.instSeq_append, hlen']
    have hstep : k + 1 + c - 1 - k = c := by omega
    rw [hstep]
    have hb' : (e.abstract1 (0 + k) c).looseBVarsBounded (c + 1) = true :=
      ConLeche.looseBVarsBounded_abstract1 e c hb
    have hih := ih fvs' (e.abstract1 (0 + k) c) (c + 1) hlen'
      (fun j hj => by
        obtain ⟨ty, hty⟩ := hidx j (by omega)
        refine ⟨ty, ?_⟩
        rw [← List.getElem?_append_left (l₂ := [Expr.fvar k tyk]) (by omega)]
        exact hty)
      (fun j ty hj =>
        ConLeche.fvarConsistent_abstract1 (by have := hbound j _ hj; omega) e c
          (hcons j ty (hsub j _ hj)))
      hb'
    rw [show k + (c + 1) - 1 = k + 1 + c - 1 from by omega] at hih
    rw [hih]
    show (e.abstract1 (0 + k) c).instantiate1 (Expr.fvar k tyk) c = e
    rw [show (0 : Nat) + k = k from by omega]
    exact ConLeche.abstract1_instantiate1 e c (hcons k tyk hlast) hb

/-- **THE EXACT OPEN/CLOSE ROUNDTRIP** (task #315): closing the leading
`nP` free variables of `e` ABOVE `c` loose binders and re-opening them
at any variable list
whose `j`-th entry is an `fvar` with index `j` returns `e` ON THE NOSE —
not merely up to annotations — as soon as every `fvar` leaf of `e`
occurs in that list: the occurrence pins each leaf's annotation to the
opener's own, which is `abstract1_instantiate1`'s side condition. -/
theorem instSeq_abstractRange_fvs_at : ∀ (nP c : Nat) (fvs : List Expr) (e : Expr),
    e.looseBVarsBounded c = true → fvs.length = nP →
    (∀ j, j < nP → ∃ ty, fvs[j]? = some (Expr.fvar j ty)) →
    (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) →
    Expr.instSeq fvs (nP + c - 1) (e.abstractRange 0 nP c) = e := by
  intro nP c fvs e hb hlen hidx hlv
  have hcons : ∀ (j : Nat) (ty : Expr), fvs[j]? = some (Expr.fvar j ty) →
      Expr.fvarConsistent j ty e := by
    intro j ty hj
    refine fvarConsistent_of_leaves e (fun l hl hl1 => ?_)
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (hlv l hl)
    have hilt : i < nP := by
      have hlt : i < fvs.length := by
        rcases Nat.lt_or_ge i fvs.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hi; exact nomatch hi
      omega
    obtain ⟨tyi, htyi⟩ := hidx i hilt
    rw [hi] at htyi
    have h12 : l.1 = i ∧ l.2 = tyi := by simpa using htyi
    have hij : i = j := by rw [← h12.1, hl1]
    subst hij
    rw [hj] at hi
    have hfin : Expr.fvar i ty = Expr.fvar l.1 l.2 := Option.some.inj hi
    exact (by simpa using hfin : i = l.1 ∧ ty = l.2).2.symm
  exact instSeq_abstractRange_consistent nP fvs e c hlen hidx hcons hb

/-- The round trip at cut `0`: `instSeq_abstractRange_fvs_at`'s
original spelling, which every earlier consumer calls. -/
theorem instSeq_abstractRange_fvs (nP : Nat) (fvs : List Expr) (e : Expr)
    (hb : e.looseBVarsBounded 0 = true) (hlen : fvs.length = nP)
    (hidx : ∀ j, j < nP → ∃ ty, fvs[j]? = some (Expr.fvar j ty))
    (hlv : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs) :
    Expr.instSeq fvs (nP - 1) (e.abstractRange 0 nP 0) = e := by
  have := instSeq_abstractRange_fvs_at nP 0 fvs e hb hlen hidx hlv
  rwa [show nP + 0 - 1 = nP - 1 from by omega] at this

/-- A stripped telescope's binder domain is a SUBTERM of the type: its
`fvar` leaves are among the whole type's.  (`Expr.stripPis` peels a
`∀` without instantiating, so each domain stands where it was.) -/
theorem stripPis_binder_leaves :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis k = some (bs, body) →
      ∀ (i : Nat) (b : Expr × BinderMeta), bs[i]? = some b →
        ∀ lf ∈ b.1.fvarLeaves, lf ∈ e.fvarLeaves := by
  intro k
  induction k with
  | zero =>
    intro e bs body h i b hb
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hb
    simp at hb
  | succ k ih =>
    intro e bs body h i b hb
    match e, h with
    | .forallE ty bo m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, -⟩ : (ty, m) :: bs' = bs ∧ body' = body := by simpa using heq
      intro lf hlf
      rw [Expr.fvarLeaves]
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        exact List.mem_append_left _ hlf
      | succ i =>
        simp only [List.getElem?_cons_succ] at hb
        exact List.mem_append_right _ (ih hstrip i b hb lf hlf)

/-! ## (C) A member's own constructor run, positionally -/

/-- The global-index tagging is invisible to the second component: the
selection `MutualBlock.ownCtors` makes, read through `Prod.snd`, is the
plain filter. -/
private theorem zipIdxSel_map_snd (mm : Nat) :
    ∀ (l : List MutualCtor) (s : Nat),
      (((l.zipIdx s).map fun (c, J) => (J, c)).filter
        fun (_, c) => c.member == mm).map Prod.snd
        = l.filter fun c => c.member == mm := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons c l ih =>
    intro s
    by_cases hc : c.member = mm
    · simp [List.zipIdx_cons, hc, ih (s + 1)]
    · simp [List.zipIdx_cons, hc, ih (s + 1)]

private theorem ownCtors_map_snd (b : MutualBlock) (mm : Nat) :
    (b.ownCtors mm).map Prod.snd = b.ctors.filter fun c => c.member == mm :=
  zipIdxSel_map_snd mm b.ctors 0

/-- Below a group's index nothing is selected: `auxBlock` tags every
constructor of the type at index `i` with `i`. -/
private theorem auxCtorsFlat_filter_nil {lps : List Name} {mm : Nat} :
    ∀ (L : List AuxType) (s : Nat), mm < s →
      (((L.zipIdx s).map fun (t, mIdx) =>
          t.ctors.map fun c =>
            (⟨⟨c.1, lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten).filter
        (fun c => c.member == mm) = [] := by
  intro L
  induction L with
  | nil => intro s _; rfl
  | cons a L ih =>
    intro s hs
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.filter_append,
      ih (s + 1) (by omega), List.append_nil]
    refine List.filter_eq_nil_iff.mpr (fun c hc => ?_)
    obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
    simp only [beq_iff_eq]
    omega

/-- **The tagged flattening IS the group**: the constructors of the
flattened, index-tagged type list whose tag is `s + d` are exactly the
`d`-th type's, in the `d`-th type's own order. -/
private theorem auxCtorsFlat_filter_eq {lps : List Name} {mm : Nat} :
    ∀ (L : List AuxType) (s d : Nat) (t : AuxType), L[d]? = some t → mm = s + d →
      ((((L.zipIdx s).map fun (t, mIdx) =>
          t.ctors.map fun c =>
            (⟨⟨c.1, lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten).filter
        fun c => c.member == mm)
        = t.ctors.map fun c => (⟨⟨c.1, lps, c.2.1⟩, c.2.2, mm⟩ : MutualCtor) := by
  intro L
  induction L with
  | nil => intro s d t ht _; exact absurd ht (by simp)
  | cons a L ih =>
    intro s d t ht hmm
    simp only [List.zipIdx_cons, List.map_cons, List.flatten_cons, List.filter_append]
    cases d with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      obtain rfl : s = mm := by omega
      rw [← ht]
      have h1 : ∀ c ∈ (a.ctors.map fun c =>
          (⟨⟨c.1, lps, c.2.1⟩, c.2.2, s⟩ : MutualCtor)), (c.member == s) = true := by
        intro c hc
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
        simp
      rw [List.filter_eq_self.mpr h1, auxCtorsFlat_filter_nil L (s + 1) (by omega)]
      simp
    | succ d =>
      simp only [List.getElem?_cons_succ] at ht
      have h0 : ((a.ctors.map fun c =>
          (⟨⟨c.1, lps, c.2.1⟩, c.2.2, s⟩ : MutualCtor)).filter
            fun c => c.member == mm) = [] := by
        refine List.filter_eq_nil_iff.mpr (fun c hc => ?_)
        obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
        simp only [beq_iff_eq]
        omega
      rw [h0, List.nil_append]
      exact ih (s + 1) d t ht (by omega)

/-- **A MEMBER'S OWN CONSTRUCTOR RUN, POSITIONALLY** (task #315):
`auxBlock` flattens the elimination's type list into `b.ctors`, tagging
each constructor with its type's index, so the `ownCtors` selection at
`mIdx` is the `mIdx`-th type's constructor list in its own order — and
under the install's grouping guard the `j`-th entry's GLOBAL index is
`b.ownOffset mIdx + j`. -/
theorem auxBlock_ownCtors_getElem? {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (hb : auxBlock p st = some b) (hg : mutualCtorsGrouped b.ctors = true) :
    ∀ (mIdx j : Nat) (t : AuxType) (c : Name × Expr × Nat),
      st.types[mIdx]? = some t → t.ctors[j]? = some c →
      (b.ownCtors mIdx)[j]? =
        some (b.ownOffset mIdx + j, (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)) := by
  intro mIdx j t c ht hcj
  obtain ⟨-, -, -, hct⟩ := auxBlock_fields hb
  have hsnd : (b.ownCtors mIdx).map Prod.snd
      = t.ctors.map fun c => (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor) := by
    rw [ownCtors_map_snd, hct]
    exact auxCtorsFlat_filter_eq st.types 0 mIdx t ht (by omega)
  have hmap : ((b.ownCtors mIdx)[j]?).map Prod.snd
      = some (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor) := by
    rw [← List.getElem?_map, hsnd, List.getElem?_map, hcj]
    rfl
  cases hown : (b.ownCtors mIdx)[j]? with
  | none => rw [hown] at hmap; exact nomatch hmap
  | some q =>
    obtain ⟨J, mc⟩ := q
    rw [hown] at hmap
    obtain rfl : mc = (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor) :=
      Option.some.inj hmap
    obtain rfl : J = b.ownOffset mIdx + j := ownCtors_getElem?_idx hg hown
    rfl

/-- The same reading in the block's own constructor list: the corollary
`checkMutualCore`'s consumers take, the position `b.ownOffset mIdx + j`
being the one the recursor generators index by. -/
theorem auxBlock_ctors_getElem? {p : NestedParts} {st : ElimState} {b : MutualBlock}
    (hb : auxBlock p st = some b) (hg : mutualCtorsGrouped b.ctors = true) :
    ∀ (mIdx j : Nat) (t : AuxType) (c : Name × Expr × Nat),
      st.types[mIdx]? = some t → t.ctors[j]? = some c →
      b.ctors[b.ownOffset mIdx + j]? =
        some (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor) := by
  intro mIdx j t c ht hcj
  exact (ownCtors_getElem?_ctors (auxBlock_ownCtors_getElem? hb hg mIdx j t c ht hcj)).1

/-! ## The block's own constructors, positionally (task #315 M8)

The nested route's SKELETON is a function of the recognised block, so
the walk has to say that member `m`'s auxiliary constructors are `m`'s
own constructors of the stream — names and field counts, in order.
The elimination's input carries them (`nestedTypes0` selects by the
tag), the elimination keeps them (`elimNested_types_prefix` preserves
exactly the `(name, nF)` pairs), and `auxBlock` tags them back
(`auxBlock_ownCtors_getElem?`). -/

/-- The elimination's input at a member: the tag selection over the
zipped annotated constructors is the block's own selection, read at
the declared names. -/
private theorem nestedTypes0_ctors_pairs {m : Nat} :
    ∀ (cs : List MutualCtor) (csA : List ConstantVal),
      csA.map (·.name) = cs.map (·.cv.name) →
      ((cs.zip csA).filterMap (fun x =>
          if x.1.member == m then some (x.2.name, x.2.type, x.1.nF) else none)).map
            (fun c => (c.1, c.2.2))
        = (cs.filter (fun c => c.member == m)).map (fun c => (c.cv.name, c.nF))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, cA :: csA, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.filterMap_cons, List.filter_cons]
    by_cases hm : (c.member == m) = true
    · simp only [hm, if_pos, List.map_cons, h.1]
      exact congrArg _ (nestedTypes0_ctors_pairs cs csA h.2)
    · simp only [hm, Bool.false_eq_true]
      exact nestedTypes0_ctors_pairs cs csA h.2

/-- **MEMBER `m`'s AUXILIARY CONSTRUCTORS ARE ITS OWN** (task #315 M8):
the auxiliary block's `ownCtors m` carries the stream's own
constructor names and field counts for member `m`, in declaration
order. -/
theorem auxBlock_ownCtors_pairs {env : Env} {p : NestedParts}
    {fmsA ctorsA : List ConstantVal} {st : ElimState} {b : MutualBlock}
    (hnames : ctorsA.map (·.name) = p.ctors.map (·.cv.name))
    (he : elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA) = .ok st)
    (hb : auxBlock p st = some b) (hg : mutualCtorsGrouped b.ctors = true)
    {m : Nat} {t₀ : AuxType} (ht₀ : (nestedTypes0 p fmsA ctorsA)[m]? = some t₀) :
    (b.ownCtors m).map (fun x => (x.2.cv.name, x.2.nF))
      = (p.ctors.filter (fun c => c.member == m)).map (fun c => (c.cv.name, c.nF)) := by
  obtain ⟨t, ht, -, -, -, hct⟩ := elimNested_types_prefix he m t₀ ht₀
  have hpairs : t.ctors.map (fun c => (c.1, c.2.2))
      = (p.ctors.filter (fun c => c.member == m)).map (fun c => (c.cv.name, c.nF)) := by
    rw [hct]
    have h0 : t₀.ctors = (p.ctors.zip ctorsA).filterMap (fun x =>
        if x.1.member == m then some (x.2.name, x.2.type, x.1.nF) else none) := by
      unfold nestedTypes0 at ht₀
      rw [List.getElem?_map, List.getElem?_zipIdx] at ht₀
      cases hf : fmsA[m]? with
      | none => rw [hf] at ht₀; simp at ht₀
      | some cvT =>
        rw [hf] at ht₀
        simp only [Nat.zero_add, Option.map_some, Option.some.injEq] at ht₀
        rw [← ht₀]
    rw [h0]
    exact nestedTypes0_ctors_pairs p.ctors ctorsA hnames
  have hlen : (b.ownCtors m).length = t.ctors.length := auxBlock_ownCtors_length hb m t ht
  have hmap : (b.ownCtors m).map (fun x => (x.2.cv.name, x.2.nF))
      = t.ctors.map (fun c => (c.1, c.2.2)) := by
    refine List.ext_getElem? ?_
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    cases hcj : t.ctors[j]? with
    | some c => rw [auxBlock_ownCtors_getElem? hb hg m j t c ht hcj]; rfl
    | none =>
      have hj : t.ctors.length ≤ j := List.getElem?_eq_none_iff.mp hcj
      rw [List.getElem?_eq_none_iff.mpr (by omega)]
      rfl
  rw [hmap]
  exact hpairs

end ConLeche
