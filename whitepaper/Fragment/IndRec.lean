module

public import Fragment.IndSem

@[expose] public section

/-!
# The model of an inductive block: the recursor

**The recursor** is a function of the parameters, the motive, the
minors, the indices and the major, `recSem`.  Its **graph**
`RecGraph` is a least fixed point on predicates (`Lfp`, `IndLib.lean`
— the ambient logic's impredicative `Prop` provides it outright): "the
value at the constructor value of fitting fields is the constructor's
minor applied to the fields and to the inductive hypotheses, where
each hypothesis is the recursor's value at the field (through its own
telescope at a reflexive field)".  The graph is **total** on the
family (`RecGraph_total`, by induction over the family, which is the
set-theoretic least fixed point's induction, `Fam_induction`) and
**single-valued** (`RecGraph_fun`, by induction over the graph): above
a proposition a member is the tagged tuple of its fields, which decode
it uniquely (tags and tuples are injective); at a proposition the
major is the point and every instance decodes it, so the subsingleton
criterion (`Uniq`, discharged in `Uniq.lean`) is what makes the
decodings agree — the one sort-dependent fact.  Together that is the
recursion theorem; `recSem` chooses the value, and the ι law follows
(`recSem_eq`).  The recursor's **typing**, that its value lies in the
motive at the indices and the major, is again induction over the
family, from the minors' typing (`recSem_mem`).

Con-leche: the recursor as the single value of its graph, one
mechanism for every sort and regime (`GraphRecKit.exu`,
`ConLeche/SetModel/GraphRec.lean`: `Dec` the decodings, `huniq` the
sort-dependent fact — `huniq_of_dec` by injectivity above a
proposition and by the subsingleton criterion at one — and `ind` the
block's own induction; `Semantics/Tower/BlockRecTower.lean`).
-/

namespace Fragment
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- **Uniqueness of decodings**: at a proposition, two decodings of a
member of the fibre at fitting parameters are equal — what the
subsingleton criterion buys (`Uniq.lean`).  Con-leche: `huniq` of
`GraphRecKit`, in the regime SQ. -/
noncomputable def Uniq : Prop :=
  S.z ls = true → ∀ ps : List V, FitsVals M (S.ψ ls) base S.params ps →
    ∀ (is : List V) (x x' : V), S.Mem M ls ps is x → S.Mem M ls ps is x' → x = x'

variable (q : Bool)

/-- **An inductive hypothesis' value** relative to a graph `R`: at a
reflexive field, the abstraction over the field's telescope of `R`'s
values at the field's index expressions and the field applied to the
telescope's variables (at a recursive field — the telescope empty —
just `R`'s value at the field). -/
noncomputable def IhOk (R : RecP V) (ps : List V) (m : V) (mins fs : List V) : Nat × Field → V → Prop
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ∃ g : (Nat → V) → V, ih = lamCtx M (S.ψ ls) q env tele g ∧
      ∀ ys, FitsVals M (S.ψ ls) env tele ys →
        R ps m mins (S.idxVals M ls (consList ys env) es) (appList (fieldVal fs k) ys.reverse)
          (g (consList ys env))
  | (_, .ordinary _), _ => False
  | (_, .container), _ => False

/-- **The operator** whose least fixed point is the recursor's graph:
at the constructor value of fitting fields, the value is the
constructor's minor at the fields and the inductive hypotheses.
Con-leche: the graph functor `gStep` (`GraphRec.lean`). -/
noncomputable def rstep (R : RecP V) (ps : List V) (m : V) (mins is : List V) (t v : V) : Prop :=
  ∃ j c fs ihs, S.ctors[j]? = some c ∧ S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs ∧
    is = S.idxVals M ls (consList fs (envP ps)) c.idx ∧ t = S.ctorVal ls j fs ∧
    ListRel (S.IhOk M ls q R ps m mins fs) c.recFields ihs ∧
    v = appList (S.minorAt mins j) (fs.reverse ++ ihs)

/-- The operator on sextuples. -/
noncomputable def rstepT (R : List V × V × List V × List V × V × V → Prop)
    (t : List V × V × List V × List V × V × V) : Prop :=
  S.rstep M ls q (fun ps m mins is x v => R (ps, m, mins, is, x, v))
    t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2

/-- **The recursor's graph**: the least fixed point of `rstep`.
Con-leche: `gGraph`. -/
noncomputable def RecGraph (ps : List V) (m : V) (mins is : List V) (t v : V) : Prop :=
  Lfp (S.rstepT M ls q) (ps, m, mins, is, t, v)

theorem IhOk_mono {R R' : RecP V} (h : ∀ ps m mins is x v, R ps m mins is x v → R' ps m mins is x v)
    (ps : List V) (m : V) (mins fs : List V) :
    ∀ (kf : Nat × Field) (ih : V),
      S.IhOk M ls q R ps m mins fs kf ih → S.IhOk M ls q R' ps m mins fs kf ih := by
  intro kf ih hh
  match kf, hh with
  | (_, .ordinary _), hh => exact hh.elim
  | (_, .container), hh => exact hh.elim
  | (_, .reflexive _ _), ⟨g, hg, hall⟩ => exact ⟨g, hg, fun ys hys => h _ _ _ _ _ _ (hall ys hys)⟩

theorem rstepT_mono : Mono (S.rstepT M ls q) := by
  intro R R' h t hs
  obtain ⟨j, c, fs, ihs, hc, hfit, his, hx, hihs, hv⟩ := hs
  exact ⟨j, c, fs, ihs, hc, hfit, his, hx,
    ListRel.mono (S.IhOk_mono M ls q (fun ps m mins is x v => h (ps, m, mins, is, x, v)) _ _ _ _)
      hihs, hv⟩

theorem RecGraph_intro {ps : List V} {m : V} {mins is : List V} {t v : V}
    (h : S.rstep M ls q (S.RecGraph M ls q) ps m mins is t v) :
    S.RecGraph M ls q ps m mins is t v :=
  Lfp.closed (S.rstepT_mono M ls q) h

theorem RecGraph_elim {ps : List V} {m : V} {mins is : List V} {t v : V}
    (h : S.RecGraph M ls q ps m mins is t v) :
    S.rstep M ls q (S.RecGraph M ls q) ps m mins is t v :=
  Lfp.unfold (S.rstepT_mono M ls q) h

theorem RecGraph_ind {P : RecP V}
    (h : ∀ ps m mins is t v,
      S.rstep M ls q (fun ps m mins is t v => S.RecGraph M ls q ps m mins is t v ∧ P ps m mins is t v)
        ps m mins is t v → P ps m mins is t v)
    {ps : List V} {m : V} {mins is : List V} {t v : V} (hg : S.RecGraph M ls q ps m mins is t v) :
    P ps m mins is t v :=
  Lfp.induction (S.rstepT_mono M ls q)
    (P := fun t => P t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2)
    (fun _ ht => h _ _ _ _ _ _ ht) hg

/-- **Two decodings of one value agree**: above a proposition the
value is the tagged tuple of either (tags and tuples are injective);
at a proposition by uniqueness of decodings. -/
theorem decode_unique (hu : S.Uniq M ls) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps)
    {is : List V} {j j' : Nat} {c c' : CtorSpec} {fs fs' : List V}
    (hc : S.ctors[j]? = some c) (hc' : S.ctors[j']? = some c')
    (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs)
    (hfit' : S.FitsFields M ls (S.Fam M ls ps) ps c'.fields fs')
    (his : is = S.idxVals M ls (consList fs (envP ps)) c.idx)
    (his' : is = S.idxVals M ls (consList fs' (envP ps)) c'.idx)
    (ht : S.ctorVal ls j fs = S.ctorVal ls j' fs') : j = j' ∧ fs = fs' := by
  have key : tag (S.tagOf j) (tuple fs.reverse) = tag (S.tagOf j') (tuple fs'.reverse) := by
    cases hz : S.z ls with
    | false =>
      unfold ctorVal at ht
      rw [hz] at ht
      simpa using ht
    | true =>
      exact hu hz ps hp is _ _ ⟨j, c, fs, hc, hfit, his, rfl⟩ ⟨j', c', fs', hc', hfit', his', rfl⟩
  obtain ⟨hjj, hfs⟩ := tag_inj key
  refine ⟨?_, List.reverse_inj.mp (tuple_inj hfs)⟩
  simp only [tagOf] at hjj
  omega

/-- **Single-valuedness of the graph**: two values at one major come
from one decoding, and their inductive hypotheses agree by induction
over the graph.  Con-leche: the uniqueness half of `GraphRecKit.exu`. -/
theorem RecGraph_fun (hu : S.Uniq M ls) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps)
    {m : V} {mins is : List V} {t v v' : V}
    (h : S.RecGraph M ls q ps m mins is t v) (h' : S.RecGraph M ls q ps m mins is t v') : v = v' := by
  refine S.RecGraph_ind M ls q
    (P := fun ps m mins is t v => FitsVals M (S.ψ ls) base S.params ps →
      ∀ v', S.RecGraph M ls q ps m mins is t v' → v = v') ?_ h hp v' h'
  intro ps m mins is t v hs hp v' h'
  obtain ⟨j, c, fs, ihs, hc, hfit, his, ht, hihs, hv⟩ := hs
  obtain ⟨j', c', fs', ihs', hc', hfit', his', ht', hihs', hv'⟩ := S.RecGraph_elim M ls q h'
  obtain ⟨rfl, rfl⟩ := S.decode_unique M ls hu hp hc hc' hfit hfit' his his' (ht.symm.trans ht')
  rw [hc] at hc'
  cases hc'
  subst hv hv'
  congr 2
  refine ListRel.unique ?_ hihs hihs'
  intro kf ih ih' h1 h2
  match kf, h1, h2 with
  | (_, .ordinary _), h1, _ => exact h1.elim
  | (_, .container), h1, _ => exact h1.elim
  | (_, .reflexive _ _), ⟨_, hg1, hg⟩, ⟨_, hg1', hg'⟩ =>
    rw [hg1, hg1']
    exact lamCtx_congr M _ fun ys hys => (hg ys hys).2 hp _ (hg' ys hys)

/-- **The recursor's semantic value** at parameters, motive, minors,
indices and the major: the one the graph relates, if any.
Con-leche: `recSel`, the graph's selector. -/
noncomputable def recSem (ps : List V) (m : V) (mins is : List V) (t : V) : V :=
  open Classical in
  if h : ∃ v, S.RecGraph M ls q ps m mins is t v then Classical.choose h else pt

theorem recSem_eq_of (hu : S.Uniq M ls) {ps : List V} (hp : FitsVals M (S.ψ ls) base S.params ps)
    {m : V} {mins is : List V} {t v : V} (h : S.RecGraph M ls q ps m mins is t v) :
    S.recSem M ls q ps m mins is t = v := by
  unfold recSem
  rw [dite_eq_left ⟨v, h⟩]
  exact S.RecGraph_fun M ls q hu hp (Classical.choose_spec ⟨v, h⟩) h

theorem RecGraph_recSem {ps : List V} {m : V} {mins is : List V} {t : V}
    (h : ∃ v, S.RecGraph M ls q ps m mins is t v) :
    S.RecGraph M ls q ps m mins is t (S.recSem M ls q ps m mins is t) := by
  unfold recSem
  rw [dite_eq_left h]
  exact Classical.choose_spec h

/-- **The inductive hypotheses' semantic values**, one per reflexive
field: the recursor at the field, through the field's telescope. -/
noncomputable def ihSem (ps : List V) (m : V) (mins fs : List V) : Nat × Field → V
  | (k, .reflexive tele es) =>
    let env := consList (earlier fs k) (envP ps)
    lamCtx M (S.ψ ls) q env tele fun ρ' =>
      S.recSem M ls q ps m mins (S.idxVals M ls ρ' es)
        (appList (fieldVal fs k) (readEnv tele.length ρ').reverse)
  | (_, .ordinary _) => pt
  | (_, .container) => pt

/-- **Totality of the graph on the family** (with single-valuedness,
the recursion theorem): by induction over the family — at a
constructor instance over the family's separation by "the graph has a
value", every application of a reflexive field has one, and the
inductive hypotheses' semantic values build the instance's.
Con-leche: the existence half of `GraphRecKit.exu`, by `ind`. -/
theorem RecGraph_total {ps : List V} (hpl : S.nest = none) (hnr : S.NoRecDep)
    (hb : S.DomsBounded M ls ps)
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) (m : V) (mins : List V) :
    ∃ v, S.RecGraph M ls q ps m mins is t v := by
  have hco := S.contOk_of_plain M ls hpl ps
  revert m mins
  refine S.Fam_induction M ls hnr hb hco
    (fun is t => ∀ m mins, ∃ v, S.RecGraph M ls q ps m mins is t v) ?_ is t ht
  intro is t hs m mins
  obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
  have hfitF := S.FitsFields_of_sep M ls hco _ hfit
  suffices hihs : ListRel (S.IhOk M ls q (S.RecGraph M ls q) ps m mins fs) c.recFields
      (c.recFields.map (S.ihSem M ls q ps m mins fs)) from
    ⟨_, S.RecGraph_intro M ls q ⟨j, c, fs, _, hc, hfitF, his, rfl, hihs, rfl⟩⟩
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container =>
    rw [S.fieldSet_container_none M ls hpl] at hget
    exact absurd hget (not_mem_empty _)
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhOk, ihSem]
    refine ⟨_, rfl, ?_⟩
    intro ys hys
    have hlen := FitsVals_length M _ hys
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
    simp only [readEnv_consList hlen]
    exact S.RecGraph_recSem M ls q ((mem_sep.mp hmem).2 m mins)

/-- The inductive hypotheses' semantic values are what the graph
demands. -/
theorem IhOk_ihSem {ps : List V} (hpl : S.nest = none) (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    {c : CtorSpec} {fs : List V} (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs)
    (m : V) (mins : List V) :
    ListRel (S.IhOk M ls q (S.RecGraph M ls q) ps m mins fs) c.recFields
      (c.recFields.map (S.ihSem M ls q ps m mins fs)) := by
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container =>
    rw [S.fieldSet_container_none M ls hpl] at hget
    exact absurd hget (not_mem_empty _)
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhOk, ihSem]
    refine ⟨_, rfl, ?_⟩
    intro ys hys
    have hlen := FitsVals_length M _ hys
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
    simp only [readEnv_consList hlen]
    exact S.RecGraph_recSem M ls q (S.RecGraph_total M ls q hpl hnr hb hmem m mins)

/-- **The ι equation**: at a constructor value whose fields fit the
family, the recursor is the minor at the fields and the inductive
hypotheses' values.  Con-leche: `GraphRecKit.rec_eq`. -/
theorem recSem_eq {ps : List V} (hpl : S.nest = none) (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hu : S.Uniq M ls)
    (hp : FitsVals M (S.ψ ls) base S.params ps) {j : Nat} {c : CtorSpec} {fs : List V}
    (hc : S.ctors[j]? = some c) (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs)
    (m : V) (mins : List V) :
    S.recSem M ls q ps m mins (S.idxVals M ls (consList fs (envP ps)) c.idx) (S.ctorVal ls j fs)
      = appList (S.minorAt mins j)
          (fs.reverse ++ c.recFields.map (S.ihSem M ls q ps m mins fs)) :=
  S.recSem_eq_of M ls q hu hp (S.RecGraph_intro M ls q
    ⟨j, c, fs, _, hc, hfit, rfl, rfl, S.IhOk_ihSem M ls q hpl hnr hb hfit m mins, rfl⟩)

/-! ### The recursor's typing -/

/-- An inductive hypothesis' value lies in the motive at the field's
indices and the field (through the telescope at a reflexive field). -/
noncomputable def IhTyped (ps : List V) (m : V) (fs : List V) : Nat × Field → V → Prop
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ih ∈ˢ piCtx M (S.ψ ls) q env tele fun ρ' =>
      appList m ((S.idxVals M ls ρ' es).reverse ++
        [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])
  | (_, .ordinary _), _ => True
  | (_, .container), _ => False

/-- **A minor's typing**: at fitting fields and typed inductive
hypotheses, the minor's value lies in the motive at the constructor's
index expressions and its value. -/
noncomputable def MinorOk (ps : List V) (m : V) (mins : List V) (j : Nat) (c : CtorSpec) : Prop :=
  ∀ fs, S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs →
    ∀ ihs, ListRel (S.IhTyped M ls q ps m fs) c.recFields ihs →
      appList (S.minorAt mins j) (fs.reverse ++ ihs) ∈ˢ
        appList m ((S.idxVals M ls (consList fs (envP ps)) c.idx).reverse ++ [S.ctorVal ls j fs])

/-- **The recursor's typing**: at a member of the fibre, the
recursor's value lies in the motive at the indices and the member —
by induction over the family, from the minors' typing. -/
theorem recSem_mem {ps : List V} (hpl : S.nest = none) (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hu : S.Uniq M ls)
    (hp : FitsVals M (S.ψ ls) base S.params ps) (m : V) (mins : List V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOk M ls q ps m mins j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) :
    S.recSem M ls q ps m mins is t ∈ˢ appList m (is.reverse ++ [t]) := by
  have hco := S.contOk_of_plain M ls hpl ps
  refine S.Fam_induction M ls hnr hb hco
    (fun is t => S.recSem M ls q ps m mins is t ∈ˢ appList m (is.reverse ++ [t])) ?_ is t ht
  intro is t hs
  obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
  have hfitF := S.FitsFields_of_sep M ls hco _ hfit
  rw [S.recSem_eq_of M ls q hu hp (S.RecGraph_intro M ls q
    ⟨j, c, fs, _, hc, hfitF, his, rfl, S.IhOk_ihSem M ls q hpl hnr hb hfitF m mins, rfl⟩)]
  subst his
  refine hmin j c hc fs hfitF _ (ListRel.map ?_)
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container =>
    rw [S.fieldSet_container_none M ls hpl] at hget
    exact absurd hget (not_mem_empty _)
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhTyped, ihSem]
    refine lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_
    · have hlen := FitsVals_length M _ hys
      have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
      simp only [readEnv_consList hlen]
      exact (mem_sep.mp hmem).2
    · have hlen := FitsVals_length M _ hys
      have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
      simp only [readEnv_consList hlen]
      exact hmo hq _ _ (mem_sep.mp hmem).1

/-- **The inductive hypotheses' values are typed**: at fitting
fields, each `ihSem` lies in the motive at the field (through its
telescope at a reflexive field) — `recSem_mem` at every recursive
position. -/
theorem IhTyped_ihSem {ps : List V} (hpl : S.nest = none) (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hu : S.Uniq M ls)
    (hp : FitsVals M (S.ψ ls) base S.params ps) (m : V) (mins : List V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOk M ls q ps m mins j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    {c : CtorSpec} {fs : List V} (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs) :
    ListRel (S.IhTyped M ls q ps m fs) c.recFields (c.recFields.map (S.ihSem M ls q ps m mins fs)) := by
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container =>
    rw [S.fieldSet_container_none M ls hpl] at hget
    exact absurd hget (not_mem_empty _)
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhTyped, ihSem]
    refine lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_
    · have hlen := FitsVals_length M _ hys
      have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
      simp only [readEnv_consList hlen]
      exact S.recSem_mem M ls q hpl hnr hb hu hp m mins hmin hmo hmem
    · have hlen := FitsVals_length M _ hys
      have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
      simp only [readEnv_consList hlen]
      exact hmo hq _ _ hmem

/-! ## The recursor's set -/

/-- **The recursor's set** at its own levels `lsr` (the elimination
level in front, if large): the abstraction over its context — the
parameters, the motive, the minors, the indices, the major — of the
recursor's semantic value, the family read at the block's levels. -/
noncomputable def recSet (lsr : List Nat) : V :=
  let ψr := valOf S.recLparams lsr
  let ls := S.lparams.map ψr
  let q := S.q.holds ψr
  lamCtx (S.M₂ M) ψr q base
    (S.famVars (S.n + 1) :: S.indicesAt (S.n + 1) ++ S.minorsCtx ++ [S.motiveTy] ++ S.params)
    fun ρ' =>
      S.recSem M ls q (readEnv S.nP (shiftE (1 + S.nI + S.n + 1) 0 ρ')) (ρ' (1 + S.nI + S.n))
        (readEnv S.n (shiftE (1 + S.nI) 0 ρ')) (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0)

/-- **The model of the installed block**: the recursor on top. -/
noncomputable def M₃ : Name → List Nat → V :=
  fun n ls' => if n = S.recName then S.recSet M ls' else S.M₂ M n ls'

end IndSpec

end Fragment
