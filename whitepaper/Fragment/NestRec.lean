module

public import Fragment.IndSem

@[expose] public section

/-!
# The recursors of a nested block, in the model

A nested block has two recursors with one prefix — the parameters, a
motive for the block, a motive for the class, the block's minor
premises and the class's — and they are **one graph**: the least
relation closed under the block's rules (at a tagged tuple of fields
fitting a constructor, the value is the constructor's minor at the
fields and the inductive hypotheses) and the class's rules (at a
tagged tuple of fields fitting a constructor of the container at the
instantiation — read in the block's terms, `classCtor` — the value is
that constructor's class minor at the fields and the hypotheses),
where a hypothesis at a recursive field is the graph's value at the
member (`(false, is)`) and at a container field the graph's value at
the class (`(true, [])`).  The graph is single-valued (tags and tuples
are injective) and total on the family and the class together, **by
induction over the family and over the class interleaved**: a
container field's value is in the class at the approximant, and the
class's own induction (`ClassLaws`, from the container's fixed point,
`NestClass.lean`) supplies the values at its members' member fields.
The ι laws of both recursors follow, and so does the typing of both.

Large elimination is refused unless the block's sort is never `Prop`
(`OkN`), so the recursion equation is only ever needed above a
proposition (`hz : S.z ls = false`): the major is itself the tagged
tuple, no witness device is needed, and at a proposition both
recursors are the point.

Con-leche: the graph route of `Model/Inductives/BlockRecGraph.lean`,
the class rows of `GenClsSem.lean`.
-/

namespace Fragment
open SetLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-- **The extras of the nested recursors' prefix**, as values: the
block's motive, the class's motive, the block's minors and the class's
minors (both innermost first). -/
structure RecEx (V : Type u) where
  /-- The block's motive. -/
  m : V
  /-- The class's motive. -/
  m1 : V
  /-- The block's minor premises, innermost first. -/
  mins : List V
  /-- The class's minor premises, innermost first. -/
  minsK : List V

/-- The nested graph's shape: parameters, extras, target (the family
at index values, or the class), witness, value. -/
abbrev RecPN (V : Type u) := List V → RecEx V → IndSpec.JIdx V → V → V → Prop

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-! ## The class at a member set -/

/-- The field sets of a constructor of the container read in the
block's terms, at a member set `X` and with the class's members
restricted by `Q`: a (translated) recursive field is the member field,
ranging over `X`; a container field is the container's recursive
field, ranging over the class at `X` restricted by `Q`; an ordinary
field is the container's, read as the block reads it. -/
noncomputable def classFieldSet (X : V) (Q : V → Prop) (ps fs : List V) : Field → V
  | .recursive _ => X
  | .container => sep (S.classSet M ls N ps X) Q
  | f => S.fieldSet M ls (S.bound M ls) (S.Mem M ls) ps fs f

/-- Field values fitting a (translated) constructor of the container
at a member set and a restriction (both innermost first). -/
noncomputable def ClassFits (X : V) (Q : V → Prop) (ps : List V) : List Field → List V → Prop
  | [], [] => True
  | f :: fs, v :: vs => ClassFits X Q ps fs vs ∧ v ∈ˢ S.classFieldSet M ls N X Q ps vs f
  | _, _ => False

/-- **The class** at the parameters: the class at the family's fibre
at the member's index values — what a container field ranges over. -/
noncomputable def classAt (ps : List V) : V :=
  S.classSet M ls N ps (S.Fam M ls ps (S.memberIdx M ls N ps))

/-- Inversion of the class at a member set: a member is a tagged tuple
of fields fitting a constructor of the container. -/
def ClassInv (ps : List V) (X : V) : Prop :=
  ∀ x, x ∈ˢ S.classSet M ls N ps X → ∃ j c fs, N.K.ctors[j]? = some c ∧
    S.ClassFits M ls N X (fun _ => True) ps (S.classCtor N c).fields fs ∧ x = tag j (tuple fs.reverse)

/-- Introduction into the class at a member set. -/
def ClassIntro (ps : List V) (X : V) : Prop :=
  ∀ j c fs, N.K.ctors[j]? = some c →
    S.ClassFits M ls N X (fun _ => True) ps (S.classCtor N c).fields fs →
    tag j (tuple fs.reverse) ∈ˢ S.classSet M ls N ps X

/-- **Induction over the class** at a member set: a predicate closed
under the container's constructors (with the class's members at the
container fields satisfying it) holds on the class. -/
def ClassInd (ps : List V) (X : V) : Prop :=
  ∀ Q : V → Prop,
    (∀ j c fs, N.K.ctors[j]? = some c →
      S.ClassFits M ls N X (fun y => y ∈ˢ S.classSet M ls N ps X ∧ Q y) ps
        (S.classCtor N c).fields fs →
      Q (tag j (tuple fs.reverse))) →
    ∀ x, x ∈ˢ S.classSet M ls N ps X → Q x

/-- **The class's laws** at every member set in the result universe:
inversion, introduction, induction — the container's fixed point, read
in the block's terms (`NestClass.lean`). -/
structure ClassLaws (ps : List V) : Prop where
  /-- Inversion. -/
  inv : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.ClassInv M ls N ps X
  /-- Introduction. -/
  intro : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.ClassIntro M ls N ps X
  /-- Induction. -/
  ind : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.ClassInd M ls N ps X
  /-- The class at a member set is in the result universe. -/
  mem_univ : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.classSet M ls N ps X ∈ˢ (univ (S.u₀ ls) : V)
  /-- The class grows with the member set. -/
  mono : ∀ X Y, X ⊆ˢ Y → X ∈ˢ (univ (S.u₀ ls) : V) → Y ∈ˢ (univ (S.u₀ ls) : V) →
    S.classSet M ls N ps X ⊆ˢ S.classSet M ls N ps Y

/-! ## The graph -/

variable (q : Bool)

/-- **An inductive hypothesis' value** relative to a graph `R`: at a
recursive field the graph's value at the family (at the field's index
values) and the field; at a reflexive field the abstraction over the
field's telescope of those values; at a container field the graph's
value at the class and the field. -/
noncomputable def IhOkN (R : RecPN V) (ps : List V) (ex : RecEx V) (fs : List V) :
    Nat × Field → V → Prop
  | (k, .recursive es), ih =>
    let is := S.idxVals M ls (consList (earlier fs k) (envP ps)) es
    R ps ex (false, is) (fieldVal fs k) ih
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ∃ g : (Nat → V) → V, ih = lamCtx M (S.ψ ls) q env tele g ∧
      ∀ ys, FitsVals M (S.ψ ls) env tele ys →
        let is := S.idxVals M ls (consList ys env) es
        R ps ex (false, is) (appList (fieldVal fs k) ys.reverse) (g (consList ys env))
  | (k, .container), ih => R ps ex (true, []) (fieldVal fs k) ih
  | (_, .ordinary _), _ => False

/-- The class minor for the container's constructor `j` among the
class minors (innermost first). -/
def minorKAt (minsK : List V) (j : Nat) : V := minsK.getD (N.nK - 1 - j) pt

/-- **The operator** whose least fixed point is the joint graph: the
block's rules at the family, the class's rules at the class. -/
noncomputable def rstepN (R : RecPN V) (ps : List V) (ex : RecEx V) (tgt : JIdx V) (x v : V) :
    Prop :=
  (∃ j c fs ihs is, tgt = (false, is) ∧ S.ctors[j]? = some c ∧
    S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs ∧
    is = S.idxVals M ls (consList fs (envP ps)) c.idx ∧ x = tag (S.tagOf j) (tuple fs.reverse) ∧
    ListRel (S.IhOkN M ls q R ps ex fs) c.recFields ihs ∧
    v = appList (S.minorAt ex.mins j) (fs.reverse ++ ihs)) ∨
  (∃ j c fs ihs, tgt = (true, []) ∧ N.K.ctors[j]? = some c ∧
    S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs ∧
    x = tag j (tuple fs.reverse) ∧
    ListRel (S.IhOkN M ls q R ps ex fs) (S.classCtor N c).recFields ihs ∧
    v = appList (minorKAt N ex.minsK j) (fs.reverse ++ ihs))

/-- The operator on quintuples. -/
noncomputable def rstepTN (R : List V × RecEx V × JIdx V × V × V → Prop)
    (t : List V × RecEx V × JIdx V × V × V) : Prop :=
  S.rstepN M ls N q (fun ps ex tgt x v => R (ps, ex, tgt, x, v)) t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2

/-- **The joint graph** of the two recursors: the least fixed point of
`rstepN`. -/
noncomputable def RecGraphN (ps : List V) (ex : RecEx V) (tgt : JIdx V) (x v : V) : Prop :=
  Lfp (S.rstepTN M ls N q) (ps, ex, tgt, x, v)

/-- **The recursors' value**: the one the graph relates, if any. -/
noncomputable def recFnN (ps : List V) (ex : RecEx V) (tgt : JIdx V) (x : V) : V :=
  open Classical in
  if h : ∃ v, S.RecGraphN M ls N q ps ex tgt x v then Classical.choose h else pt

/-- **`T.rec`'s semantic value** at parameters, extras, indices and the
major: the graph's value at the family. -/
noncomputable def recSemN (ps : List V) (ex : RecEx V) (is : List V) (t : V) : V :=
  S.recFnN M ls N q ps ex (false, is) t

/-- **`T.rec_1`'s semantic value** at parameters, extras and the major:
the graph's value at the class. -/
noncomputable def rec1Sem (ps : List V) (ex : RecEx V) (t : V) : V :=
  S.recFnN M ls N q ps ex (true, []) t

/-- **The inductive hypotheses' semantic values**: `T.rec` at a
recursive field (through its telescope at a reflexive one), `T.rec_1`
at a container field. -/
noncomputable def ihSemN (ps : List V) (ex : RecEx V) (fs : List V) : Nat × Field → V
  | (k, .recursive es) =>
    S.recSemN M ls N q ps ex (S.idxVals M ls (consList (earlier fs k) (envP ps)) es) (fieldVal fs k)
  | (k, .reflexive tele es) =>
    let env := consList (earlier fs k) (envP ps)
    lamCtx M (S.ψ ls) q env tele fun ρ' =>
      S.recSemN M ls N q ps ex (S.idxVals M ls ρ' es)
        (appList (fieldVal fs k) (readEnv tele.length ρ').reverse)
  | (k, .container) => S.rec1Sem M ls N q ps ex (fieldVal fs k)
  | (_, .ordinary _) => pt

/-- An inductive hypothesis' value lies in the block's motive at the
field's index values and the field (through the telescope at a
reflexive field), or in the class's motive at the field. -/
noncomputable def IhTypedN (ps : List V) (ex : RecEx V) (fs : List V) : Nat × Field → V → Prop
  | (k, .recursive es), ih =>
    ih ∈ˢ appList ex.m ((S.idxVals M ls (consList (earlier fs k) (envP ps)) es).reverse ++ [fieldVal fs k])
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ih ∈ˢ piCtx M (S.ψ ls) q env tele fun ρ' =>
      appList ex.m ((S.idxVals M ls ρ' es).reverse ++
        [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])
  | (k, .container), ih => ih ∈ˢ appList ex.m1 [fieldVal fs k]
  | (_, .ordinary _), _ => True

/-- **A block minor's typing**: at fitting fields and typed inductive
hypotheses, the minor's value lies in the block's motive at the
constructor's index values and its value. -/
noncomputable def MinorOkN (ps : List V) (ex : RecEx V) (j : Nat) (c : CtorSpec) : Prop :=
  ∀ fs, S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs →
    ∀ ihs, ListRel (S.IhTypedN M ls q ps ex fs) c.recFields ihs →
      appList (S.minorAt ex.mins j) (fs.reverse ++ ihs) ∈ˢ
        appList ex.m ((S.idxVals M ls (consList fs (envP ps)) c.idx).reverse ++ [S.ctorVal ls j fs])

/-- **A class minor's typing**: at fields fitting the container's
constructor at the instantiation and typed hypotheses, the class
minor's value lies in the class's motive at the constructor's value. -/
noncomputable def MinorOkK (ps : List V) (ex : RecEx V) (j : Nat) (c : CtorSpec) : Prop :=
  ∀ fs, S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs →
    ∀ ihs, ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields ihs →
      appList (minorKAt N ex.minsK j) (fs.reverse ++ ihs) ∈ˢ
        appList ex.m1 [tag j (tuple fs.reverse)]

/-! ## The fixed-point laws of the graph -/

theorem IhOkN_mono {R R' : RecPN V}
    (h : ∀ ps ex tgt x v, R ps ex tgt x v → R' ps ex tgt x v)
    (ps : List V) (ex : RecEx V) (fs : List V) :
    ∀ (kf : Nat × Field) (ih : V),
      S.IhOkN M ls q R ps ex fs kf ih → S.IhOkN M ls q R' ps ex fs kf ih := by
  sorry

theorem rstepTN_mono : Mono (S.rstepTN M ls N q) := by
  sorry

theorem RecGraphN_intro {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x v : V}
    (h : S.rstepN M ls N q (S.RecGraphN M ls N q) ps ex tgt x v) :
    S.RecGraphN M ls N q ps ex tgt x v :=
  Lfp.closed (S.rstepTN_mono M ls N q) h

theorem RecGraphN_elim {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x v : V}
    (h : S.RecGraphN M ls N q ps ex tgt x v) :
    S.rstepN M ls N q (S.RecGraphN M ls N q) ps ex tgt x v :=
  Lfp.unfold (S.rstepTN_mono M ls N q) h

theorem RecGraphN_ind {P : RecPN V}
    (h : ∀ ps ex tgt x v,
      S.rstepN M ls N q (fun ps ex tgt x v => S.RecGraphN M ls N q ps ex tgt x v ∧ P ps ex tgt x v)
        ps ex tgt x v → P ps ex tgt x v)
    {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x v : V}
    (hg : S.RecGraphN M ls N q ps ex tgt x v) : P ps ex tgt x v :=
  Lfp.induction (S.rstepTN_mono M ls N q)
    (P := fun t => P t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) (fun _ ht => h _ _ _ _ _ ht) hg

/-- **Single-valuedness of the joint graph**: tags and tuples are
injective, and a block value's tag is never a class value's — the
block's constructors are tagged after the container's. -/
theorem RecGraphN_fun {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x v v' : V}
    (h : S.RecGraphN M ls N q ps ex tgt x v) (h' : S.RecGraphN M ls N q ps ex tgt x v') : v = v' := by
  sorry

theorem recFnN_eq {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x v : V}
    (h : S.RecGraphN M ls N q ps ex tgt x v) : S.recFnN M ls N q ps ex tgt x = v := by
  unfold recFnN
  rw [dif_pos ⟨v, h⟩]
  exact S.RecGraphN_fun M ls N q (Classical.choose_spec ⟨v, h⟩) h

theorem RecGraphN_recFnN {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x : V}
    (h : ∃ v, S.RecGraphN M ls N q ps ex tgt x v) :
    S.RecGraphN M ls N q ps ex tgt x (S.recFnN M ls N q ps ex tgt x) := by
  obtain ⟨v, hv⟩ := h
  rw [S.recFnN_eq M ls N q hv]; exact hv

/-- **Totality of the joint graph** on the family and on the class
(above a proposition): by induction over the family, with an inner
induction over the class at the approximant's fibre at every container
field. -/
theorem RecGraphN_total (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V) :
    (∀ is x, S.Mem M ls ps is x → ∃ v, S.RecGraphN M ls N q ps ex (false, is) x v) ∧
    (∀ x, x ∈ˢ S.classAt M ls N ps → ∃ v, S.RecGraphN M ls N q ps ex (true, []) x v) := by
  sorry

/-- The inductive hypotheses' semantic values are what the graph
demands, at a block constructor's fitting fields. -/
theorem IhOkN_ihSemN (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {c : CtorSpec} (hcm : c ∈ S.ctors) {fs : List V}
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs) :
    ListRel (S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs) c.recFields
      (c.recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  sorry

/-- The inductive hypotheses' semantic values are what the graph
demands, at a container constructor's fitting fields. -/
theorem IhOkN_ihSemN_class (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {c : CtorSpec} (hcm : c ∈ N.K.ctors) {fs : List V}
    (hfit : S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    ListRel (S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs) (S.classCtor N c).recFields
      ((S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  sorry

/-- **The ι equation of `T.rec`**: at a constructor value whose fields
fit, the recursor is the minor at the fields and the hypotheses'
values. -/
theorem recSemN_eq (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) {fs : List V}
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs) :
    S.recSemN M ls N q ps ex (S.idxVals M ls (consList fs (envP ps)) c.idx) (S.ctorVal ls j fs)
      = appList (S.minorAt ex.mins j) (fs.reverse ++ c.recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  sorry

/-- **The ι equation of `T.rec_1`**: at a container constructor's
value (the tagged tuple of fields fitting it at the instantiation),
the auxiliary recursor is the class minor at the fields and the
hypotheses' values. -/
theorem rec1Sem_eq (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c) {fs : List V}
    (hfit : S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    S.rec1Sem M ls N q ps ex (tag j (tuple fs.reverse))
      = appList (minorKAt N ex.minsK j)
          (fs.reverse ++ (S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  sorry

/-! ## Typing -/

/-- **The recursors' typing** (above a proposition): at a member of
the fibre, `T.rec`'s value lies in the block's motive at the indices
and the member; at a member of the class, `T.rec_1`'s value lies in
the class's motive at it — by the interleaved induction, from the
minors' typing. -/
theorem recSemN_mem (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c) :
    (∀ is t, t ∈ˢ S.Fam M ls ps is → S.recSemN M ls N q ps ex is t ∈ˢ appList ex.m (is.reverse ++ [t])) ∧
    (∀ t, t ∈ˢ S.classAt M ls N ps → S.rec1Sem M ls N q ps ex t ∈ˢ appList ex.m1 [t]) := by
  sorry

/-- **The inductive hypotheses' values are typed**, at a block
constructor's fitting fields. -/
theorem IhTypedN_ihSemN (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    {c : CtorSpec} (hcm : c ∈ S.ctors) {fs : List V}
    (hfit : S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs) :
    ListRel (S.IhTypedN M ls q ps ex fs) c.recFields (c.recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  sorry

/-- **The inductive hypotheses' values are typed**, at a container
constructor's fitting fields. -/
theorem IhTypedN_ihSemN_class (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    {c : CtorSpec} (hcm : c ∈ N.K.ctors) {fs : List V}
    (hfit : S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields
      ((S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  sorry

/-- **The motives are inhabited** on the family and on the class, at
a proposition (where the values are not the recursors'): by the
interleaved induction from the minors' typing, with inhabited truth
values as the hypotheses. -/
theorem motive_inhabitedN (hN : S.nest = some N) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList ex.m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    (hmo1 : q = true → ∀ t, t ∈ˢ S.classAt M ls N ps → appList ex.m1 [t] ∈ˢ (univ 0 : V)) :
    (∀ is t, t ∈ˢ S.Fam M ls ps is → ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [t])) ∧
    (∀ t, t ∈ˢ S.classAt M ls N ps → ∃ v, v ∈ˢ appList ex.m1 [t]) := by
  sorry

end IndSpec

end Fragment
