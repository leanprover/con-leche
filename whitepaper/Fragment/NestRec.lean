module

public import Fragment.NestSem

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
where a hypothesis at a reflexive field is the graph's value at the
family (`(false, is)`, under the field's telescope) and at a container
field the graph's value at the class (`(true, [])`).  The graph is
single-valued (tags and tuples are injective) and total on the family
and the class together, **by induction over the family and over the
class interleaved**: a container field's value is in the class at the
approximant (the family's separation by "the graph has a value"), and
the class's own induction (`ClassLaws`, from the container's fixed
point, `NestClass.lean`) supplies the values at its members' parameter
fields.  The ι laws of both recursors follow, and so does the typing
of both.

Large elimination is refused unless the block's sort is never `Prop`
(`OkN`), so the recursion equation is only ever needed above a
proposition (`hz : S.z ls = false`): the major is itself the tagged
tuple, no witness device is needed, and at a proposition both
recursors are the point.

Con-leche: the graph route over the classes, `SetModel/NestRec.lean`
(`NestKit.ind`: the strengthened predicate "lies in the true class ∧
the property", the induction over the container's family at the
separated frame), `Model/Inductives/BlockRecGraph.lean`, the class
rows of `GenClsSem.lean`.
-/

namespace Fragment open NestInfo (nPK nK memberVar isMember Positive memberLevel)
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-- **The joint index** of the two recursors' graph: the family at
index values (`(false, is)`), or the class (`(true, [])`). -/
abbrev JIdx (V : Type u) := Bool × List V

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
at index values, or the class), major, value. -/
abbrev RecPN (V : Type u) := List V → RecEx V → JIdx V → V → V → Prop

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-! ## The class at a parameter set -/

/-- The field sets of a constructor of the container read in the
block's terms, at a parameter set `X` and with the class's members
restricted by `Q`: a (translated) reflexive field is the parameter field
(recursive: the telescope is empty), ranging over `X`; a container
field is the container's recursive field, ranging over the class at
`X` restricted by `Q`; an ordinary field is the container's, read as
the block reads it. -/
noncomputable def classFieldSet (X : V) (Q : V → Prop) (ps fs : List V) : Field → V
  | .reflexive _ _ => X
  | .container => sep (S.classSet M ls N ps X) Q
  | f => S.fieldSet M ls (S.Fam M ls ps) ps fs f

/-- Field values fitting a (translated) constructor of the container
at a parameter set and a restriction (both innermost first). -/
noncomputable def ClassFits (X : V) (Q : V → Prop) (ps : List V) : List Field → List V → Prop
  | [], [] => True
  | f :: fs, v :: vs => ClassFits X Q ps fs vs ∧ v ∈ˢ S.classFieldSet M ls N X Q ps vs f
  | _, _ => False

/-- **The class** at the parameters: the class at the family's fibre
at the nested occurrence's index values — what a container field ranges over. -/
noncomputable def classAt (ps : List V) : V :=
  S.classSet M ls N ps (S.Fam M ls ps (S.memberIdx M ls N ps))

/-- Inversion of the class at a parameter set: a member is a tagged tuple
of fields fitting a constructor of the container. -/
def ClassInv (ps : List V) (X : V) : Prop :=
  ∀ x, x ∈ˢ S.classSet M ls N ps X → ∃ j c fs, N.K.ctors[j]? = some c ∧
    S.ClassFits M ls N X (fun _ => True) ps (S.classCtor N c).fields fs ∧ x = tag j (tuple fs.reverse)

/-- Introduction into the class at a parameter set. -/
def ClassIntro (ps : List V) (X : V) : Prop :=
  ∀ j c fs, N.K.ctors[j]? = some c →
    S.ClassFits M ls N X (fun _ => True) ps (S.classCtor N c).fields fs →
    tag j (tuple fs.reverse) ∈ˢ S.classSet M ls N ps X

/-- **Induction over the class** at a parameter set: a predicate closed
under the container's constructors (with the class's members at the
container fields satisfying it) holds on the class. -/
def ClassInd (ps : List V) (X : V) : Prop :=
  ∀ Q : V → Prop,
    (∀ j c fs, N.K.ctors[j]? = some c →
      S.ClassFits M ls N X (fun y => y ∈ˢ S.classSet M ls N ps X ∧ Q y) ps
        (S.classCtor N c).fields fs →
      Q (tag j (tuple fs.reverse))) →
    ∀ x, x ∈ˢ S.classSet M ls N ps X → Q x

/-- **The class's laws** at every parameter set in the result universe:
inversion, introduction, induction — the container's fixed point, read
in the block's terms (`NestClass.lean`). -/
structure ClassLaws (ps : List V) : Prop where
  /-- Inversion. -/
  inv : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.ClassInv M ls N ps X
  /-- Introduction. -/
  intro : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.ClassIntro M ls N ps X
  /-- Induction. -/
  ind : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.ClassInd M ls N ps X
  /-- The class at a parameter set is in the result universe. -/
  mem_univ : ∀ X, X ∈ˢ (univ (S.u₀ ls) : V) → S.classSet M ls N ps X ∈ˢ (univ (S.u₀ ls) : V)
  /-- The class grows with the parameter set. -/
  mono : ∀ X Y, X ⊆ˢ Y → X ∈ˢ (univ (S.u₀ ls) : V) → Y ∈ˢ (univ (S.u₀ ls) : V) →
    S.classSet M ls N ps X ⊆ˢ S.classSet M ls N ps Y

/-! ## The graph -/

variable (q : Bool)

/-- **An inductive hypothesis' value** relative to a graph `R`: at a
reflexive field the abstraction over the field's telescope of the
graph's values at the family (at the field's index values) and the
field applied to the telescope's variables; at a container field the
graph's value at the class and the field. -/
noncomputable def IhOkN (R : RecPN V) (ps : List V) (ex : RecEx V) (fs : List V) :
    Nat × Field → V → Prop
  | (k, .reflexive tele es), ih =>
    let env := consList (earlier fs k) (envP ps)
    ∃ g : (Nat → V) → V, ih = lamCtx M (S.ψ ls) q env tele g ∧
      ∀ ys, FitsVals M (S.ψ ls) env tele ys →
        let is := S.idxVals M ls (consList ys env) es
        R ps ex (false, is) (appList (fieldVal fs k) ys.reverse) (g (consList ys env))
  | (k, .container), ih => R ps ex (true, []) (fieldVal fs k) ih
  | (_, .ordinary _), _ => False

/-- An inductive hypothesis' value at a recursive field (a reflexive
field with an empty telescope): the graph's value at the field. -/
theorem IhOkN_nil (R : RecPN V) (ps : List V) (ex : RecEx V) (fs : List V) (k : Nat)
    (es : List Expr) (ih : V) :
    S.IhOkN M ls q R ps ex fs (k, .reflexive [] es) ih ↔
      R ps ex (false, S.idxVals M ls (consList (earlier fs k) (envP ps)) es) (fieldVal fs k) ih := by
  simp only [IhOkN, lamCtx_nil]
  constructor
  · rintro ⟨g, rfl, hall⟩
    exact hall [] trivial
  · intro h
    refine ⟨fun _ => ih, rfl, fun ys hys => ?_⟩
    cases ys with
    | nil => exact h
    | cons _ _ => exact hys.elim

/-- The class minor for the container's constructor `j` among the
class minors (innermost first). -/
def minorKAt (minsK : List V) (j : Nat) : V := minsK.getD (N.nK - 1 - j) pt

/-- **The operator** whose least fixed point is the joint graph: the
block's rules at the family, the class's rules at the class. -/
noncomputable def rstepN (R : RecPN V) (ps : List V) (ex : RecEx V) (tgt : JIdx V) (x v : V) :
    Prop :=
  (∃ j c fs ihs is, tgt = (false, is) ∧ S.ctors[j]? = some c ∧
    S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs ∧
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
reflexive field (through its telescope), `T.rec_1` at a container
field. -/
noncomputable def ihSemN (ps : List V) (ex : RecEx V) (fs : List V) : Nat × Field → V
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
  ∀ fs, S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs →
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

end IndSpec

/-! ## Small pieces -/

/-- Pairwise witnesses along a list. -/
theorem ListRel.exists_of_forall {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ bs, ListRel R l bs
  | [], _ => ⟨[], trivial⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := ListRel.exists_of_forall fun a' ha' => h a' (List.mem_cons_of_mem a ha')
    exact ⟨b :: bs, hb, hbs⟩

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat) (N : NestInfo)

/-! ### The translated constructors' fields -/

/-- A field of a translated constructor is the container's field at
that position, translated. -/
theorem classCtor_fields_get (c : CtorSpec) {k : Nat} {f : Field}
    (h : (S.classCtor N c).fields[(S.classCtor N c).fields.length - 1 - k]? = some f)
    (hk : k < (S.classCtor N c).fields.length) :
    ∃ f₀, c.fields[c.fields.length - 1 - k]? = some f₀ ∧ f = S.classField N k f₀ := by
  simp only [classCtor, S.length_classFields] at h hk
  rw [S.classFields_getElem?] at h
  cases hf₀ : c.fields[c.fields.length - 1 - k]? with
  | none => simp [hf₀] at h
  | some f₀ =>
    rw [hf₀] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨f₀, rfl, ?_⟩
    rw [← h]
    exact congrArg (fun i => S.classField N i f₀)
      (by omega : c.fields.length - 1 - (c.fields.length - 1 - k) = k)

/-- The only reflexive field of a translated constructor is the
parameter field — recursive (an empty telescope), at the nested occurrence's index
expressions lifted over the earlier fields.  (A reflexive field with
a telescope never arises: the container is positive, so its fields
are the parameter field, its own recursive fields and ordinary ones.  The
interleaved inductions need that: such a field of the class would
range over the *whole* family, which the outer induction's
approximant does not reach.) -/
theorem classField_reflexive {k : Nat} {f₀ : Field} {tele es : List Expr}
    (h : S.classField N k f₀ = .reflexive tele es) : tele = [] ∧ es = N.idx.map (Expr.liftN k ·) := by
  cases f₀ with
  | ordinary A =>
    simp only [classField] at h
    by_cases hm : N.isMember k (.ordinary A) = true
    · rw [ite_eq_left hm] at h
      exact ⟨(Field.reflexive.inj h).1.symm, (Field.reflexive.inj h).2.symm⟩
    · rw [ite_eq_right hm] at h
      exact Field.noConfusion h
  | reflexive _ _ => simp [classField] at h
  | container => simp [classField] at h


/-- Lifted expressions read under pushed values of the lifting's
length read as under the environment below. -/
theorem idxVals_liftN (ps : List V) {fs : List V} {k : Nat} (hk : fs.length = k) (es : List Expr) :
    S.idxVals M ls (consList fs (envP ps)) (es.map (Expr.liftN k ·)) = S.idxVals M ls (envP ps) es := by
  simp only [idxVals, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp]
  rw [interp_liftN, shiftE_consList' hk]

omit [IndLib V] in
theorem length_earlier {fs : List V} {k : Nat} (hk : k ≤ fs.length) : (earlier fs k).length = k := by
  simp only [earlier, List.length_drop]; omega

/-- The parameter field's index values, read under the earlier fields,
are the nested occurrence's index values. -/
theorem memberIdx_earlier (ps : List V) {fs : List V} {k : Nat} (hk : k ≤ fs.length) :
    S.idxVals M ls (consList (earlier fs k) (envP ps)) (N.idx.map (Expr.liftN k ·))
      = S.memberIdx M ls N ps :=
  S.idxVals_liftN M ls ps (length_earlier hk) N.idx

/-! ### Fitting the translated constructors -/

theorem ClassFits_length {X : V} {Q : V → Prop} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.ClassFits M ls N X Q ps fields fs →
      fs.length = fields.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [ClassFits_length h.1]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Each field of a fitting list is a member of its domain at the
earlier fields. -/
theorem ClassFits_get {X : V} {Q : V → Prop} {ps : List V} :
    ∀ {fields : List Field} {fs : List V}, S.ClassFits M ls N X Q ps fields fs →
      ∀ {k : Nat} {f : Field}, fields[fields.length - 1 - k]? = some f → k < fields.length →
        fieldVal fs k ∈ˢ S.classFieldSet M ls N X Q ps (earlier fs k) f
  | [], [], _, k, _, _, hk => by simp at hk
  | f' :: fields, v :: fs, hf, k, f, h, hk => by
    have hlen := S.ClassFits_length M ls N hf.1
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
      exact ClassFits_get hf.1 h hk'
  | [], _ :: _, hf, _, _, _, _ => hf.elim
  | _ :: _, [], hf, _, _, _, _ => hf.elim

/-- A translated field's set grows with the parameter set (the class by
the class's law), and the restriction can be dropped. -/
theorem classFieldSet_mono {ps : List V} (hcl : S.ClassLaws M ls N ps) {X Y : V}
    (hX : X ∈ˢ (univ (S.u₀ ls) : V)) (hY : Y ∈ˢ (univ (S.u₀ ls) : V)) (hXY : X ⊆ˢ Y)
    {Q : V → Prop} (fs : List V) :
    ∀ f : Field, S.classFieldSet M ls N X Q ps fs f ⊆ˢ S.classFieldSet M ls N Y (fun _ => True) ps fs f
  | .reflexive _ _ => hXY
  | .container => by
    intro v hv
    simp only [classFieldSet, mem_sep] at hv ⊢
    exact ⟨hcl.mono X Y hXY hX hY v hv.1, trivial⟩
  | .ordinary _ => Sub.refl _

/-- Fields fitting a translated constructor at a parameter set fit it at
a larger one, unrestricted. -/
theorem ClassFits_mono {ps : List V} (hcl : S.ClassLaws M ls N ps) {X Y : V}
    (hX : X ∈ˢ (univ (S.u₀ ls) : V)) (hY : Y ∈ˢ (univ (S.u₀ ls) : V)) (hXY : X ⊆ˢ Y)
    {Q : V → Prop} :
    ∀ {fields : List Field} {fs : List V},
      S.ClassFits M ls N X Q ps fields fs → S.ClassFits M ls N Y (fun _ => True) ps fields fs
  | [], [], _ => trivial
  | _ :: _, _ :: fs, hf =>
    ⟨ClassFits_mono hcl hX hY hXY hf.1, S.classFieldSet_mono M ls N hcl hX hY hXY fs _ _ hf.2⟩
  | [], _ :: _, hf => hf.elim
  | _ :: _, [], hf => hf.elim

variable (q : Bool)

/-! ## The fixed-point laws of the graph -/

theorem IhOkN_mono {R R' : RecPN V}
    (h : ∀ ps ex tgt x v, R ps ex tgt x v → R' ps ex tgt x v)
    (ps : List V) (ex : RecEx V) (fs : List V) :
    ∀ (kf : Nat × Field) (ih : V),
      S.IhOkN M ls q R ps ex fs kf ih → S.IhOkN M ls q R' ps ex fs kf ih := by
  intro kf ih hh
  match kf, hh with
  | (_, .ordinary _), hh => exact hh.elim
  | (_, .container), hh => exact h _ _ _ _ _ hh
  | (_, .reflexive _ _), ⟨g, hg, hall⟩ => exact ⟨g, hg, fun ys hys => h _ _ _ _ _ (hall ys hys)⟩

theorem rstepTN_mono : Mono (S.rstepTN M ls N q) := by
  intro R R' h t hs
  rcases hs with ⟨j, c, fs, ihs, is, htgt, hc, hfit, his, hx, hihs, hv⟩ |
    ⟨j, c, fs, ihs, htgt, hc, hfit, hx, hihs, hv⟩
  · exact Or.inl ⟨j, c, fs, ihs, is, htgt, hc, hfit, his, hx,
      ListRel.mono (S.IhOkN_mono M ls q (fun ps ex tgt x v => h (ps, ex, tgt, x, v)) _ _ _) hihs, hv⟩
  · exact Or.inr ⟨j, c, fs, ihs, htgt, hc, hfit, hx,
      ListRel.mono (S.IhOkN_mono M ls q (fun ps ex tgt x v => h (ps, ex, tgt, x, v)) _ _ _) hihs, hv⟩

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
  refine S.RecGraphN_ind M ls N q
    (P := fun ps ex tgt x v => ∀ v', S.RecGraphN M ls N q ps ex tgt x v' → v = v') ?_ h v' h'
  intro ps ex tgt x v hs v' h'
  -- the hypotheses agree, by the induction hypothesis at every position
  have huniq : ∀ (fs : List V) (kf : Nat × Field) (ih ih' : V),
      S.IhOkN M ls q (fun ps ex tgt x v => S.RecGraphN M ls N q ps ex tgt x v ∧
        ∀ v', S.RecGraphN M ls N q ps ex tgt x v' → v = v') ps ex fs kf ih →
      S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs kf ih' → ih = ih' := by
    intro fs kf ih ih' h1 h2
    match kf, h1, h2 with
    | (_, .ordinary _), h1, _ => exact h1.elim
    | (_, .container), h1, h2 => exact h1.2 _ h2
    | (_, .reflexive _ _), ⟨_, hg1, hg⟩, ⟨_, hg1', hg'⟩ =>
      rw [hg1, hg1']
      exact lamCtx_congr M _ fun ys hys => (hg ys hys).2 _ (hg' ys hys)
  have hs' := S.RecGraphN_elim M ls N q h'
  rcases hs with ⟨j, c, fs, ihs, is, htgt, hc, -, -, hx, hihs, hv⟩ |
    ⟨j, c, fs, ihs, htgt, hc, -, hx, hihs, hv⟩
  · rcases hs' with ⟨j', c', fs', ihs', is', htgt', hc', -, -, hx', hihs', hv'⟩ |
      ⟨j', c', fs', ihs', htgt', hc', -, hx', hihs', hv'⟩
    · subst hx
      obtain ⟨hjj, hfs⟩ := tag_inj hx'
      obtain rfl : j = j' := by simp only [tagOf] at hjj; omega
      have := List.reverse_inj.mp (tuple_inj hfs)
      subst this
      rw [hc] at hc'
      cases hc'
      subst hv hv'
      congr 2
      exact ListRel.unique (huniq fs) hihs hihs'
    · rw [htgt] at htgt'; simp at htgt'
  · rcases hs' with ⟨j', c', fs', ihs', is', htgt', hc', -, -, hx', hihs', hv'⟩ |
      ⟨j', c', fs', ihs', htgt', hc', -, hx', hihs', hv'⟩
    · rw [htgt] at htgt'; simp at htgt'
    · subst hx
      obtain ⟨rfl, hfs⟩ := tag_inj hx'
      have := List.reverse_inj.mp (tuple_inj hfs)
      subst this
      rw [hc] at hc'
      cases hc'
      subst hv hv'
      congr 2
      exact ListRel.unique (huniq fs) hihs hihs'

theorem recFnN_eq {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x v : V}
    (h : S.RecGraphN M ls N q ps ex tgt x v) : S.recFnN M ls N q ps ex tgt x = v := by
  unfold recFnN
  rw [dite_eq_left ⟨v, h⟩]
  exact S.RecGraphN_fun M ls N q (Classical.choose_spec ⟨v, h⟩) h

theorem RecGraphN_recFnN {ps : List V} {ex : RecEx V} {tgt : JIdx V} {x : V}
    (h : ∃ v, S.RecGraphN M ls N q ps ex tgt x v) :
    S.RecGraphN M ls N q ps ex tgt x (S.recFnN M ls N q ps ex tgt x) := by
  obtain ⟨v, hv⟩ := h
  rw [S.recFnN_eq M ls N q hv]; exact hv

/-! ### Totality -/

/-- The container clause of a block constructor's fields at the family:
the class at the family's fibre at the nested occurrence. -/
theorem fieldSet_container_Fam (hN : S.nest = some N) (ps fs : List V) :
    S.fieldSet M ls (S.Fam M ls ps) ps fs .container = S.classAt M ls N ps :=
  S.fieldSet_container M ls hN _ ps fs

/-- **The inner step**: at fields fitting a translated constructor at
a parameter set `X` with a graph value at every member of `X` and at
every `Q`-member of the class at `X`, the hypotheses' semantic values
are what the graph demands. -/
theorem IhOkN_ihSemN_class_of {ps : List V} (ex : RecEx V)
    {X : V} {Q : V → Prop}
    (hkey : ∀ x, x ∈ˢ X → ∃ v, S.RecGraphN M ls N q ps ex (false, S.memberIdx M ls N ps) x v)
    (hQ : ∀ y, y ∈ˢ S.classSet M ls N ps X → Q y → ∃ v, S.RecGraphN M ls N q ps ex (true, []) y v)
    {c : CtorSpec} {fs : List V}
    (hfit : S.ClassFits M ls N X Q ps (S.classCtor N c).fields fs) :
    ListRel (S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs) (S.classCtor N c).recFields
      ((S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.ClassFits_get M ls N hfit hf hk
  have hlen := S.ClassFits_length M ls N hfit
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | reflexive tele es =>
    obtain ⟨f₀, -, hfe⟩ := S.classCtor_fields_get N c hf hk
    obtain ⟨rfl, hes⟩ := S.classField_reflexive N hfe.symm
    dsimp only at hes
    subst hes
    dsimp only [classFieldSet] at hget
    rw [S.IhOkN_nil]
    dsimp only [ihSemN, lamCtx_nil, readEnv_zero, List.reverse_nil, appList_nil, recSemN]
    rw [S.memberIdx_earlier M ls N ps (by omega)]
    exact S.RecGraphN_recFnN M ls N q (hkey _ hget)
  | container =>
    dsimp only [classFieldSet] at hget
    rw [mem_sep] at hget
    dsimp only [IhOkN, ihSemN]
    exact S.RecGraphN_recFnN M ls N q (hQ _ hget.1 hget.2)

/-- **The inner induction**: the graph is total on the class at a
parameter set inside the fibre on which it is total. -/
theorem class_total_of {ps : List V} (hcl : S.ClassLaws M ls N ps) (ex : RecEx V) {X : V}
    (hX : X ∈ˢ (univ (S.u₀ ls) : V)) (hXF : X ⊆ˢ S.Fam M ls ps (S.memberIdx M ls N ps))
    (hkey : ∀ x, x ∈ˢ X → ∃ v, S.RecGraphN M ls N q ps ex (false, S.memberIdx M ls N ps) x v) :
    ∀ x, x ∈ˢ S.classSet M ls N ps X → ∃ v, S.RecGraphN M ls N q ps ex (true, []) x v := by
  refine hcl.ind X hX (fun y => ∃ v, S.RecGraphN M ls N q ps ex (true, []) y v) ?_
  intro j c fs hc hfit
  exact ⟨_, S.RecGraphN_intro M ls N q (Or.inr ⟨j, c, fs, _, rfl, hc,
    S.ClassFits_mono M ls N hcl hX (S.Fam_mem_univ M ls _ _) hXF hfit, rfl,
    S.IhOkN_ihSemN_class_of M ls N q ex hkey (fun _ _ hy => hy.2) hfit,
    rfl⟩)⟩

/-- A block constructor's fields fitting the family's separation by a
property: each reflexive field's applications have the property, and
each container field's value is in the class at the separated fibre. -/
theorem sep_fields {ps : List V} (hN : S.nest = some N) (P : List V → V → Prop) {c : CtorSpec}
    {fs : List V}
    (hfit : S.FitsFields M ls (fun is' => sep (S.Fam M ls ps is') (P is')) ps c.fields fs)
    {k : Nat} {f : Field} (hf : c.fields[c.fields.length - 1 - k]? = some f)
    (hk : k < c.fields.length) :
    match f with
    | .reflexive tele es =>
      ∀ ys, FitsVals M (S.ψ ls) (consList (earlier fs k) (envP ps)) tele ys →
        let is := S.idxVals M ls (consList ys (consList (earlier fs k) (envP ps))) es
        appList (fieldVal fs k) ys.reverse ∈ˢ S.Fam M ls ps is ∧
          P is (appList (fieldVal fs k) ys.reverse)
    | .container =>
      fieldVal fs k ∈ˢ S.classSet M ls N ps
        (sep (S.Fam M ls ps (S.memberIdx M ls N ps)) (P (S.memberIdx M ls N ps)))
    | .ordinary _ => True := by
  have hget := S.FitsFields_get M ls hfit hf hk
  cases f with
  | ordinary _ => trivial
  | reflexive tele es =>
    intro ys hys
    dsimp only [fieldSet] at hget
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
    exact mem_sep.mp hmem
  | container =>
    rw [S.fieldSet_container M ls hN] at hget
    exact hget

/-- **Totality of the joint graph** on the family and on the class
(above a proposition): by induction over the family, with an inner
induction over the class at the approximant's fibre at every container
field. -/
theorem RecGraphN_total (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V) :
    (∀ is x, x ∈ˢ S.Fam M ls ps is → ∃ v, S.RecGraphN M ls N q ps ex (false, is) x v) ∧
    (∀ x, x ∈ˢ S.classAt M ls N ps → ∃ v, S.RecGraphN M ls N q ps ex (true, []) x v) := by
  have key : ∀ is x, x ∈ˢ S.Fam M ls ps is → ∃ v, S.RecGraphN M ls N q ps ex (false, is) x v := by
    refine S.Fam_induction M ls hnr hb hco
      (fun is x => ∃ v, S.RecGraphN M ls N q ps ex (false, is) x v) ?_
    intro is x hs
    obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
    have hfitF := S.FitsFields_of_sep M ls hco _ hfit
    have hcv : S.ctorVal ls j fs = tag (S.tagOf j) (tuple fs.reverse) := by simp [ctorVal, hz]
    suffices hihs : ListRel (S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs) c.recFields
        (c.recFields.map (S.ihSemN M ls N q ps ex fs)) from
      ⟨_, S.RecGraphN_intro M ls N q (Or.inl ⟨j, c, fs, _, is, rfl, hc, hfitF, his, hcv, hihs, rfl⟩)⟩
    refine ListRel.map ?_
    intro kf hkf
    obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
    have hsep := S.sep_fields M ls N hN _ hfit hf hk
    obtain ⟨k, f⟩ := kf
    cases f with
    | ordinary _ => simp [Field.isRec] at hrec
    | reflexive tele es =>
      dsimp only [IhOkN, ihSemN]
      refine ⟨_, rfl, ?_⟩
      intro ys hys
      have hlen := FitsVals_length M _ hys
      simp only [readEnv_consList hlen]
      exact S.RecGraphN_recFnN M ls N q (hsep ys hys).2
    | container =>
      dsimp only [IhOkN, ihSemN]
      refine S.RecGraphN_recFnN M ls N q (S.class_total_of M ls N q hcl ex ?_ ?_ ?_ _ hsep)
      · exact sep_mem_univ (S.Fam_mem_univ M ls ps _)
      · exact sep_sub
      · intro x hx
        exact (mem_sep.mp hx).2
  refine ⟨key, ?_⟩
  exact S.class_total_of M ls N q hcl ex (S.Fam_mem_univ M ls _ _) (Sub.refl _)
    fun x hx => key _ x hx

/-- The inductive hypotheses' semantic values are what the graph
demands, at a block constructor's fitting fields. -/
theorem IhOkN_ihSemN (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {c : CtorSpec} {fs : List V}
    (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs) :
    ListRel (S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs) c.recFields
      (c.recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  have ht := S.RecGraphN_total M ls N q hN hz hnr hb hco hcl ex
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhOkN, ihSemN]
    refine ⟨_, rfl, ?_⟩
    intro ys hys
    have hlen := FitsVals_length M _ hys
    have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
    simp only [readEnv_consList hlen]
    exact S.RecGraphN_recFnN M ls N q (ht.1 _ _ hmem)
  | container =>
    rw [S.fieldSet_container_Fam M ls N hN] at hget
    dsimp only [IhOkN, ihSemN]
    exact S.RecGraphN_recFnN M ls N q (ht.2 _ hget)

/-- The inductive hypotheses' semantic values are what the graph
demands, at a container constructor's fitting fields. -/
theorem IhOkN_ihSemN_class (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {c : CtorSpec} {fs : List V}
    (hfit : S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    ListRel (S.IhOkN M ls q (S.RecGraphN M ls N q) ps ex fs) (S.classCtor N c).recFields
      ((S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  have ht := S.RecGraphN_total M ls N q hN hz hnr hb hco hcl ex
  exact S.IhOkN_ihSemN_class_of M ls N q ex (fun x hx => ht.1 _ _ hx) (fun y hy _ => ht.2 y hy) hfit

/-- **The ι equation of `T.rec`**: at a constructor value whose fields
fit, the recursor is the minor at the fields and the hypotheses'
values. -/
theorem recSemN_eq (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {j : Nat} {c : CtorSpec} (hc : S.ctors[j]? = some c) {fs : List V}
    (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs) :
    S.recSemN M ls N q ps ex (S.idxVals M ls (consList fs (envP ps)) c.idx) (S.ctorVal ls j fs)
      = appList (S.minorAt ex.mins j) (fs.reverse ++ c.recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  have hcv : S.ctorVal ls j fs = tag (S.tagOf j) (tuple fs.reverse) := by simp [ctorVal, hz]
  unfold recSemN
  rw [hcv]
  exact S.recFnN_eq M ls N q (S.RecGraphN_intro M ls N q (Or.inl ⟨j, c, fs, _, _, rfl, hc, hfit, rfl,
    rfl, S.IhOkN_ihSemN M ls N q hN hz hnr hb hco hcl ex hfit, rfl⟩))

/-- **The ι equation of `T.rec_1`**: at a container constructor's
value (the tagged tuple of fields fitting it at the instantiation),
the auxiliary recursor is the class minor at the fields and the
hypotheses' values. -/
theorem rec1Sem_eq (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c) {fs : List V}
    (hfit : S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    S.rec1Sem M ls N q ps ex (tag j (tuple fs.reverse))
      = appList (minorKAt N ex.minsK j)
          (fs.reverse ++ (S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  unfold rec1Sem
  exact S.recFnN_eq M ls N q (S.RecGraphN_intro M ls N q (Or.inr ⟨j, c, fs, _, rfl, hc, hfit, rfl,
    S.IhOkN_ihSemN_class M ls N q hN hz hnr hb hco hcl ex hfit, rfl⟩))

/-! ## Typing -/

/-- **The inner step of the typing**: at fields fitting a translated
constructor at a parameter set on which `T.rec` is typed, with `T.rec_1`
typed on the `Q`-members of the class at it, the hypotheses' semantic
values are typed. -/
theorem IhTypedN_ihSemN_class_of {ps : List V} (ex : RecEx V)
    {X : V} {Q : V → Prop}
    (hkey : ∀ x, x ∈ˢ X → S.recFnN M ls N q ps ex (false, S.memberIdx M ls N ps) x ∈ˢ
      appList ex.m ((S.memberIdx M ls N ps).reverse ++ [x]))
    (hQ : ∀ y, y ∈ˢ S.classSet M ls N ps X → Q y →
      S.rec1Sem M ls N q ps ex y ∈ˢ appList ex.m1 [y])
    {c : CtorSpec} {fs : List V}
    (hfit : S.ClassFits M ls N X Q ps (S.classCtor N c).fields fs) :
    ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields
      ((S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
  have hget := S.ClassFits_get M ls N hfit hf hk
  have hlen := S.ClassFits_length M ls N hfit
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | reflexive tele es =>
    obtain ⟨f₀, -, hfe⟩ := S.classCtor_fields_get N c hf hk
    obtain ⟨rfl, hes⟩ := S.classField_reflexive N hfe.symm
    dsimp only at hes
    subst hes
    dsimp only [classFieldSet] at hget
    dsimp only [IhTypedN, ihSemN, piCtx_nil, lamCtx_nil, readEnv_zero, List.reverse_nil, appList_nil,
      recSemN]
    rw [S.memberIdx_earlier M ls N ps (by omega)]
    exact hkey _ hget
  | container =>
    dsimp only [classFieldSet] at hget
    rw [mem_sep] at hget
    dsimp only [IhTypedN, ihSemN]
    exact hQ _ hget.1 hget.2

/-- **The inner induction of the typing**: `T.rec_1` is typed on the
class at a parameter set inside the fibre on which `T.rec` is typed. -/
theorem class_mem_of (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c) {X : V}
    (hX : X ∈ˢ (univ (S.u₀ ls) : V)) (hXF : X ⊆ˢ S.Fam M ls ps (S.memberIdx M ls N ps))
    (hkey : ∀ x, x ∈ˢ X → S.recFnN M ls N q ps ex (false, S.memberIdx M ls N ps) x ∈ˢ
      appList ex.m ((S.memberIdx M ls N ps).reverse ++ [x])) :
    ∀ x, x ∈ˢ S.classSet M ls N ps X → S.rec1Sem M ls N q ps ex x ∈ˢ appList ex.m1 [x] := by
  refine hcl.ind X hX (fun y => S.rec1Sem M ls N q ps ex y ∈ˢ appList ex.m1 [y]) ?_
  intro j c fs hc hfit
  have hfitM := S.ClassFits_mono M ls N hcl hX (S.Fam_mem_univ M ls _ _) hXF hfit
  show S.rec1Sem M ls N q ps ex (tag j (tuple fs.reverse)) ∈ˢ appList ex.m1 [tag j (tuple fs.reverse)]
  rw [S.rec1Sem_eq M ls N q hN hz hnr hb hco hcl ex hc hfitM]
  exact hminK j c hc fs hfitM _ (S.IhTypedN_ihSemN_class_of M ls N q ex hkey
    (fun _ _ hy => hy.2) hfit)

/-- **The recursors' typing** (above a proposition): at a member of
the fibre, `T.rec`'s value lies in the block's motive at the indices
and the member; at a member of the class, `T.rec_1`'s value lies in
the class's motive at it — by the interleaved induction, from the
minors' typing.  At a motive into a proposition the block's motive
must be a truth value (for the reflexive fields' hypotheses). -/
theorem recSemN_mem (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList ex.m (is.reverse ++ [t]) ∈ˢ (univ 0 : V)) :
    (∀ is t, t ∈ˢ S.Fam M ls ps is → S.recSemN M ls N q ps ex is t ∈ˢ appList ex.m (is.reverse ++ [t])) ∧
    (∀ t, t ∈ˢ S.classAt M ls N ps → S.rec1Sem M ls N q ps ex t ∈ˢ appList ex.m1 [t]) := by
  have key : ∀ is x, x ∈ˢ S.Fam M ls ps is →
      S.recFnN M ls N q ps ex (false, is) x ∈ˢ appList ex.m (is.reverse ++ [x]) := by
    refine S.Fam_induction M ls hnr hb hco
      (fun is x => S.recFnN M ls N q ps ex (false, is) x ∈ˢ appList ex.m (is.reverse ++ [x])) ?_
    intro is x hs
    obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
    have hfitF := S.FitsFields_of_sep M ls hco _ hfit
    have hcv : S.ctorVal ls j fs = tag (S.tagOf j) (tuple fs.reverse) := by simp [ctorVal, hz]
    subst his
    rw [hcv, S.recFnN_eq M ls N q (S.RecGraphN_intro M ls N q (Or.inl ⟨j, c, fs, _, _, rfl, hc, hfitF,
      rfl, rfl, S.IhOkN_ihSemN M ls N q hN hz hnr hb hco hcl ex hfitF, rfl⟩)), ← hcv]
    refine hmin j c hc fs hfitF _ (ListRel.map ?_)
    intro kf hkf
    obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
    have hsep := S.sep_fields M ls N hN _ hfit hf hk
    obtain ⟨k, f⟩ := kf
    cases f with
    | ordinary _ => simp [Field.isRec] at hrec
    | reflexive tele es =>
      dsimp only [IhTypedN, ihSemN]
      refine lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_
      · have hlen := FitsVals_length M _ hys
        simp only [readEnv_consList hlen, recSemN]
        exact (hsep ys hys).2
      · have hlen := FitsVals_length M _ hys
        simp only [readEnv_consList hlen]
        exact hmo hq _ _ (hsep ys hys).1
    | container =>
      dsimp only [IhTypedN, ihSemN]
      refine S.class_mem_of M ls N q hN hz hnr hb hco hcl ex hminK ?_ ?_ ?_ _ hsep
      · exact sep_mem_univ (S.Fam_mem_univ M ls ps _)
      · exact sep_sub
      · intro x hx
        exact (mem_sep.mp hx).2
  refine ⟨fun is t ht => key is t ht, ?_⟩
  exact S.class_mem_of M ls N q hN hz hnr hb hco hcl ex hminK (S.Fam_mem_univ M ls _ _) (Sub.refl _)
    fun x hx => key _ x hx

/-- **The inductive hypotheses' values are typed**, at a block
constructor's fitting fields. -/
theorem IhTypedN_ihSemN (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList ex.m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    {c : CtorSpec} {fs : List V}
    (hfit : S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs) :
    ListRel (S.IhTypedN M ls q ps ex fs) c.recFields (c.recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  have hrec := S.recSemN_mem M ls N q hN hz hnr hb hco hcl ex hmin hminK hmo
  refine ListRel.map ?_
  intro kf hkf
  obtain ⟨hf, hk, hrec'⟩ := mem_recFields hkf
  have hget := S.FitsFields_get M ls hfit hf hk
  obtain ⟨k, f⟩ := kf
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec'
  | reflexive tele es =>
    dsimp only [fieldSet] at hget
    dsimp only [IhTypedN, ihSemN]
    refine lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_
    · have hlen := FitsVals_length M _ hys
      have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
      simp only [readEnv_consList hlen]
      exact hrec.1 _ _ hmem
    · have hlen := FitsVals_length M _ hys
      have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
      simp only [readEnv_consList hlen]
      exact hmo hq _ _ hmem
  | container =>
    rw [S.fieldSet_container_Fam M ls N hN] at hget
    dsimp only [IhTypedN, ihSemN]
    exact hrec.2 _ hget

/-- **The inductive hypotheses' values are typed**, at a container
constructor's fitting fields. -/
theorem IhTypedN_ihSemN_class (hN : S.nest = some N) (hz : S.z ls = false) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList ex.m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    {c : CtorSpec} {fs : List V}
    (hfit : S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields
      ((S.classCtor N c).recFields.map (S.ihSemN M ls N q ps ex fs)) := by
  have hrec := S.recSemN_mem M ls N q hN hz hnr hb hco hcl ex hmin hminK hmo
  exact S.IhTypedN_ihSemN_class_of M ls N q ex (fun x hx => hrec.1 _ _ hx)
    (fun y hy _ => hrec.2 y hy) hfit

/-- **The motives are inhabited** on the family and on the class, at
a proposition (where the values are not the recursors'): by the
interleaved induction from the minors' typing, with inhabited truth
values as the hypotheses. -/
theorem motive_inhabitedN (hN : S.nest = some N) {ps : List V}
    (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps) (hco : S.ContOk M ls ps)
    (hcl : S.ClassLaws M ls N ps) (ex : RecEx V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOkN M ls q ps ex j c)
    (hminK : ∀ j c, N.K.ctors[j]? = some c → S.MinorOkK M ls N q ps ex j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList ex.m (is.reverse ++ [t]) ∈ˢ (univ 0 : V)) :
    (∀ is t, t ∈ˢ S.Fam M ls ps is → ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [t])) ∧
    (∀ t, t ∈ˢ S.classAt M ls N ps → ∃ v, v ∈ˢ appList ex.m1 [t]) := by
  -- the inner induction, at a parameter set inside the fibre on which the block's motive is inhabited
  have inner : ∀ (X : V) (x : V), x ∈ˢ S.classSet M ls N ps X → X ∈ˢ (univ (S.u₀ ls) : V) →
      X ⊆ˢ S.Fam M ls ps (S.memberIdx M ls N ps) →
      (∀ x, x ∈ˢ X → ∃ v, v ∈ˢ appList ex.m ((S.memberIdx M ls N ps).reverse ++ [x])) →
      ∃ v, v ∈ˢ appList ex.m1 [x] := by
    intro X x hx hX hXF hkey
    refine hcl.ind X hX (fun y => ∃ v, v ∈ˢ appList ex.m1 [y]) ?_ x hx
    intro j c fs hc hfit
    have hfitM := S.ClassFits_mono M ls N hcl hX (S.Fam_mem_univ M ls _ _) hXF hfit
    obtain ⟨ihs, hihs⟩ : ∃ ihs, ListRel (S.IhTypedN M ls q ps ex fs) (S.classCtor N c).recFields ihs := by
      refine ListRel.exists_of_forall fun kf hkf => ?_
      obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
      have hget := S.ClassFits_get M ls N hfit hf hk
      have hlen := S.ClassFits_length M ls N hfit
      obtain ⟨k, f⟩ := kf
      cases f with
      | ordinary _ => simp [Field.isRec] at hrec
      | reflexive tele es =>
        obtain ⟨f₀, -, hfe⟩ := S.classCtor_fields_get N c hf hk
        obtain ⟨rfl, hes⟩ := S.classField_reflexive N hfe.symm
        dsimp only at hes
        subst hes
        dsimp only [classFieldSet] at hget
        dsimp only [IhTypedN, piCtx_nil, readEnv_zero, List.reverse_nil, appList_nil]
        rw [S.memberIdx_earlier M ls N ps (by omega)]
        exact hkey _ hget
      | container =>
        dsimp only [classFieldSet] at hget
        rw [mem_sep] at hget
        dsimp only [IhTypedN]
        exact hget.2.2
    exact ⟨_, hminK j c hc fs hfitM ihs hihs⟩
  have key : ∀ is x, x ∈ˢ S.Fam M ls ps is → ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [x]) := by
    refine S.Fam_induction M ls hnr hb hco
      (fun is x => ∃ v, v ∈ˢ appList ex.m (is.reverse ++ [x])) ?_
    intro is x hs
    obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
    have hfitF := S.FitsFields_of_sep M ls hco _ hfit
    subst his
    -- the inductive hypotheses: one inhabitant of each hypothesis' type
    obtain ⟨ihs, hihs⟩ : ∃ ihs, ListRel (S.IhTypedN M ls q ps ex fs) c.recFields ihs := by
      refine ListRel.exists_of_forall fun kf hkf => ?_
      obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
      have hsep := S.sep_fields M ls N hN _ hfit hf hk
      obtain ⟨k, f⟩ := kf
      cases f with
      | ordinary _ => simp [Field.isRec] at hrec
      | reflexive tele es =>
        dsimp only [IhTypedN]
        refine ⟨lamCtx M (S.ψ ls) q _ tele fun ρ' => pickMem (appList ex.m ((S.idxVals M ls ρ' es).reverse ++
          [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])),
          lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_⟩
        · have hlen := FitsVals_length M _ hys
          refine pickMem_mem ?_
          simp only [readEnv_consList hlen]
          exact (hsep ys hys).2
        · have hlen := FitsVals_length M _ hys
          simp only [readEnv_consList hlen]
          exact hmo hq _ _ (hsep ys hys).1
      | container =>
        dsimp only [IhTypedN]
        refine inner _ _ hsep ?_ ?_ ?_
        · exact sep_mem_univ (S.Fam_mem_univ M ls ps _)
        · exact sep_sub
        · intro x hx
          exact (mem_sep.mp hx).2
    exact ⟨_, hmin j c hc fs hfitF ihs hihs⟩
  refine ⟨fun is t ht => key is t ht, fun t ht => ?_⟩
  exact inner _ _ ht (S.Fam_mem_univ M ls _ _) (Sub.refl _) fun x hx => key _ x hx

end IndSpec

end Fragment
