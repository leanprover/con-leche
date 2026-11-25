module

import ConLeche.SetModel.GraphRec
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# The nested recursor's graph kit: majors over several CLASSES

The graph kit (`SetModel/GraphRec.lean`, `GraphRecKit`) asks ONE thing of
the majors: an induction principle (`ind`).  At a flat block the majors
are the members' carriers and `ind` is the block's lfp induction.  At a
NESTED block the recursor family also ranges over the CONTAINER CLASSES
— `List Tree`, `Rose T`, `List (Rose T)` — each the least fixed point of
its OWN operator, at its OWN instantiation (the container's lfp clause at
the parameter frame the instantiation reads).  This module builds the
kit over such a family of classes and proves `ind` from the classes'
own clauses, by a STRENGTHENED PREDICATE:

* a class is a clause (`SClause`: an operator per parameter frame, its
  fit relation and injections) at its TRUE frame `fr b`;
* its container fields' classes are reached, during the induction, at
  SEPARATED frames — the instantiation read at the enclosing class's
  separated tuple; which frames count is the kit's `Adm` (admissible:
  "a frame whose parameter positions hold elements satisfying `G : V`");
* at such a frame the class's own induction runs with the predicate
  "lies in the TRUE class ∧ the property"; membership in the true class
  is re-established at each constructor by the class's clause at the
  TRUE frame (the fibre law, backwards, and closure), after moving the
  constructor's fit from the separated frame and tuple to the true ones
  (`trans`).  The only inclusion the induction itself produces is the
  separation `sep ⊆ carrier`.

In this first-order formulation, frames of class `b` are finite tuples
`Fin (frLen b) → V`, `G : V` is an unbounded set of encoded majors
`nenc b c t y`, `SClause` carries `DefTupleOp`, and `NestKit.ind` is
guarded by `HasSep K.U P`.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

open Tower

universe u

variable {V : Type u} [SetTheory V]

/-! ## Clauses -/

/-- **A class presentation**: the set-level lfp clause of an inductive
block as a function of its finite parameter frame (`Fin len → V`).  The
index sets do not depend on the frame (an instance's index telescope is
hole-free). -/
structure SClause (V : Type u) [SetTheory V] (len : Nat) where
  /-- the level -/
  w : Nat
  /-- the width (components) -/
  N : Nat
  /-- per component: the index-tuple set -/
  Is : Nat → V
  /-- the operator at a frame -/
  Φ : (Fin len → V) → (Nat → V) → Nat → V
  /-- first-order tuple definability of the operator at every frame -/
  hΦ : ∀ ρ : Fin len → V, DefTupleOp N (Φ ρ)
  /-- the fit relation at a frame and a hole tuple: `Fits ρ X t c j fs` -/
  Fits : (Fin len → V) → (Nat → V) → V → Nat → Nat → List V → Prop
  /-- the injections: `inj c j fs` -/
  inj : Nat → Nat → List V → V

namespace SClause

variable {len : Nat}

/-- The carrier at a frame: the least pre-fixed tuple. -/
noncomputable def carrier (C : SClause V len) (ρ : Fin len → V) : Nat → V :=
  lfpTuple C.w C.N C.Is (C.Φ ρ) (C.hΦ ρ)

/-- **The clause at a frame**: what `lfpTuple`'s laws need, and what the
operator is (the fibre law). -/
structure OkAt (C : SClause V len) (ρ : Fin len → V) : Prop where
  mono : MonoTuple C.w C.N C.Is (C.Φ ρ)
  maps : MapsTuple C.w C.N C.Is (C.Φ ρ)
  closed : ∃ L, IsClosedTuple C.w C.N C.Is (C.Φ ρ) L
  fibre : ∀ X, InTupleSpace C.w C.N C.Is X → ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ x,
    x ∈ˢ app (C.Φ ρ X c) t ↔ ∃ j fs, C.Fits ρ X t c j fs ∧ x = C.inj c j fs

variable {C : SClause V len}

theorem carrier_mem (C : SClause V len) (ρ : Fin len → V) :
    InTupleSpace C.w C.N C.Is (C.carrier ρ) :=
  lfpTuple_mem _ _ _ _ _

/-- **Introduction**: a spine fitting at the carrier is, injected, a
member of the carrier (the fibre law backwards, then closure). -/
theorem OkAt.inj_mem {ρ : Fin len → V} (h : C.OkAt ρ) {c : Nat} (hc : c < C.N)
    {t : V} (ht : t ∈ˢ C.Is c) {j : Nat} {fs : List V} (hf : C.Fits ρ (C.carrier ρ) t c j fs) :
    C.inj c j fs ∈ˢ app (C.carrier ρ c) t :=
  lfpTuple_closed h.closed h.mono h.maps c hc t ht _
    ((h.fibre _ (C.carrier_mem ρ) c hc t ht _).mpr ⟨j, fs, hf, rfl⟩)

/-- **The class's induction principle** at a frame (for a `DefRel 2`
predicate): `lfpTuple_induction_of_def` read through the fibre law. -/
theorem OkAt.ind {ρ : Fin len → V} (h : C.OkAt ρ) (Q : Nat → V → V → Prop)
    (hQdef : ∀ c, c < C.N → DefRel 2 fun v => Q c (v 0) (v 1))
    (hstep : ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ j fs,
      C.Fits ρ (sepTuple_of_def C.w C.N C.Is (C.Φ ρ) (C.hΦ ρ) Q hQdef) t c j fs →
      Q c t (C.inj c j fs)) :
    ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ x, x ∈ˢ app (C.carrier ρ c) t → Q c t x := by
  refine lfpTuple_induction_of_def h.closed h.mono h.maps Q hQdef fun c hc t ht x hx => ?_
  obtain ⟨j, fs, hf, rfl⟩ :=
    (h.fibre _ (sepTuple_mem _ _ _ _ _ _ _ _) c hc t ht x).mp hx
  exact hstep c hc t ht j fs hf

/-- **The class's induction principle** at a frame with explicit `HasSep` /
`HasGraph` witnesses. -/
theorem OkAt.ind_sep {ρ : Fin len → V} (h : C.OkAt ρ) (Q : Nat → V → V → Prop)
    (hSep : ∀ m, m < C.N → ∀ i, HasSep (app (C.carrier ρ m) i) (Q m i))
    (hGr : ∀ m (hm : m < C.N), HasGraph (C.Is m) fun i =>
      dropTo (strictU C.w) (sep (app (C.carrier ρ m) i) (Q m i) (hSep m hm i)))
    (hstep : ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ j fs,
      C.Fits ρ (sepTuple C.w C.N C.Is (C.Φ ρ) (C.hΦ ρ) Q hSep hGr) t c j fs →
      Q c t (C.inj c j fs)) :
    ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ x, x ∈ˢ app (C.carrier ρ c) t → Q c t x := by
  refine lfpTuple_induction h.closed h.mono h.maps Q hSep hGr fun c hc t ht x hx => ?_
  obtain ⟨j, fs, hf, rfl⟩ :=
    (h.fibre _ (sepTuple_mem _ _ _ _ _ _ _ _) c hc t ht x).mp hx
  exact hstep c hc t ht j fs hf

end SClause

/-! ## Majors and decodings -/

/-- **A decoding**: the class, the component, the index tuple, the
constructor and the fields. -/
structure NDec (V : Type u) where
  cls : Nat
  c : Nat
  t : V
  j : Nat
  fs : List V

/-- **The major** of class `b`, component `c`, index tuple `t`, value `x`. -/
noncomputable def nenc (b c : Nat) (t x : V) : V := kpair (vnat b) (tagged c t x)

theorem nenc_inj {b c b' c' : Nat} {t x t' x' : V} (h : nenc b c t x = nenc b' c' t' x') :
    b = b' ∧ c = c' ∧ t = t' ∧ x = x' := by
  unfold nenc at h
  obtain ⟨h1, h2⟩ := kpair_inj h
  obtain ⟨h3, h4, h5⟩ := tagged_inj h2
  exact ⟨vnat_inj h1, h3, h4, h5⟩

theorem DefFun.nenc_apply {p : Nat} (b c : Nat) {T X : (Fin p → V) → V}
    (hT : DefFun p T) (hX : DefFun p X) :
    DefFun p fun env => nenc b c (T env) (X env) :=
  DefFun.kpair_apply (DefFun.const (vnat b)) (DefFun.tagged_apply c hT hX)

/-- Set-level extension of `G : V` by the encoded elements `nenc b c t y`
of one class's hole tuple `Y` (`c < N`, `t ∈ˢ Is c`, `y ∈ˢ app (Y c) t`). -/
noncomputable def addOwn (G : V) (b N : Nat) (Is Y : Nat → V) : V :=
  binUnion G (image (kpair (vnat b)) (unionSet N Is Y)
    (hasImage_of_defFun1 (DefFun.kpair_apply (DefFun.const (vnat b)) (DefFun.proj 0)) _))

theorem mem_addOwn {G : V} {b N : Nat} {Is Y : Nat → V} {u : V} :
    u ∈ˢ addOwn G b N Is Y ↔
      u ∈ˢ G ∨ ∃ c t y, c < N ∧ t ∈ˢ Is c ∧ y ∈ˢ app (Y c) t ∧ u = nenc b c t y := by
  unfold addOwn
  rw [mem_binUnion, mem_image]
  constructor
  · rintro (hu | ⟨p, hp, rfl⟩)
    · exact Or.inl hu
    · obtain ⟨c, hc, t, ht, y, hy, rfl⟩ := mem_unionSet.mp hp
      exact Or.inr ⟨c, t, y, hc, ht, hy, rfl⟩
  · rintro (hu | ⟨c, t, y, hc, ht, hy, rfl⟩)
    · exact Or.inl hu
    · exact Or.inr ⟨tagged c t y, tagged_mem_unionSet hc ht hy, rfl⟩

theorem mem_addOwn_nenc {G : V} {b N : Nat} {Is Y : Nat → V} {b' c : Nat} {t y : V} :
    nenc b' c t y ∈ˢ addOwn G b N Is Y ↔
      nenc b' c t y ∈ˢ G ∨ (b' = b ∧ c < N ∧ t ∈ˢ Is c ∧ y ∈ˢ app (Y c) t) := by
  rw [mem_addOwn]
  constructor
  · rintro (h | ⟨c', t', y', hc', ht', hy', heq⟩)
    · exact Or.inl h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := nenc_inj heq
      exact Or.inr ⟨rfl, hc', ht', hy'⟩
  · rintro (h | ⟨rfl, hc, ht, hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, t, y, hc, ht, hy, rfl⟩

theorem DefFun.addOwn_apply {p : Nat} (b N : Nat)
    {G : (Fin p → V) → V} {Is Y : Nat → (Fin p → V) → V}
    (hG : DefFun p G)
    (hIs : ∀ c, c < N → DefFun p (Is c))
    (hY : ∀ c, c < N → DefFun p (Y c)) :
    DefFun p fun env => addOwn (G env) b N (fun c => Is c env) (fun c => Y c env) := by
  unfold addOwn
  exact DefFun.binUnion_apply hG
    (DefFun.image_apply_curry
      (DefFun.kpair_apply (DefFun.const (vnat b)) (DefFun.proj 0))
      (DefFun.unionSet_apply N hIs hY))

/-- **The majors** of a family of classes `cl` at their true frames `fr`. -/
noncomputable def nestU (nC : Nat) {frLen : Nat → Nat}
    (cl : (b : Nat) → SClause V (frLen b))
    (fr : (b : Nat) → Fin (frLen b) → V) : V :=
  sigmaPairs (sep omega (fun a => ∃ n, n < nC ∧ a = vnat n) (hasSep_unionDom nC))
    (boundFibre nC fun b => unionSet (cl b).N (cl b).Is ((cl b).carrier (fr b)))
    (hasSigmaPairs_boundFibre _ nC _)

theorem mem_nestU {nC : Nat} {frLen : Nat → Nat}
    {cl : (b : Nat) → SClause V (frLen b)} {fr : (b : Nat) → Fin (frLen b) → V} {u : V} :
    u ∈ˢ nestU nC cl fr ↔
      ∃ b c t x, b < nC ∧ c < (cl b).N ∧ t ∈ˢ (cl b).Is c ∧
        x ∈ˢ app ((cl b).carrier (fr b) c) t ∧ u = nenc b c t x := by
  unfold nestU
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨a, ha, p, hp, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ha
    rw [boundFibre_vnat_lt _ hn] at hp
    obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hp
    exact ⟨n, c, t, x, hn, hc, ht, hx, rfl⟩
  · rintro ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩
    refine ⟨vnat b, mem_sep.mpr ⟨vnat_mem_omega b, b, hb, rfl⟩, tagged c t x, ?_, rfl⟩
    rw [boundFibre_vnat_lt _ hb]
    exact tagged_mem_unionSet hc ht hx

/-! ## The kit -/

/-- **The nested recursion data over several classes.**  Classes are
`b < nC`; class `b` is the clause `cl b` at its TRUE frame `fr b : Fin (frLen b) → V`;
its nesting depth is `dp b` (below `D`).  `Adm b G ρ`: `ρ` is a frame at
which class `b` is visited during the induction, its parameter positions
holding elements whose encodings `nenc b' c' t' y` lie in `G : V`. -/
structure NestKit (V : Type u) [SetTheory V] where
  /-- the number of classes -/
  nC : Nat
  /-- frame arity per class -/
  frLen : Nat → Nat
  /-- the classes' clauses -/
  cl : (b : Nat) → SClause V (frLen b)
  /-- the TRUE frames -/
  fr : (b : Nat) → Fin (frLen b) → V
  /-- the nesting depth -/
  dp : Nat → Nat
  /-- a bound on the depths -/
  D : Nat
  hD : ∀ b, b < nC → dp b < D
  /-- the admissible (separated) frames, parameterized by set `G : V` -/
  Adm : (b : Nat) → V → (Fin (frLen b) → V) → Prop
  /-- the recursive calls' majors at a decoding -/
  pred : NDec V → V
  /-- the clause holds at every admissible frame -/
  ok : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → (cl b).OkAt ρ
  /-- **the tie to the true frame** (positivity at the instantiation, then
  the clause's `fitsMono`): at an admissible frame whose parameter
  positions hold true elements, a spine fitting at holes below the true
  carrier fits at the true frame and carrier -/
  trans : ∀ b, b < nC → ∀ G : V,
    (∀ b' c t y, nenc b' c t y ∈ˢ G → y ∈ˢ app ((cl b').carrier (fr b') c) t) →
    ∀ ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    TupleLe (cl b).N (cl b).Is Y ((cl b).carrier (fr b)) →
    ∀ t c j fs, c < (cl b).N → (cl b).Fits ρ Y t c j fs →
      (cl b).Fits (fr b) ((cl b).carrier (fr b)) t c j fs
  /-- **the call targets**, at a spine fitting at an admissible frame:
  an own recursive field, a parameter-position element (`nenc ∈ˢ G`),
  or an element of a DEEPER class at an admissible frame for `G`
  extended by the current hole tuple (`addOwn`) -/
  calls : ∀ b, b < nC → ∀ G : V, ∀ ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    ∀ c t j fs, c < (cl b).N → t ∈ˢ (cl b).Is c → (cl b).Fits ρ Y t c j fs →
    ∀ u, u ∈ˢ pred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < nC ∧ c' < (cl b').N ∧
      t' ∈ˢ (cl b').Is c' ∧ u = nenc b' c' t' y ∧
      ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ nenc b' c' t' y ∈ˢ G ∨
        (dp b < dp b' ∧ ∃ ρ', Adm b' (addOwn G b (cl b).N (cl b).Is Y) ρ' ∧
          y ∈ˢ app ((cl b').carrier ρ' c') t'))
  /-- **the true frames are admissible** at a class with an index, once the
  shallower classes' true elements have encodings in `G` (a class with no
  index has no element, and needs no frame) -/
  top : ∀ b, b < nC → (∃ c, c < (cl b).N ∧ ∃ t, t ∈ˢ (cl b).Is c) →
    ∀ G : V, (∀ b' c t y, b' < nC → dp b' < dp b → c < (cl b').N →
      t ∈ˢ (cl b').Is c → y ∈ˢ app ((cl b').carrier (fr b') c) t → nenc b' c t y ∈ˢ G) →
    Adm b G (fr b)

namespace NestKit

variable (K : NestKit V)

/-- The true class `b`: its clause's carrier at its true frame. -/
noncomputable def KT (b : Nat) : Nat → V := (K.cl b).carrier (K.fr b)

/-- **The majors**: the tagged elements of every true class. -/
noncomputable def U : V := nestU K.nC K.cl K.fr

theorem mem_U {u : V} :
    u ∈ˢ K.U ↔ ∃ b c t x, b < K.nC ∧ c < (K.cl b).N ∧ t ∈ˢ (K.cl b).Is c ∧
      x ∈ˢ app (K.KT b c) t ∧ u = nenc b c t x :=
  mem_nestU

theorem nenc_mem_U {b c : Nat} {t x : V} (hb : b < K.nC) (hc : c < (K.cl b).N)
    (ht : t ∈ˢ (K.cl b).Is c) (hx : x ∈ˢ app (K.KT b c) t) : nenc b c t x ∈ˢ K.U :=
  K.mem_U.mpr ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩

/-- **The decodings**: a spine fitting one of the class's constructors
at its TRUE frame and carrier. -/
def Dec (u : V) (d : NDec V) : Prop :=
  d.cls < K.nC ∧ d.c < (K.cl d.cls).N ∧ d.t ∈ˢ (K.cl d.cls).Is d.c ∧
    (K.cl d.cls).Fits (K.fr d.cls) (K.KT d.cls) d.t d.c d.j d.fs ∧
    u = nenc d.cls d.c d.t ((K.cl d.cls).inj d.c d.j d.fs)

/-- The class `b`, if it has an index, is a clause at its true frame (from `top` and `ok`). -/
theorem okT {b : Nat} (hb : b < K.nC) (hne : ∃ c, c < (K.cl b).N ∧ ∃ t, t ∈ˢ (K.cl b).Is c) :
    (K.cl b).OkAt (K.fr b) :=
  K.ok b hb _ _ (K.top b hb hne K.U fun _ _ _ _ hb' _ hc' ht' hy => K.nenc_mem_U hb' hc' ht' hy)

/-- The property, strengthened by membership in the true class. -/
def Good (P : V → Prop) (b c : Nat) (t y : V) : Prop :=
  y ∈ˢ app (K.KT b c) t ∧ P (nenc b c t y)

/-! ### The strengthened induction at an admissible frame -/

/-- One class, the deeper classes assumed (with `P` separated as `Pset := sep K.U P hSep`). -/
theorem claim_step (P : V → Prop) (hSep : HasSep K.U P)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u)
    {b : Nat} (hb : b < K.nC)
    (ih : ∀ b', b' < K.nC → K.dp b < K.dp b' → ∀ G : V,
      (∀ b'' c t y, nenc b'' c t y ∈ˢ G → K.Good P b'' c t y) →
      ∀ ρ, K.Adm b' G ρ → ∀ c, c < (K.cl b').N → ∀ t, t ∈ˢ (K.cl b').Is c →
      ∀ y, y ∈ˢ app ((K.cl b').carrier ρ c) t → K.Good P b' c t y)
    (G : V) (hG : ∀ b' c t y, nenc b' c t y ∈ˢ G → K.Good P b' c t y)
    (ρ : Fin (K.frLen b) → V) (hρ : K.Adm b G ρ) :
    ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.Good P b c t y := by
  have hok := K.ok b hb G ρ hρ
  let Pset := sep K.U P hSep
  let GoodP : Nat → V → V → Prop := fun c t y => y ∈ˢ app (K.KT b c) t ∧ nenc b c t y ∈ˢ Pset
  have hGoodP_def : ∀ c, c < (K.cl b).N → DefRel 2 fun v => GoodP c (v 0) (v 1) := fun c _ =>
    DefRel.and
      (DefRel.mem_apply (DefFun.proj 1)
        (DefFun.app_apply (DefFun.const (K.KT b c)) (DefFun.proj 0)))
      (DefRel.mem_apply (DefFun.nenc_apply b c (DefFun.proj 0) (DefFun.proj 1))
        (DefFun.const Pset))
  suffices hmain : ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → GoodP c t y by
    intro c hc t ht y hy
    obtain ⟨hyT, hyP⟩ := hmain c hc t ht y hy
    exact ⟨hyT, (mem_sep.mp hyP).2⟩
  refine hok.ind GoodP hGoodP_def fun c hc t ht j fs hf => ?_
  -- the separated tuple, below the true carrier (a separation)
  let S := sepTuple_of_def (K.cl b).w (K.cl b).N (K.cl b).Is ((K.cl b).Φ ρ) ((K.cl b).hΦ ρ)
    GoodP hGoodP_def
  have hSmem : InTupleSpace (K.cl b).w (K.cl b).N (K.cl b).Is S := sepTuple_mem _ _ _ _ _ _ _ _
  have hSgood : ∀ c', c' < (K.cl b).N → ∀ t', t' ∈ˢ (K.cl b).Is c' → ∀ y, y ∈ˢ app (S c') t' →
      K.Good P b c' t' y := fun c' _ t' ht' y hy => by
    obtain ⟨hyT, hyP⟩ := (mem_app_sepTuple_imp ht' hy).2
    exact ⟨hyT, (mem_sep.mp hyP).2⟩
  have hSle : TupleLe (K.cl b).N (K.cl b).Is S (K.KT b) :=
    fun c' hc' t' ht' y hy => (hSgood c' hc' t' ht' y hy).1
  -- the SAME spine fits at the true frame and carrier
  have hfT : (K.cl b).Fits (K.fr b) (K.KT b) t c j fs :=
    K.trans b hb G (fun b' c' t' y hy => (hG b' c' t' y hy).1) ρ hρ S hSmem hSle t c j fs hc hf
  have hmemT : (K.cl b).inj c j fs ∈ˢ app (K.KT b c) t :=
    (K.okT hb ⟨c, hc, t, ht⟩).inj_mem hc ht hfT
  have hmemU := K.nenc_mem_U hb hc ht hmemT
  refine ⟨hmemT, mem_sep.mpr ⟨hmemU,
    hP _ hmemU ⟨⟨b, c, t, j, fs⟩, ⟨hb, hc, ht, hfT, rfl⟩, ?_⟩⟩⟩
  intro u hu
  obtain ⟨b', c', t', y, hb', hc', ht', rfl, hcase⟩ := K.calls b hb G ρ hρ S hSmem c t j fs hc ht hf u hu
  rcases hcase with ⟨rfl, hy⟩ | hy | ⟨hdp, ρ', hρ', hy⟩
  · exact (hSgood c' hc' t' ht' y hy).2
  · exact (hG _ _ _ _ hy).2
  · refine (ih b' hb' hdp _ ?_ ρ' hρ' c' hc' t' ht' y hy).2
    intro b'' c'' t'' y'' hmem
    rcases mem_addOwn_nenc.mp hmem with h | ⟨rfl, hc'', ht'', hy''⟩
    · exact hG _ _ _ _ h
    · exact hSgood c'' hc'' t'' ht'' y'' hy''

/-- **The strengthened induction**: at every admissible frame whose
parameter positions hold good elements, every element of the class is
in the TRUE class and has the property. -/
theorem claim (P : V → Prop) (hSep : HasSep K.U P)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ b, b < K.nC → ∀ G : V, (∀ b' c t y, nenc b' c t y ∈ˢ G → K.Good P b' c t y) →
      ∀ ρ, K.Adm b G ρ → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.Good P b c t y := by
  suffices h : ∀ n, ∀ b, b < K.nC → K.D - K.dp b ≤ n → ∀ G : V,
      (∀ b' c t y, nenc b' c t y ∈ˢ G → K.Good P b' c t y) →
      ∀ ρ, K.Adm b G ρ → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.Good P b c t y from
    fun b hb => h _ b hb (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro b hb hn
    have := K.hD b hb
    omega
  | succ n ihn =>
    intro b hb hn
    refine K.claim_step P hSep hP hb fun b' hb' hdp => ihn b' hb' ?_
    have := K.hD b' hb'
    omega

private theorem hasSep_shallower (K : NestKit V) (b : Nat) :
    HasSep K.U fun u =>
      ∃ b', b' < K.nC ∧ K.dp b' < K.dp b ∧ ∃ c, c < (K.cl b').N ∧ ∃ t y, u = nenc b' c t y := by
  refine hasSep_of_defPred ?_
  refine DefRel.finExists_lt fun b' _ => DefRel.and (DefRel.constProp (K.dp b' < K.dp b)) ?_
  refine DefRel.finExists_lt fun c _ => ?_
  refine DefRel.exists_curry (DefRel.exists_curry ?_)
  exact DefRel.eq_apply (DefFun.proj 2) (DefFun.nenc_apply b' c (DefFun.proj 1) (DefFun.proj 0))

/-- **Every true class is good**, shallow classes first. -/
theorem top_good (P : V → Prop) (hSep : HasSep K.U P)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ b, b < K.nC → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app (K.KT b c) t → K.Good P b c t y := by
  suffices h : ∀ m, ∀ b, b < K.nC → K.dp b ≤ m → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app (K.KT b c) t → K.Good P b c t y from
    fun b hb => h _ b hb (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro b hb hm c hc t ht
    let G := sep K.U (fun u =>
      ∃ b', b' < K.nC ∧ K.dp b' < K.dp b ∧ ∃ c, c < (K.cl b').N ∧ ∃ t y, u = nenc b' c t y)
      (hasSep_shallower K b)
    refine K.claim P hSep hP b hb G ?_ (K.fr b) ?_ c hc t ht
    · intro b' c' t' y hy
      obtain ⟨_, b'', _, hdp, _⟩ := mem_sep.mp hy
      omega
    · exact K.top b hb ⟨c, hc, t, ht⟩ G fun b' c' t' y hb' hdp hc' ht' hy =>
        mem_sep.mpr ⟨K.nenc_mem_U hb' hc' ht' hy, b', hb', hdp, c', hc', t', y, rfl⟩
  | succ m ihm =>
    intro b hb hm c hc t ht
    let G := sep K.U (fun u =>
      ∃ b', b' < K.nC ∧ K.dp b' < K.dp b ∧ ∃ c, c < (K.cl b').N ∧ ∃ t y, u = nenc b' c t y)
      (hasSep_shallower K b)
    refine K.claim P hSep hP b hb G ?_ (K.fr b) ?_ c hc t ht
    · intro b' c' t' y hy
      obtain ⟨huU, b'', hb'', hdp, c'', hc'', t'', y'', heq⟩ := mem_sep.mp hy
      obtain ⟨rfl, rfl, rfl, rfl⟩ := nenc_inj heq
      obtain ⟨b₁, c₁, t₁, y₁, hb₁, hc₁, ht₁, hy₁, heq₁⟩ := K.mem_U.mp huU
      obtain ⟨rfl, rfl, rfl, rfl⟩ := nenc_inj heq₁
      exact ihm b' hb₁ (by omega) c' hc₁ t' ht₁ y hy₁
    · exact K.top b hb ⟨c, hc, t, ht⟩ G fun b' c' t' y hb' hdp hc' ht' hy =>
        mem_sep.mpr ⟨K.nenc_mem_U hb' hc' ht' hy, b', hb', hdp, c', hc', t', y, rfl⟩

/-- **The induction principle of the majors** (guarded by `HasSep K.U P`) —
`GraphRecKit.ind`, from the classes' own clauses. -/
theorem ind : ∀ P : V → Prop, HasSep K.U P →
    (∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) →
    ∀ u, u ∈ˢ K.U → P u := by
  intro P hSep hP u hu
  obtain ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩ := K.mem_U.mp hu
  exact (K.top_good P hSep hP b hb c hc t ht x hx).2

/-- Convenience form of `ind` when `P` is `DefPredOn K.U P`. -/
theorem ind_of_def (P : V → Prop) (hPdef : DefPredOn K.U P)
    (hstep : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ u, u ∈ˢ K.U → P u :=
  K.ind P (hasSep_of_def hPdef) hstep

end NestKit

end ConLeche.SetTheory
