module

public import ConLeche.SetModel.GraphRec
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.HoleOp
@[expose] public section

/-!
# The nested recursor's graph kit: majors over several CLASSES (lane NESTIND-KIT)

The graph kit (`SetModel/GraphRec.lean`, `GraphRecKit`) asks ONE thing of
the majors: an induction principle (`ind`).  At a flat block the majors
are the members' carriers and `ind` is the block's lfp induction.  At a
NESTED block the recursor family also ranges over the CONTAINER CLASSES
— `List Tree`, `Rose T`, `List (Rose T)` — each the least fixed point of
its OWN operator, at its OWN instantiation (the container's lfp clause at
the parameter frame the instantiation reads).  This module builds the
kit over such a family of classes and proves `ind` from the classes'
own clauses, by the STRENGTHENED PREDICATE of the probe
`_tmp/uniform-inds/E2E-probe-nestind.lean`, generalised:

* a class is a clause (`SClause`: an operator per parameter frame, its
  fit relation and injections) at its TRUE frame `fr b`;
* its container fields' classes are reached, during the induction, at
  SEPARATED frames — the instantiation read at the enclosing class's
  separated tuple; which frames count is the kit's `Adm` (admissible:
  "a frame whose parameter positions hold elements satisfying `G`");
* at such a frame the class's own induction runs with the predicate
  "lies in the TRUE class ∧ the property"; membership in the true class
  is re-established at each constructor by the class's clause at the
  TRUE frame (the fibre law, backwards, and closure), after moving the
  constructor's fit from the separated frame and tuple to the true ones
  (`trans`).  The only inclusion the induction itself produces is the
  separation `sep ⊆ carrier`.

**What is used of a class** (charter items 2, 4): its clause at each
frame the induction visits (`OkAt`: monotone in its own holes, a closed
tuple, the fibre law) and ONE fact per class tying a frame to the true
one, `trans`: a constructor fitting at an admissible frame, at holes
below the true carrier, fits at the true frame and the true carrier.  At
the term level `trans` is `LfpDatum.hfits_mono` along the relation
between the instantiation's two hole frames (the constructor's
positivity AT THE INSTANTIATION, `CtorPos` — what `nestPos`'s container
descent certifies, keyed by the instantiation) followed by the clause's
own `fitsMono` at the true frame.  Nothing is asked of a container "in
its parameter": no `value_mono`, no `carrier_mono_param`, no Bekić, no
joint (wide) operator.

**Why `trans` is at the FIT level, not the value level.**  At `Prop`
every injection is the point, so a value-level inclusion
("`carrier ρ ⊆ carrier (fr b)`") followed by a re-decoding at the true
frame yields SOME decoding of the major, not the one whose calls the
induction hypothesis covers (GRAPH1's `fitsMono` point).  The kit's
premise moves the SAME spine.

**Why the call targets are classified by frame (`calls`).**  A call
target of a constructor fitting at a separated frame is (1) one of the
class's own recursive fields (in the separated tuple — the induction
hypothesis), (2) an element at a PARAMETER position (it satisfies the
admissibility predicate `G`: it lies in an enclosing class and has the
property), or (3) an element of a DEEPER class at a frame read off the
current separated tuple (the recursion into the next nesting level,
with `G` extended by the current class's separated tuple).  Without (2)'s
link between a frame and the elements it holds, `ind` is FALSE: the
smallest counterexample is `T : Prop ::= node (W T)`,
`W α ::= wrap (h : g α)` with `g α := {pt}` at every frame — every
clause holds, `trans` holds (`{pt} ⊆ {pt}`), but the major `pt` of `T`
decodes as `node (wrap pt)`, whose call is `wrap pt`, whose call is
`pt` again: the property `False` is closed and `ind` fails.  The
missing fact is exactly (2) — the parameter positions of a frame read
at the separated tuple hold separated elements — which at the term
level is the instantiation's reading (`⟦Ds⟧` at the hole frame of the
separated tuple).

**`exu`.**  `NestKit.toKit` packages the classes as a `GraphRecKit`
(`hpred` derived, `ind` proved); `NestKit.exu` is `GraphRecKit.exu`
under the recursor's typing (`hst`) and `huniq`.  `huniq` is discharged
per regime: `huniq_of_prop` at `ℓ = 0` (decodings need not be unique —
the case the fit-level `trans` is for), `NestKit.huniq_of_inj` above
(the classes' injections injective at the true fits).

**Instances** (`SetModel/NestRecEx.lean`): `Tree`/`List`, `Rose`/`List`,
and `T`/`Rose T`/`List (Rose T)` (two nesting levels), over the HOLEOP
block data (`UBlock.toSClause`), at every level, `Prop` included.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

open Tower

universe u

variable {V : Type u} [SetTheory V]

/-! ## Clauses -/

/-- **A class presentation**: the set-level lfp clause of an inductive
block as a function of its parameter frame (of type `F`).  The index
sets do not depend on the frame (an instance's index telescope is
hole-free). -/
structure SClause (V : Type u) [SetTheory V] (F : Type u) where
  /-- the level -/
  w : Nat
  /-- the width (components) -/
  N : Nat
  /-- per component: the index-tuple set -/
  Is : Nat → V
  /-- the operator at a frame -/
  Φ : F → (Nat → V) → Nat → V
  /-- the fit relation at a frame and a hole tuple: `Fits ρ X t c j fs` -/
  Fits : F → (Nat → V) → V → Nat → Nat → List V → Prop
  /-- the injections: `inj c j fs` -/
  inj : Nat → Nat → List V → V

namespace SClause

variable {F : Type u}

/-- The carrier at a frame: the least pre-fixed tuple. -/
noncomputable def carrier (C : SClause V F) (ρ : F) : Nat → V := lfpTuple C.w C.N C.Is (C.Φ ρ)

/-- **The clause at a frame**: what `lfpTuple`'s laws need, and what the
operator is (the fibre law). -/
structure OkAt (C : SClause V F) (ρ : F) : Prop where
  mono : MonoTuple C.w C.N C.Is (C.Φ ρ)
  closed : ∃ L, IsClosedTuple C.w C.N C.Is (C.Φ ρ) L
  fibre : ∀ X, InTupleSpace C.w C.N C.Is X → ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ x,
    x ∈ˢ app (C.Φ ρ X c) t ↔ ∃ j fs, C.Fits ρ X t c j fs ∧ x = C.inj c j fs

variable {C : SClause V F}

theorem carrier_mem (C : SClause V F) (ρ : F) : InTupleSpace C.w C.N C.Is (C.carrier ρ) :=
  lfpTuple_mem _ _ _ _

/-- **Introduction**: a spine fitting at the carrier is, injected, a
member of the carrier (the fibre law backwards, then closure). -/
theorem OkAt.inj_mem {ρ : F} (h : C.OkAt ρ) {c : Nat} (hc : c < C.N) {t : V} (ht : t ∈ˢ C.Is c)
    {j : Nat} {fs : List V} (hf : C.Fits ρ (C.carrier ρ) t c j fs) :
    C.inj c j fs ∈ˢ app (C.carrier ρ c) t :=
  lfpTuple_closed h.closed h.mono c hc t ht _
    ((h.fibre _ (C.carrier_mem ρ) c hc t ht _).mpr ⟨j, fs, hf, rfl⟩)

/-- **The class's induction principle** at a frame: `lfpTuple_induction`
read through the fibre law. -/
theorem OkAt.ind {ρ : F} (h : C.OkAt ρ) (Q : Nat → V → V → Prop)
    (hstep : ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ j fs,
      C.Fits ρ (sepTuple C.w C.N C.Is (C.Φ ρ) Q) t c j fs → Q c t (C.inj c j fs)) :
    ∀ c, c < C.N → ∀ t, t ∈ˢ C.Is c → ∀ x, x ∈ˢ app (C.carrier ρ c) t → Q c t x := by
  refine lfpTuple_induction h.closed h.mono Q fun c hc t ht x hx => ?_
  obtain ⟨j, fs, hf, rfl⟩ := (h.fibre _ (sepTuple_mem _ _ _ _ Q) c hc t ht x).mp hx
  exact hstep c hc t ht j fs hf

end SClause

/-- A separated component, read at an index tuple of its index set. -/
theorem mem_app_sepTuple {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}
    {Q : Nat → V → V → Prop} {c : Nat} {t y : V} (ht : t ∈ˢ Is c) :
    y ∈ˢ app (sepTuple w k Is Φ Q c) t ↔ y ∈ˢ app (lfpTuple w k Is Φ c) t ∧ Q c t y := by
  unfold sepTuple
  rw [app_graph ht, mem_sep]

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

/-- A predicate on tagged elements (class, component, index, value)
extended by the elements of one class's hole tuple `Y`. -/
def addOwn (G : Nat → Nat → V → V → Prop) (b N : Nat) (Is Y : Nat → V) :
    Nat → Nat → V → V → Prop :=
  fun b' c t y => G b' c t y ∨ (b' = b ∧ c < N ∧ t ∈ˢ Is c ∧ y ∈ˢ app (Y c) t)

/-! ## The kit -/

/-- **The nested recursion data over several classes.**  Classes are
`b < nC`; class `b` is the clause `cl b` at its TRUE frame `fr b`; its
nesting depth is `dp b` (below `D`).  `Adm b G ρ`: `ρ` is a frame at
which class `b` is visited during the induction, its parameter positions
holding elements that satisfy `G`. -/
structure NestKit (V : Type u) [SetTheory V] (F : Type u) where
  /-- the number of classes -/
  nC : Nat
  /-- the classes' clauses -/
  cl : Nat → SClause V F
  /-- the TRUE frames -/
  fr : Nat → F
  /-- the nesting depth -/
  dp : Nat → Nat
  /-- a bound on the depths -/
  D : Nat
  hD : ∀ b, b < nC → dp b < D
  /-- the admissible (separated) frames -/
  Adm : Nat → (Nat → Nat → V → V → Prop) → F → Prop
  /-- the recursive calls' majors at a decoding -/
  pred : NDec V → V
  /-- the clause holds at every admissible frame -/
  ok : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → (cl b).OkAt ρ
  /-- **the tie to the true frame** (positivity at the instantiation, then
  the clause's `fitsMono`): at an admissible frame whose parameter
  positions hold true elements, a spine fitting at holes below the true
  carrier fits at the true frame and carrier -/
  trans : ∀ b, b < nC → ∀ G, (∀ b' c t y, G b' c t y → y ∈ˢ app ((cl b').carrier (fr b') c) t) →
    ∀ ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    TupleLe (cl b).N (cl b).Is Y ((cl b).carrier (fr b)) →
    ∀ t c j fs, (cl b).Fits ρ Y t c j fs → (cl b).Fits (fr b) ((cl b).carrier (fr b)) t c j fs
  /-- **the call targets**, at a spine fitting at an admissible frame:
  an own recursive field, a parameter-position element (satisfying `G`),
  or an element of a DEEPER class at an admissible frame for `G`
  extended by the current hole tuple -/
  calls : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    ∀ c t j fs, c < (cl b).N → t ∈ˢ (cl b).Is c → (cl b).Fits ρ Y t c j fs →
    ∀ u, u ∈ˢ pred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < nC ∧ c' < (cl b').N ∧
      t' ∈ˢ (cl b').Is c' ∧ u = nenc b' c' t' y ∧
      ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ G b' c' t' y ∨
        (dp b < dp b' ∧ ∃ ρ', Adm b' (addOwn G b (cl b).N (cl b).Is Y) ρ' ∧
          y ∈ˢ app ((cl b').carrier ρ' c') t'))
  /-- **the true frames are admissible** once the shallower classes' true
  elements satisfy `G` -/
  top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (cl b').N →
      t ∈ˢ (cl b').Is c → y ∈ˢ app ((cl b').carrier (fr b') c) t → G b' c t y) →
    Adm b G (fr b)

namespace NestKit

variable {F : Type u} (K : NestKit V F)

/-- The true class `b`: its clause's carrier at its true frame. -/
noncomputable def KT (b : Nat) : Nat → V := (K.cl b).carrier (K.fr b)

/-- **The majors**: the tagged elements of every true class. -/
noncomputable def U : V :=
  sigmaPairs (sep omega fun a => ∃ n, n < K.nC ∧ a = vnat n)
    (natFibre fun b => unionSet (K.cl b).N (K.cl b).Is (K.KT b))

theorem mem_U {u : V} :
    u ∈ˢ K.U ↔ ∃ b c t x, b < K.nC ∧ c < (K.cl b).N ∧ t ∈ˢ (K.cl b).Is c ∧
      x ∈ˢ app (K.KT b c) t ∧ u = nenc b c t x := by
  unfold U
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨a, ha, p, hp, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ha
    rw [natFibre_vnat] at hp
    obtain ⟨c, hc, t, ht, x, hx, rfl⟩ := mem_unionSet.mp hp
    exact ⟨n, c, t, x, hn, hc, ht, hx, rfl⟩
  · rintro ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩
    refine ⟨vnat b, mem_sep.mpr ⟨vnat_mem_omega b, b, hb, rfl⟩, tagged c t x, ?_, rfl⟩
    rw [natFibre_vnat]
    exact tagged_mem_unionSet hc ht hx

theorem nenc_mem_U {b c : Nat} {t x : V} (hb : b < K.nC) (hc : c < (K.cl b).N)
    (ht : t ∈ˢ (K.cl b).Is c) (hx : x ∈ˢ app (K.KT b c) t) : nenc b c t x ∈ˢ K.U :=
  K.mem_U.mpr ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩

/-- **The decodings**: a spine fitting one of the class's constructors
at its TRUE frame and carrier. -/
def Dec (u : V) (d : NDec V) : Prop :=
  d.cls < K.nC ∧ d.c < (K.cl d.cls).N ∧ d.t ∈ˢ (K.cl d.cls).Is d.c ∧
    (K.cl d.cls).Fits (K.fr d.cls) (K.KT d.cls) d.t d.c d.j d.fs ∧
    u = nenc d.cls d.c d.t ((K.cl d.cls).inj d.c d.j d.fs)

/-- The class `b` at its true frame is a clause (from `top` and `ok`). -/
theorem okT {b : Nat} (hb : b < K.nC) : (K.cl b).OkAt (K.fr b) :=
  K.ok b hb _ _ (K.top b hb (fun _ _ _ _ => True) fun _ _ _ _ _ _ _ _ _ => trivial)

/-- The property, strengthened by membership in the true class. -/
def Good (P : V → Prop) (b c : Nat) (t y : V) : Prop :=
  y ∈ˢ app (K.KT b c) t ∧ P (nenc b c t y)

/-! ### The strengthened induction at an admissible frame -/

/-- One class, the deeper classes assumed. -/
theorem claim_step (P : V → Prop)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u)
    {b : Nat} (hb : b < K.nC)
    (ih : ∀ b', b' < K.nC → K.dp b < K.dp b' → ∀ G, (∀ b'' c t y, G b'' c t y → K.Good P b'' c t y) →
      ∀ ρ, K.Adm b' G ρ → ∀ c, c < (K.cl b').N → ∀ t, t ∈ˢ (K.cl b').Is c →
      ∀ y, y ∈ˢ app ((K.cl b').carrier ρ c) t → K.Good P b' c t y)
    (G : Nat → Nat → V → V → Prop) (hG : ∀ b' c t y, G b' c t y → K.Good P b' c t y)
    (ρ : F) (hρ : K.Adm b G ρ) :
    ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.Good P b c t y := by
  have hok := K.ok b hb G ρ hρ
  have hokT := K.okT hb
  refine hok.ind (fun c t y => K.Good P b c t y) fun c hc t ht j fs hf => ?_
  -- the separated tuple, below the true carrier (a separation)
  let S := sepTuple (K.cl b).w (K.cl b).N (K.cl b).Is ((K.cl b).Φ ρ) fun c t y => K.Good P b c t y
  have hSmem : InTupleSpace (K.cl b).w (K.cl b).N (K.cl b).Is S := sepTuple_mem _ _ _ _ _
  have hSgood : ∀ c', c' < (K.cl b).N → ∀ t', t' ∈ˢ (K.cl b).Is c' → ∀ y, y ∈ˢ app (S c') t' →
      K.Good P b c' t' y := fun c' _ t' ht' y hy => ((mem_app_sepTuple ht').mp hy).2
  have hSle : TupleLe (K.cl b).N (K.cl b).Is S (K.KT b) :=
    fun c' hc' t' ht' y hy => (hSgood c' hc' t' ht' y hy).1
  -- the SAME spine fits at the true frame and carrier
  have hfT : (K.cl b).Fits (K.fr b) (K.KT b) t c j fs :=
    K.trans b hb G (fun b' c' t' y hy => (hG b' c' t' y hy).1) ρ hρ S hSmem hSle t c j fs hf
  have hmemT : (K.cl b).inj c j fs ∈ˢ app (K.KT b c) t := hokT.inj_mem hc ht hfT
  refine ⟨hmemT, hP _ (K.nenc_mem_U hb hc ht hmemT) ⟨⟨b, c, t, j, fs⟩, ⟨hb, hc, ht, hfT, rfl⟩, ?_⟩⟩
  intro u hu
  obtain ⟨b', c', t', y, hb', hc', ht', rfl, hcase⟩ := K.calls b hb G ρ hρ S hSmem c t j fs hc ht hf u hu
  rcases hcase with ⟨rfl, hy⟩ | hy | ⟨hdp, ρ', hρ', hy⟩
  · exact (hSgood c' hc' t' ht' y hy).2
  · exact (hG _ _ _ _ hy).2
  · refine (ih b' hb' hdp _ ?_ ρ' hρ' c' hc' t' ht' y hy).2
    rintro b'' c'' t'' y'' (h | ⟨rfl, hc'', ht'', hy''⟩)
    · exact hG _ _ _ _ h
    · exact hSgood c'' hc'' t'' ht'' y'' hy''

/-- **The strengthened induction**: at every admissible frame whose
parameter positions hold good elements, every element of the class is
in the TRUE class and has the property. -/
theorem claim (P : V → Prop)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ b, b < K.nC → ∀ G, (∀ b' c t y, G b' c t y → K.Good P b' c t y) →
      ∀ ρ, K.Adm b G ρ → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.Good P b c t y := by
  suffices h : ∀ n, ∀ b, b < K.nC → K.D - K.dp b ≤ n → ∀ G,
      (∀ b' c t y, G b' c t y → K.Good P b' c t y) →
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
    refine K.claim_step P hP hb fun b' hb' hdp => ihn b' hb' ?_
    have := K.hD b' hb'
    omega

/-- **Every true class is good**, shallow classes first. -/
theorem top_good (P : V → Prop)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ b, b < K.nC → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app (K.KT b c) t → K.Good P b c t y := by
  suffices h : ∀ m, ∀ b, b < K.nC → K.dp b ≤ m → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app (K.KT b c) t → K.Good P b c t y from
    fun b hb => h _ b hb (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro b hb hm
    refine K.claim P hP b hb (fun b' c t y => b' < K.nC ∧ K.dp b' < K.dp b ∧ c < (K.cl b').N ∧
      t ∈ˢ (K.cl b').Is c ∧ y ∈ˢ app (K.KT b' c) t) ?_ (K.fr b) ?_
    · rintro b' c t y ⟨-, hdp, -⟩; omega
    · exact K.top b hb _ fun b' c t y hb' hdp hc ht hy => ⟨hb', hdp, hc, ht, hy⟩
  | succ m ihm =>
    intro b hb hm
    refine K.claim P hP b hb (fun b' c t y => b' < K.nC ∧ K.dp b' < K.dp b ∧ c < (K.cl b').N ∧
      t ∈ˢ (K.cl b').Is c ∧ y ∈ˢ app (K.KT b' c) t) ?_ (K.fr b) ?_
    · rintro b' c t y ⟨hb', hdp, hc, ht, hy⟩
      exact ihm b' hb' (by omega) c hc t ht y hy
    · exact K.top b hb _ fun b' c t y hb' hdp hc ht hy => ⟨hb', hdp, hc, ht, hy⟩

/-- **The induction principle of the majors** — `GraphRecKit.ind`,
from the classes' own clauses. -/
theorem ind : ∀ P : V → Prop,
    (∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) →
    ∀ u, u ∈ˢ K.U → P u := by
  intro P hP u hu
  obtain ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩ := K.mem_U.mp hu
  exact (K.top_good P hP b hb c hc t ht x hx).2

/-- **The call targets are majors.** -/
theorem hpred : ∀ u, u ∈ˢ K.U → ∀ d, K.Dec u d → K.pred d ⊆ˢ K.U := by
  rintro _ - ⟨b, c, t, j, fs⟩ ⟨hb, hc, ht, hf, -⟩ u hu
  let G0 : Nat → Nat → V → V → Prop := fun b' c t y =>
    b' < K.nC ∧ c < (K.cl b').N ∧ t ∈ˢ (K.cl b').Is c ∧ y ∈ˢ app (K.KT b' c) t
  have hρ : K.Adm b G0 (K.fr b) :=
    K.top b hb G0 fun b' c t y hb' _ hc ht hy => ⟨hb', hc, ht, hy⟩
  obtain ⟨b', c', t', y, hb', hc', ht', rfl, hcase⟩ :=
    K.calls b hb G0 (K.fr b) hρ (K.KT b) ((K.cl b).carrier_mem _) c t j fs hc ht hf u hu
  refine K.nenc_mem_U hb' hc' ht' ?_
  rcases hcase with ⟨rfl, hy⟩ | ⟨-, -, -, hy⟩ | ⟨-, ρ', hρ', hy⟩
  · exact hy
  · exact hy
  · refine (K.claim (fun _ => True) (fun _ _ _ => trivial) b' hb' _ ?_ ρ' hρ' c' hc' t' ht' y hy).1
    rintro b'' c'' t'' y'' (⟨-, -, -, h⟩ | ⟨rfl, hc'', ht'', hy''⟩)
    · exact ⟨h, trivial⟩
    · exact ⟨hy'', trivial⟩

/-! ### The graph kit and the recursion theorem -/

/-- **The nested recursor family as a graph kit**: majors over every
class, decodings at the true frames, `hpred` and `ind` proved; the
bound `B`, the step `st`, its typing `hst` and `huniq` given. -/
noncomputable def toKit (ℓ : Nat) (B : V → V) (st : NDec V → V → V)
    (hB : ∀ u, u ∈ˢ K.U → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ K.U → ∀ d, K.Dec u d → ∀ g,
      g ∈ˢ piSet (K.pred d) (fun j => app (gGraph ℓ K.U K.Dec K.pred B st) j) → st d g ∈ˢ B u)
    (huniq : ∀ u, u ∈ˢ K.U → ∀ d d', K.Dec u d → K.Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v') :
    GraphRecKit ℓ K.U (NDec V) where
  Dec := K.Dec
  pred := K.pred
  B := B
  st := st
  hpred := K.hpred
  hB := hB
  hst := hst
  huniq := huniq
  ind := K.ind

/-- **The recursion theorem at a nested block**: the graph has exactly
one value at every major of every class. -/
theorem exu (ℓ : Nat) (B : V → V) (st : NDec V → V → V)
    (hB : ∀ u, u ∈ˢ K.U → B u ∈ˢ (univ ℓ : V))
    (hst : ∀ u, u ∈ˢ K.U → ∀ d, K.Dec u d → ∀ g,
      g ∈ˢ piSet (K.pred d) (fun j => app (gGraph ℓ K.U K.Dec K.pred B st) j) → st d g ∈ˢ B u)
    (huniq : ∀ u, u ∈ˢ K.U → ∀ d d', K.Dec u d → K.Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v') :
    ∀ u, u ∈ˢ K.U → Single (gGraph ℓ K.U K.Dec K.pred B st) u :=
  (K.toKit ℓ B st hB hst huniq).exu

/-- **`huniq` from injective injections** (the `Type` regime): if at
every class two spines fitting at the true frame with equal injections
are equal, decodings are unique. -/
theorem huniq_of_inj {B : V → V}
    (hinj : ∀ b, b < K.nC → ∀ c t j fs j' fs',
      (K.cl b).Fits (K.fr b) (K.KT b) t c j fs → (K.cl b).Fits (K.fr b) (K.KT b) t c j' fs' →
      (K.cl b).inj c j fs = (K.cl b).inj c j' fs' → j = j' ∧ fs = fs') :
    ∀ u, u ∈ˢ K.U → ∀ d d', K.Dec u d → K.Dec u d' →
      d = d' ∨ ∀ v v', v ∈ˢ B u → v' ∈ˢ B u → v = v' := by
  rintro u - ⟨b, c, t, j, fs⟩ ⟨b', c', t', j', fs'⟩ ⟨hb, -, -, hf, rfl⟩ ⟨-, -, -, hf', h⟩
  obtain ⟨rfl, rfl, rfl, hx⟩ := nenc_inj h
  obtain ⟨rfl, rfl⟩ := hinj b hb c t j fs j' fs' hf hf' hx
  exact Or.inl rfl

end NestKit

/-! ## HOLEOP block data as classes -/

namespace UBlock

variable {w k : Nat}

/-- **A HOLEOP block datum as a class presentation**, its frame the
parameter `α` (the frame of its field readings `ρ` fixed). -/
noncomputable def toSClause (d : UBlock V w k) (ρ : Nat → V) : SClause V V where
  w := w
  N := k
  Is := d.Is
  Φ := fun α X => uPhi d ρ α X
  Fits := fun α X t c j fs => ∃ ct, (d.ctors c)[j]? = some ct ∧
    FitsS (teleOf ct.fields ρ X α) fs ∧ ct.idx (fconsList fs ρ) = t
  inj := fun _ j fs => uinj w j fs

variable (d : UBlock V w k) (ρ : Nat → V)

theorem toSClause_carrier (α : V) : (d.toSClause ρ).carrier α = d.carrier ρ α := rfl

/-- The clause at a parameter of the level with a closed tuple. -/
theorem toSClause_ok {α : V} (hα : α ∈ˢ (univ w : V)) (hcl : d.Closed ρ α) :
    (d.toSClause ρ).OkAt α where
  mono := uPhi_mono d ρ hα
  closed := hcl
  fibre := by
    intro X _ c _ t ht x
    show x ∈ˢ app (uPhi d ρ α X c) t ↔ _
    rw [mem_uPhi d ρ α X ht]
    constructor
    · rintro ⟨j, fs, ct, hct, hf, hi, rfl⟩
      exact ⟨j, fs, ⟨ct, hct, hf, hi⟩, rfl⟩
    · rintro ⟨j, fs, ⟨ct, hct, hf, hi⟩, rfl⟩
      exact ⟨j, fs, ct, hct, hf, hi, rfl⟩

/-- **The fit grows** with the hole tuple and the parameter: the block's
positivity (`Pos.mono`, through `teleOf_sub`). -/
theorem toSClause_fits_mono {α β : V} (hα : α ∈ˢ (univ w : V)) (hβ : β ∈ˢ (univ w : V))
    (hαβ : α ⊆ˢ β) {X Y : Nat → V} (hX : InTupleSpace w k d.Is X) (hY : InTupleSpace w k d.Is Y)
    (hXY : TupleLe k d.Is X Y) {t : V} {c j : Nat} {fs : List V}
    (h : (d.toSClause ρ).Fits α X t c j fs) : (d.toSClause ρ).Fits β Y t c j fs := by
  obtain ⟨ct, hct, hf, hi⟩ := h
  exact ⟨ct, hct, FitsS.mono (teleOf_sub hX hY hXY hα hβ hαβ ct.fields ct.pos ρ) hf, hi⟩

/-- **The injections are injective** at the fits (`w ≠ 0`). -/
theorem toSClause_inj (hw : w ≠ 0) {α : V} {X : Nat → V} {t : V} {c j j' : Nat}
    {fs fs' : List V} (hf : (d.toSClause ρ).Fits α X t c j fs)
    (hf' : (d.toSClause ρ).Fits α X t c j' fs')
    (h : (d.toSClause ρ).inj c j fs = (d.toSClause ρ).inj c j' fs') : j = j' ∧ fs = fs' := by
  obtain ⟨ct, hct, hfs, -⟩ := hf
  obtain ⟨ct', hct', hfs', -⟩ := hf'
  change uinj w j fs = uinj w j' fs' at h
  rw [uinj_pos hw, uinj_pos hw] at h
  obtain ⟨rfl, hm⟩ := Tower.inj_inj h
  rw [hct] at hct'
  cases hct'
  exact ⟨rfl, mkTower_inj ((FitsS.length_eq hfs).trans (FitsS.length_eq hfs').symm) hm⟩

end UBlock

end ConLeche.SetTheory
