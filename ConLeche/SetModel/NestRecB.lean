module

public import ConLeche.SetModel.NestRec
@[expose] public section

/-!
# The nested kit, Route B: `trans` only at majors of the TRUE class (lane NESTIND)

`NestKit` (`SetModel/NestRec.lean`) asks `trans` at every spine fitting
at an admissible frame: the constructor's positivity AT THE
INSTANTIATION (finding F10 of lane NESTIND — a fact of the positivity
stage's run, which the recursor stage does not carry).  Route B (the
coordinator's ruling on F12, 2026-09-25) asks it only where the
injected value already lies in the TRUE class:

* `trans` — a spine fitting at an admissible frame whose injection is a
  member of the true class fits at the true frame and carrier.  At
  `w ≠ 0` this is `LfpClause.mkInj` at the true frame (the true
  decoding of the injection is the same constructor and the same
  fields; injections do not depend on the frame), with no positivity;
* `hpredT` — the call targets of a TRUE decoding are majors (the old
  kit derived this from its `trans`; here it is the rule's own call
  typing read at the true values, lane NESTIND's F3).

The induction is RELATIVISED to the true class: at an admissible frame,
every element of the class that lies in the true class has the
property (`claim`); the property of a call target comes from the class
hypotheses once `hpredT` places it in its true class.  `calls` and
`top` are the old kit's, and `ind` is `GraphRecKit.ind`.
-/

namespace ConLeche.SetTheory

open Tower

universe u

variable {V : Type u} [SetTheory V]

/-- **The nested recursion data over several classes, Route B.** The
fields of `NestKit`, with `trans` asked only at a major of the true
class, and `hpredT`. -/
structure NestKitB (V : Type u) [SetTheory V] (F : Type u) where
  nC : Nat
  cl : Nat → SClause V F
  fr : Nat → F
  dp : Nat → Nat
  D : Nat
  hD : ∀ b, b < nC → dp b < D
  Adm : Nat → (Nat → Nat → V → V → Prop) → F → Prop
  pred : NDec V → V
  ok : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → (cl b).OkAt ρ
  /-- **the tie to the true frame, at a true major**: a spine fitting at
  an admissible frame whose injection lies in the true class fits at the
  true frame and carrier -/
  trans : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    ∀ t c j fs, c < (cl b).N → t ∈ˢ (cl b).Is c → (cl b).Fits ρ Y t c j fs →
    (cl b).inj c j fs ∈ˢ app ((cl b).carrier (fr b) c) t →
    (cl b).Fits (fr b) ((cl b).carrier (fr b)) t c j fs
  calls : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    ∀ c t j fs, c < (cl b).N → t ∈ˢ (cl b).Is c → (cl b).Fits ρ Y t c j fs →
    ∀ u, u ∈ˢ pred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < nC ∧ c' < (cl b').N ∧
      t' ∈ˢ (cl b').Is c' ∧ u = nenc b' c' t' y ∧
      ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ G b' c' t' y ∨
        (dp b < dp b' ∧ ∃ ρ', Adm b' (addOwn G b (cl b).N (cl b).Is Y) ρ' ∧
          y ∈ˢ app ((cl b').carrier ρ' c') t'))
  top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (cl b').N →
      t ∈ˢ (cl b').Is c → y ∈ˢ app ((cl b').carrier (fr b') c) t → G b' c t y) →
    Adm b G (fr b)

namespace NestKitB

variable {F : Type u} (K : NestKitB V F)

/-- The true class `b`. -/
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

/-- A major's class, component, index and value, read back. -/
theorem of_nenc_mem_U {b c : Nat} {t x : V} (h : nenc b c t x ∈ˢ K.U) :
    x ∈ˢ app (K.KT b c) t := by
  obtain ⟨b', c', t', x', -, -, -, hx, he⟩ := K.mem_U.mp h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := nenc_inj he
  exact hx

/-- **The decodings**: a spine fitting at the TRUE frame and carrier. -/
def Dec (u : V) (d : NDec V) : Prop :=
  d.cls < K.nC ∧ d.c < (K.cl d.cls).N ∧ d.t ∈ˢ (K.cl d.cls).Is d.c ∧
    (K.cl d.cls).Fits (K.fr d.cls) (K.KT d.cls) d.t d.c d.j d.fs ∧
    u = nenc d.cls d.c d.t ((K.cl d.cls).inj d.c d.j d.fs)

theorem okT {b : Nat} (hb : b < K.nC) : (K.cl b).OkAt (K.fr b) :=
  K.ok b hb _ _ (K.top b hb (fun _ _ _ _ => True) fun _ _ _ _ _ _ _ _ _ => trivial)

/-- The property, relativised to the true class. -/
def GoodB (P : V → Prop) (b c : Nat) (t y : V) : Prop :=
  y ∈ˢ app (K.KT b c) t → P (nenc b c t y)

variable (hpredT : ∀ u, u ∈ˢ K.U → ∀ d, K.Dec u d → K.pred d ⊆ˢ K.U)
include hpredT

/-- One class, the deeper classes assumed (relativised). -/
theorem claim_step (P : V → Prop)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u)
    {b : Nat} (hb : b < K.nC)
    (ih : ∀ b', b' < K.nC → K.dp b < K.dp b' → ∀ G, (∀ b'' c t y, G b'' c t y → K.GoodB P b'' c t y) →
      ∀ ρ, K.Adm b' G ρ → ∀ c, c < (K.cl b').N → ∀ t, t ∈ˢ (K.cl b').Is c →
      ∀ y, y ∈ˢ app ((K.cl b').carrier ρ c) t → K.GoodB P b' c t y)
    (G : Nat → Nat → V → V → Prop) (hG : ∀ b' c t y, G b' c t y → K.GoodB P b' c t y)
    (ρ : F) (hρ : K.Adm b G ρ) :
    ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.GoodB P b c t y := by
  have hok := K.ok b hb G ρ hρ
  have hokT := K.okT hb
  refine hok.ind (fun c t y => K.GoodB P b c t y) ?_
  intro c hc t ht j fs hf hmemT
  let S := sepTuple (K.cl b).w (K.cl b).N (K.cl b).Is ((K.cl b).Φ ρ) fun c t y => K.GoodB P b c t y
  have hSmem : InTupleSpace (K.cl b).w (K.cl b).N (K.cl b).Is S := sepTuple_mem _ _ _ _ _
  have hSgood : ∀ c', c' < (K.cl b).N → ∀ t', t' ∈ˢ (K.cl b).Is c' → ∀ y, y ∈ˢ app (S c') t' →
      K.GoodB P b c' t' y := fun c' _ t' ht' y hy => ((mem_app_sepTuple ht').mp hy).2
  -- the SAME spine fits at the true frame and carrier (the injection is a true major)
  have hfT : (K.cl b).Fits (K.fr b) (K.KT b) t c j fs :=
    K.trans b hb G ρ hρ S hSmem t c j fs hc ht hf hmemT
  have hu : nenc b c t ((K.cl b).inj c j fs) ∈ˢ K.U := K.nenc_mem_U hb hc ht hmemT
  have hdec : K.Dec (nenc b c t ((K.cl b).inj c j fs)) ⟨b, c, t, j, fs⟩ := ⟨hb, hc, ht, hfT, rfl⟩
  refine hP _ hu ⟨⟨b, c, t, j, fs⟩, hdec, ?_⟩
  intro u hu'
  have huU : u ∈ˢ K.U := hpredT _ hu _ hdec u hu'
  obtain ⟨b', c', t', y, hb', hc', ht', rfl, hcase⟩ :=
    K.calls b hb G ρ hρ S hSmem c t j fs hc ht hf u hu'
  have hyT := K.of_nenc_mem_U huU
  rcases hcase with ⟨rfl, hy⟩ | hy | ⟨hdp, ρ', hρ', hy⟩
  · exact hSgood c' hc' t' ht' y hy hyT
  · exact hG _ _ _ _ hy hyT
  · refine ih b' hb' hdp _ ?_ ρ' hρ' c' hc' t' ht' y hy hyT
    rintro b'' c'' t'' y'' (h | ⟨rfl, hc'', ht'', hy''⟩)
    · exact hG _ _ _ _ h
    · exact hSgood c'' hc'' t'' ht'' y'' hy''

/-- **The relativised induction** at every admissible frame. -/
theorem claim (P : V → Prop)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ b, b < K.nC → ∀ G, (∀ b' c t y, G b' c t y → K.GoodB P b' c t y) →
      ∀ ρ, K.Adm b G ρ → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.GoodB P b c t y := by
  suffices h : ∀ n, ∀ b, b < K.nC → K.D - K.dp b ≤ n → ∀ G,
      (∀ b' c t y, G b' c t y → K.GoodB P b' c t y) →
      ∀ ρ, K.Adm b G ρ → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app ((K.cl b).carrier ρ c) t → K.GoodB P b c t y from
    fun b hb => h _ b hb (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro b hb hn
    have := K.hD b hb
    omega
  | succ n ihn =>
    intro b hb hn
    refine K.claim_step hpredT P hP hb fun b' hb' hdp => ihn b' hb' ?_
    have := K.hD b' hb'
    omega

/-- **Every true major has the property**, shallow classes first. -/
theorem top_good (P : V → Prop)
    (hP : ∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) :
    ∀ b, b < K.nC → ∀ c, c < (K.cl b).N → ∀ t, t ∈ˢ (K.cl b).Is c →
      ∀ y, y ∈ˢ app (K.KT b c) t → P (nenc b c t y) := by
  suffices h : ∀ m, ∀ b, b < K.nC → K.dp b ≤ m → ∀ c, c < (K.cl b).N →
      ∀ t, t ∈ˢ (K.cl b).Is c → ∀ y, y ∈ˢ app (K.KT b c) t → P (nenc b c t y) from
    fun b hb => h _ b hb (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro b hb hm c hc t ht y hy
    refine K.claim hpredT P hP b hb (fun b' c t y => b' < K.nC ∧ K.dp b' < K.dp b ∧
      c < (K.cl b').N ∧ t ∈ˢ (K.cl b').Is c ∧ y ∈ˢ app (K.KT b' c) t) ?_ (K.fr b) ?_
      c hc t ht y hy hy
    · rintro b' c t y ⟨-, hdp, -⟩; omega
    · exact K.top b hb _ fun b' c t y hb' hdp hc ht hy => ⟨hb', hdp, hc, ht, hy⟩
  | succ m ihm =>
    intro b hb hm c hc t ht y hy
    refine K.claim hpredT P hP b hb (fun b' c t y => b' < K.nC ∧ K.dp b' < K.dp b ∧
      c < (K.cl b').N ∧ t ∈ˢ (K.cl b').Is c ∧ y ∈ˢ app (K.KT b' c) t) ?_ (K.fr b) ?_
      c hc t ht y hy hy
    · rintro b' c t y ⟨hb', hdp, hc, ht, hy⟩ -
      exact ihm b' hb' (by omega) c hc t ht y hy
    · exact K.top b hb _ fun b' c t y hb' hdp hc ht hy => ⟨hb', hdp, hc, ht, hy⟩

/-- **The induction principle of the majors** (Route B). -/
theorem ind : ∀ P : V → Prop,
    (∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) →
    ∀ u, u ∈ˢ K.U → P u := by
  intro P hP u hu
  obtain ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩ := K.mem_U.mp hu
  exact K.top_good hpredT P hP b hb c hc t ht x hx

end NestKitB

end ConLeche.SetTheory
