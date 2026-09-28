module

public import ConLeche.SetModel.NestRecCls
@[expose] public section

/-!
# The class kit: `NestKit` with calls into frames holding OTHER classes' carriers

`NestKit` (`SetModel/NestRec.lean`) proves the majors' induction from the
classes' own clauses; its third kind of call target is an element of a
DEEPER class at a frame admissible for `addOwn G b Y` — the current
class's separated tuple added to the enclosing good elements.  That is
too narrow for the CLASSCHECK class kit (PROOFPLAN §4.2, experiment E2):
at F13 (`TL | node : List (RL TL)`, `RL α | node : α → List (RL α)`) the
member `TL`'s field lands in `λ = List (RL TL)` at the frame
`z_ρ := T_ρ(S)` — the TRUE carrier of ANOTHER class `ρ = RL TL` at the
member's separated tuple `S`.  Its elements are not in `addOwn G TL S`;
they are good by the claim at `ρ` (deeper than `TL`).

**`extN`** is that closure, stratified: layer `0` is `addOwn G b Y`,
layer `n + 1` adds the elements of every class `e` DEEPER than `b` at a
frame admissible for layer `n`.  `ClassKit.calls`' third case asks for
SOME layer.  `claim_step` proves every layer good by an inner induction
on `n`, each step the outer induction hypothesis at a deeper class — the
same `ih` `NestKit.claim_step` already has.  `ClassKit.ind` has
`NestKit.ind`'s statement; `NestKit.toClassKit` shows the old kit is
the layer-`0` case; `ClassKit.toNodeInd` feeds the same decoded
interface (`NestNodeInd`) the recursor side reads.
-/

namespace ConLeche.SetTheory

open Tower

universe u

variable {V : Type u} [SetTheory V]

/-- **The extended hypothesis set**, layer `n`: `addOwn G b Y`, closed
`n` times under "an element of a deeper class's carrier at a frame
admissible for the previous layer". -/
def extN {F : Type u} (nC : Nat) (cl : Nat → SClause V F) (dp : Nat → Nat)
    (Adm : Nat → (Nat → Nat → V → V → Prop) → F → Prop)
    (G : Nat → Nat → V → V → Prop) (b : Nat) (Y : Nat → V) : Nat → Nat → Nat → V → V → Prop
  | 0 => addOwn G b (cl b).N (cl b).Is Y
  | n + 1 => fun b' c t y => extN nC cl dp Adm G b Y n b' c t y ∨
      (b' < nC ∧ dp b < dp b' ∧ c < (cl b').N ∧ t ∈ˢ (cl b').Is c ∧
        ∃ ρ', Adm b' (extN nC cl dp Adm G b Y n) ρ' ∧ y ∈ˢ app ((cl b').carrier ρ' c) t)

/-- **The class kit**: `NestKit` with the third call case over `extN`. -/
structure ClassKit (V : Type u) [SetTheory V] (F : Type u) where
  nC : Nat
  cl : Nat → SClause V F
  fr : Nat → F
  dp : Nat → Nat
  D : Nat
  hD : ∀ b, b < nC → dp b < D
  Adm : Nat → (Nat → Nat → V → V → Prop) → F → Prop
  pred : NDec V → V
  ok : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → (cl b).OkAt ρ
  trans : ∀ b, b < nC → ∀ G, (∀ b' c t y, G b' c t y → y ∈ˢ app ((cl b').carrier (fr b') c) t) →
    ∀ ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    TupleLe (cl b).N (cl b).Is Y ((cl b).carrier (fr b)) →
    ∀ t c j fs, c < (cl b).N → (cl b).Fits ρ Y t c j fs →
      (cl b).Fits (fr b) ((cl b).carrier (fr b)) t c j fs
  /-- the call targets: an own recursive field, a parameter-position
  element, or an element of a DEEPER class at a frame admissible for
  SOME layer of `extN` -/
  calls : ∀ b, b < nC → ∀ G ρ, Adm b G ρ → ∀ Y, InTupleSpace (cl b).w (cl b).N (cl b).Is Y →
    ∀ c t j fs, c < (cl b).N → t ∈ˢ (cl b).Is c → (cl b).Fits ρ Y t c j fs →
    ∀ u, u ∈ˢ pred ⟨b, c, t, j, fs⟩ → ∃ b' c' t' y, b' < nC ∧ c' < (cl b').N ∧
      t' ∈ˢ (cl b').Is c' ∧ u = nenc b' c' t' y ∧
      ((b' = b ∧ y ∈ˢ app (Y c') t') ∨ G b' c' t' y ∨
        (dp b < dp b' ∧ ∃ n ρ', Adm b' (extN nC cl dp Adm G b Y n) ρ' ∧
          y ∈ˢ app ((cl b').carrier ρ' c') t'))
  top : ∀ b, b < nC → ∀ G, (∀ b' c t y, b' < nC → dp b' < dp b → c < (cl b').N →
      t ∈ˢ (cl b').Is c → y ∈ˢ app ((cl b').carrier (fr b') c) t → G b' c t y) →
    Adm b G (fr b)

/-- **The old kit is the layer-`0` case.** -/
def NestKit.toClassKit {F : Type u} (K : NestKit V F) : ClassKit V F where
  nC := K.nC
  cl := K.cl
  fr := K.fr
  dp := K.dp
  D := K.D
  hD := K.hD
  Adm := K.Adm
  pred := K.pred
  ok := K.ok
  trans := K.trans
  calls := fun b hb G ρ hρ Y hY c t j fs hc ht hf u hu => by
    obtain ⟨b', c', t', y, h1, h2, h3, h4, h5⟩ := K.calls b hb G ρ hρ Y hY c t j fs hc ht hf u hu
    exact ⟨b', c', t', y, h1, h2, h3, h4,
      h5.imp_right (Or.imp_right fun ⟨hdp, ρ', hA, hy⟩ => ⟨hdp, 0, ρ', hA, hy⟩)⟩
  top := K.top

namespace ClassKit

variable {F : Type u} (K : ClassKit V F)

/-- The true class `b`. -/
noncomputable def KT (b : Nat) : Nat → V := (K.cl b).carrier (K.fr b)

/-- The majors. -/
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

/-- The decodings at the TRUE frame and carrier. -/
def Dec (u : V) (d : NDec V) : Prop :=
  d.cls < K.nC ∧ d.c < (K.cl d.cls).N ∧ d.t ∈ˢ (K.cl d.cls).Is d.c ∧
    (K.cl d.cls).Fits (K.fr d.cls) (K.KT d.cls) d.t d.c d.j d.fs ∧
    u = nenc d.cls d.c d.t ((K.cl d.cls).inj d.c d.j d.fs)

theorem okT {b : Nat} (hb : b < K.nC) : (K.cl b).OkAt (K.fr b) :=
  K.ok b hb _ _ (K.top b hb (fun _ _ _ _ => True) fun _ _ _ _ _ _ _ _ _ => trivial)

/-- The property, strengthened by membership in the true class. -/
def Good (P : V → Prop) (b c : Nat) (t y : V) : Prop :=
  y ∈ˢ app (K.KT b c) t ∧ P (nenc b c t y)

/-- One class, the deeper classes assumed: every layer of `extN` is good
(inner induction on the layer), then `NestKit.claim_step`'s argument. -/
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
  let S := sepTuple (K.cl b).w (K.cl b).N (K.cl b).Is ((K.cl b).Φ ρ) fun c t y => K.Good P b c t y
  have hSmem : InTupleSpace (K.cl b).w (K.cl b).N (K.cl b).Is S := sepTuple_mem _ _ _ _ _
  have hSgood : ∀ c', c' < (K.cl b).N → ∀ t', t' ∈ˢ (K.cl b).Is c' → ∀ y, y ∈ˢ app (S c') t' →
      K.Good P b c' t' y := fun c' _ t' ht' y hy => ((mem_app_sepTuple ht').mp hy).2
  have hSle : TupleLe (K.cl b).N (K.cl b).Is S (K.KT b) :=
    fun c' hc' t' ht' y hy => (hSgood c' hc' t' ht' y hy).1
  -- every layer of the extended hypothesis set is good
  have hext : ∀ n b' c' t' y, extN K.nC K.cl K.dp K.Adm G b S n b' c' t' y → K.Good P b' c' t' y := by
    intro n
    induction n with
    | zero =>
      rintro b' c' t' y (h | ⟨rfl, hc', ht', hy⟩)
      · exact hG _ _ _ _ h
      · exact hSgood c' hc' t' ht' y hy
    | succ n ihn =>
      rintro b' c' t' y (h | ⟨hb', hdp, hc', ht', ρ', hρ', hy⟩)
      · exact ihn _ _ _ _ h
      · exact ih b' hb' hdp _ ihn ρ' hρ' c' hc' t' ht' y hy
  have hfT : (K.cl b).Fits (K.fr b) (K.KT b) t c j fs :=
    K.trans b hb G (fun b' c' t' y hy => (hG b' c' t' y hy).1) ρ hρ S hSmem hSle t c j fs hc hf
  have hmemT : (K.cl b).inj c j fs ∈ˢ app (K.KT b c) t := hokT.inj_mem hc ht hfT
  refine ⟨hmemT, hP _ (K.nenc_mem_U hb hc ht hmemT) ⟨⟨b, c, t, j, fs⟩, ⟨hb, hc, ht, hfT, rfl⟩, ?_⟩⟩
  intro u hu
  obtain ⟨b', c', t', y, hb', hc', ht', rfl, hcase⟩ := K.calls b hb G ρ hρ S hSmem c t j fs hc ht hf u hu
  rcases hcase with ⟨rfl, hy⟩ | hy | ⟨hdp, n, ρ', hρ', hy⟩
  · exact (hSgood c' hc' t' ht' y hy).2
  · exact (hG _ _ _ _ hy).2
  · exact (ih b' hb' hdp _ (hext n) ρ' hρ' c' hc' t' ht' y hy).2

/-- The strengthened induction at every admissible frame. -/
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

/-- Every true class is good, shallow classes first. -/
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

/-- **The induction principle of the majors** — `NestKit.ind`'s statement. -/
theorem ind : ∀ P : V → Prop,
    (∀ u, u ∈ˢ K.U → (∃ d, K.Dec u d ∧ ∀ j, j ∈ˢ K.pred d → P j) → P u) →
    ∀ u, u ∈ˢ K.U → P u := by
  intro P hP u hu
  obtain ⟨b, c, t, x, hb, hc, ht, hx, rfl⟩ := K.mem_U.mp hu
  exact (K.top_good P hP b hb c hc t ht x hx).2

/-- The class kit's induction, decoded (the recursor side's interface). -/
noncomputable def toNodeInd : NestNodeInd V F where
  nC := K.nC
  cl := K.cl
  fr := K.fr
  pred := K.pred
  inj_mem := fun _ _ _ _ _ hb hc ht hf => (K.okT hb).inj_mem hc ht hf
  ind := fun P hstep b c t x hb hc ht hx => by
    refine K.ind P (fun u _ ⟨d, hd, hpd⟩ => ?_) _ (K.nenc_mem_U hb hc ht hx)
    obtain ⟨hdb, hdc, hdt, hdf, rfl⟩ := hd
    exact hstep _ _ _ _ _ hdb hdc hdt hdf hpd

end ClassKit

end ConLeche.SetTheory
