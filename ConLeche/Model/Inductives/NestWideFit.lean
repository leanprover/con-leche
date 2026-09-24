module

public import ConLeche.Model.Annot.LfpHoleOp
public import ConLeche.SetModel.NestWideAt
public import ConLeche.Model.Annot.LfpHoleWitness

public section

/-!
# (W) for a nested block from its wide fits (lane NESTW, L7 step 3, the consumer)

The Model-tier record the producer (the inversion of the positivity walk)
must deliver for a nested block's datum `D` at a level assignment `ψ` and
a parameter frame `ρp`, and the theorem that it gives the hole operator
its closed tuple (`NestWideFits.closed`) through the set-level wide
presentation (`WideFits.toWideAt`, `SetModel/NestWideAt.lean`).

The record (`NestWideFits`) is stated at the HOLE FIT (`LfpDatum.HFits`):
* `n` wide keys — the walk's FRAME OCCURRENCES (NESTW F-W3) — each with
  its container GROUP (`NestGroup`: the container's recorded block `D`,
  its level assignment at the instantiation, its parameter frame read off
  the wide tuple, the frame's depth) and its component there;
* per wide constructor a FLAT field list (`FField`: hole-free, or a
  Π-tower over a member hole or a key hole) and a result index — member
  `c`'s constructor `j` is the block's with every nested occurrence a key
  hole; key `q`'s constructor `j` is its container's at the instantiation;
* the containers' clauses (`gcl`), the level (`gw`: "mutually inductive
  types must live in the same universe", `nestInstType`), the containers'
  parameter frames satisfied (`gsat`), N2 (`idx`: a key's index set does
  not depend on the wide tuple);
* U4 at every non-ordinary field (`munread`/`kunread`, F-W1: the kernel
  fact NESTKERN's U4 extension supplies);
* **the fits** (`mfit`, `kfit`): a spine fitting a member's constructor at
  the hole frame of the members fits its flat fields at the wide tuple,
  once the keys dominate their values; a spine fitting a container's
  constructor at the group's tuple read at the keys fits the key's flat
  fields, once the deeper keys dominate.

The member injections are the hole operator's (the tagged tower of the
fields and a trailing point, `LfpDatum.holeOp_fibre`); the keys' are the
containers' clauses' `inj` (F-W2).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.SetTheory.Tower (mkTower)
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-- **A key group at the instantiation** (a container frame's reached
group): the container's recorded block, its level assignment at the
instantiation, its parameter frame read off the wide tuple, and the
frame's depth in the walk. -/
structure NestGroup (V : Type w) [SetTheory V] where
  D : LfpDatum V
  ψ : Name → Nat
  ρ : (Nat → V) → Nat → V
  dep : Nat

/-- **The key groups** of the wide presentation: a key's group, its
component there, the group's index sets and operator at the parameter
frame read off the wide tuple. -/
@[expose] noncomputable def nestKeyGroups (grp cmp : Nat → Nat) (G : Nat → NestGroup V) :
    KeyGroups V where
  grp := grp
  cmp := cmp
  g := fun g => (G g).D.N
  IsG := fun g W => (G g).D.idx (G g).ψ ((G g).ρ W)
  Θ := fun g W => (G g).D.Φ (G g).ψ ((G g).ρ W)
  dep := fun g => (G g).dep

/-- **The wide presentation of a nested block, at the hole fit** (see
the module docstring). -/
structure NestWideFits (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) : Type w where
  /-- the number of wide keys (the walk's frame occurrences) -/
  n : Nat
  /-- key ↦ its group, its component there -/
  grp : Nat → Nat
  cmp : Nat → Nat
  /-- group ↦ the container's block at the instantiation -/
  G : Nat → NestGroup V
  /-- the keys' index sets -/
  kIs : Nat → V
  /-- the frame the flat fields read -/
  ρ₀ : Nat → V
  /-- member `c`'s constructor `j`: flat fields, result index -/
  mf : Nat → Nat → List (FField V)
  mi : Nat → Nat → (Nat → V) → V
  /-- key `q`'s constructor `j`: flat fields, result index -/
  kf : Nat → Nat → List (FField V)
  ki : Nat → Nat → (Nat → V) → V
  /-- the containers' lfp clauses -/
  gcl : ∀ q, q < n → ∃ acv, LfpClause acv (G (grp q)).D
  /-- the containers live in the block's universe -/
  gw : ∀ q, q < n → (G (grp q)).D.w (G (grp q)).ψ = D.w ψ
  /-- the containers' parameter frames are satisfied -/
  gsat : ∀ q, q < n → ∀ W, InTupleSpace (D.w ψ) (D.N + n) (catTup D.N (D.idx ψ ρp) kIs) W →
    Sat V ((G (grp q)).D.params (G (grp q)).ψ).reverse ((G (grp q)).ρ W)
  cmp_lt : ∀ q, q < n → cmp q < (G (grp q)).D.N
  inj : ∀ q q', q < n → q' < n → grp q = grp q' → cmp q = cmp q' → q = q'
  /-- N2: a key's index set is its component's -/
  idx : ∀ q, q < n → ∀ W, InTupleSpace (D.w ψ) (D.N + n) (catTup D.N (D.idx ψ ρp) kIs) W →
    (G (grp q)).D.idx (G (grp q)).ψ ((G (grp q)).ρ W) (cmp q) = kIs q
  mwf : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ f ∈ mf c j, f.WF (D.w ψ) (D.N + n)
  kwf : ∀ q, q < n → ∀ j, j < (G (grp q)).D.nctors (cmp q) → ∀ f ∈ kf q j,
    f.WF (D.w ψ) (D.N + n)
  /-- U4 at every non-ordinary field (F-W1) -/
  munread : ∀ c, c < D.N → ∀ j, j < D.nctors c → HoleUnread (mf c j) ρ₀ ρ₀
  kunread : ∀ q, q < n → ∀ j, j < (G (grp q)).D.nctors (cmp q) → HoleUnread (kf q j) ρ₀ ρ₀
  /-- **the members' fit** -/
  mfit : ∀ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → InTupleSpace (D.w ψ) n kIs Y →
    Dominated D.N n (catTup D.N (D.idx ψ ρp) kIs) ((nestKeyGroups grp cmp G).ev (D.w ψ))
      (catTup D.N X Y) →
    ∀ c, c < D.N → ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ j fs, D.HFits ψ ρp X t c j fs →
    FitsF (mf c j) ρ₀ (catTup D.N X Y) fs ∧ mi c j (fconsList fs ρ₀) = t
  /-- **the keys' fit**, at every tuple of the group agreeing with the
  wide tuple at the reached components -/
  kfit : ∀ W, InTupleSpace (D.w ψ) (D.N + n) (catTup D.N (D.idx ψ ρp) kIs) W → ∀ q, q < n →
    (∀ q', q' < n → (G (grp q)).dep < (G (grp q')).dep →
      FamLe (kIs q') ((nestKeyGroups grp cmp G).ev (D.w ψ) q' W) (W (D.N + q'))) →
    ∀ Z, InTupleSpace (D.w ψ) (G (grp q)).D.N
        ((G (grp q)).D.idx (G (grp q)).ψ ((G (grp q)).ρ W)) Z →
      (∀ q', q' < n → grp q' = grp q → Z (cmp q') = W (D.N + q')) →
    ∀ t, t ∈ˢ kIs q → ∀ j fs,
      (G (grp q)).D.HFits (G (grp q)).ψ ((G (grp q)).ρ W) Z t (cmp q) j fs →
      FitsF (kf q j) ρ₀ W fs ∧ ki q j (fconsList fs ρ₀) = t

namespace NestWideFits

variable {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V}

/-- The member injection: the hole operator's tagged tower. -/
@[expose] noncomputable def mInj : Nat → Nat → List V → V := fun _ j fs =>
  ConLeche.SetTheory.Tower.inj j (mkTower (fs ++ [(pt : V)]))

theorem mInj_univ {w' : Nat} (hw : w' ≠ 0) (c j : Nat) {fs : List V}
    (h : ∀ y ∈ fs, y ∈ˢ (univ w' : V)) : mInj c j fs ∈ˢ (univ w' : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have := uinj_mem_univ_pos hw j (fs := fs ++ [(pt : V)]) fun y hy => by
    rcases List.mem_append.mp hy with hy | hy
    · exact h y hy
    · rw [List.mem_singleton.mp hy]
      exact hU.transitive (unitSet_mem_univ w') pt_mem_unitSet
  rwa [uinj_pos hw] at this

/-- **The set-level flat fits** of the record, given the hole operator's
fibre premises (`LfpDatum.holeOp_fibre`). -/
noncomputable def toWideFits (F : NestWideFits D ψ ρp) (hw : D.w ψ ≠ 0)
    (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (happ : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.HolesApplied ψ c j)
    (hres : ∀ c, c < D.N → ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length) :
    WideFits (D.w ψ) D.N (D.idx ψ ρp) (D.holeOp ψ ρp) where
  n := F.n
  kIs := F.kIs
  ρ₀ := F.ρ₀
  P := nestKeyGroups F.grp F.cmp F.G
  mn := D.nctors
  mf := F.mf
  mi := F.mi
  mι := mInj
  kn := fun q => (F.G (F.grp q)).D.nctors (F.cmp q)
  kf := F.kf
  ki := F.ki
  kι := fun q j fs => (F.G (F.grp q)).D.inj (F.G (F.grp q)).ψ (F.cmp q) j fs
  mwf := F.mwf
  kwf := F.kwf
  munread := F.munread
  kunread := F.kunread
  mιU := fun c _ j _ h => mInj_univ hw c j h
  cmp_lt := F.cmp_lt
  inj := F.inj
  idx := F.idx
  functor := fun W hW q hq => by
    obtain ⟨acv, hcl⟩ := F.gcl q hq
    have h := hcl.functor _ _ (F.gsat q hq W hW)
    rw [F.gw q hq] at h
    exact h
  mfib := fun X Y hX hY hd c hc t ht x hx => by
    obtain ⟨j, fs, hf, rfl⟩ := (LfpDatum.holeOp_fibre hok hkN X (happ c hc) (hres c hc) ht x).mp hx
    obtain ⟨hmf, hmi⟩ := F.mfit X Y hX hY hd c hc t ht j fs hf
    exact ⟨j, hf.1, fs, hmf, hmi, by rw [if_neg hw]; rfl⟩
  kfib := fun W hW q hq hdeep t ht x hx => by
    obtain ⟨acv, hcl⟩ := F.gcl q hq
    let P := nestKeyGroups (V := V) F.grp F.cmp F.G
    have hidx : ∀ q', q' < F.n → P.IsG (P.grp q') W (P.cmp q') = catTup D.N (D.idx ψ ρp) F.kIs (D.N + q') :=
      fun q' hq' => (F.idx q' hq' W hW).trans (catTup_add _ _ q').symm
    have hfill := KeyGroups.fill_inTupleSpace (P := P) hW hidx (P.grp q)
    have hsat := F.gsat q hq W hW
    have htG : t ∈ˢ (F.G (F.grp q)).D.idx (F.G (F.grp q)).ψ ((F.G (F.grp q)).ρ W) (F.cmp q) := by
      rw [F.idx q hq W hW]; exact ht
    have hfill' : InTupleSpace ((F.G (F.grp q)).D.w (F.G (F.grp q)).ψ) (F.G (F.grp q)).D.N
        ((F.G (F.grp q)).D.idx (F.G (F.grp q)).ψ ((F.G (F.grp q)).ρ W))
        (P.fill (D.w ψ) D.N F.n (F.grp q) W) := by
      rw [F.gw q hq]; exact hfill
    obtain ⟨j, fs, hf, rfl⟩ := (hcl.fibre _ _ hsat _ hfill' (F.cmp q) (F.cmp_lt q hq) t htG x).mp hx
    have hagree : ∀ q', q' < F.n → F.grp q' = F.grp q →
        P.fill (D.w ψ) D.N F.n (F.grp q) W (F.cmp q') = W (D.N + q') := by
      intro q' hq' hg
      rw [← hg]
      exact KeyGroups.fill_reached (P := P) hq' F.inj W
    obtain ⟨hkf, hki⟩ := F.kfit W hW q hq hdeep _ hfill hagree t ht j fs hf
    exact ⟨j, hf.1, fs, hkf, hki, rfl⟩

/-- **(W) for a nested block's hole operator**, from its wide fits, at a
`Type`-valued parameter frame. -/
theorem closed (F : NestWideFits D ψ ρp) (hw : D.w ψ ≠ 0)
    (hok : D.HoleTmOk ψ ρp) (hkN : D.k ≤ D.N)
    (happ : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.HolesApplied ψ c j)
    (hres : ∀ c, c < D.N → ∀ j, j < D.nctors c → (D.resIdx ψ c j).length = (D.ids c ψ).length) :
    ∃ L, IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) (D.holeOp ψ ρp) L :=
  (F.toWideFits hw hok hkN happ hres).closed hw

end NestWideFits

/-! ## The adapter: Model field readings as flat fields (L7 step 3.1)

What a producer of `NestWideFits.mfit`/`kfit` reads a constructor's
fields with: `fitsF_of_reads` turns per-field inclusions of the Model
readings into the flat fields' fit; the flat fields of the three field
kinds are `plainF` (hole-free), `rtelOf … m` (a Π-tower over member
`m`'s hole) and `rtelOf … (k + q)` (over key `q`'s hole), with the
inclusions `interp_sub_plainF`, `interp_mkPisAV_sub_rtelOf` (the tower)
over `interp_holeApp_frame` (a member hole applied to the parameters)
or a key's container reading. -/

section Adapter

omit [SetTheory V] in
theorem fcons_eq_cons (a : V) (ρ : Nat → V) : fcons a ρ = cons a ρ :=
  funext fun i => by cases i <;> rfl

omit [SetTheory V] in
theorem fconsList_eq_consList : ∀ (as : List V) (ρ : Nat → V), fconsList as ρ = consList as ρ
  | [], _ => rfl
  | a :: as, ρ => by
    show fconsList as (fcons a ρ) = consList as (cons a ρ)
    rw [fcons_eq_cons, fconsList_eq_consList]

theorem consList_getD_rev : ∀ (L : List V) (σ : Nat → V) {i : Nat}, i < L.length →
    consList L σ i = L.getD (L.length - 1 - i) pt
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, σ, i, h => by
    rw [consList_cons]
    rcases Nat.lt_or_ge i L.length with hi | hi
    · rw [consList_getD_rev L (cons a σ) hi, List.length_cons,
        show L.length + 1 - 1 - i = (L.length - 1 - i) + 1 by omega, List.getD_cons_succ]
    · obtain rfl : i = L.length := by simp at h; omega
      have := consList_apply_add L (cons a σ) 0
      rw [Nat.zero_add] at this
      rw [this, List.length_cons, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]
      rfl

open Classical in
/-- A set, kept where it is a member of the universe. -/
@[expose] noncomputable def keepU (w : Nat) (S : V) : V := if S ∈ˢ (univ w : V) then S else empty

theorem keepU_mem (w : Nat) (S : V) : keepU w S ∈ˢ (univ w : V) := by
  unfold keepU; split
  · assumption
  · exact empty_mem_univ w

theorem keepU_of_mem {w : Nat} {S : V} (h : S ∈ˢ (univ w : V)) : keepU w S = S := by
  unfold keepU; rw [if_pos h]

/-- **The fit from the fields' readings**: a spine fitting a field list
fits a flat field list whose field types contain the readings. -/
theorem fitsF_of_reads {X : Nat → V} :
    ∀ {Fs : List AnnotTerm} {ffs : List (FField V)} {σ ρ : Nat → V} {fs : List V},
      ffs.length = Fs.length →
      (∀ l, l < Fs.length → ∀ as : List V, SpineFit σ (Fs.take l) as →
        interp V (consList as σ) (Fs.getD l default)
          ⊆ˢ (ffs.getD l (.plain fun _ => empty)).read (fconsList as ρ) X) →
      SpineFit σ Fs fs → FitsF ffs ρ X fs
  | [], [], _, _, [], _, _, _ => trivial
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | [], [], _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _ :: _, _, _, [], _, _, h => h.elim
  | F :: Fs, f :: ffs, σ, ρ, a :: fs, hlen, hr, hsp => by
    refine ⟨hr 0 (by simp) [] trivial a hsp.1, ?_⟩
    refine fitsF_of_reads (σ := cons a σ) (ρ := fcons a ρ) (by simpa using hlen) (fun l hl as has => ?_) hsp.2
    exact hr (l + 1) (by simpa using hl) (a :: as) ⟨hsp.1, has⟩

/-- A hole-free field as a flat field (kept in the universe). -/
@[expose] noncomputable def plainF (w : Nat) (F : AnnotTerm) : FField V :=
  .plain fun ρ => keepU w (interp V ρ F)

theorem plainF_wf (w K : Nat) (F : AnnotTerm) : (plainF (V := V) w F).WF w K :=
  fun _ => keepU_mem w _

theorem interp_sub_plainF {w : Nat} {σ ρ : Nat → V} {F : AnnotTerm}
    (heq : interp V σ F = interp V ρ F) (hU : interp V σ F ∈ˢ (univ w : V)) (X : Nat → V) :
    interp V σ F ⊆ˢ (plainF w F).read ρ X := by
  show _ ⊆ˢ keepU w (interp V ρ F)
  rw [← heq, keepU_of_mem hU]
  exact Subset.refl _

/-- A Π-tower of hole-free domains over a hole (a member's or a key's) as
a flat field type, the domains kept in the universe. -/
@[expose] noncomputable def rtelOf (w : Nat) :
    List (Nat × Nat × AnnotTerm) → Nat → ((Nat → V) → V) → RTel V
  | [], tgt, es => .hole tgt es
  | d :: tl, tgt, es => .pi d.2.1 (fun ρ => keepU w (interp V ρ d.2.2)) (rtelOf w tl tgt es)

theorem rtelOf_wf {w K : Nat} : ∀ (tl : List (Nat × Nat × AnnotTerm)) {tgt : Nat}
    {es : (Nat → V) → V}, (∀ d ∈ tl, d.2.1 ≠ 0) → tgt < K → (rtelOf w tl tgt es).WF w K
  | [], _, _, _, h => h
  | d :: tl, _, _, hb, h =>
    ⟨hb d List.mem_cons_self, fun _ => keepU_mem w _,
      rtelOf_wf tl (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd')) h⟩

/-- **A Π-tower's reading lies in its flat field type** when its domains
read alike at the two frames and are sets of the level, and its body lies
in the hole's fibre. -/
theorem interp_mkPisAV_sub_rtelOf {w : Nat} {X : Nat → V} {tgt : Nat} {es : (Nat → V) → V}
    {b : AnnotTerm} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) {σ ρ : Nat → V},
      (∀ q dd, tl[q]? = some dd → ∀ bs : List V, SpineFit σ ((tl.take q).map (·.2.2)) bs →
        interp V (consList bs σ) dd.2.2 = interp V (consList bs ρ) dd.2.2 ∧
        interp V (consList bs σ) dd.2.2 ∈ˢ (univ w : V)) →
      (∀ bs : List V, SpineFit σ (tl.map (·.2.2)) bs →
        interp V (consList bs σ) b ⊆ˢ app (X tgt) (es (consList bs ρ))) →
      interp V σ (mkPisAV tl b) ⊆ˢ (rtelOf w tl tgt es).read ρ X
  | [], σ, ρ, _, hb => by
    have := hb [] trivial
    simpa [mkPisAV, rtelOf, RTel.read] using this
  | d :: tl, σ, ρ, hd, hb => by
    obtain ⟨heq, hU⟩ := hd 0 d rfl [] trivial
    simp only [consList_nil] at heq hU
    show piR d.2.1 (interp V σ d.2.2) (fun x => interp V (cons x σ) (mkPisAV tl b))
      ⊆ˢ piR d.2.1 (keepU w (interp V ρ d.2.2)) (fun a => (rtelOf w tl tgt es).read (fcons a ρ) X)
    rw [← heq, keepU_of_mem hU]
    refine piR_subset_mono fun x hx => ?_
    rw [fcons_eq_cons]
    refine interp_mkPisAV_sub_rtelOf tl (fun q dd hq bs hbs => ?_) (fun bs hbs => ?_)
    · have := hd (q + 1) dd (by simpa using hq) (x :: bs) ⟨hx, by simpa using hbs⟩
      simpa [consList_cons] using this
    · have := hb (x :: bs) ⟨hx, hbs⟩
      simpa [consList_cons] using this

/-- **A hole-free term reads alike at every hole frame** (below the same
local values). -/
theorem interp_frame_noHole (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (X X' : Nat → V)
    (as : List V) {e : AnnotTerm} (h : NoBVar (LfpDatum.holeSlots D.k as.length) e) :
    interp V (consList as (D.frame ψ ρp X)) e = interp V (consList as (D.frame ψ ρp X')) e := by
  refine interp_congr_noBVar e h fun i hi => ?_
  rcases Nat.lt_or_ge i as.length with h1 | h1
  · rw [consList_getD_rev _ _ h1, consList_getD_rev _ _ h1]
  have hk : ∀ Y : Nat → V, ((List.range D.k).map (D.holeVal ψ ρp Y)).length = D.k := by simp
  have e1 := consList_apply_add as (D.frame ψ ρp X) (i - as.length)
  have e2 := consList_apply_add as (D.frame ψ ρp X') (i - as.length)
  rw [Nat.sub_add_cancel h1] at e1 e2
  rw [e1, e2]
  unfold LfpDatum.frame
  have h2 : D.k ≤ i - as.length := by
    unfold LfpDatum.holeSlots at hi; omega
  have f1 := consList_apply_add ((List.range D.k).map (D.holeVal ψ ρp X)) ρp (i - as.length - D.k)
  have f2 := consList_apply_add ((List.range D.k).map (D.holeVal ψ ρp X')) ρp (i - as.length - D.k)
  rw [hk, Nat.sub_add_cancel h2] at f1 f2
  rw [f1, f2]

/-- **A member hole applied to the parameters and fitting indices reads
as the member's family** at the index tuple, at every hole frame. -/
theorem interp_holeApp_frame {D : LfpDatum V} {ψ : Name → Nat} {ρp X : Nat → V}
    (hok : D.HoleTmOk ψ ρp) {m : Nat} (hm : m < D.k) (L : List V) (es : List AnnotTerm)
    (his : SpineFit ρp (D.ids m ψ) (es.map (interp V (consList L (D.frame ψ ρp X))))) :
    interp V (consList L (D.frame ψ ρp X)) (AnnotTerm.mkAppN (.bvar (L.length + (D.k - 1 - m)))
        (holeParams D.k (D.params ψ).length L.length ++ es))
      = app (X m) (tupW (D.u m ψ) (es.map (interp V (consList L (D.frame ψ ρp X))))) := by
  rw [interp_mkAppN_foldl, List.map_append, map_interp_holeParams]
  have hk : ((List.range D.k).map (D.holeVal ψ ρp X)).length = D.k := by simp
  have hhole : interp V (consList L (D.frame ψ ρp X)) (.bvar (L.length + (D.k - 1 - m)))
      = D.holeVal ψ ρp X m := by
    show consList L (D.frame ψ ρp X) (L.length + (D.k - 1 - m)) = _
    rw [show L.length + (D.k - 1 - m) = (D.k - 1 - m) + L.length by omega, consList_apply_add]
    unfold LfpDatum.frame
    rw [consList_getD_rev _ _ (by rw [hk]; omega), hk,
      show D.k - 1 - (D.k - 1 - m) = m by omega, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hm]
    rfl
  have hpar : holeParamVals D.k (D.params ψ).length L.length (consList L (D.frame ψ ρp X))
      = frameIdx (D.pars m ψ).length ρp := by
    rw [(hok m hm).1.1]
    unfold holeParamVals frameIdx
    refine List.map_congr_left fun p hp => ?_
    have hp' := List.mem_range.mp hp
    rw [show L.length + D.k + (D.params ψ).length - 1 - p
        = (D.k + ((D.params ψ).length - 1 - p)) + L.length by omega, consList_apply_add]
    unfold LfpDatum.frame
    have := consList_apply_add ((List.range D.k).map (D.holeVal ψ ρp X)) ρp
      ((D.params ψ).length - 1 - p)
    rw [hk, Nat.add_comm] at this
    exact this
  rw [hhole, hpar]
  exact D.holeVal_app (hok m hm).1.2 his

end Adapter

end ConLeche.Model
