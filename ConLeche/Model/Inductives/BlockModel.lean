module

public import ConLeche.Model.Inductives.BlockRep
public section

/-!
# The block's representation, from the stages' semantic outputs (task #315 M3)

`blockModelAt_of_stages`: every clause of `BlockRep.lean`'s
`BlockModelAt` at the fixpoint route's data — the operator is
`blockPhi`, the injections the tagged tuples of the member-LOCAL sum
route, the members' leaves `blockTyAV`.

The one bridge the record needs and the tower files do not have is
between the two spellings of "a spine fits constructor `j`'s entries":
the operator's is a `SpineFit` along the X-chain (`chainXBIGo`, at the
frame carrying the index tuple and the family tuple), the record's is
`FitsFrom` at the parameter frame with the recursive entries named as
SETS (`slotSet` at the target component).  They are the same relation
(`fitsFrom_iff_spineFit_chainXBIGo`): the X-chain's recursive entry
denotes that slot (`xEntryB_rec`) and its ordinary entry is the
domain's own reading two frames up (`xEntryB_ord`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The two spellings of a constructor's fit -/

/-- **The X-chain's fit IS the record's `FitsFrom`.**  Along the
X-chain the frame carries the index tuple and the family tuple and a
recursive entry is the slot's TERM (`slotXBI` at the target
component); in the record the frame is the parameter frame alone and a
recursive entry is the slot's VALUE.  The premise is the operator's own
(`BlockChainsOk.hfit`): at a family tuple of the space the recursive
slots fit. -/
theorem fitsFrom_iff_spineFit_chainXBIGo {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} (hIall : BlockIdxOk (V := V) k uf ρp Idss)
    {Y t : V} {rs : List Bool} {tgts : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t i as Fs →
      (SpineFit (consList as (cons t (cons Y ρp))) (chainXBIGo uf Idss rs tgts tls Eis Fs i) bs
        ↔ FitsFrom rs
            (fun l ρ => slotSet w (uf (tgts.getD l 0)) ρ (tls.getD l []) (Eis.getD l [])
              (projS (tgts.getD l 0) Y)) i (consList as ρp) Fs bs)
  | [], _, _, [], _, _ => Iff.rfl
  | [], _, _, _ :: _, _, _ => Iff.rfl
  | _ :: _, _, _, [], _, _ => Iff.rfl
  | F :: Fs, i, as, b :: bs, hi, hfit => by
    subst hi
    rw [chainXBIGo_cons]
    have hhead : interp V (consList as (cons t (cons Y ρp)))
          (xEntryB uf Idss rs tgts tls Eis F as.length)
        = (if rs.getD as.length false then
             slotSet w (uf (tgts.getD as.length 0)) (consList as ρp) (tls.getD as.length [])
               (Eis.getD as.length []) (projS (tgts.getD as.length 0) Y)
           else interp V (consList as ρp) F) := by
      by_cases hr : rs.getD as.length false = true
      · obtain ⟨hct, hsf⟩ := hfit.1 hr
        rw [xEntryB_rec (Y := Y) F as t (hIall _ hct) hr hsf, if_pos hr]
      · have hr' : rs.getD as.length false = false := by simpa using hr
        rw [xEntryB_ord F as t hr', if_neg (by rw [hr']; exact Bool.false_ne_true)]
    constructor
    · rintro ⟨hb, hrest⟩
      refine ⟨by rw [← hhead]; exact hb, ?_⟩
      rw [consList_snoc'] at hrest ⊢
      exact (fitsFrom_iff_spineFit_chainXBIGo hIall Fs (as.length + 1) (as ++ [b]) bs
        (length_snoc' b as) (hfit.2 b hb)).mp hrest
    · rintro ⟨hb, hrest⟩
      have hb' : b ∈ˢ interp V (consList as (cons t (cons Y ρp)))
          (xEntryB uf Idss rs tgts tls Eis F as.length) := by rw [hhead]; exact hb
      refine ⟨hb', ?_⟩
      rw [consList_snoc'] at hrest ⊢
      exact (fitsFrom_iff_spineFit_chainXBIGo hIall Fs (as.length + 1) (as ++ [b]) bs
        (length_snoc' b as) (hfit.2 b hb')).mpr hrest

/-- `FitsFrom` reads the slot function only at the positions of its own
field list. -/
theorem FitsFrom.congr_slot {rs : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length → ∀ σ : Nat → V, slot (i + l) σ = slot' (i + l) σ) →
      FitsFrom rs slot i ρ Fs as → FitsFrom rs slot' i ρ Fs as
  | _, _, [], [], _, _ => trivial
  | _, _, [], _ :: _, _, h => h.elim
  | _, _, _ :: _, [], _, h => h.elim
  | i, ρ, F :: Fs, a :: as, hag, h => by
    refine ⟨?_, FitsFrom.congr_slot (fun l hl σ => ?_) h.2⟩
    · have h0 := hag 0 (by simp) ρ
      rw [Nat.add_zero] at h0
      have h1 : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) := h.1
      show a ∈ˢ (if rs.getD i false then slot' i ρ else interp V ρ F)
      by_cases hr : rs.getD i false = true
      · rw [if_pos hr] at h1 ⊢
        rw [← h0]; exact h1
      · have hr' : rs.getD i false = false := by simpa using hr
        rw [hr'] at h1 ⊢
        exact h1
    · have := hag (l + 1) (by simpa using hl) σ
      rwa [show i + (l + 1) = i + 1 + l from by omega] at this

/-- **A constructor's fit, read at its DOMAINS**: `FitsFrom` and
`SpineFit` walk the same list at the same frames and differ only at a
RECURSIVE position, where the first asks the value in the block's slot
and the second in the domain's own reading.  Where the two agree at
every recursive position of the list, the fixpoint route's fit IS the
domains' fit — the step from `BlockData.ChainFit` (what the carrier's
case analysis hands back) to `SpineFit` (what a rule's certificates
ask for). -/
theorem spineFit_of_fitsFrom {rs : List Bool} {slot : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length → ∀ bs : List V,
        FitsFrom rs slot i ρ (Fs.take l) bs → rs.getD (i + l) false = true →
        slot (i + l) (consList bs ρ) = interp V (consList bs ρ) (Fs.getD l default)) →
      FitsFrom rs slot i ρ Fs as → SpineFit ρ Fs as
  | _, _, [], [], _, _ => trivial
  | _, _, [], _ :: _, _, h => h.elim
  | _, _, _ :: _, [], _, h => h.elim
  | i, ρ, F :: Fs, a :: as, hag, h => by
    refine ⟨?_, spineFit_of_fitsFrom (fun l hl bs hb hr => ?_) h.2⟩
    · have h1 : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) := h.1
      by_cases hr : rs.getD i false = true
      · rw [if_pos hr] at h1
        have h0 := hag 0 (by simp) [] trivial (by rw [Nat.add_zero]; exact hr)
        rw [Nat.add_zero] at h0
        simp only [consList_nil] at h0
        rw [h0] at h1
        exact h1
      · have hr' : rs.getD i false = false := by simpa using hr
        rw [hr'] at h1
        exact h1
    · have hb' : FitsFrom rs slot i ρ ((F :: Fs).take (l + 1)) (a :: bs) := ⟨h.1, hb⟩
      have hag' := hag (l + 1) (by simpa using hl) (a :: bs) hb'
        (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hr)
      rw [show i + (l + 1) = i + 1 + l from by omega] at hag'
      exact hag'

/-- The converse of `spineFit_of_fitsFrom`: under the same agreement
a domains' fit is the fixpoint route's fit — what turns a RULE's
fitting spine back into the constructor's `ChainFit` at the carrier
(`hctorAt`'s first conjunct). -/
theorem fitsFrom_of_spineFit {rs : List Bool} {slot : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length → ∀ bs : List V,
        FitsFrom rs slot i ρ (Fs.take l) bs → rs.getD (i + l) false = true →
        slot (i + l) (consList bs ρ) = interp V (consList bs ρ) (Fs.getD l default)) →
      SpineFit ρ Fs as → FitsFrom rs slot i ρ Fs as
  | _, _, [], [], _, _ => trivial
  | _, _, [], _ :: _, _, h => h.elim
  | _, _, _ :: _, [], _, h => h.elim
  | i, ρ, F :: Fs, a :: as, hag, h => by
    have hhd : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) := by
      by_cases hr : rs.getD i false = true
      · rw [if_pos hr]
        have h0 := hag 0 (by simp) [] trivial (by rw [Nat.add_zero]; exact hr)
        rw [Nat.add_zero] at h0
        simp only [consList_nil] at h0
        rw [h0]
        exact h.1
      · have hr' : rs.getD i false = false := by simpa using hr
        rw [hr']
        exact h.1
    refine ⟨hhd, fitsFrom_of_spineFit (fun l hl bs hb hr => ?_) h.2⟩
    have hb' : FitsFrom rs slot i ρ ((F :: Fs).take (l + 1)) (a :: bs) := ⟨hhd, hb⟩
    have hag' := hag (l + 1) (by simpa using hl) (a :: bs) hb'
      (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hr)
    rw [show i + (l + 1) = i + 1 + l from by omega] at hag'
    exact hag'

/-! ## The operator's fibre, both regimes in one equivalence -/

/-- **The block operator's fibre at a tuple of the space**: an element
is the injection of a spine fitting one of the component's OWN
constructors, whose index readings are the tuple's components — the
`fibre` clause of `BlockModelAt`, stated at the operator's own
spelling.  The tag is member-LOCAL (`j` is the component's own
constructor position) and at a `Prop`-valued block every element is
the point. -/
theorem blockStepV_mem_iff {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {rsss : Nat → List (List Bool)}
    {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}
    (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) (x : V) :
    x ∈ˢ blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m Y t ↔
      ∃ j fs, j < (Fsss m).length ∧
        FitsFrom ((rsss m).getD j [])
          (fun l σ => slotSet w (uf ((((tgtsss m).getD j []).getD l 0))) σ
            (((tlsss m).getD j []).getD l []) (((Eisss m).getD j []).getD l [])
            (projS (((tgtsss m).getD j []).getD l 0) Y)) 0 ρp ((Fsss m).getD j []) fs ∧
        (∀ l, l < (Idss m).length →
          interp V (consList fs ρp) (((Esss m).getD j []).getD l default) = projS l t) ∧
        x = (if w = 0 then (pt : V) else inj j (mkTower (fs ++ [pt]))) := by
  constructor
  · intro hx
    by_cases hw : w = 0
    · subst hw
      obtain ⟨rfl, j, fs, hj, hlen, hsp, hall⟩ := blockStepV_zero_elim hx
      refine ⟨j, fs, hj, ?_, ?_, by rw [if_pos rfl]⟩
      · have := (fitsFrom_iff_spineFit_chainXBIGo (Y := Y) (t := t) h.hI ((Fsss m).getD j []) 0 []
          fs rfl (h.hfit Y hY m hm t ht j hj)).mp (by simpa using hsp)
        simpa using this
      · exact (EqAll_eqsXI_gen (X := Y) (t := t) hlen).mp hall
    · obtain ⟨j, fs, rfl, hj, hlen, hsp, hall⟩ := blockStepV_elim hw hx
      refine ⟨j, fs, hj, ?_, ?_, by rw [if_neg hw]⟩
      · have := (fitsFrom_iff_spineFit_chainXBIGo (Y := Y) (t := t) h.hI ((Fsss m).getD j []) 0 []
          fs rfl (h.hfit Y hY m hm t ht j hj)).mp (by simpa using hsp)
        simpa using this
      · exact (EqAll_eqsXI_gen (X := Y) (t := t) hlen).mp hall
  · rintro ⟨j, fs, hj, hfit, heq, rfl⟩
    have hlen : fs.length = ((Fsss m).getD j []).length := hfit.length_eq
    have hsp : SpineFit (cons t (cons Y ρp))
        (chainXBIGo uf Idss ((rsss m).getD j []) ((tgtsss m).getD j []) ((tlsss m).getD j [])
          ((Eisss m).getD j []) ((Fsss m).getD j []) 0) fs := by
      have := (fitsFrom_iff_spineFit_chainXBIGo (Y := Y) (t := t) h.hI ((Fsss m).getD j []) 0 []
        fs rfl (h.hfit Y hY m hm t ht j hj)).mpr (by simpa using hfit)
      simpa using this
    have hall : EqAll (consList fs (cons t (cons Y ρp)))
        (eqsXI (Idss m).length ((Fsss m).getD j []).length ((Esss m).getD j [])) :=
      (EqAll_eqsXI_gen (X := Y) (t := t) hlen).mpr heq
    have hspE : SpineFit (cons t (cons Y ρp))
        (chainXBI uf Idss (Idss m).length ((rsss m).getD j []) ((tgtsss m).getD j [])
          ((tlsss m).getD j []) ((Eisss m).getD j []) ((Fsss m).getD j [])
          ((Esss m).getD j [])) (fs ++ [pt]) :=
      spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩
    have hfib : sumFibre w (cons t (cons Y ρp))
        (chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m)
          (Fsss m) (Esss m)) j
        = towerSet w (teleOfFields (cons t (cons Y ρp))
            (chainXBI uf Idss (Idss m).length ((rsss m).getD j []) ((tgtsss m).getD j [])
              ((tlsss m).getD j []) ((Eisss m).getD j []) ((Fsss m).getD j [])
              ((Esss m).getD j []))) :=
      sumFibre_of_getElem? (by rw [chainsXBI_getElem?, if_pos hj])
    unfold blockStepV
    by_cases hw : w = 0
    · subst hw
      rw [if_pos rfl]
      refine pt_mem_sumSet_zero (i := j) (a := pt) ?_
      rw [hfib]
      exact pt_mem_tower_teleOfFields hspE
    · rw [if_neg hw]
      refine inj_mem hw ?_
      rw [hfib]
      exact mkTower_mem_teleOfFields hw hspE


/-- **The X-chain entry's VALUE** — `fitsFrom_iff_spineFit_chainXBIGo`'s
own head computation, as a lemma: at a prefix where the recursive slot
fits, the entry reads to the slot's set at a recursive position and to
the domain's reading at an ordinary one. -/
theorem xEntryB_value {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} (hIall : BlockIdxOk (V := V) k uf ρp Idss)
    {Y t : V} {rs : List Bool} {tgts : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    {F : AnnotTerm} {as : List V}
    (hfit : rs.getD as.length false = true → tgts.getD as.length 0 < k ∧
      SlotFit (uf (tgts.getD as.length 0)) w ρp (Idss (tgts.getD as.length 0))
        (tls.getD as.length []) (Eis.getD as.length []) as) :
    interp V (consList as (cons t (cons Y ρp))) (xEntryB uf Idss rs tgts tls Eis F as.length)
      = (if rs.getD as.length false then
           slotSet w (uf (tgts.getD as.length 0)) (consList as ρp) (tls.getD as.length [])
             (Eis.getD as.length []) (projS (tgts.getD as.length 0) Y)
         else interp V (consList as ρp) F) := by
  by_cases hr : rs.getD as.length false = true
  · obtain ⟨hct, hsf⟩ := hfit hr
    rw [xEntryB_rec (Y := Y) F as t (hIall _ hct) hr hsf, if_pos hr]
  · have hr' : rs.getD as.length false = false := by simpa using hr
    rw [xEntryB_ord F as t hr', if_neg (by rw [hr']; exact Bool.false_ne_true)]

/-- **The operator's slot premise, along a REAL field prefix**: from
`SlotsFitXB` at the empty prefix, a spine that fits the constructor's
own entries at a tuple carries the recursive slot's `SlotFit` at every
recursive position.  The walk is `fitsFrom_iff_spineFit_chainXBIGo`'s,
advanced by the `FitsFrom` head rather than by the X-chain's. -/
theorem slotFit_of_slotsFitXB {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} (hIall : BlockIdxOk (V := V) k uf ρp Idss)
    {Y t : V} {rs : List Bool} {tgts : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (l : Nat) (Fs : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t i as Fs →
      FitsFrom rs (fun m σ => slotSet w (uf (tgts.getD m 0)) σ (tls.getD m []) (Eis.getD m [])
          (projS (tgts.getD m 0) Y)) i (consList as ρp) (Fs.take l) bs →
      rs.getD (i + l) false = true → l < Fs.length →
      tgts.getD (i + l) 0 < k ∧
      SlotFit (uf (tgts.getD (i + l) 0)) w ρp (Idss (tgts.getD (i + l) 0))
        (tls.getD (i + l) []) (Eis.getD (i + l) []) (as ++ bs) := by
  intro l
  induction l with
  | zero =>
    intro Fs i as bs hi hfit hb hr hl
    cases Fs with
    | nil => exact absurd hl (Nat.not_lt_zero _)
    | cons F Fs =>
      cases bs with
      | nil =>
        subst hi
        rw [List.append_nil, Nat.add_zero] at *
        exact hfit.1 hr
      | cons b bs => exact hb.elim
  | succ l ih =>
    intro Fs i as bs hi hfit hb hr hl
    cases Fs with
    | nil => exact absurd hl (Nat.not_lt_zero _)
    | cons F Fs =>
      cases bs with
      | nil => exact hb.elim
      | cons b bs =>
        subst hi
        have hhead : b ∈ˢ interp V (consList as (cons t (cons Y ρp)))
            (xEntryB uf Idss rs tgts tls Eis F as.length) := by
          rw [xEntryB_value hIall hfit.1]
          exact hb.1
        have hnext := hfit.2 b hhead
        have hbs : FitsFrom rs (fun m σ => slotSet w (uf (tgts.getD m 0)) σ (tls.getD m [])
            (Eis.getD m []) (projS (tgts.getD m 0) Y)) (as.length + 1)
            (consList (as ++ [b]) ρp) (Fs.take l) bs := by
          rw [← consList_snoc']
          exact hb.2
        have hq := ih Fs (as.length + 1) (as ++ [b]) bs (length_snoc' b as) hnext hbs
          (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
          (by simpa using hl)
        rw [show as.length + 1 + l = as.length + (l + 1) from by omega,
          List.append_assoc] at hq
        exact hq

/-! ## The slot operator's fibre and the slots' index fit -/

/-- The fixpoint route's slot operator at the block data. -/
noncomputable abbrev BlockData.slotPhi (d : BlockData V) (ψ : Name → Nat) (ρp : Nat → V) :
    (Nat → V) → Nat → V :=
  blockPhi d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
    (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ)

section Slot

variable {d : BlockData V}
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    (hok : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      BlockChainsOk d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
        (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ))
    (hlenC : ∀ (ψ : Name → Nat) (c : Nat), (d.Fss c ψ).length = (d.ctorsM c).length)
    (htgts : ∀ (ψ : Name → Nat) (c j l : Nat), j < (d.ctorsM c).length →
      l < ((d.Fss c ψ).getD j []).length →
      ((d.tgtss c).getD j []).getD l 0 = d.tgts c j l ∧ d.tgts c j l < d.N)
include hinj hok hlenC htgts

/-- **The slot operator's fibre**: the injections of the spines fitting a
constructor's `ChainFit`. -/
theorem blockSlotFibre :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → ∀ c, c < d.N →
    ∀ t, t ∈ˢ d.idx ψ ρp c → ∀ x,
      x ∈ˢ app (d.slotPhi ψ ρp X c) t ↔
        ∃ j fs, j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs ∧ x = d.inj ψ c j fs := by
  intro ψ ρp hρ X hX c hc t ht x
  have h := hok ψ ρp hρ
  have hY := ndMkTowerSet_mem_famsSpaceB (V := V) (k := d.N) (w := d.w ψ) (ρp := ρp)
    (uf := fun c => d.uM c ψ) (Idss := fun c => d.IdsM c ψ) hX
  unfold BlockData.slotPhi
  rw [app_blockPhi (uf := fun c => d.uM c ψ) (Idss := fun c => d.IdsM c ψ) ht,
    blockStepV_mem_iff h hY hc ht x]
  constructor
  · rintro ⟨j, fs, hj, hfit, heq, rfl⟩
    rw [hlenC] at hj
    refine ⟨j, fs, hj, ⟨?_, heq⟩, (hinj ψ c j fs).symm⟩
    refine FitsFrom.congr_slot (fun l hl σ => ?_) hfit
    rw [Nat.zero_add]
    obtain ⟨htg, hlt⟩ := htgts ψ c j l hj hl
    show slotSet _ _ _ _ _ _ = _
    rw [htg, projS_ndMkTowerSet_zero hlt]
    rfl
  · rintro ⟨j, fs, hj, ⟨hfit, heq⟩, rfl⟩
    refine ⟨j, fs, by rw [hlenC]; exact hj, ?_, heq, hinj ψ c j fs⟩
    refine FitsFrom.congr_slot (fun l hl σ => ?_) hfit
    rw [Nat.zero_add]
    obtain ⟨htg, hlt⟩ := htgts ψ c j l hj hl
    show _ = slotSet _ _ _ _ _ _
    rw [htg, projS_ndMkTowerSet_zero hlt]
    rfl

omit hinj in
/-- **The slots' index fit**, off the slot chains' premise bundle. -/
theorem blockIdxFit_of_chains : d.IdxFit := by
  intro ψ ρp hρ X hX c hc t ht j hj i hi hr as hb
  have h := hok ψ ρp hρ
  have hY := ndMkTowerSet_mem_famsSpaceB (V := V) (k := d.N) (w := d.w ψ) (ρp := ρp)
    (uf := fun c => d.uM c ψ) (Idss := fun c => d.IdsM c ψ) hX
  have hSF := h.hfit _ hY c hc t ht j (by rw [hlenC]; exact hj)
  have hb' : FitsFrom ((d.rss c).getD j [])
      (fun m σ => slotSet (d.w ψ) (d.uM (((d.tgtss c).getD j []).getD m 0) ψ) σ
        (((d.tlss c ψ).getD j []).getD m []) (((d.Eiss c ψ).getD j []).getD m [])
        (projS (((d.tgtss c).getD j []).getD m 0)
          (ndMkTowerSet X 0 d.N))) 0 (consList [] ρp)
      (((d.Fss c ψ).getD j []).take i) as := by
    rw [consList_nil]
    refine FitsFrom.congr_slot (fun l hl σ => ?_) hb
    rw [Nat.zero_add]
    obtain ⟨htg, hlt⟩ := htgts ψ c j l hj (by
      have hli : l < i := by
        have h' := hl
        rw [List.length_take] at h'
        omega
      omega)
    show _ = slotSet _ _ _ _ _ _
    rw [htg, projS_ndMkTowerSet_zero hlt]
    rfl
  have hq := slotFit_of_slotsFitXB h.hI i ((d.Fss c ψ).getD j []) 0 [] as rfl hSF hb' ?_ hi
  · obtain ⟨htg, hlt⟩ := htgts ψ c j i hj hi
    rw [Nat.zero_add, List.nil_append, htg] at hq
    exact hq.2
  · rw [Nat.zero_add]; exact hr

end Slot

/-! ## The representation -/

/-- **The block's representation, from the stages' outputs.**  Every
clause of `BlockModelAt` at the fixpoint route's data: the operator
agrees with `blockPhi` at the components' chains ON THE TUPLE SPACE
(`hPhi` — the datum's operator is the hole operator, lane HOLE2), the injections the
member-LOCAL sum route's tagged tuples (`hinj`), the members' leaves
`blockTyAV` (`hleaf`), the constructors' `sumMkAV` (`hctorLeaf`).  The
remaining hypotheses are the stages' own facts: the operator's premise
bundle at every parameter frame (`hok`), the data's lengths, the
parameter-telescope interchanges the members and the constructors were
checked to agree on (`hparams`, `hparamsC` — `blockParamsIff` and
`ctorFramesGen` at the run), the per-field target readings (`htgts`)
and the constructors' result index fit (`hresFit`, the constructors'
typing: their result applications were inferred at the opened
telescope). -/
theorem blockModelAt_of_stages {env : Env} (mo : EnvModel V env) {names : List Name}
    {d : BlockData V}
    -- what the representation IS
    (hnames : d.memberNames = names)
    (hPhi : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ X, InTupleSpace (d.w ψ) d.N (d.idx ψ ρp) X → ∀ c, c < d.N →
      d.Φ ψ ρp X c = d.slotPhi ψ ρp X c)
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    -- the operator's premise bundle, at every parameter frame
    (hok : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      BlockChainsOk d.N (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
        (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ))
    -- the data's shape
    (hlenC : ∀ (ψ : Name → Nat) (c : Nat), (d.Fss c ψ).length = (d.ctorsM c).length)
    (hN0 : 0 < d.N)
    (hlenPps : ∀ (ψ : Name → Nat) (c : Nat), c < d.N →
      (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (htgts : ∀ (ψ : Name → Nat) (c j l : Nat), j < (d.ctorsM c).length →
      l < ((d.Fss c ψ).getD j []).length →
      ((d.tgtss c).getD j []).getD l 0 = d.tgts c j l ∧ d.tgts c j l < d.N)
    -- the members' leaves and the members' parameter agreement
    (hleaf : ∀ mm, mm < d.k → ∀ ψ : Name → Nat, mo.acval (d.memberName mm) ψ
      = blockTyAV d.N (d.w ψ) (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) d.rss d.tgtss
          (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ) (fun c => d.Fss c ψ) (fun c => d.Ess c ψ)
          (d.ppsM mm ψ) mm)
    (hparams : ∀ (ψ : Name → Nat) (c : Nat), c < d.N → ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρ)
    -- the constructors' leaves and their parameter frames
    (hctorLeaf : ∀ c, c < d.N → ∀ (j : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM c)[j]? = some cA → ∀ ψ : Name → Nat, mo.acval cA.1.name ψ
        = sumMkAV (d.w ψ) j (d.dsF c j ψ) (((d.dsF c j ψ).drop d.nP).map (·.2.2))
            (uChains (d.Fss c ψ)))
    (hFssD : ∀ (ψ : Name → Nat) (c j : Nat), j < (d.ctorsM c).length →
      (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2))
    (hdsLen : ∀ (ψ : Name → Nat) (c j : Nat), j < (d.ctorsM c).length →
      (d.dsF c j ψ).length = d.nP + ((d.Fss c ψ).getD j []).length)
    (hparamsC : ∀ (ψ : Name → Nat) (c j : Nat), c < d.N → j < (d.ctorsM c).length →
      ∀ ρ : Nat → V,
      Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.dsF c j ψ).take d.nP).map (·.2.2)).reverse ρ)
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
      ∀ c, c < d.N → SumFieldsOkB (d.w ψ) ρ (uChains (d.Fss c ψ)))
    -- the constructors' RESULT index readings fit the component's telescope
    (hresFit : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat V (d.params ψ).reverse ρ →
      ∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ fs : List V, SpineFit ρ ((d.Fss c ψ).getD j []) fs →
      SpineFit ρ (d.IdsM c ψ) (((d.Ess c ψ).getD j []).map (interp V (consList fs ρ))))
    -- the operator's MONOTONICITY, from positivity (lane HOLE2): given the
    -- fibre law and the slots' index fit (which make the fit the hole fit)
    (hmono : d.IdxFit → d.Fibre → ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (d.params ψ).reverse ρp → MonoTuple (d.w ψ) d.N (d.idx ψ ρp) (d.Φ ψ ρp)) :
    BlockModelAt mo names d := by
  have hlenParams : ∀ (ψ : Name → Nat) (c : Nat), c < d.N →
      (((d.ppsM c ψ).take d.nP).map (·.2.2)).length = d.nP := by
    intro ψ c hc
    rw [List.length_map, List.length_take, hlenPps ψ c hc]
    omega
  have hlenParamsD : ∀ ψ : Name → Nat, (d.params ψ).length = d.nP :=
    fun ψ => hlenParams ψ 0 hN0
  -- the parameter spine at ANY component's own telescope
  have hspP : ∀ (ψ : Name → Nat) (c : Nat), c < d.N → ∀ (ρ : Nat → V) (as : List V),
      SpineFit ρ (d.params ψ) as → SpineFit ρ (((d.ppsM c ψ).take d.nP).map (·.2.2)) as := by
    intro ψ c hc ρ as hsp
    exact (spineFit_iff_of_sat_iff (by rw [hlenParamsD, hlenParams ψ c hc]) (hparams ψ c hc) ρ as
      (by rw [hsp.length_eq, hlenParamsD])).mp hsp
  have hspPC : ∀ (ψ : Name → Nat) (c j : Nat), c < d.N → j < (d.ctorsM c).length →
      ∀ (ρ : Nat → V) (as : List V),
      SpineFit ρ (d.params ψ) as → SpineFit ρ (((d.dsF c j ψ).take d.nP).map (·.2.2)) as := by
    intro ψ c j hc hj ρ as hsp
    have hl : (((d.dsF c j ψ).take d.nP).map (·.2.2)).length = d.nP := by
      rw [List.length_map, List.length_take, hdsLen ψ c j hj]
      omega
    exact (spineFit_iff_of_sat_iff (by rw [hlenParamsD, hl]) (hparamsC ψ c j hc hj) ρ as
      (by rw [hsp.length_eq, hlenParamsD])).mp hsp
  have hfib : d.Fibre := by
    intro ψ ρp hρ X hX c hc t ht x
    rw [hPhi ψ ρp hρ X hX c hc]
    exact blockSlotFibre hinj hok hlenC htgts ψ ρp hρ X hX c hc t ht x
  have hidx : d.IdxFit := blockIdxFit_of_chains hok hlenC htgts
  refine ⟨hnames, ?_, ?_, ?_, ?_, ?_, ?_, hresFit, ?_, ?_⟩
  · -- idxOk
    intro ψ ρp hρ c hc
    exact (hok ψ ρp hρ).hI c hc
  · -- functor
    intro ψ ρp hρ
    have h := hok ψ ρp hρ
    refine ⟨hmono hidx hfib ψ ρp hρ, fun X hX m hm => ?_, ?_⟩
    · rw [hPhi ψ ρp hρ X hX m hm]; exact blockPhi_maps h X hX m hm
    · obtain ⟨L, hL⟩ := h.hclosed
      exact ⟨L, (isClosedTuple_congr (fun _ _ => rfl)
        (fun X hX m hm => (hPhi ψ ρp hρ X hX m hm).symm)).mp hL⟩
  · exact hfib
  · -- leaf
    intro mm hmm ψ ρ as is hsa hsi
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := d.satOfSpine hsa
    have h := hok ψ (consList as ρ) hsat
    have hlenI : is.length = (d.IdsM mm ψ).length := hsi.length_eq
    have hsp : SpineFit ρ ((d.ppsM mm ψ).map (·.2.2)) (as ++ is) := by
      have hsplit : (d.ppsM mm ψ).map (·.2.2)
          = ((d.ppsM mm ψ).take d.nP).map (·.2.2) ++ d.IdsM mm ψ := by
        show _ = _ ++ ((d.ppsM mm ψ).drop d.nP).map (·.2.2)
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      exact SpineFit.append
        (hspP ψ mm (Nat.lt_of_lt_of_le hmm (Nat.le_add_right _ _)) ρ as hsa) hsi
    have hsh : shiftE (d.IdsM mm ψ).length 0 (consList (as ++ is) ρ) = consList as ρ := by
      rw [consList_append, ← hlenI]
      have := shiftE_consList_add (V := V) is 0 (consList as ρ)
      rwa [shiftE_zero_zero] at this
    have hfr : ConLeche.Semantics.frameIdx (d.IdsM mm ψ).length (consList (as ++ is) ρ) = is :=
      ConLeche.Semantics.frameIdx_of (d.IdsM mm ψ).length hlenI ρ
    have hbase : BlockBaseI d.N (d.w ψ) (consList (as ++ is) ρ) (fun c => d.uM c ψ)
        (fun c => d.IdsM c ψ) d.rss d.tgtss (fun c => d.tlss c ψ) (fun c => d.Eiss c ψ)
        (fun c => d.Fss c ψ) (fun c => d.Ess c ψ) mm := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hsh]; exact h.hI
      · rw [hsh]; exact h.hok
      · rw [hsh, hfr]; exact hsi
    rw [hleaf mm hmm ψ,
      blockTyG_fold (show mm < d.N from Nat.lt_of_lt_of_le hmm (Nat.le_add_right _ _))
        hsp hbase, hsh, hfr]
    congr 1
    exact lfpTuple_congr (fun _ _ => rfl)
      (fun X hX m hm => (hPhi ψ (consList as ρ) hsat X hX m hm).symm)
      (Nat.lt_of_lt_of_le hmm (Nat.le_add_right _ _))
  · -- ctor
    intro c hc j cA hj ψ ρ as fs hsa hsf
    have hjl : j < (d.ctorsM c).length := (List.getElem?_eq_some_iff.mp hj).1
    have hsat : Sat V (d.params ψ).reverse (consList as ρ) := d.satOfSpine hsa
    rw [hctorLeaf c hc j cA hj ψ, hinj]
    by_cases hw : d.w ψ = 0
    · rw [if_pos hw, hw, sumMkAV_zero, foldl_app_pt]
    · rw [if_neg hw]
      have h2 : SpineFit (consList as ρ) (((d.dsF c j ψ).drop d.nP).map (·.2.2)) fs := by
        rw [← hFssD ψ c j hjl]; exact hsf
      have hjF : j < (d.Fss c ψ).length := by rw [hlenC]; exact hjl
      have h3 : (uChains (d.Fss c ψ))[j]?
          = some (((d.dsF c j ψ).drop d.nP).map (·.2.2) ++ [idxEqAV []]) := by
        rw [uChains_getElem?, List.getElem?_eq_getElem hjF]
        show some _ = some _
        rw [show (d.Fss c ψ)[j] = (d.Fss c ψ).getD j [] from by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjF, Option.getD_some],
          hFssD ψ c j hjl]
      have h4 := sumMkAV_fold (V := V) (w := d.w ψ) (j := j)
        (pds := (d.dsF c j ψ).take d.nP) (fds := (d.dsF c j ψ).drop d.nP)
        (Fss := uChains (d.Fss c ψ)) (ρ := ρ) (as := as) (bs := fs)
        hw (hspPC ψ c j hc hjl ρ as hsa) h2 (hFssOk ψ (consList as ρ) hsat c hc) h3
      rw [List.take_append_drop] at h4
      exact h4
  · exact hidx
  · -- mkZero
    intro ψ hw c j fs
    rw [hinj, if_pos hw]
  · -- mkInj
    intro ψ hw c hc j fs j' fs' hj hj' hlen hlen' heq
    rw [hinj, hinj, if_neg hw, if_neg hw] at heq
    obtain ⟨rfl, hT⟩ := inj_inj heq
    refine ⟨rfl, ?_⟩
    have hll : (fs ++ [pt]).length = (fs' ++ [pt]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [hlen, hlen']
    have := mkTower_inj hll hT
    exact List.append_cancel_right this

end ConLeche.Model
