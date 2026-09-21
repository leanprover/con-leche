module

public import ConLeche.Semantics.Tower.BlockLeafI
public import ConLeche.Semantics.Tower.FixFamI
public import ConLeche.SetModel.TupleContainer
@[expose] public section

/-!
# The block functor's laws (task #315, the uniform route at `k` members)

`BlockLeafI.lean` spells the block's operator and reads it; this module
proves what the least pre-fixed TUPLE needs of it — monotonicity, that
it preserves the tuple space, a closed tuple, the fixed-point equation,
and the identification of each member's fibre with the indexed sum
route's restricted tagged union.  It is `FixFamI.lean` at `k`, and the
generic halves of that file (the X-frame kit, the Π-tower and telescope
lemmas, the terminator, `SlotFit`/`slotSet`) are REUSED rather than
restated: they never mention the family slot's shape, only its value.

What is new at `k`:

* a recursive slot reads the TARGET's component of the family tuple
  (`slotXBI_interp`: `slotSet … (projS c Y)`), so monotonicity is
  componentwise (`MonoTuple`) and the slots' fit
  (`SlotsFitXB`) carries the target;
* the premise bundle `BlockChainsOk` is the k = 1 `XChainsOk` with the
  members quantified and the closed FAMILY replaced by a closed TUPLE;
* the fibre law `blockFam_app_eq_sum` is per member, with MEMBER-LOCAL
  constructor tags — member `m`'s sum runs over member `m`'s own
  constructors, `inj j` with `j` the member-local position.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The recursive slot at a family tuple -/

section Slot

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The recursive slot at the tuple frame** reads the target's
component: the k = 1 slot's value at `projS c Y`. -/
theorem slotXBI_interp {c : Nat} (hI : IdxOk (uf c) ρp (Idss c)) {Y : V}
    (as : List V) (t : V) {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hfit : SlotFit (uf c) w ρp (Idss c) tl Eis as) :
    interp V (consList as (cons t (cons Y ρp))) (slotXBI (uf c) (Idss c) c tl Eis as.length)
      = slotSet w (uf c) (consList as ρp) tl Eis (projS c Y) := by
  unfold slotXBI slotSet
  rw [← piTele_liftTele2 t Y tl as []]
  refine interp_mkPisAV_piTele (v := w) ?_ ?_
  · intro d hd
    unfold liftTele2 at hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    have hj' : j < tl.length := List.mem_range.mp hj
    have hmem : tl.getD j default ∈ tl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
      exact List.getElem_mem hj'
    show (tl.getD j default).2.1 = 0 ↔ w = 0
    exact hfit.2.1 _ hmem
  · intro bs hbs
    rw [(spineFit_liftTele2 t Y tl as bs)] at hbs
    have hlen : bs.length = tl.length := by
      have := hbs.length_eq; simpa using this
    obtain ⟨hEok, hsp⟩ := hfit.2.2 bs hbs
    have hval := (tuplerApp_facts (X := Y) (t := t) hI (as ++ bs) hEok hsp).1
    simp only [List.nil_append]
    rw [← consList_append, interp_app, projAV_interp, interp_bvar,
      show as.length + 1 + tl.length = (as ++ bs).length + 1 from by simp [hlen]; omega,
      show as.length + 2 + tl.length = (as ++ bs).length + 2 from by simp [hlen]; omega,
      show as.length + tl.length = (as ++ bs).length from by simp [hlen],
      Xframe_X, hval, consList_append]

/-- **The recursive slot at the tuple frame is graded**, and its value
lives in the block's universe: the projection into the family tuple is
graded by the tuple's own tower structure. -/
theorem slotXBI_wellDenoted (hIall : BlockIdxOk (V := V) k uf ρp Idss) {c : Nat} (hc : c < k)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) (as : List V) (t : V)
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    (hfit : SlotFit (uf c) w ρp (Idss c) tl Eis as) :
    WellDenoted V (consList as (cons t (cons Y ρp))) (slotXBI (uf c) (Idss c) c tl Eis as.length) ∧
    (w ≠ 0 → slotSet w (uf c) (consList as ρp) tl Eis (projS c Y) ∈ˢ (univ w : V)) := by
  have hI := hIall c hc
  have hproj : projS c Y ∈ˢ lfpFamSpace V w (idxSet (uf c) ρp (Idss c)) := by
    have := projS_mem_ndTowerSet V (blockR_ne_zero k w uf) k 0 hY c hc
    rwa [Nat.zero_add] at this
  have hFu : ∀ m, m < 0 + k → lfpFamSpace V w (idxSet (uf m) ρp (Idss m))
      ∈ˢ (univ (blockR k w uf) : V) := fun m hm =>
    famSpace_mem_blockR (by omega) (idxTyAV_facts (hIall m (by omega))).2.1
  have hprojok : ∀ (cs : List V) (t' : V),
      WellDenoted V (consList cs (cons t' (cons Y ρp))) (projAV c (.bvar (cs.length + 1))) :=
    fun cs t' => projAV_wellDenoted_ndTower V (blockR_ne_zero k w uf) c k 0
      (.bvar (cs.length + 1)) _ hc hFu trivial (by rw [interp_bvar, Xframe_X]; exact hY)
  constructor
  · unfold slotXBI
    refine WellDenoted_mkPisAV_of (w := w) (fieldsOkB_liftTele2 t Y tl as hfit.1) fun bs hsp => ?_
    have hsp' := (spineFit_liftTele2 t Y tl as bs).mp hsp
    have hlen : bs.length = tl.length := by rw [hsp'.length_eq, List.length_map]
    obtain ⟨hEok, hspE⟩ := hfit.2.2 bs hsp'
    have htok := (tuplerApp_facts (X := Y) (t := t) hI (as ++ bs) hEok hspE).2
    have htv := (tuplerApp_facts (X := Y) (t := t) hI (as ++ bs) hEok hspE).1
    rw [show as.length + 1 + tl.length = (as ++ bs).length + 1 from by simp [hlen]; omega,
      show as.length + 2 + tl.length = (as ++ bs).length + 2 from by simp [hlen]; omega,
      show as.length + tl.length = (as ++ bs).length from by simp [hlen], ← consList_append,
      WellDenoted_app]
    refine ⟨hprojok (as ++ bs) t, htok, w + 1, idxSet (uf c) ρp (Idss c),
      fun _ => (univ w : V), ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [projAV_interp, interp_bvar, Xframe_X]
      exact hproj
    · rw [htv]
      exact tupW_mem hspE
  · intro hw
    unfold slotSet
    refine piTele_mem_univ hw _ hfit.1 fun bs hsp => ?_
    simp only [List.nil_append]
    rw [← consList_append]
    obtain ⟨hEok, hspE⟩ := hfit.2.2 bs hsp
    exact app_mem_piR_pos (Nat.succ_ne_zero w) hproj (tupW_mem hspE)

end Slot

/-! ## The slots' fit and the functor's premise bundle -/

section Fit

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- The recursive slots' fit along one constructor's X-chain at a
family tuple `Y`: at each recursive position the field's TARGET is a
member of the block and the slot fits there (`SlotsFitX` at `k`). -/
def SlotsFitXB (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (rs : List Bool) (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) (Y t : V) :
    Nat → List V → List AnnotTerm → Prop
  | _, _, [] => True
  | i, as, F :: Fs =>
    (rs.getD i false = true → tgts.getD i 0 < k ∧
      SlotFit (uf (tgts.getD i 0)) w ρp (Idss (tgts.getD i 0))
        (tls.getD i []) (Eis.getD i []) as) ∧
    ∀ a, a ∈ˢ interp V (consList as (cons t (cons Y ρp))) (xEntryB uf Idss rs tgts tls Eis F i) →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t (i + 1) (as ++ [a]) Fs

/-- **The block functor's full premise** — `XChainsOk` at `k`: the
members' index telescopes graded, the X-chains graded at every family
tuple and index tuple, the recursive slots fitting there, and a closed
TUPLE.  Every clause quantifies over ALL tuples of the family space and
all parameter frames, not over the carrier (falsifier F0's finding: the
formation of an injection is derivable from the functor's laws only at
that generality). -/
structure BlockChainsOk (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (rsss : Nat → List (List Bool))
    (tgtsss : Nat → List (List Nat))
    (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
    (Eisss : Nat → List (List (List AnnotTerm))) (Fsss Esss : Nat → List (List AnnotTerm)) :
    Prop where
  hI : BlockIdxOk k uf ρp Idss
  hok : BlockChainsOkI k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss
  hfit : ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ m, m < k → ∀ t, t ∈ˢ idxSet (uf m) ρp (Idss m) →
    ∀ j, j < (Fsss m).length →
      SlotsFitXB k w ρp uf Idss ((rsss m).getD j []) ((tgtsss m).getD j [])
        ((tlsss m).getD j []) ((Eisss m).getD j []) Y t 0 [] ((Fsss m).getD j [])
  /-- the closure witness: a closed TUPLE.  At `w = 0` it is
  `blockPhi_closed_zero` below; at `w ≠ 0` it is the block's member
  container (`tupleContainer_closed_exists`), whose SHAPES must be
  tagged by (component, constructor) globally — falsifier F1's finding:
  the kit strips its own member tag before reading positions and
  targets off the shape, and the same constructor shape can occur at
  two components with different targets. -/
  hclosed : ∃ L, IsClosedTuple w k (blockIdx uf ρp Idss)
    (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) L

/-- A recursive entry reads the target's component of the tuple. -/
theorem xEntryB_rec {Y : V} {rs : List Bool} {tgts : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    (F : AnnotTerm) (as : List V) (t : V)
    (hI : IdxOk (uf (tgts.getD as.length 0)) ρp (Idss (tgts.getD as.length 0)))
    (hri : rs.getD as.length false = true)
    (hfit : SlotFit (uf (tgts.getD as.length 0)) w ρp (Idss (tgts.getD as.length 0))
      (tls.getD as.length []) (Eis.getD as.length []) as) :
    interp V (consList as (cons t (cons Y ρp))) (xEntryB uf Idss rs tgts tls Eis F as.length)
      = slotSet w (uf (tgts.getD as.length 0)) (consList as ρp) (tls.getD as.length [])
          (Eis.getD as.length []) (projS (tgts.getD as.length 0) Y) := by
  unfold xEntryB
  rw [if_pos hri]
  exact slotXBI_interp hI as t hfit

/-- An ordinary entry reads the domain. -/
theorem xEntryB_ord {Y : V} {rs : List Bool} {tgts : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    (F : AnnotTerm) (as : List V) (t : V) (hri : rs.getD as.length false = false) :
    interp V (consList as (cons t (cons Y ρp))) (xEntryB uf Idss rs tgts tls Eis F as.length)
      = interp V (consList as ρp) F := by
  unfold xEntryB
  rw [if_neg (by rw [hri]; exact Bool.false_ne_true)]
  exact interp_chainXI_ord F as t Y

end Fit

/-! ## Monotonicity -/

section Mono

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rs : List Bool} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Eis : List (List AnnotTerm)} {n nF : Nat} {Es : List AnnotTerm}

/-- **The X-chain telescope is monotone** in the family tuple,
componentwise at the targets. -/
theorem chainXBIGo_tele_sub (hIall : BlockIdxOk (V := V) k uf ρp Idss) {Y Z : V}
    (hYZ : ∀ c, c < k → FamLe (idxSet (uf c) ρp (Idss c)) (projS c Y) (projS c Z)) {t : V} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t i as Fs → as.length + Fs.length = nF →
      TeleS.Sub
        (teleOfFields (consList as (cons t (cons Y ρp)))
          (chainXBIGo uf Idss rs tgts tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
        (teleOfFields (consList as (cons t (cons Z ρp)))
          (chainXBIGo uf Idss rs tgts tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
  | [], i, as, hi, _, hnF => by
    simp only [chainXBIGo, List.nil_append, teleOfFields]
    rw [interp_termXI (X := Y) (Y := Z) (by simpa using hnF)]
    exact .cons (Subset.refl _) fun _ _ => .nil
  | F :: Fs, i, as, hi, hfit, hnF => by
    subst hi
    rw [chainXBIGo_cons, List.cons_append]
    simp only [teleOfFields]
    refine .cons ?_ fun a ha => ?_
    · by_cases hri : rs.getD as.length false = true
      · obtain ⟨hc, hsf⟩ := hfit.1 hri
        rw [xEntryB_rec (Y := Y) F as t (hIall _ hc) hri hsf,
          xEntryB_rec (Y := Z) F as t (hIall _ hc) hri hsf]
        exact slotSet_mono (hYZ _ hc) hsf
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntryB_ord F as t hri', xEntryB_ord F as t hri']
        exact Subset.refl _
    · rw [consList_snoc', consList_snoc']
      exact chainXBIGo_tele_sub hIall hYZ Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
        (hfit.2 a ha) (by simp at hnF ⊢; omega)

/-- The fit restricts along a smaller family tuple. -/
theorem slotsFitXB_mono (hIall : BlockIdxOk (V := V) k uf ρp Idss) {Y Z : V}
    (hZY : ∀ c, c < k → FamLe (idxSet (uf c) ρp (Idss c)) (projS c Z) (projS c Y)) {t : V} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t i as Fs →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Z t i as Fs
  | [], _, _, _, _ => trivial
  | F :: Fs, i, as, hi, hfit => by
    subst hi
    refine ⟨hfit.1, fun a ha => ?_⟩
    have ha' : a ∈ˢ interp V (consList as (cons t (cons Y ρp)))
        (xEntryB uf Idss rs tgts tls Eis F as.length) := by
      by_cases hri : rs.getD as.length false = true
      · obtain ⟨hc, hsf⟩ := hfit.1 hri
        rw [xEntryB_rec (Y := Z) F as t (hIall _ hc) hri hsf] at ha
        rw [xEntryB_rec (Y := Y) F as t (hIall _ hc) hri hsf]
        exact slotSet_mono (hZY _ hc) hsf a ha
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntryB_ord F as t hri'] at ha
        rw [xEntryB_ord F as t hri']
        exact ha
    exact slotsFitXB_mono hIall hZY Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
      (hfit.2 a ha')

end Mono

/-! ## The functor's laws -/

section Functor

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- A tuple of the tuple space, tupled up, is in the family space. -/
theorem ndMkTowerSet_mem_famsSpaceB {Xs : Nat → V}
    (hXs : InTupleSpace w k (blockIdx uf ρp Idss) Xs) :
    ndMkTowerSet Xs 0 k ∈ˢ famsSpaceB k w ρp uf Idss :=
  ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun c hc => by
    rw [lfpFamSpace_eq']
    exact hXs c (by omega)

theorem projS_ndMkTowerSet_zero {Xs : Nat → V} {c : Nat} (hc : c < k) :
    projS c (ndMkTowerSet Xs 0 k) = Xs c := by
  rw [projS_ndMkTowerSet k 0 c hc, Nat.zero_add]

theorem app_blockPhi {Xs : Nat → V} {m : Nat} {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    SetTheory.app (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss Xs m) t
      = blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m (ndMkTowerSet Xs 0 k) t :=
  app_lamR_pos (Nat.succ_ne_zero w) ht

/-- **The block's fibre is monotone** in the family tuple. -/
theorem blockStepV_mono (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    {Y Z : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss)
    (hYZ : ∀ c, c < k → FamLe (idxSet (uf c) ρp (Idss c)) (projS c Y) (projS c Z))
    {m : Nat} (hm : m < k) {t : V} (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m Y t
      ⊆ˢ blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m Z t := by
  unfold blockStepV
  refine sumSet_mono fun j => ?_
  unfold sumFibre
  by_cases hj : j < (Fsss m).length
  · rw [chainsXBI_getElem?, if_pos hj]
    show towerSet w (teleOfFields (cons t (cons Y ρp)) (chainXBI _ _ _ _ _ _ _ _ _))
      ⊆ˢ towerSet w (teleOfFields (cons t (cons Z ρp)) (chainXBI _ _ _ _ _ _ _ _ _))
    refine towerSet_mono ?_
    unfold chainXBI
    have := chainXBIGo_tele_sub (V := V) (k := k) (w := w) (n := (Idss m).length)
      (nF := ((Fsss m).getD j []).length) (Es := (Esss m).getD j []) (t := t)
      h.hI hYZ ((Fsss m).getD j []) 0 [] rfl (h.hfit Y hY m hm t ht j hj) (by simp)
    simpa only [consList_nil] using this
  · rw [chainsXBI_getElem?, if_neg hj]
    exact Subset.refl _

/-- **The block's operator is monotone on the tuple space.** -/
theorem blockPhi_mono (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    MonoTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) := by
  intro X Y hX _ hXY m hm t ht
  rw [app_blockPhi (uf := uf) (Idss := Idss) ht, app_blockPhi (uf := uf) (Idss := Idss) ht]
  refine blockStepV_mono h (ndMkTowerSet_mem_famsSpaceB hX) (fun c hc => ?_) hm ht
  rw [projS_ndMkTowerSet_zero hc, projS_ndMkTowerSet_zero hc]
  exact hXY c hc

/-- **The block's operator preserves the tuple space.** -/
theorem blockPhi_maps (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    MapsTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) := by
  intro X hX m hm
  show lamR (w + 1) (idxSet (uf m) ρp (Idss m)) _ ∈ˢ famSpace w (blockIdx uf ρp Idss m)
  rw [← lfpFamSpace_eq']
  exact lamR_mem fun t ht =>
    blockStepV_univ h.hok (ndMkTowerSet_mem_famsSpaceB hX) hm ht

/-- **At a `Prop`-valued block the top tuple is closed** — the `w = 0`
half of (W), with no container at all (`closedTuple_zero`). -/
theorem blockPhi_closed_zero (h : BlockChainsOk k 0 ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    ∃ L, IsClosedTuple 0 k (blockIdx uf ρp Idss)
      (blockPhi k 0 ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) L :=
  closedTuple_zero (blockPhi_maps h)

/-- The carrier is in the tuple space, with no premise (the least
pre-fixed tuple is total). -/
theorem blockFam_mem (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (rsss : Nat → List (List Bool)) (tgtsss : Nat → List (List Nat))
    (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
    (Eisss : Nat → List (List (List AnnotTerm))) (Fsss Esss : Nat → List (List AnnotTerm)) :
    InTupleSpace w k (blockIdx uf ρp Idss)
      (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :=
  lfpTuple_mem w k _ _

/-- **The fixed-point equation**, per member and fibrewise: member
`m`'s fibre at `t` is the functor's fibre at the carrier tuple. -/
theorem blockFam_app_eq (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    {m : Nat} (hm : m < k) {t : V} (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m
        (ndMkTowerSet (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) 0 k) t
      = SetTheory.app (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m) t := by
  have := app_lfpTuple_eq h.hclosed (blockPhi_mono h) (blockPhi_maps h) hm ht
  rwa [app_blockPhi (uf := uf) (Idss := Idss) ht] at this

end Functor

end ConLeche.Semantics
