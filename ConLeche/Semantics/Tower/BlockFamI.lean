module

public import ConLeche.Semantics.Tower.BlockLeafI
public import ConLeche.Semantics.Tower.FixFamI
import ConLeche.SetModel.TupleContainer
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

/-- **The target's component of a tuple of the family space** is a
family over the target's index tuples. -/
theorem projS_mem_famsSpaceB {c : Nat} (hc : c < k) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) :
    projS c Y ∈ˢ lfpFamSpace V w (idxSet (uf c) ρp (Idss c)) := by
  have := projS_mem_ndTowerSet V (blockR_ne_zero k w uf) k 0 hY c hc
  rwa [Nat.zero_add] at this

/-- **The projected family variable is graded** at the X-frame. -/
theorem projAV_X_wellDenoted (hIall : BlockIdxOk (V := V) k uf ρp Idss) {c : Nat} (hc : c < k)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) (cs : List V) (t' : V) :
    WellDenoted V (consList cs (cons t' (cons Y ρp))) (projAV c (.bvar (cs.length + 1))) := by
  have hFu : ∀ m, m < 0 + k → lfpFamSpace V w (idxSet (uf m) ρp (Idss m))
      ∈ˢ (univ (blockR k w uf) : V) := fun m hm =>
    famSpace_mem_blockR (by omega) (idxTyAV_facts (hIall m (by omega))).2.1
  exact projAV_wellDenoted_ndTower V (blockR_ne_zero k w uf) c k 0
    (.bvar (cs.length + 1)) _ hc hFu trivial (by rw [interp_bvar, Xframe_X]; exact hY)

/-- **The recursive call at the tuple frame** — `recSlot_facts` at `k`:
the application of the TARGET's component of the family variable to the
tupler at the index expressions has the expected value, is graded, and
lands in the block's universe. -/
theorem recSlotB_facts (hIall : BlockIdxOk (V := V) k uf ρp Idss) {c : Nat} (hc : c < k)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) (as : List V) (t : V) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V (consList as ρp) E)
    (hsp : SpineFit ρp (Idss c) (Es.map (interp V (consList as ρp)))) :
    interp V (consList as (cons t (cons Y ρp)))
        (.app (projAV c (.bvar (as.length + 1)))
          (AnnotTerm.mkAppN ((tuplerAV (uf c) (Idss c)).liftN (as.length + 2) 0)
            (Es.map (·.liftN 2 as.length))))
      = SetTheory.app (projS c Y) (tupW (uf c) (Es.map (interp V (consList as ρp)))) ∧
    WellDenoted V (consList as (cons t (cons Y ρp)))
      (.app (projAV c (.bvar (as.length + 1)))
        (AnnotTerm.mkAppN ((tuplerAV (uf c) (Idss c)).liftN (as.length + 2) 0)
          (Es.map (·.liftN 2 as.length)))) ∧
    SetTheory.app (projS c Y) (tupW (uf c) (Es.map (interp V (consList as ρp))))
      ∈ˢ (univ w : V) := by
  obtain ⟨htv, htok⟩ := tuplerApp_facts (X := Y) (t := t) (hIall c hc) as hEok hsp
  have hXm : projS c Y ∈ˢ piR (w + 1) (idxSet (uf c) ρp (Idss c)) fun _ => (univ w : V) :=
    projS_mem_famsSpaceB hc hY
  refine ⟨?_, ?_, ?_⟩
  · rw [interp_app, projAV_interp, interp_bvar, Xframe_X, htv]
  · rw [WellDenoted_app]
    refine ⟨projAV_X_wellDenoted hIall hc hY as t, htok, w + 1, idxSet (uf c) ρp (Idss c),
      fun _ => (univ w : V), ?_, ?_, fun h => absurd h (Nat.succ_ne_zero w)⟩
    · rw [projAV_interp, interp_bvar, Xframe_X]; exact hXm
    · rw [htv]; exact tupW_mem hsp
  · exact app_mem_piR_pos (Nat.succ_ne_zero w) hXm (tupW_mem hsp)

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
  have hproj : projS c Y ∈ˢ lfpFamSpace V w (idxSet (uf c) ρp (Idss c)) :=
    projS_mem_famsSpaceB hc hY
  have hprojok : ∀ (cs : List V) (t' : V),
      WellDenoted V (consList cs (cons t' (cons Y ρp))) (projAV c (.bvar (cs.length + 1))) :=
    fun cs t' => projAV_X_wellDenoted hIall hc hY cs t'
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
  `blockPhi_closed_zero_of` below; at `w ≠ 0` it is the block's member
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
theorem blockPhi_maps_of (hok : BlockChainsOkI k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    MapsTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) := by
  intro X hX m hm
  show lamR (w + 1) (idxSet (uf m) ρp (Idss m)) _ ∈ˢ famSpace w (blockIdx uf ρp Idss m)
  rw [← lfpFamSpace_eq']
  exact lamR_mem fun t ht =>
    blockStepV_univ hok (ndMkTowerSet_mem_famsSpaceB hX) hm ht

theorem blockPhi_maps (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    MapsTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :=
  blockPhi_maps_of h.hok

/-- **At a `Prop`-valued block the top tuple is closed** — the `w = 0`
half of (W), with no container at all (`closedTuple_zero`). -/
theorem blockPhi_closed_zero_of
    (hok : BlockChainsOkI k 0 ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    ∃ L, IsClosedTuple 0 k (blockIdx uf ρp Idss)
      (blockPhi k 0 ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) L :=
  closedTuple_zero (blockPhi_maps_of hok)

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

/-! ## The identification with the real chains — the per-member fibre law -/

section Real

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- `ChainRealBI μ … i as Fs₀ Fs`: constructor's real chain `Fs`
against the chain `Fs₀` the operator was spelled from, hereditarily at
the frame `(ρp, as)`.  At a recursive position the field's TARGET is a
member, the slot fits at the target, and the real domain reads to the
TARGET's carrier at the field's index tuples; at an ordinary position
the two are the same term. -/
def ChainRealBI (μ : Nat → V) (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (rs : List Bool) (tgts : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) :
    Nat → List V → List AnnotTerm → List AnnotTerm → Prop
  | _, _, [], [] => True
  | i, as, F₀ :: Fs₀, F :: Fs =>
    (if rs.getD i false then
      tgts.getD i 0 < k ∧
      SlotFit (uf (tgts.getD i 0)) w ρp (Idss (tgts.getD i 0))
        (tls.getD i []) (Eis.getD i []) as ∧
      interp V (consList as ρp) F
        = slotSet w (uf (tgts.getD i 0)) (consList as ρp) (tls.getD i [])
            (Eis.getD i []) (μ (tgts.getD i 0))
     else F = F₀) ∧
    ∀ a, a ∈ˢ interp V (consList as ρp) F →
      ChainRealBI μ k w ρp uf Idss rs tgts tls Eis (i + 1) (as ++ [a]) Fs₀ Fs
  | _, _, _, _ => False

/-- **The X-chain tower at the carrier tuple and a member's index
tuple is that member's real restricted tower** at the index spine. -/
theorem towerSet_chainXB_eq (hIall : BlockIdxOk (V := V) k uf ρp Idss) {m : Nat} (hm : m < k)
    {μ : Nat → V} {is : List V} (hsp : SpineFit ρp (Idss m) is)
    {rs : List Bool} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis : List (List AnnotTerm)} {nF : Nat} {Es : List AnnotTerm}
    (hEs : Es.length = (Idss m).length) :
    ∀ (Fs₀ Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i →
      ChainRealBI μ k w ρp uf Idss rs tgts tls Eis i as Fs₀ Fs → as.length + Fs.length = nF →
      towerSet w (teleOfFields
          (consList as (cons (tupW (uf m) is) (cons (ndMkTowerSet μ 0 k) ρp)))
          (chainXBIGo uf Idss rs tgts tls Eis Fs₀ i
            ++ [idxEqAV (eqsXI (Idss m).length nF Es)]))
        = towerSet w (teleOfFields (consList as (consList is ρp))
          (liftFields (Idss m).length i Fs
            ++ [idxEqAV (idxEqsAt (Idss m).length (Idss m).length nF Es)]))
  | [], [], i, as, hi, _, hnF => by
    simp only [chainXBIGo, liftFields_nil, List.nil_append, teleOfFields, towerSet]
    have hislen : is.length = (Idss m).length := hsp.length_eq
    have hlen : as.length = nF := by simpa using hnF
    have h1 : interp V (consList as (cons (tupW (uf m) is) (cons (ndMkTowerSet μ 0 k) ρp)))
        (idxEqAV (eqsXI (Idss m).length nF Es))
        = interp V (consList as (consList is ρp))
          (idxEqAV (idxEqsAt (Idss m).length (Idss m).length nF Es)) := by
      rw [idxEqAV_interp, idxEqAV_interp]
      congr 1
      exact propext ((EqAll_eqsXI (hIall m hm) hsp hlen).trans
        (EqAll_idxEqsAt' hislen hlen hEs).symm)
    rw [h1]
  | [], _ :: _, _, _, _, hc, _ => hc.elim
  | _ :: _, [], _, _, _, hc, _ => hc.elim
  | F₀ :: Fs₀, F :: Fs, i, as, hi, hc, hnF => by
    subst hi
    have hislen : is.length = (Idss m).length := hsp.length_eq
    rw [chainXBIGo_cons, liftFields_cons, List.cons_append, List.cons_append]
    simp only [teleOfFields, towerSet]
    obtain ⟨hhead, htail⟩ := hc
    have hA : interp V (consList as (cons (tupW (uf m) is) (cons (ndMkTowerSet μ 0 k) ρp)))
        (xEntryB uf Idss rs tgts tls Eis F₀ as.length)
        = interp V (consList as (consList is ρp)) (F.liftN (Idss m).length as.length) := by
      rw [interp_liftIdx F as is hislen]
      by_cases hri : rs.getD as.length false = true
      · rw [if_pos hri] at hhead
        obtain ⟨hct, hf, heq⟩ := hhead
        rw [xEntryB_rec (Y := ndMkTowerSet μ 0 k) F₀ as (tupW (uf m) is) (hIall _ hct) hri hf,
          projS_ndMkTowerSet_zero hct, heq]
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [if_neg (by rw [hri']; exact Bool.false_ne_true)] at hhead
        rw [xEntryB_ord F₀ as (tupW (uf m) is) hri', hhead]
    rw [hA]
    refine sigmaSet_congr' fun a ha => ?_
    rw [consList_snoc', consList_snoc']
    refine towerSet_chainXB_eq hIall hm hsp hEs Fs₀ Fs (as.length + 1) (as ++ [a])
      (length_snoc' a as) (htail a ?_) (by simp at hnF ⊢; omega)
    rwa [interp_liftIdx F as is hislen] at ha

/-- `ChainsRealBI`: `ChainRealBI` for every constructor of member `m`,
at the carrier tuple. -/
def ChainsRealBI (μ : Nat → V) (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (m : Nat) (rss : List (List Bool)) (tgtss : List (List Nat))
    (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (Fss₀ Fss Ess : List (List AnnotTerm)) : Prop :=
  Fss₀.length = Fss.length ∧ Ess.length = Fss.length ∧
  (∀ j, j < Fss.length → (Ess.getD j []).length = (Idss m).length) ∧
  (∀ j, j < Fss.length → (Fss₀.getD j []).length = (Fss.getD j []).length) ∧
  ∀ j, j < Fss.length →
    ChainRealBI μ k w ρp uf Idss (rss.getD j []) (tgtss.getD j []) (tlss.getD j [])
      (Eiss.getD j []) 0 [] (Fss₀.getD j []) (Fss.getD j [])

variable {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **THE PER-MEMBER FIBRE LAW**: member `m`'s fibre at an index spine
is the indexed sum route's restricted tagged union of member `m`'s OWN
constructors — the tag `j` is MEMBER-LOCAL, `inj j` with `j` member
`m`'s own constructor position. -/
theorem blockFam_app_eq_sum (h : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    {m : Nat} (hm : m < k) {Fss' : List (List AnnotTerm)}
    (hreal : ChainsRealBI (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
      k w ρp uf Idss m (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) Fss' (Esss m))
    {is : List V} (hsp : SpineFit ρp (Idss m) is) :
    SetTheory.app (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m)
        (tupW (uf m) is)
      = sumSet w (sumFibre w (consList is ρp)
          (rChains (Idss m).length (Idss m).length Fss' (Esss m))) := by
  rw [← blockFam_app_eq h hm (tupW_mem hsp)]
  unfold blockStepV
  refine sumSet_congr fun j => ?_
  obtain ⟨hl₀, hlE, hEs, hlen, hc⟩ := hreal
  unfold sumFibre
  by_cases hj : j < Fss'.length
  · have hjF : j < (Fsss m).length := by omega
    rw [chainsXBI_getElem?, if_pos hjF, rChains_getElem?, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem (by omega)]
    show towerSet w (teleOfFields (cons (tupW (uf m) is) (cons _ ρp))
        (chainXBI _ _ _ _ _ _ _ _ _))
      = towerSet w (teleOfFields (consList is ρp)
          (rChain (Idss m).length (Idss m).length Fss'[j] (Esss m)[j]))
    unfold chainXBI rChain
    have hg1 : Fss'[j] = Fss'.getD j [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hg2 : (Esss m)[j] = (Esss m).getD j [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [hg1, hg2]
    have := towerSet_chainXB_eq (w := w) (nF := ((Fsss m).getD j []).length)
      h.hI hm hsp (hEs j hj) ((Fsss m).getD j []) (Fss'.getD j []) 0 [] rfl (hc j hj)
      (by simp only [List.length_nil, Nat.zero_add]; exact (hlen j hj).symm)
    rw [← hlen j hj]
    simpa only [consList_nil] using this
  · have hjF : ¬ j < (Fsss m).length := by omega
    rw [chainsXBI_getElem?, if_neg hjF, rChains_getElem?, List.getElem?_eq_none (by omega)]

end Real

/-! ## Elimination at a stage, and (W) at `w ≠ 0` -/

section Elim

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **Stage elimination** (graph regime): a member of the operator's
fibre at `(Y, t)` is the injection of a point-terminated tuple fitting
one of MEMBER `m`'s OWN constructors' X-chains — the tag is
member-local — with the index equation holding. -/
theorem blockStepV_elim (hw : w ≠ 0) {m : Nat} {Y t x : V}
    (hx : x ∈ˢ blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m Y t) :
    ∃ j fs, x = inj j (mkTower (fs ++ [pt])) ∧ j < (Fsss m).length ∧
      fs.length = ((Fsss m).getD j []).length ∧
      SpineFit (cons t (cons Y ρp))
        (chainXBIGo uf Idss ((rsss m).getD j []) ((tgtsss m).getD j []) ((tlsss m).getD j [])
          ((Eisss m).getD j []) ((Fsss m).getD j []) 0) fs ∧
      EqAll (consList fs (cons t (cons Y ρp)))
        (eqsXI (Idss m).length ((Fsss m).getD j []).length ((Esss m).getD j [])) := by
  unfold blockStepV at hx
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
  unfold sumFibre at ha
  by_cases hj : j < (Fsss m).length
  · rw [chainsXBI_getElem?, if_pos hj] at ha
    obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
    unfold chainXBI at hfit heta
    obtain ⟨fs, hfs, hsp, hall⟩ := spineFit_append_idxEq.mp hfit
    have hlen : fs.length = ((Fsss m).getD j []).length := by
      have := hsp.length_eq
      rwa [chainXBIGo_length] at this
    refine ⟨j, fs, ?_, hj, hlen, hsp, hall⟩
    rw [heta, hfs]
  · rw [chainsXBI_getElem?, if_neg hj] at ha
    exact absurd ha (not_mem_empty _)

/-- **Stage elimination** (squash regime). -/
theorem blockStepV_zero_elim {m : Nat} {Y t x : V}
    (hx : x ∈ˢ blockStepV 0 ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m Y t) :
    x = pt ∧ ∃ j fs, j < (Fsss m).length ∧ fs.length = ((Fsss m).getD j []).length ∧
      SpineFit (cons t (cons Y ρp))
        (chainXBIGo uf Idss ((rsss m).getD j []) ((tgtsss m).getD j []) ((tlsss m).getD j [])
          ((Eisss m).getD j []) ((Fsss m).getD j []) 0) fs ∧
      EqAll (consList fs (cons t (cons Y ρp)))
        (eqsXI (Idss m).length ((Fsss m).getD j []).length ((Esss m).getD j [])) := by
  unfold blockStepV at hx
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
  refine ⟨rfl, ?_⟩
  unfold sumFibre at ha
  by_cases hj : j < (Fsss m).length
  · rw [chainsXBI_getElem?, if_pos hj] at ha
    obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
    have hfit' := fitsS_teleOfFields.mp hfit
    unfold chainXBI at hfit'
    obtain ⟨fs, -, hsp, hall⟩ := spineFit_append_idxEq.mp hfit'
    have hlen : fs.length = ((Fsss m).getD j []).length := by
      have := hsp.length_eq
      rwa [chainXBIGo_length] at this
    exact ⟨j, fs, hj, hlen, hsp, hall⟩
  · rw [chainsXBI_getElem?, if_neg hj] at ha
    exact absurd ha (not_mem_empty _)

/-- The recursive components of a tuple fitting the X-chain at a family
tuple lie in the slot's value at the field's TARGET component. -/
theorem fitsXBI_slot_mem (hIall : BlockIdxOk (V := V) k uf ρp Idss) {Y t : V} {rs : List Bool}
    {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis : List (List AnnotTerm)} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t i as Fs →
      SpineFit (consList as (cons t (cons Y ρp))) (chainXBIGo uf Idss rs tgts tls Eis Fs i) bs →
      ∀ l, l < bs.length → rs.getD (i + l) false = true →
        tgts.getD (i + l) 0 < k ∧
        SlotFit (uf (tgts.getD (i + l) 0)) w ρp (Idss (tgts.getD (i + l) 0))
          (tls.getD (i + l) []) (Eis.getD (i + l) []) (as ++ bs.take l) ∧
        bs.getD l pt ∈ˢ slotSet w (uf (tgts.getD (i + l) 0)) (consList (as ++ bs.take l) ρp)
          (tls.getD (i + l) []) (Eis.getD (i + l) []) (projS (tgts.getD (i + l) 0) Y)
  | [], _, _, [], _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, h, _, _, _ => h.elim
  | _ :: _, _, _, [], _, _, h, _, _, _ => h.elim
  | F :: Fs, i, as, b :: bs, hi, hfit, h, l, hl, hr => by
    subst hi
    rw [chainXBIGo_cons] at h
    obtain ⟨hb, hrest⟩ := h
    cases l with
    | zero =>
      rw [Nat.add_zero] at hr ⊢
      obtain ⟨hct, hsf⟩ := hfit.1 hr
      rw [xEntryB_rec (Y := Y) F as t (hIall _ hct) hr hsf] at hb
      simpa using ⟨hct, hsf, hb⟩
    | succ l =>
      rw [consList_snoc'] at hrest
      have := fitsXBI_slot_mem hIall Fs (as.length + 1) (as ++ [b]) bs (length_snoc' b as)
        (hfit.2 b hb) hrest l (by simpa using hl)
        (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
      rw [show as.length + 1 + l = as.length + (l + 1) from by omega] at this
      simpa [List.append_assoc] using this

end Elim

/-! ## (W) at `w ≠ 0`: the block as a member container -/

section Witness

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **(W) at a block, graph regime**: `tupleContainer_closed_exists`
at the block's operator, with the elimination stated at the SPELLED
fibre.

**The shapes must be tagged by (component, constructor) globally.**
The kit strips its own member tag before reading positions (`B a`) and
targets (`tgtM a p`, `tgtI a p`) off the shape, so a shape that is only
the constructor's shadow tuple does not determine them: falsifier F1
has `List.cons` occurring at two components with different targets.
`A m i`'s members must therefore carry `m` and the constructor's
member-local index themselves.

Note also that `helim` quantifies over ALL tuples of the tuple space
and the whole parameter frame is free — narrowing either to the carrier
breaks falsifier F0. -/
theorem blockPhi_closed_container (hw : w ≠ 0)
    (A : Nat → V → V) (B : V → V) (tgtM : V → V → Nat) (tgtI : V → V → V)
    (mk : Nat → V → V → V)
    (hA : ∀ m, m < k → ∀ i, i ∈ˢ idxSet (uf m) ρp (Idss m) → A m i ∈ˢ (univ w : V))
    (hB : ∀ m, m < k → ∀ i a, i ∈ˢ idxSet (uf m) ρp (Idss m) → a ∈ˢ A m i →
      B a ∈ˢ (univ w : V))
    (htgt : ∀ m, m < k → ∀ i a p, i ∈ˢ idxSet (uf m) ρp (Idss m) → a ∈ˢ A m i → p ∈ˢ B a →
      tgtM a p < k ∧ tgtI a p ∈ˢ idxSet (uf (tgtM a p)) ρp (Idss (tgtM a p)))
    (hmkU : ∀ m, m < k → ∀ i a g, i ∈ˢ idxSet (uf m) ρp (Idss m) → a ∈ˢ A m i →
      g ∈ˢ (univ w : V) → mk m a g ∈ˢ (univ w : V))
    (helim : ∀ Xs, InTupleSpace w k (blockIdx uf ρp Idss) Xs → ∀ m, m < k →
      ∀ i, i ∈ˢ idxSet (uf m) ρp (Idss m) →
      ∀ x, x ∈ˢ blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m
          (ndMkTowerSet Xs 0 k) i →
        ∃ a, a ∈ˢ A m i ∧ ∃ g, g ∈ˢ piSet (B a) (fun p => SetTheory.app (Xs (tgtM a p)) (tgtI a p)) ∧
          x = mk m a g) :
    ∃ L, IsClosedTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) L :=
  tupleContainer_closed_exists hw _ A B tgtM tgtI mk hA hB htgt hmkU
    fun Xs hXs m hm i hi x hx => by
      rw [app_blockPhi (uf := uf) (Idss := Idss) hi] at hx
      exact helim Xs hXs m hm i hi x hx

end Witness

end ConLeche.Semantics
