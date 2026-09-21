module

public import ConLeche.Semantics.Tower.BlockLeafI
import ConLeche.Semantics.Tower.FixFamI
import ConLeche.Semantics.Tower.FixTuple
import ConLeche.SetTheory.Derive.LfpCompose
@[expose] public section

/-!
# THE FALSIFIER: at `k = 1` the block model IS the one-member route

The uniform route's leaf (`BlockLeafI.lean`) spells a block of `k`
members; the ONE fixpoint route's leaf (`FixLeafI.lean`) spells a
single family.  At `k = 1` they must read to the same set — otherwise
the Model tier's port could not cross one lemma at a time, and the
route would be a second checker rather than a generalisation of the
first.  This module proves it, at the leaf:

    ⟦blockTyAV 1 w uf Idss … pps 0⟧ = ⟦nativeTyAVI (uf 0) w pps (Idss 0) …⟧

The two terms are NOT equal: the block's recursive slot reads the
family through `proj_0` of a ONE-component tuple where the one-member
route reads the family variable directly, and the block's carrier is
`proj_0` of a one-component tuple lfp where the one-member route's is
`lfpFamSet`.  What is equal is what they DENOTE, and the equality has
exactly the three pieces the design predicted:

* `projS 0 (mkTower [x]) = x` — the tuple's one component, at the term
  level (`projAV 0` on the leaf) and inside every recursive slot;
* `lfpTuple_one` (`SetTheory/Derive/LfpTuple.lean`), which needs no
  hypothesis: a single family IS the one-member tuple;
* `lfpTuple_congr` (`SetTheory/Derive/LfpCompose.lean`), because the
  two operators are DIFFERENT functions that agree only on the tuple
  space — `oneTuple fixFunVI` computes by `app`, the block's `blockPhi`
  by the spelled arms.

The one hypothesis is syntactic and is what a one-member block's parts
always satisfy: every recursive field targets member `0`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## Two Π-towers over the same binder data, at two frames -/

/-- The two frames agree on the tower's domains and, under every
binder, on its body. -/
def PiTowerAgree (R R' : AnnotTerm) :
    List (Nat × Nat × AnnotTerm) → (Nat → V) → (Nat → V) → Prop
  | [], σ, σ' => interp V σ R = interp V σ' R'
  | d :: ds, σ, σ' =>
    interp V σ d.2.2 = interp V σ' d.2.2 ∧
      ∀ x, PiTowerAgree R R' ds (cons x σ) (cons x σ')

theorem interp_mkPisAV_of_agree {R R' : AnnotTerm} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (σ σ' : Nat → V),
      PiTowerAgree R R' ds σ σ' →
      interp V σ (mkPisAV ds R) = interp V σ' (mkPisAV ds R')
  | [], _, _, h => h
  | d :: ds, σ, σ', h => by
    show piR d.2.1 (interp V σ d.2.2) (fun x => interp V (cons x σ) (mkPisAV ds R))
      = piR d.2.1 (interp V σ' d.2.2) (fun x => interp V (cons x σ') (mkPisAV ds R'))
    rw [h.1]
    exact piR_congr fun x _ => interp_mkPisAV_of_agree ds (cons x σ) (cons x σ') (h.2 x)

/-! ## The slot and the chain at `k = 1` -/

section One

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- Two application folds along lists of terms that read equally, from
equal heads, agree. -/
theorem foldl_app_agree {f f' : V} (hf : f = f') :
    ∀ (L : List AnnotTerm) (σ σ' : Nat → V),
      (∀ E ∈ L, interp V σ E = interp V σ' E) →
      L.foldl (fun r a => SetTheory.app r (interp V σ a)) f
        = L.foldl (fun r a => SetTheory.app r (interp V σ' a)) f'
  | [], _, _, _ => hf
  | E :: L, σ, σ', h => by
    refine foldl_app_agree ?_ L σ σ' fun E' hE' => h E' (List.mem_cons_of_mem _ hE')
    show SetTheory.app f (interp V σ E) = SetTheory.app f' (interp V σ' E)
    rw [hf, h E List.mem_cons_self]

/-- The lifted field telescope reads the same at two frames that
differ only in the family slot. -/
theorem liftTele2_agree {R R' : AnnotTerm} (ρp : Nat → V) (t Y X : V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      (∀ bs : List V, bs.length = tl.length →
        interp V (consList (as ++ bs) (cons t (cons Y ρp))) R
          = interp V (consList (as ++ bs) (cons t (cons X ρp))) R') →
      PiTowerAgree R R' (liftTele2 as.length tl)
        (consList as (cons t (cons Y ρp))) (consList as (cons t (cons X ρp)))
  | [], as, h => by
    have := h [] rfl
    simpa [liftTele2, PiTowerAgree] using this
  | d :: tl, as, h => by
    rw [liftTele2_cons]
    refine ⟨?_, fun x => ?_⟩
    · show interp V (consList as (cons t (cons Y ρp))) (d.2.2.liftN 2 as.length)
        = interp V (consList as (cons t (cons X ρp))) (d.2.2.liftN 2 as.length)
      rw [interp_chainXI_ord, interp_chainXI_ord]
    · rw [consList_snoc', consList_snoc']
      have hrec := liftTele2_agree (R := R) (R' := R') ρp t Y X tl (as ++ [x])
        (fun bs hbs => by
          have := h (x :: bs) (by simpa using hbs)
          simpa [List.append_assoc] using this)
      rw [length_snoc'] at hrec
      exact hrec

/-- **The block's recursive slot at `k = 1` reads the one-member
route's**: the family tuple's one component is the family. -/
theorem slotXBI_interp_one {t Y X : V} (hY : projS 0 Y = X)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) (as : List V) :
    interp V (consList as (cons t (cons Y ρp)))
        (slotXBI (uf 0) (Idss 0) 0 tl Eis as.length)
      = interp V (consList as (cons t (cons X ρp)))
        (slotXI (uf 0) (Idss 0) tl Eis as.length) := by
  unfold slotXBI slotXI
  refine interp_mkPisAV_of_agree _ _ _
    (liftTele2_agree
      (R := .app (projAV 0 (.bvar (as.length + 1 + tl.length)))
        (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
          (Eis.map (·.liftN 2 (as.length + tl.length)))))
      (R' := .app (.bvar (as.length + 1 + tl.length))
        (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
          (Eis.map (·.liftN 2 (as.length + tl.length)))))
      ρp t Y X tl as fun bs hbs => ?_)
  have hlen : (as ++ bs).length = as.length + tl.length := by simp [hbs]
  have hhead : interp V (consList (as ++ bs) (cons t (cons Y ρp)))
      (projAV 0 (.bvar (as.length + 1 + tl.length))) = X := by
    rw [projAV_interp, interp_bvar,
      show as.length + 1 + tl.length = (as ++ bs).length + 1 from by omega, Xframe_X, hY]
  have hhead' : interp V (consList (as ++ bs) (cons t (cons X ρp)))
      (.bvar (as.length + 1 + tl.length)) = X := by
    rw [interp_bvar, show as.length + 1 + tl.length = (as ++ bs).length + 1 from by omega,
      Xframe_X]
  have hargs : interp V (consList (as ++ bs) (cons t (cons Y ρp)))
      (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
        (Eis.map (·.liftN 2 (as.length + tl.length))))
      = interp V (consList (as ++ bs) (cons t (cons X ρp)))
        (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
          (Eis.map (·.liftN 2 (as.length + tl.length)))) := by
    rw [interp_mkAppN, interp_mkAppN,
      show as.length + 2 + tl.length = (as ++ bs).length + 2 from by omega,
      show as.length + tl.length = (as ++ bs).length from by omega]
    have hf : interp V (consList (as ++ bs) (cons t (cons Y ρp)))
        ((tuplerAV (uf 0) (Idss 0)).liftN ((as ++ bs).length + 2) 0)
        = interp V (consList (as ++ bs) (cons t (cons X ρp)))
          ((tuplerAV (uf 0) (Idss 0)).liftN ((as ++ bs).length + 2) 0) := by
      rw [interp_liftN, interp_liftN, shiftE_Xframe, shiftE_Xframe]
    have hE : ∀ E ∈ Eis.map (·.liftN 2 (as ++ bs).length),
        interp V (consList (as ++ bs) (cons t (cons Y ρp))) E
          = interp V (consList (as ++ bs) (cons t (cons X ρp))) E := by
      intro E hE
      obtain ⟨E', -, rfl⟩ := List.mem_map.mp hE
      rw [interp_chainXI_ord, interp_chainXI_ord]
    exact foldl_app_agree hf _ _ _ hE
  show interp V (consList (as ++ bs) (cons t (cons Y ρp)))
      (.app (projAV 0 (.bvar (as.length + 1 + tl.length))) _)
    = interp V (consList (as ++ bs) (cons t (cons X ρp)))
      (.app (.bvar (as.length + 1 + tl.length)) _)
  rw [interp_app, interp_app, hhead, hhead', hargs]

end One

/-! ## The chain, the step and the carrier at `k = 1` -/

omit [SetTheory V] in
theorem chainXBIGo_cons (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) (F : AnnotTerm) (Fs : List AnnotTerm) (i : Nat) :
    chainXBIGo uf Idss rs tgts tls Eis (F :: Fs) i
      = (if rs.getD i false then
          slotXBI (uf (tgts.getD i 0)) (Idss (tgts.getD i 0)) (tgts.getD i 0)
            (tls.getD i []) (Eis.getD i []) i
         else F.liftN 2 i) :: chainXBIGo uf Idss rs tgts tls Eis Fs (i + 1) := rfl

section Chain

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rs : List Bool} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Eis : List (List AnnotTerm)} {n nF : Nat} {Es : List AnnotTerm}

/-- **The block's X-chain at `k = 1` builds the one-member route's
tower**, at the family tuple and its one component. -/
theorem towerSet_chainXB_one (htg : ∀ i, tgts.getD i 0 = 0) {t Y X : V} (hY : projS 0 Y = X) :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i → as.length + Fs.length = nF →
      towerSet w (teleOfFields (consList as (cons t (cons Y ρp)))
          (chainXBIGo uf Idss rs tgts tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
        = towerSet w (teleOfFields (consList as (cons t (cons X ρp)))
          (chainXIGo (uf 0) (Idss 0) rs tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
  | [], _, as, _, hnF => by
    simp only [chainXBIGo, chainXIGo, List.nil_append, teleOfFields, towerSet]
    rw [interp_termXI (X := Y) (Y := X) (by simpa using hnF)]
  | F :: Fs, i, as, hi, hnF => by
    subst hi
    rw [chainXBIGo_cons, chainXIGo_cons, List.cons_append, List.cons_append]
    simp only [teleOfFields, towerSet]
    have hhead : interp V (consList as (cons t (cons Y ρp)))
        (if rs.getD as.length false then
          slotXBI (uf (tgts.getD as.length 0)) (Idss (tgts.getD as.length 0))
            (tgts.getD as.length 0) (tls.getD as.length []) (Eis.getD as.length []) as.length
         else F.liftN 2 as.length)
        = interp V (consList as (cons t (cons X ρp)))
          (xEntry (uf 0) (Idss 0) rs tls Eis F as.length) := by
      unfold xEntry
      by_cases hri : rs.getD as.length false = true
      · rw [if_pos hri, if_pos hri, htg as.length]
        exact slotXBI_interp_one hY _ _ as
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [if_neg (by rw [hri']; exact Bool.false_ne_true),
          if_neg (by rw [hri']; exact Bool.false_ne_true),
          interp_chainXI_ord, interp_chainXI_ord]
    rw [hhead]
    refine sigmaSet_congr' fun a _ => ?_
    rw [consList_snoc', consList_snoc']
    exact towerSet_chainXB_one htg hY Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
      (by simp at hnF ⊢; omega)

end Chain

section Step

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **The block's fibre at `k = 1` is the one-member route's.** -/
theorem blockStepV_one (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0) {t Y X : V}
    (hY : projS 0 Y = X) :
    blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss 0 Y t
      = fixStepI (uf 0) w ρp (Idss 0) (Idss 0).length (rsss 0) (tlsss 0) (Eisss 0)
          (Fsss 0) (Esss 0) X t := by
  unfold blockStepV fixStepI
  refine sumSet_congr fun j => ?_
  unfold sumFibre
  by_cases hj : j < (Fsss 0).length
  · rw [chainsXBI_getElem?, if_pos hj, chainsXI_getElem?, if_pos hj]
    show towerSet w (teleOfFields (cons t (cons Y ρp)) (chainXBI _ _ _ _ _ _ _ _ _))
      = towerSet w (teleOfFields (cons t (cons X ρp)) (chainXI _ _ _ _ _ _ _ _))
    unfold chainXBI chainXI
    have := towerSet_chainXB_one (w := w) (ρp := ρp) (uf := uf) (Idss := Idss)
      (rs := (rsss 0).getD j []) (tgts := (tgtsss 0).getD j [])
      (tls := (tlsss 0).getD j []) (Eis := (Eisss 0).getD j [])
      (n := (Idss 0).length) (nF := ((Fsss 0).getD j []).length) (Es := (Esss 0).getD j [])
      (t := t) (Y := Y) (X := X)
      (fun i => htg j i) hY ((Fsss 0).getD j []) 0 [] rfl (by simp)
    simpa only [consList_nil] using this
  · rw [chainsXBI_getElem?, if_neg hj, chainsXI_getElem?, if_neg hj]

/-- **The block's carrier at `k = 1` is the one-member route's.** -/
theorem blockFam_one (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0) :
    blockFam 1 w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss 0
      = fixFamI (uf 0) w ρp (Idss 0) (Idss 0).length (rsss 0) (tlsss 0) (Eisss 0)
          (Fsss 0) (Esss 0) := by
  rw [fixFamI_eq_lfpTuple]
  unfold blockFam
  refine lfpTuple_congr (fun m hm => ?_) (fun Xs hXs m hm => ?_) Nat.zero_lt_one
  · obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    rfl
  · obtain rfl : m = 0 := Nat.lt_one_iff.mp hm
    have hX0 : Xs 0 ∈ˢ lfpFamSpace V w (idxSet (uf 0) ρp (Idss 0)) := by
      rw [lfpFamSpace_eq']
      exact hXs 0 Nat.zero_lt_one
    show lamR (w + 1) (idxSet (uf 0) ρp (Idss 0)) _ = _
    rw [oneTuple, fixFunVI_app hX0]
    unfold famFI
    refine lamR_congr fun t _ => ?_
    exact blockStepV_one htg (projS_ndMkTowerSet 1 0 0 Nat.zero_lt_one)

end Step

/-! ## The leaf -/

section Leaf

variable {w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **THE FALSIFIER AT THE LEAF**: at `k = 1` the block route's
type-former leaf and the one-member route's read to the SAME set.

The premises are the two leaves' own (`ParamsOkXBI` and `ParamsOkXI`);
at `k = 1` they say the same thing about the same data, but the
implication between them is a `WellDenoted` frame-congruence over the
chain rather than an equality of readings, and it is not needed for
this statement.  The carrier-level falsifier `blockFam_one` — the
mathematical content — carries NO premise beyond `htg`. -/
theorem blockTyAV_one (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0) :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkXBI 1 w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss 0 pps →
      ParamsOkXI (uf 0) w ρ (Idss 0) (rsss 0) (tlsss 0) (Eisss 0) (Fsss 0) (Esss 0) pps →
      interp V ρ (blockTyAV 1 w uf Idss rsss tgtsss tlsss Eisss Fsss Esss pps 0)
        = interp V ρ (nativeTyAVI (uf 0) w pps (Idss 0) (rsss 0) (tlsss 0) (Eisss 0)
            (Fsss 0) (Esss 0))
  | [], ρ, hb, hf => by
    show interp V ρ (.app (projAV 0 ((blockBodyAV 1 w uf Idss rsss tgtsss tlsss Eisss Fsss
        Esss).liftN (Idss 0).length 0)) (mkTowerGo (uf 0) (Idss 0)))
      = interp V ρ (.app ((fixBodyAVI (uf 0) w (Idss 0) (Idss 0).length (rsss 0) (tlsss 0)
          (Eisss 0) (Fsss 0) (Esss 0)).liftN (Idss 0).length 0) (mkTowerGo (uf 0) (Idss 0)))
    rw [(blockLeafBody_facts Nat.zero_lt_one hb).1, (fixLeafBody_facts hf).1, blockFam_one htg]
  | d :: pps, ρ, hb, hf => by
    show lamR (w + 1) (interp V ρ d.2.2)
        (fun a => interp V (cons a ρ) (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
      = lamR (w + 1) (interp V ρ d.2.2)
        (fun a => interp V (cons a ρ) (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
    exact lamR_congr fun a ha => blockTyAV_one htg (hb.2.2 a ha) (hf.2.2 a ha)

end Leaf

end ConLeche.Semantics
