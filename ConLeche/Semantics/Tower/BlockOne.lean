module

public import ConLeche.Semantics.Tower.BlockLeafI
public import ConLeche.Semantics.Tower.FixFamI
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
        (xEntryB uf Idss rs tgts tls Eis F as.length)
        = interp V (consList as (cons t (cons X ρp)))
          (xEntry (uf 0) (Idss 0) rs tls Eis F as.length) := by
      unfold xEntry xEntryB
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

/-- The leaf identity under BOTH leaves' premises; `blockTyAV_one`
below drops the second. -/
theorem blockTyAV_one_of (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0) :
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
    exact lamR_congr fun a ha => blockTyAV_one_of htg (hb.2.2 a ha) (hf.2.2 a ha)

end Leaf

/-! ## `BlockChainsOkI` implies the one-member route's premise

The readings agree (§ above); what is left is that the GRADING does,
and that is a frame congruence rather than an equality.  Everything the
chain sees except the family slot itself is either lifted past it or
reads the index slot, so `NoBVar`/`AgreeOff` (`Semantics/NoBVar.lean`)
carries it; the recursive slot's own body is the one place where the
two terms differ, and there the two application clauses' witnesses are
literally the same objects. -/

omit [SetTheory V] in
/-- A lifted term mentions no variable in the gap the lifting opened. -/
theorem noBVar_liftN {n : Nat} :
    ∀ (e : AnnotTerm) (k : Nat) (P : Nat → Prop), (∀ i, P i → k ≤ i ∧ i < k + n) →
      NoBVar P (e.liftN n k) := by
  intro e
  induction e with
  | bvar i =>
    intro k P hP
    show ¬ P (if i < k then i else i + n)
    intro h
    obtain ⟨h1, h2⟩ := hP _ h
    split at h1 <;> split at h2 <;> omega
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro k P hP; exact ⟨ihf k P hP, iha k P hP⟩
  | eqE a b iha ihb => intro k P hP; exact ⟨iha k P hP, ihb k P hP⟩
  | fst e ihe => intro k P hP; exact ihe k P hP
  | snd e ihe => intro k P hP; exact ihe k P hP
  | lam u A b ihA ihb =>
    intro k P hP
    refine ⟨ihA k P hP, ihb (k + 1) (shiftP P) ?_⟩
    intro i hi
    cases i with
    | zero => exact absurd hi (by simp [shiftP])
    | succ i => have := hP i hi; omega
  | pi u v A B ihA ihB =>
    intro k P hP
    refine ⟨ihA k P hP, ihB (k + 1) (shiftP P) ?_⟩
    intro i hi
    cases i with
    | zero => exact absurd hi (by simp [shiftP])
    | succ i => have := hP i hi; omega

omit [SetTheory V] in
theorem noBVar_mkAppN {P : Nat → Prop} :
    ∀ (args : List AnnotTerm) (f : AnnotTerm), NoBVar P f → (∀ a ∈ args, NoBVar P a) →
      NoBVar P (AnnotTerm.mkAppN f args)
  | [], _, hf, _ => hf
  | a :: args, f, hf, hargs =>
    noBVar_mkAppN args (.app f a) ⟨hf, hargs a List.mem_cons_self⟩
      fun b hb => hargs b (List.mem_cons_of_mem _ hb)

omit [SetTheory V] in
theorem noBVar_projAV {P : Nat → Prop} :
    ∀ (l : Nat) (e : AnnotTerm), NoBVar P e → NoBVar P (projAV l e)
  | 0, _, h => h
  | l + 1, e, h => noBVar_projAV l (.snd e) h

/-- **The projection chain's grading crosses a frame change** that the
subject's reading survives. -/
theorem projAV_wellDenoted_frame :
    ∀ (l : Nat) (e : AnnotTerm) (σ σ' : Nat → V),
      interp V σ e = interp V σ' e → (WellDenoted V σ e → WellDenoted V σ' e) →
      WellDenoted V σ (projAV l e) → WellDenoted V σ' (projAV l e)
  | 0, e, σ, σ', hv, hok, h => by
    have h' : WellDenoted V σ (.fst e) := h
    show WellDenoted V σ' (.fst e)
    rw [WellDenoted_fst] at h' ⊢
    obtain ⟨he, u, v, A, Bf, h1, h2, h3⟩ := h'
    exact ⟨hok he, u, v, A, Bf, by rw [← hv]; exact h1, h2, h3⟩
  | l + 1, e, σ, σ', hv, hok, h => by
    refine projAV_wellDenoted_frame l (.snd e) σ σ' ?_ ?_ h
    · show ssnd (interp V σ e) = ssnd (interp V σ' e)
      rw [hv]
    · intro hs
      rw [WellDenoted_snd] at hs ⊢
      obtain ⟨he, u, v, A, Bf, h1, h2, h3⟩ := hs
      exact ⟨hok he, u, v, A, Bf, by rw [← hv]; exact h1, h2, h3⟩

/-- The equation chain's grading crosses a frame change whose sides'
readings and gradings do. -/
theorem eqChainAV_wellDenoted_frame :
    ∀ (eqs : List (AnnotTerm × AnnotTerm)) (σ σ' : Nat → V),
      (∀ e ∈ eqs, interp V σ e.1 = interp V σ' e.1 ∧ interp V σ e.2 = interp V σ' e.2) →
      (∀ e ∈ eqs, (WellDenoted V σ e.1 → WellDenoted V σ' e.1) ∧
        (WellDenoted V σ e.2 → WellDenoted V σ' e.2)) →
      WellDenoted V σ (eqChainAV eqs) → WellDenoted V σ' (eqChainAV eqs)
  | [], _, _, _, _, h => h
  | (a, b) :: r, σ, σ', hv, hok, h => by
    have h' : WellDenoted V σ (.pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0)) := h
    show WellDenoted V σ' (.pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0))
    rw [WellDenoted_pi, WellDenoted_eqE]
    rw [WellDenoted_pi, WellDenoted_eqE] at h'
    obtain ⟨⟨ha, hb⟩, htail⟩ := h'
    have hA : interp V σ (.eqE a b : AnnotTerm) = interp V σ' (.eqE a b) := by
      rw [interp_eqE, interp_eqE, (hv (a, b) List.mem_cons_self).1,
        (hv (a, b) List.mem_cons_self).2]
    refine ⟨⟨(hok (a, b) List.mem_cons_self).1 ha, (hok (a, b) List.mem_cons_self).2 hb⟩,
      fun x hx => ?_⟩
    rw [WellDenoted_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
    have hx' : x ∈ˢ interp V σ (.eqE a b : AnnotTerm) := by rw [hA]; exact hx
    have hrest := htail x hx'
    rw [WellDenoted_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons,
      shiftE_zero_zero] at hrest
    exact eqChainAV_wellDenoted_frame r σ σ'
      (fun e he => hv e (List.mem_cons_of_mem _ he))
      (fun e he => hok e (List.mem_cons_of_mem _ he)) hrest

section Trans

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The terminator's grading crosses the family slot**: its left
sides are lifted past it and its right sides read the INDEX slot. -/
theorem termXI_wellDenoted_frame {t Y X : V} {as : List V} {nF : Nat} (hlen : as.length = nF)
    {n : Nat} {Es : List AnnotTerm} :
    WellDenoted V (consList as (cons t (cons Y ρp))) (idxEqAV (eqsXI n nF Es))
      → WellDenoted V (consList as (cons t (cons X ρp))) (idxEqAV (eqsXI n nF Es)) := by
  subst hlen
  intro h
  have h' : WellDenoted V (consList as (cons t (cons Y ρp)))
      (.pi 0 0 (eqChainAV (eqsXI n as.length Es)) (.const .empty [0])) := h
  rw [WellDenoted_pi] at h'
  show WellDenoted V (consList as (cons t (cons X ρp)))
    (.pi 0 0 (eqChainAV (eqsXI n as.length Es)) (.const .empty [0]))
  rw [WellDenoted_pi]
  refine ⟨?_, fun _ _ => trivial⟩
  refine eqChainAV_wellDenoted_frame _ _ _ (fun e he => ?_) (fun e he => ?_) h'.1
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
    exact ⟨interp_chainXI_ord _ as t Y |>.trans (interp_chainXI_ord _ as t X).symm, by
      show interp V _ (projAV l (.bvar as.length)) = interp V _ (projAV l (.bvar as.length))
      rw [projAV_interp, projAV_interp, interp_bvar, interp_bvar, Xframe_t, Xframe_t]⟩
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
    refine ⟨fun hw => (WellDenoted_chainXI_ord _ as t X).mpr
      ((WellDenoted_chainXI_ord _ as t Y).mp hw), fun hw => ?_⟩
    refine projAV_wellDenoted_frame l (.bvar as.length) _ _ ?_ (fun _ => trivial) hw
    rw [interp_bvar, interp_bvar, Xframe_t, Xframe_t]

/-- The `WellDenoted` twin of `PiTowerAgree`: the tower's domains read
equally and its bodies' gradings cross. -/
def PiTowerTrans (R R' : AnnotTerm) :
    List (Nat × Nat × AnnotTerm) → (Nat → V) → (Nat → V) → Prop
  | [], σ, σ' => WellDenoted V σ R → WellDenoted V σ' R'
  | d :: ds, σ, σ' =>
    interp V σ d.2.2 = interp V σ' d.2.2 ∧
      (WellDenoted V σ d.2.2 → WellDenoted V σ' d.2.2) ∧
      ∀ x, PiTowerTrans R R' ds (cons x σ) (cons x σ')

theorem wellDenoted_mkPisAV_of_trans {R R' : AnnotTerm} :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (σ σ' : Nat → V),
      PiTowerTrans R R' ds σ σ' →
      WellDenoted V σ (mkPisAV ds R) → WellDenoted V σ' (mkPisAV ds R')
  | [], _, _, h, hw => h hw
  | d :: ds, σ, σ', h, hw => by
    have hw' : WellDenoted V σ (.pi d.1 d.2.1 d.2.2 (mkPisAV ds R)) := hw
    show WellDenoted V σ' (.pi d.1 d.2.1 d.2.2 (mkPisAV ds R'))
    rw [WellDenoted_pi]
    rw [WellDenoted_pi] at hw'
    refine ⟨h.2.1 hw'.1, fun x hx => ?_⟩
    exact wellDenoted_mkPisAV_of_trans ds (cons x σ) (cons x σ') (h.2.2 x)
      (hw'.2 x (by rw [h.1]; exact hx))

theorem liftTele2_trans {R R' : AnnotTerm} (ρp : Nat → V) (t Y X : V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (as : List V),
      (∀ bs : List V, bs.length = tl.length →
        WellDenoted V (consList (as ++ bs) (cons t (cons Y ρp))) R →
        WellDenoted V (consList (as ++ bs) (cons t (cons X ρp))) R') →
      PiTowerTrans R R' (liftTele2 as.length tl)
        (consList as (cons t (cons Y ρp))) (consList as (cons t (cons X ρp)))
  | [], as, h => by
    have := h [] rfl
    simpa [liftTele2, PiTowerTrans] using this
  | d :: tl, as, h => by
    rw [liftTele2_cons]
    refine ⟨?_, ?_, fun x => ?_⟩
    · show interp V (consList as (cons t (cons Y ρp))) (d.2.2.liftN 2 as.length)
        = interp V (consList as (cons t (cons X ρp))) (d.2.2.liftN 2 as.length)
      rw [interp_chainXI_ord, interp_chainXI_ord]
    · exact fun hw => (WellDenoted_chainXI_ord _ as t X).mpr
        ((WellDenoted_chainXI_ord _ as t Y).mp hw)
    · rw [consList_snoc', consList_snoc']
      have hrec := liftTele2_trans (R := R) (R' := R') ρp t Y X tl (as ++ [x])
        (fun bs hbs => by
          have := h (x :: bs) (by simpa using hbs)
          simpa [List.append_assoc] using this)
      rw [length_snoc'] at hrec
      exact hrec

end Trans

/-! ## The two frames agree off the family slot -/

omit [SetTheory V] in
theorem consList_apply_lt : ∀ (cs : List V) (ρ ρ' : Nat → V) (i : Nat), i < cs.length →
    consList cs ρ i = consList cs ρ' i
  | [], _, _, _, h => absurd h (by simp)
  | c :: cs, ρ, ρ', i, h => by
    rw [consList_cons, consList_cons]
    by_cases hi : i < cs.length
    · exact consList_apply_lt cs _ _ i hi
    · have hie : i = cs.length := by simp at h; omega
      subst hie
      rw [← Nat.zero_add cs.length, consList_apply_add, consList_apply_add]
      rfl

omit [SetTheory V] in
/-- **The two X-frames agree off the family slot** — index
`cs.length + 1` under `cs` binders. -/
theorem agreeOff_Xframe {ρp : Nat → V} (t Y X : V) (cs : List V) :
    AgreeOff (fun i => i = cs.length + 1)
      (consList cs (cons t (cons Y ρp))) (consList cs (cons t (cons X ρp))) := by
  intro i hi
  by_cases hlt : i < cs.length
  · exact consList_apply_lt cs _ _ i hlt
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + cs.length := ⟨i - cs.length, by omega⟩
    rw [consList_apply_add, consList_apply_add]
    match j with
    | 0 => rfl
    | 1 => exact absurd (by omega : 1 + cs.length = cs.length + 1) hi
    | j + 2 => rfl

/-! ## The recursive slot's grading, and the whole chain's -/

section Fields

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}

/-- **The block's recursive slot at `k = 1` is graded where the
one-member route's is.**  Everything the slot sees except the family
variable is lifted past it (`NoBVar`/`AgreeOff`), and at the variable
itself the two application clauses' witnesses are the same objects. -/
theorem slotXBI_wellDenoted_one {t Y X : V} (hY : projS 0 Y = X)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) (as : List V) :
    WellDenoted V (consList as (cons t (cons Y ρp)))
        (slotXBI (uf 0) (Idss 0) 0 tl Eis as.length)
      → WellDenoted V (consList as (cons t (cons X ρp)))
        (slotXI (uf 0) (Idss 0) tl Eis as.length) := by
  unfold slotXBI slotXI
  refine wellDenoted_mkPisAV_of_trans _ _ _
    (liftTele2_trans
      (R := .app (projAV 0 (.bvar (as.length + 1 + tl.length)))
        (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
          (Eis.map (·.liftN 2 (as.length + tl.length)))))
      (R' := .app (.bvar (as.length + 1 + tl.length))
        (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
          (Eis.map (·.liftN 2 (as.length + tl.length)))))
      ρp t Y X tl as fun bs hbs => ?_)
  intro hw
  have hp : (as ++ bs).length = as.length + tl.length := by simp [hbs]
  have hag := agreeOff_Xframe (ρp := ρp) t Y X (as ++ bs)
  have hnb : NoBVar (fun i => i = (as ++ bs).length + 1)
      (AnnotTerm.mkAppN ((tuplerAV (uf 0) (Idss 0)).liftN (as.length + 2 + tl.length) 0)
        (Eis.map (·.liftN 2 (as.length + tl.length)))) := by
    refine noBVar_mkAppN _ _ ?_ fun a ha => ?_
    · exact noBVar_liftN _ 0 _ fun i hi => by omega
    · obtain ⟨E, -, rfl⟩ := List.mem_map.mp ha
      exact noBVar_liftN _ _ _ fun i hi => by omega
  have htv := interp_congr_noBVar (V := V) _ hnb hag
  have htok := WellDenoted_congr_noBVar (V := V) _ hnb hag
  have hqv : interp V (consList (as ++ bs) (cons t (cons Y ρp)))
      (projAV 0 (.bvar (as.length + 1 + tl.length)))
      = interp V (consList (as ++ bs) (cons t (cons X ρp)))
        (.bvar (as.length + 1 + tl.length)) := by
    rw [projAV_interp, interp_bvar, interp_bvar,
      show as.length + 1 + tl.length = (as ++ bs).length + 1 from by omega,
      Xframe_X, Xframe_X, hY]
  have hw' : WellDenoted V (consList (as ++ bs) (cons t (cons Y ρp)))
      (.app (projAV 0 (.bvar (as.length + 1 + tl.length))) _) := hw
  rw [WellDenoted_app] at hw'
  obtain ⟨-, ha, v, A, B, h1, h2, h3⟩ := hw'
  show WellDenoted V (consList (as ++ bs) (cons t (cons X ρp)))
    (.app (.bvar (as.length + 1 + tl.length)) _)
  rw [WellDenoted_app]
  exact ⟨trivial, htok.mp ha, v, A, B, hqv ▸ h1, htv ▸ h2, h3⟩

end Fields

section ChainFields

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rs : List Bool} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Eis : List (List AnnotTerm)} {n nF : Nat} {Es : List AnnotTerm}

/-- The chains' heads read equally at the two frames. -/
theorem chainXB_head_one (htg : ∀ i, tgts.getD i 0 = 0) {t Y X : V} (hY : projS 0 Y = X)
    (F : AnnotTerm) (as : List V) :
    interp V (consList as (cons t (cons Y ρp))) (xEntryB uf Idss rs tgts tls Eis F as.length)
      = interp V (consList as (cons t (cons X ρp)))
        (xEntry (uf 0) (Idss 0) rs tls Eis F as.length) := by
  unfold xEntry xEntryB
  by_cases hri : rs.getD as.length false = true
  · rw [if_pos hri, if_pos hri, htg as.length]
    exact slotXBI_interp_one hY _ _ as
  · have hri' : rs.getD as.length false = false := by simpa using hri
    rw [if_neg (by rw [hri']; exact Bool.false_ne_true),
      if_neg (by rw [hri']; exact Bool.false_ne_true),
      interp_chainXI_ord, interp_chainXI_ord]

/-- …and their gradings cross. -/
theorem chainXB_head_ok_one (htg : ∀ i, tgts.getD i 0 = 0) {t Y X : V} (hY : projS 0 Y = X)
    (F : AnnotTerm) (as : List V) :
    WellDenoted V (consList as (cons t (cons Y ρp)))
        (xEntryB uf Idss rs tgts tls Eis F as.length)
      → WellDenoted V (consList as (cons t (cons X ρp)))
        (xEntry (uf 0) (Idss 0) rs tls Eis F as.length) := by
  unfold xEntry xEntryB
  by_cases hri : rs.getD as.length false = true
  · rw [if_pos hri, if_pos hri, htg as.length]
    exact slotXBI_wellDenoted_one hY _ _ as
  · have hri' : rs.getD as.length false = false := by simpa using hri
    rw [if_neg (by rw [hri']; exact Bool.false_ne_true),
      if_neg (by rw [hri']; exact Bool.false_ne_true)]
    exact fun hw => (WellDenoted_chainXI_ord _ as t X).mpr
      ((WellDenoted_chainXI_ord _ as t Y).mp hw)

/-- **The block's X-chain at `k = 1` is graded where the one-member
route's is** — the remaining half of the falsifier's premise. -/
theorem fieldsOkB_chainXB_one (htg : ∀ i, tgts.getD i 0 = 0) {t Y X : V} (hY : projS 0 Y = X) :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as : List V), as.length = i → as.length + Fs.length = nF →
      FieldsOkB w (consList as (cons t (cons Y ρp)))
          (chainXBIGo uf Idss rs tgts tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]) →
      FieldsOkB w (consList as (cons t (cons X ρp)))
          (chainXIGo (uf 0) (Idss 0) rs tls Eis Fs i ++ [idxEqAV (eqsXI n nF Es)])
  | [], _, as, _, hnF, h => by
    have hlen : as.length = nF := by simpa using hnF
    have h' : FieldsOkB w (consList as (cons t (cons Y ρp))) [idxEqAV (eqsXI n nF Es)] := h
    show FieldsOkB w (consList as (cons t (cons X ρp))) [idxEqAV (eqsXI n nF Es)]
    refine ⟨termXI_wellDenoted_frame hlen h'.1, fun hw => ?_, fun _ _ => trivial⟩
    rw [← interp_termXI (X := Y) (Y := X) hlen]
    exact h'.2.1 hw
  | F :: Fs, i, as, hi, hnF, h => by
    subst hi
    have h' : FieldsOkB w (consList as (cons t (cons Y ρp)))
        (xEntryB uf Idss rs tgts tls Eis F as.length
          :: (chainXBIGo uf Idss rs tgts tls Eis Fs (as.length + 1)
              ++ [idxEqAV (eqsXI n nF Es)])) := h
    show FieldsOkB w (consList as (cons t (cons X ρp)))
      (xEntry (uf 0) (Idss 0) rs tls Eis F as.length
        :: (chainXIGo (uf 0) (Idss 0) rs tls Eis Fs (as.length + 1)
            ++ [idxEqAV (eqsXI n nF Es)]))
    obtain ⟨hok, hbnd, hrest⟩ := h'
    have hv := chainXB_head_one (ρp := ρp) (uf := uf) (Idss := Idss) (rs := rs) (tgts := tgts)
      (tls := tls) (Eis := Eis) (t := t) (Y := Y) (X := X) htg hY F as
    refine ⟨chainXB_head_ok_one (ρp := ρp) (uf := uf) (Idss := Idss) (rs := rs) (tgts := tgts)
      (tls := tls) (Eis := Eis) (t := t) (Y := Y) (X := X) htg hY F as hok,
      fun hw => hv ▸ hbnd hw, fun a ha => ?_⟩
    rw [consList_snoc']
    refine fieldsOkB_chainXB_one htg hY Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
      (by simp at hnF ⊢; omega) ?_
    rw [← consList_snoc']
    exact hrest a (by rw [hv]; exact ha)

end ChainFields

section Premise

variable {w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **The block's chain premise implies the one-member route's**, at
`k = 1`: the one-component tuple of a family is in the block's
family-tuple space, and its component is the family. -/
theorem blockChainsOkI_to_fix (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0)
    (h : BlockChainsOkI 1 w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    FixChainsOkI (uf 0) w ρp (Idss 0) (Idss 0).length (rsss 0) (tlsss 0) (Eisss 0)
      (Fsss 0) (Esss 0) := by
  intro X hX t ht
  have hYmem : spair X pt ∈ˢ famsSpaceB 1 w ρp uf Idss := by
    show spair X pt ∈ˢ sigmaSet (blockR 1 w uf)
      (lfpFamSpace V w (idxSet (uf 0) ρp (Idss 0))) fun _ => unitSet
    exact spair_mem (blockR_ne_zero 1 w uf) hX pt_mem_unitSet
  have hY : projS 0 (spair X pt) = X := sfst_spair X pt
  have hblk := h (spair X pt) hYmem 0 Nat.zero_lt_one t ht
  intro Fs hFs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hFs
  have hjl : j < (Fsss 0).length := List.mem_range.mp hj
  have hY' := hblk (chainXBI uf Idss (Idss 0).length ((rsss 0).getD j []) ((tgtsss 0).getD j [])
      ((tlsss 0).getD j []) ((Eisss 0).getD j []) ((Fsss 0).getD j []) ((Esss 0).getD j []))
    (List.mem_map.mpr ⟨j, hj, rfl⟩)
  have := fieldsOkB_chainXB_one (w := w) (ρp := ρp) (uf := uf) (Idss := Idss)
    (rs := (rsss 0).getD j []) (tgts := (tgtsss 0).getD j []) (tls := (tlsss 0).getD j [])
    (Eis := (Eisss 0).getD j []) (n := (Idss 0).length)
    (nF := ((Fsss 0).getD j []).length) (Es := (Esss 0).getD j [])
    (t := t) (Y := spair X pt) (X := X)
    (fun i => htg j i) hY ((Fsss 0).getD j []) 0 [] rfl (by simp)
    (by unfold chainXBI at hY'; simpa only [consList_nil] using hY')
  unfold chainXI
  simpa only [consList_nil] using this

theorem blockBaseI_to_fix (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0) {ρ : Nat → V}
    (h : BlockBaseI 1 w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss 0) :
    FixBaseI (uf 0) w ρ (Idss 0) (rsss 0) (tlsss 0) (Eisss 0) (Fsss 0) (Esss 0) :=
  ⟨h.1 0 Nat.zero_lt_one, blockChainsOkI_to_fix htg h.2.1, h.2.2⟩

theorem paramsOkXBI_to_fix (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0) :
    ∀ (pps : List (Nat × Nat × AnnotTerm)) (ρ : Nat → V),
      ParamsOkXBI 1 w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss 0 pps →
      ParamsOkXI (uf 0) w ρ (Idss 0) (rsss 0) (tlsss 0) (Eisss 0) (Fsss 0) (Esss 0) pps
  | [], _, h => blockBaseI_to_fix htg h
  | _ :: pps, _, h =>
    ⟨h.1, h.2.1, fun a ha => paramsOkXBI_to_fix htg pps _ (h.2.2 a ha)⟩

end Premise

/-! ## The falsifier, at the leaf -/

section Falsifier

variable {w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}

/-- **THE FALSIFIER AT THE LEAF**: at `k = 1` the block route's
type-former leaf and the one-member route's read to the SAME set,
under the BLOCK leaf's own premise and the syntactic `htg` alone.

The two terms are not equal — the block reads the family through
`proj_0` of a one-component tuple, and its carrier is `proj_0` of a
one-component tuple lfp — and what is equal is what they denote.  The
carrier-level half `blockFam_one` carries no premise but `htg`. -/
theorem blockTyAV_one (htg : ∀ j i, ((tgtsss 0).getD j []).getD i 0 = 0)
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (h : ParamsOkXBI 1 w ρ uf Idss rsss tgtsss tlsss Eisss Fsss Esss 0 pps) :
    interp V ρ (blockTyAV 1 w uf Idss rsss tgtsss tlsss Eisss Fsss Esss pps 0)
      = interp V ρ (nativeTyAVI (uf 0) w pps (Idss 0) (rsss 0) (tlsss 0) (Eisss 0)
          (Fsss 0) (Esss 0)) :=
  blockTyAV_one_of htg h (paramsOkXBI_to_fix htg pps ρ h)

end Falsifier

end ConLeche.Semantics
