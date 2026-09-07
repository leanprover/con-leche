import Lech.Semantics.Tower.FixRecI
import Lech.Semantics.Tower.SumWire

/-!
# The recursive recursor leaf's closedness (task #188)

`directFixRecAVI` — the selected fixed point of the one-step
unfolding — is a closed term: the recursor type is a Π-tower over
closed binder data, the body's case split with inductive hypotheses
sits one below the K-frame, and an inductive-hypothesis argument
mentions the unfolded function, the block's variables, the field's
index expressions (moved to the payload's projections) and the
payload's projection only.
-/

namespace Lech.Semantics
open Lech.SetModel
open Lech.TT Lech.TTVerify

/-! ## Instantiation and the payload's projections -/

/-- Instantiation at a bounded term keeps the bound (one binder
consumed). -/
theorem bvarsBelow_inst {a : VExpr} {n : Nat} (ha : VExpr.bvarsBelow n a) :
    ∀ (e : VExpr) (k : Nat), VExpr.bvarsBelow (n + k + 1) e →
      VExpr.bvarsBelow (n + k) (VExpr.inst e a k)
  | .bvar i, k, he => by
    show VExpr.bvarsBelow (n + k) (if i < k then .bvar i else if i = k then VExpr.liftN k a else .bvar (i - 1))
    have hi : i < n + k + 1 := he
    split
    · show i < n + k; omega
    · split
      · exact VExprAux.bvarsBelow_liftN k a n 0 ha
      · show i - 1 < n + k; omega
  | .sort _, _, _ => trivial
  | .const _ _, _, _ => trivial
  | .app f b, k, he => ⟨bvarsBelow_inst ha f k he.1, bvarsBelow_inst ha b k he.2⟩
  | .lam A b, k, he => by
    refine ⟨bvarsBelow_inst ha A k he.1, ?_⟩
    have := bvarsBelow_inst ha b (k + 1) (by
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 from by omega]; exact he.2)
    rwa [show n + (k + 1) = n + k + 1 from by omega] at this
  | .pi A B, k, he => by
    refine ⟨bvarsBelow_inst ha A k he.1, ?_⟩
    have := bvarsBelow_inst ha B (k + 1) (by
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 from by omega]; exact he.2)
    rwa [show n + (k + 1) = n + k + 1 from by omega] at this
  | .letE T v b, k, he => by
    refine ⟨bvarsBelow_inst ha T k he.1, bvarsBelow_inst ha v k he.2.1, ?_⟩
    have := bvarsBelow_inst ha b (k + 1) (by
      rw [show n + (k + 1) + 1 = n + k + 1 + 1 from by omega]; exact he.2.2)
    rwa [show n + (k + 1) = n + k + 1 from by omega] at this
  | .eqE T b c, k, he =>
    ⟨bvarsBelow_inst ha T k he.1, bvarsBelow_inst ha b k he.2.1, bvarsBelow_inst ha c k he.2.2⟩
  | .proj _ e, k, he => bvarsBelow_inst ha e k he
  | .prf, _, _ => trivial

/-- The uniform projection of a bounded variable is bounded. -/
theorem projAV_bvar_below {i j k : Nat} (h : j < k) :
    VExpr.bvarsBelow k (projAV i (.bvar j)).erase :=
  projAV_below (i := i) (e := .bvar j) (k := k) h

/-- Substituting the payload's projections consumes the `i` virtual
field binders. -/
theorem substProj_below {K : Nat} (hK : 0 < K) :
    ∀ (i : Nat) (e : AVExpr), VExpr.bvarsBelow (K + i) e.erase →
      VExpr.bvarsBelow K (substProj i e).erase
  | 0, _, h => h
  | i + 1, e, h => by
    show VExpr.bvarsBelow K (substProj i (e.inst (projAV i (.bvar i)))).erase
    refine substProj_below hK i _ ?_
    rw [AVExpr.erase_inst]
    have := bvarsBelow_inst (n := K + i) (projAV_bvar_below (i := i) (j := i) (k := K + i) (by omega))
      e.erase 0 (by rw [Nat.add_zero]; exact h)
    rwa [Nat.add_zero] at this

/-! ## The inductive-hypothesis arguments -/

/-- An inductive-hypothesis argument at the payload frame `K + D + 1`
mentions the unfolded function (`K = k + 1 + nP + 1 + n + nIdx`, the
K-frame's depth over the function's), the block's variables, the
field's index expressions and the payload's projection. -/
theorem ihArgAV_below {k nP n nIdx D i : Nat} {Eis : List AVExpr}
    (hE : ∀ E ∈ Eis, VExpr.bvarsBelow (nP + i) E.erase) :
    VExpr.bvarsBelow (k + 1 + nP + 1 + n + nIdx + D + 1) (ihArgAV nP n nIdx D i Eis).erase := by
  unfold ihArgAV
  rw [AVExpr.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show D + 1 + nIdx + n + 1 + nP < k + 1 + nP + 1 + n + nIdx + D + 1 by omega) ?_
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_range] at hl
      show D + 1 + nIdx + (nP + 1 + n) - 1 - l < _
      omega
    · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp ha
      refine VExpr.bvarsBelow.mono (show nP + D + nIdx + n + 2 ≤ k + 1 + nP + 1 + n + nIdx + D + 1 by omega) ?_
      refine substProj_below (by omega) i _ ?_
      rw [AVExpr.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (D + nIdx + n + 2) E.erase (nP + i) i (hE E hE')
      rwa [show nP + i + (D + nIdx + n + 2) = nP + D + nIdx + n + 2 + i from by omega] at this
  · rw [List.mem_singleton] at ha
    subst ha
    exact projAV_bvar_below (by omega)

/-- The inductive-hypothesis arguments of every constructor at every
payload frame. -/
theorem ihArgsI_below {k nP n nIdx : Nat} {rss : List (List Bool)}
    {Eiss : List (List (List AVExpr))} {ar : Nat → Nat}
    (hE : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [], VExpr.bvarsBelow (nP + i) E.erase)
    (D j : Nat) :
    ∀ a ∈ ihArgsI nP n nIdx rss Eiss ar D j,
      VExpr.bvarsBelow (k + 1 + nP + 1 + n + nIdx + D + 1) a.erase := by
  intro a ha
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  exact ihArgAV_below (hE j i)

/-! ## The case split with inductive hypotheses -/

theorem caseBaseAVI_below {ℓ w n nIdx K : Nat} (hK : nIdx + n < K)
    {Fss : List (List AVExpr)} {ar : Nat → Nat} {ihArgs : Nat → Nat → List AVExpr} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (hih : ∀ a ∈ ihArgs D j, VExpr.bvarsBelow (K + D + 1) a.erase) :
    VExpr.bvarsBelow (K + D) (caseBaseAVI ℓ w Fss ar ihArgs n nIdx D j).erase := by
  refine ⟨?_, ?_⟩
  · rw [AVExpr.erase_liftN]
    have hFj : FieldsBelow K (Fss.getD j []) := by
      rw [List.getD_eq_getElem?_getD]
      cases hjF : Fss[j]? with
      | none => trivial
      | some Fs' => exact h Fs' (List.mem_of_getElem? hjF)
    exact VExprAux.bvarsBelow_liftN D _ K 0 (towerBodyAV_below hFj)
  · rw [AVExpr.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (show D + 1 + nIdx + n - 1 - j < K + D + 1 by omega) ?_
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      exact projAV_below (show (0 : Nat) < K + D + 1 by omega)
    · exact hih a ha

theorem caseRecAVI_below {ℓ w n nIdx K : Nat} (hK : nIdx + n < K) {Fss : List (List AVExpr)}
    {ar : Nat → Nat} {ihArgs : Nat → Nat → List AVExpr}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (hih : ∀ D j, ∀ a ∈ ihArgs D j, VExpr.bvarsBelow (K + D + 1) a.erase) :
    ∀ (r : Nat) {D j : Nat} {kx : AVExpr},
      VExpr.bvarsBelow (K + D) kx.erase →
      VExpr.bvarsBelow (K + D) (caseRecAVI ℓ w Fss ar ihArgs n nIdx r D j kx).erase
  | 0, _, _, _, _ => ⟨trivial, trivial⟩
  | r + 1, D, j, _, hk => by
    refine natRecAV_below (caseMotiveAV_below hK h) (caseBaseAVI_below hK h (hih D j)) ?_ hk
    refine ⟨trivial, caseMotiveBodyAV_below hK h, ?_⟩
    have := caseRecAVI_below (ℓ := ℓ) (w := w) hK (ar := ar) (ihArgs := ihArgs) h hih r
      (D := D + 2) (j := j + 1) (kx := .bvar 1) (show (1 : Nat) < K + (D + 2) by omega)
    rwa [show K + (D + 2) = K + D + 1 + 1 from by omega] at this

/-- The recursor body is bounded one below the K-frame
`K = k + 1 + nP + 1 + n + nIdx`. -/
theorem fixRecBodyAVI_below {ℓ w k nP nIdx : Nat} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {rss : List (List Bool)} {Eiss : List (List (List AVExpr))}
    (hIds : Ids.length = nIdx)
    (h : ∀ Fs' ∈ rChains (nIdx + Fss.length + 1) nIdx Fss Ess,
      FieldsBelow (k + 1 + nP + 1 + Fss.length + nIdx) Fs')
    (hE : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [], VExpr.bvarsBelow (nP + i) E.erase) :
    VExpr.bvarsBelow (k + 1 + nP + 1 + Fss.length + nIdx + 1)
      (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss).erase := by
  by_cases hw : w = 0
  · subst hw
    rw [fixRecBodyAVI_zero]
    trivial
  · rw [fixRecBodyAVI_pos hw, hIds]
    refine ⟨?_, show (0 : Nat) < k + 1 + nP + 1 + Fss.length + nIdx + 1 by omega⟩
    have := caseRecAVI_below (ℓ := ℓ) (w := w) (K := k + 1 + nP + 1 + Fss.length + nIdx)
      (ar := fun j => (Fss.getD j []).length)
      (ihArgs := ihArgsI nP Fss.length nIdx rss Eiss (fun j => (Fss.getD j []).length))
      (show nIdx + Fss.length < k + 1 + nP + 1 + Fss.length + nIdx by omega) h
      (fun D j => ihArgsI_below (k := k) (rss := rss) (ar := fun j => (Fss.getD j []).length) hE D j)
      Fss.length (D := 1) (j := 0)
      (kx := .proj 0 (.bvar 0)) (show (0 : Nat) < k + 1 + nP + 1 + Fss.length + nIdx + 1 by omega)
    exact this

/-! ## The leaf -/

/-- A field chain bounded at a depth is bounded at any deeper one. -/
theorem fieldsBelow_mono : ∀ {Fs : List AVExpr} {k k' : Nat}, k ≤ k' →
    FieldsBelow k Fs → FieldsBelow k' Fs
  | [], _, _, _, _ => trivial
  | _ :: Fs, k, k', hk, h => ⟨VExpr.bvarsBelow.mono hk h.1, fieldsBelow_mono (Fs := Fs) (by omega) h.2⟩

/-- A Π-tower over bounded binder data with a bounded conclusion is
bounded. -/
theorem mkPisAV_below_of {C : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {k : Nat}, DomsBelow k ds →
      VExpr.bvarsBelow (k + ds.length) C.erase → VExpr.bvarsBelow k (mkPisAV ds C).erase
  | [], _, _, hC => hC
  | d :: ds, k, hd, hC => by
    refine ⟨hd.1, mkPisAV_below_of hd.2 ?_⟩
    rwa [show k + 1 + ds.length = k + (d :: ds).length from by simp; omega]

theorem domsBelow_mono : ∀ {ds : List (Nat × Nat × AVExpr)} {k k' : Nat}, k ≤ k' →
    DomsBelow k ds → DomsBelow k' ds
  | [], _, _, _, _ => trivial
  | _ :: ds, k, k', hk, h => ⟨VExpr.bvarsBelow.mono hk h.1, domsBelow_mono (ds := ds) (by omega) h.2⟩

/-- **The recursor leaf is closed**: its binder data are closed, its
conclusion mentions the motive, the indices and the major, its body is
the case split one below the K-frame. -/
theorem directFixRecAVI_below {ℓ w nP s : Nat} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {rss : List (List Bool)} {Eiss : List (List (List AVExpr))}
    {rds : List (Nat × Nat × AVExpr)} (k : Nat)
    (hd : DomsBelow 0 rds) (hlen : rds.length = nP + 1 + Fss.length + Ids.length + 1)
    (hIds : Ids.length = Ids.length)
    (hFss : ∀ Fs' ∈ rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess,
      FieldsBelow (nP + 1 + Fss.length + Ids.length) Fs')
    (hE : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [], VExpr.bvarsBelow (nP + i) E.erase) :
    VExpr.bvarsBelow k (directFixRecAVI ℓ w nP Fss Ess Ids rss Eiss rds s).erase := by
  have hconc : ∀ m, VExpr.bvarsBelow (m + rds.length) (recConcAV Fss.length Ids.length).erase := by
    intro m
    have hlt : Ids.length + Fss.length < m + rds.length - 1 := by rw [hlen]; omega
    have := motAppAV_below (D' := 1) (K := m + rds.length - 1) hlt
    rw [show m + rds.length - 1 + 1 = m + rds.length from by rw [hlen]; omega] at this
    exact ⟨this, show (0 : Nat) < m + rds.length by rw [hlen]; omega⟩
  have hTy : ∀ m, VExpr.bvarsBelow m (recTyAV Fss.length Ids.length rds).erase := fun m =>
    mkPisAV_below_of (domsBelow_mono (Nat.zero_le m) hd) (hconc m)
  have hstep : ∀ m, VExpr.bvarsBelow m (fixStepAVI ℓ w nP Fss Ess Ids rss Eiss rds s).erase := by
    intro m
    refine ⟨hTy m, ?_⟩
    refine mkLamsC_below (domsBelow_mono (Nat.zero_le (m + 1)) hd) ?_
    have := fixRecBodyAVI_below (ℓ := ℓ) (w := w) (k := m) (nP := nP) (nIdx := Ids.length)
      (Fss := Fss) (Ess := Ess) (Ids := Ids) (rss := rss) (Eiss := Eiss) rfl
      (fun Fs' hFs' => fieldsBelow_mono (by omega) (hFss Fs' hFs')) hE
    rwa [show m + 1 + nP + 1 + Fss.length + Ids.length + 1 = m + 1 + rds.length from by
      rw [hlen]; omega] at this
  have hsig : VExpr.bvarsBelow k (fixSigAVI ℓ w nP Fss Ess Ids rss Eiss rds s).erase := by
    refine ⟨⟨trivial, hTy k⟩, hTy k, ?_⟩
    refine ⟨?_, ⟨?_, show (0 : Nat) < k + 1 by omega⟩, show (0 : Nat) < k + 1 by omega⟩
    · rw [AVExpr.erase_liftN]
      have := VExprAux.bvarsBelow_liftN 1 _ k 0 (hTy k)
      exact this
    · rw [AVExpr.erase_liftN]
      exact VExprAux.bvarsBelow_liftN 1 _ k 0 (hstep k)
  show VExpr.bvarsBelow k (AVExpr.erase (.proj 0 (.app (.app (.const .choice [s]) _) .prf)))
  exact ⟨⟨trivial, hsig⟩, trivial⟩

end Lech.Semantics
