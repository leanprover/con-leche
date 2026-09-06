import Setlec.Semantics.Tower.SumRec
import Setlec.Semantics.Tower.TowerWire

/-!
# The sum leaves' syntactic battery (task #175 sum-types)

The `hAclosed` rows of the three sum leaves: bound-variable bounds of
their erasures, one structural walk per spelled former, as
`TowerWire.lean` for the structure route.  The depth accounting is the
spellings' own: the tower bodies are scoped at the parameter frame `K`
and lifted by the depth `d` where they are used, so every lifted use
is bounded at `K + d` (`bvarsBelow_liftN`).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT

/-! ## The case split -/

theorem natSortMotiveAV_below (w k : Nat) :
    VExpr.bvarsBelow k (natSortMotiveAV w).erase :=
  ⟨trivial, trivial⟩

theorem natRecAV_below {u : Nat} {M z s kx : AVExpr} {k : Nat}
    (hM : VExpr.bvarsBelow k M.erase) (hz : VExpr.bvarsBelow k z.erase)
    (hs : VExpr.bvarsBelow k s.erase) (hk : VExpr.bvarsBelow k kx.erase) :
    VExpr.bvarsBelow k (natRecAV u M z s kx).erase :=
  ⟨⟨⟨⟨trivial, hM⟩, hz⟩, hs⟩, hk⟩

/-- The selector at depth `K + d` over spellings bounded at `K`. -/
theorem caseAVAt_below {w K : Nat} :
    ∀ {Ts : List AVExpr} {d : Nat} {kx : AVExpr},
      (∀ T ∈ Ts, VExpr.bvarsBelow K T.erase) →
      VExpr.bvarsBelow (K + d) kx.erase →
      VExpr.bvarsBelow (K + d) (caseAVAt w Ts d kx).erase
  | [], _, _, _, _ => trivial
  | T :: Ts, d, kx, hT, hk => by
    refine natRecAV_below (natSortMotiveAV_below w _) ?_ ?_ hk
    · rw [AVExpr.erase_liftN]
      exact VExprAux.bvarsBelow_liftN d T.erase K 0 (hT T List.mem_cons_self)
    · refine ⟨trivial, trivial, ?_⟩
      have := caseAVAt_below (w := w) (K := K) (Ts := Ts) (d := d + 2) (kx := .bvar 1)
        (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT'))
        (show (1 : Nat) < K + (d + 2) by omega)
      rwa [show K + (d + 2) = K + d + 1 + 1 from by omega] at this

/-! ## The carrier -/

theorem towers_below {w K : Nat} {Fss : List (List AVExpr)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    ∀ T ∈ Fss.map (towerBodyAV w), VExpr.bvarsBelow K T.erase := by
  intro T hT
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
  exact towerBodyAV_below (h Fs hFs)

theorem sumBodyAVPos_below {w K : Nat} {Fss : List (List AVExpr)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow K (sumBodyAVPos w Fss).erase := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_⟩
  have := caseAVAt_below (w := w) (K := K) (Ts := Fss.map (towerBodyAV w)) (d := 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + 1 by omega)
  exact this

theorem sqSumBodyAV_below {K : Nat} {Fss : List (List AVExpr)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow K (sqSumBodyAV Fss).erase := by
  refine ⟨⟨trivial, ⟨?_, trivial⟩⟩, trivial⟩
  have := caseAVAt_below (w := 0) (K := K) (Ts := Fss.map (towerBodyAV 0)) (d := 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + 1 by omega)
  exact this

theorem sumBodyAV_below {w K : Nat} {Fss : List (List AVExpr)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow K (sumBodyAV w Fss).erase := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_below h
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_below h

/-- **The type-former leaf is bounded.** -/
theorem directSumTyAV_below {w : Nat} {pps : List (Nat × Nat × AVExpr)}
    {Fss : List (List AVExpr)} {k : Nat} (hp : DomsBelow k pps)
    (hF : ∀ Fs ∈ Fss, FieldsBelow (k + pps.length) Fs) :
    VExpr.bvarsBelow k (directSumTyAV w pps Fss).erase :=
  mkLamsAV_below hp.mapC (by
    rw [List.length_map]
    exact sumBodyAV_below hF)

/-! ## The constructor -/

theorem numeralAV_below (i k : Nat) : VExpr.bvarsBelow k (numeralAV i).erase :=
  numeralAV_erase_below i k

theorem succsAV_below {k : Nat} : ∀ (j : Nat) {kx : AVExpr},
    VExpr.bvarsBelow k kx.erase → VExpr.bvarsBelow k (succsAV j kx).erase
  | 0, _, h => h
  | j + 1, _, h => ⟨trivial, succsAV_below j h⟩

theorem sumInjAtAV_below {w K : Nat} {Fss : List (List AVExpr)} {d : Nat}
    {tag payload : AVExpr} (h : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (ht : VExpr.bvarsBelow (K + d) tag.erase) (hp : VExpr.bvarsBelow (K + d) payload.erase) :
    VExpr.bvarsBelow (K + d) (sumInjAtAV w Fss d tag payload).erase := by
  refine ⟨⟨⟨⟨trivial, trivial⟩, trivial, ?_⟩, ht⟩, hp⟩
  have := caseAVAt_below (w := w) (K := K) (Ts := Fss.map (towerBodyAV w)) (d := d + 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + (d + 1) by omega)
  rwa [show K + (d + 1) = K + d + 1 from by omega] at this

/-- **The constructor leaf is bounded** (`hlen` is the frame
accounting: the field frame ends at the binder tower's). -/
theorem directSumMkAV_below {w j : Nat} {ds : List (Nat × Nat × AVExpr)}
    {Fs : List AVExpr} {Fss : List (List AVExpr)} {k nP : Nat} (hd : DomsBelow k ds)
    (hF : FieldsBelow (k + nP) Fs) (hFss : ∀ Fs' ∈ Fss, FieldsBelow (k + nP) Fs')
    (hlen : nP + Fs.length = ds.length) :
    VExpr.bvarsBelow k (directSumMkAV w j ds Fs Fss).erase :=
  mkLamsC_below hd (by
    have hmk := mkTowerGo_below (w := w) hF
    have := sumInjAtAV_below (w := w) (K := k + nP) (Fss := Fss) (d := Fs.length)
      (tag := numeralAV j) (payload := mkTowerGo w Fs) hFss (numeralAV_below j _) hmk
    rwa [show k + nP + Fs.length = k + ds.length from by omega] at this)

/-! ## The recursor -/

theorem caseMotiveBodyAV_below {ℓ w K : Nat} {Fss : List (List AVExpr)} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow (K + D + 1) (caseMotiveBodyAV ℓ w Fss D j).erase := by
  refine ⟨?_, ?_⟩
  · have := caseAVAt_below (w := w) (K := K) (Ts := (Fss.map (towerBodyAV w)).drop j)
      (d := D + 1) (kx := .bvar 0)
      (fun T hT => towers_below h T (List.mem_of_mem_drop hT))
      (show (0 : Nat) < K + (D + 1) by omega)
    rwa [show K + (D + 1) = K + D + 1 from by omega] at this
  · refine ⟨show D + 1 < K + D + 1 + 1 by omega, ?_⟩
    have := sumInjAtAV_below (w := w) (K := K) (Fss := Fss) (d := D + 2)
      (tag := succsAV j (.bvar 1)) (payload := .bvar 0) h
      (succsAV_below j (show (1 : Nat) < K + (D + 2) by omega))
      (show (0 : Nat) < K + (D + 2) by omega)
    rwa [show K + (D + 2) = K + D + 1 + 1 from by omega] at this

theorem caseMotiveAV_below {ℓ w K : Nat} {Fss : List (List AVExpr)} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow (K + D) (caseMotiveAV ℓ w Fss D j).erase :=
  ⟨trivial, caseMotiveBodyAV_below h⟩

theorem caseBaseAV_below {ℓ w K : Nat} {Fss : List (List AVExpr)} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) (hj : j < Fss.length) :
    VExpr.bvarsBelow (K + D) (caseBaseAV ℓ w Fss D j).erase := by
  refine ⟨?_, ?_⟩
  · rw [AVExpr.erase_liftN]
    have hFj : FieldsBelow K (Fss.getD j []) := by
      have hjF : Fss[j]? = some (Fss.getD j []) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      exact h _ (List.mem_of_getElem? hjF)
    exact VExprAux.bvarsBelow_liftN D _ K 0 (towerBodyAV_below hFj)
  · rw [AVExpr.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (show D - 1 - j < K + D + 1 by omega) ?_
    intro a ha
    obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hea
    exact projAV_below (show (0 : Nat) < K + D + 1 by omega)

theorem caseRecAV_below {ℓ w K : Nat} {Fss : List (List AVExpr)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    ∀ (r : Nat) {D j : Nat} {kx : AVExpr}, j + r = Fss.length →
      VExpr.bvarsBelow (K + D) kx.erase →
      VExpr.bvarsBelow (K + D) (caseRecAV ℓ w Fss r D j kx).erase
  | 0, _, _, _, _, _ => ⟨trivial, trivial⟩
  | r + 1, D, j, _, hjr, hk => by
    refine natRecAV_below (caseMotiveAV_below h) (caseBaseAV_below h (by omega)) ?_ hk
    refine ⟨trivial, caseMotiveBodyAV_below h, ?_⟩
    have := caseRecAV_below (ℓ := ℓ) (w := w) h r (D := D + 2) (j := j + 1) (kx := .bvar 1)
      (by omega) (show (1 : Nat) < K + (D + 2) by omega)
    rwa [show K + (D + 2) = K + D + 1 + 1 from by omega] at this

theorem sumRecBodyAV_below {ℓ w K : Nat} {Fss : List (List AVExpr)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow (K + (Fss.length + 2)) (sumRecBodyAV ℓ w Fss).erase :=
  ⟨caseRecAV_below h Fss.length (Nat.zero_add _) (show (0 : Nat) < K + (Fss.length + 2) by omega),
    show (0 : Nat) < K + (Fss.length + 2) by omega⟩

/-- **The recursor leaf is bounded**: the body sits at the frame
`nP + n + 2` over the parameter frame, whose tower bodies are bounded
at `k + nP`. -/
theorem directSumRecAV_below {ℓ w : Nat} {rds : List (Nat × Nat × AVExpr)}
    {Fss : List (List AVExpr)} {k nP : Nat} (hd : DomsBelow k rds)
    (hFss : ∀ Fs ∈ Fss, FieldsBelow (k + nP) Fs)
    (hlen : rds.length = nP + Fss.length + 2) :
    VExpr.bvarsBelow k (directSumRecAV ℓ w rds Fss).erase :=
  mkLamsC_below hd (by
    have := sumRecBodyAV_below (ℓ := ℓ) (w := w) (K := k + nP) hFss
    rwa [show k + nP + (Fss.length + 2) = k + rds.length from by omega] at this)

end Setlec.Semantics
