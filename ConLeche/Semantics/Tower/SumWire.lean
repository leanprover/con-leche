import ConLeche.Semantics.Tower.SumRec
import ConLeche.Semantics.Tower.TowerWire

/-!
# The sum leaves' syntactic battery (task #175 sum-types, indexed)

The `hAclosed` rows of the three sum leaves: bound-variable bounds of
their erasures, one structural walk per spelled former, as
`TowerWire.lean` for the structure route.  The depth accounting is the
spellings' own: the tower bodies are scoped at the K-frame `K` and
lifted by the depth `d` where they are used, so every lifted use is
bounded at `K + d` (`bvarsBelow_liftN`); the motive, the minors and
the index variables sit inside the K-frame (`nIdx + n < K`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr

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

/-- The restricted chains of a family are bounded at a frame `K + d`
when the field chains are bounded at `K` and the index expressions at
the constructor frames. -/
theorem rChains_below {d nIdx K : Nat} (hd : nIdx ≤ d) {Fss Ess : List (List AVExpr)}
    (hF : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (hE : ∀ j, j < Fss.length → (Ess.getD j []).length = nIdx ∧
      ∀ E ∈ Ess.getD j [], VExpr.bvarsBelow (K + (Fss.getD j []).length) E.erase) :
    ∀ Fs' ∈ rChains d nIdx Fss Ess, FieldsBelow (K + d) Fs' := by
  intro Fs' hFs'
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs'
  rw [rChains_getElem?] at hj
  cases hFj : Fss[j]? with
  | none => rw [hFj] at hj; exact nomatch hj
  | some Fs =>
    cases hEj : Ess[j]? with
    | none => rw [hFj, hEj] at hj; exact nomatch hj
    | some Es =>
      rw [hFj, hEj] at hj
      obtain rfl := Option.some.inj hj
      have hjl : j < Fss.length := (List.getElem?_eq_some_iff.mp hFj).1
      have hFsD : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hFj]; rfl
      have hEsD : Ess.getD j [] = Es := by rw [List.getD_eq_getElem?_getD, hEj]; rfl
      obtain ⟨hlenE, hEb⟩ := hE j hjl
      rw [hEsD] at hlenE hEb
      rw [hFsD] at hEb
      exact FieldsBelow_rChain hd hlenE (hF Fs (List.mem_of_getElem? hFj)) hEb

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

/-- The point-terminated tupler (graph regime): bounded at the full
field frame. -/
theorem mkTowerGoUPos_below {w : Nat} {E : AVExpr} :
    ∀ {Fs : List AVExpr} {k : Nat}, FieldsBelow k (Fs ++ [E]) →
      VExpr.bvarsBelow (k + Fs.length) (mkTowerGoUPos w E Fs).erase
  | [], k, h => by
    have hE : VExpr.bvarsBelow k E.erase := h.1
    exact ⟨⟨⟨⟨trivial, hE⟩, hE, trivial⟩, trivial⟩, trivial⟩
  | F :: Fs, k, h => by
    simp only [List.cons_append] at h
    have hF : VExpr.bvarsBelow (k + (Fs.length + 1))
        (F.liftN (Fs.length + 1)).erase := by
      rw [AVExpr.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1) F.erase k 0 h.1
      exact this
    have hbody : VExpr.bvarsBelow (k + (Fs.length + 1) + 1)
        ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1).erase := by
      rw [AVExpr.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1)
        (towerBodyAV w (Fs ++ [E])).erase (k + 1) 1 (towerBodyAV_below h.2)
      rw [show k + 1 + (Fs.length + 1) = k + (Fs.length + 1) + 1
        by omega] at this
      exact this
    have hrec : VExpr.bvarsBelow (k + (Fs.length + 1))
        (mkTowerGoUPos w E Fs).erase := by
      have := mkTowerGoUPos_below (w := w) (E := E) (Fs := Fs) (k := k + 1) h.2
      rw [show k + 1 + Fs.length = k + (Fs.length + 1) by omega] at this
      exact this
    exact ⟨⟨⟨⟨trivial, hF⟩, hF, hbody⟩,
      show Fs.length < k + (Fs.length + 1) by omega⟩, hrec⟩

/-- The point-terminated tupler, both regimes. -/
theorem mkTowerGoU_below {w : Nat} {Fs : List AVExpr} {E : AVExpr} {k : Nat}
    (h : FieldsBelow k (Fs ++ [E])) :
    VExpr.bvarsBelow (k + Fs.length) (mkTowerGoU w Fs E).erase := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; trivial
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_below h

/-- The unit-restricted chains are bounded when the chains are. -/
theorem uChains_below {K : Nat} {Fss : List (List AVExpr)} (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    ∀ Fs' ∈ uChains Fss, FieldsBelow K Fs' := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact FieldsBelow_append_idxEq (h Fs hFs) fun _ h => nomatch h

/-- **The constructor leaf is bounded** (`hlen` is the frame
accounting: the field frame ends at the binder tower's). -/
theorem directSumMkAV_below {w j : Nat} {ds : List (Nat × Nat × AVExpr)}
    {Fs : List AVExpr} {Fss : List (List AVExpr)} {k nP : Nat} (hd : DomsBelow k ds)
    (hF : FieldsBelow (k + nP) Fs) (hFss : ∀ Fs' ∈ Fss, FieldsBelow (k + nP) Fs')
    (hlen : nP + Fs.length = ds.length) :
    VExpr.bvarsBelow k (directSumMkAV w j ds Fs Fss).erase :=
  mkLamsC_below hd (by
    have hmk := mkTowerGoU_below (w := w) (E := idxEqAV [])
      (FieldsBelow_append_idxEq hF fun _ h => nomatch h)
    have := sumInjAtAV_below (w := w) (K := k + nP) (Fss := Fss) (d := Fs.length)
      (tag := numeralAV j) (payload := mkTowerGoU w Fs (idxEqAV [])) hFss (numeralAV_below j _) hmk
    rwa [show k + nP + Fs.length = k + ds.length from by omega] at this)

/-! ## The recursor -/

theorem idxVarsAV_below {nIdx D' K : Nat} (h : nIdx ≤ K) :
    ∀ a ∈ idxVarsAV nIdx D', VExpr.bvarsBelow (K + D') a.erase := by
  intro a ha
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hl
  show D' + nIdx - 1 - l < K + D'
  omega

theorem motAppAV_below {n nIdx D' K : Nat} (h : nIdx + n < K) :
    VExpr.bvarsBelow (K + D') (motAppAV n nIdx D').erase := by
  unfold motAppAV
  rw [AVExpr.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show D' + nIdx + n < K + D' by omega) ?_
  intro a ha
  obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
  exact idxVarsAV_below (by omega) ea hea

theorem caseMotiveBodyAV_below {ℓ w n nIdx K : Nat} (hK : nIdx + n < K)
    {Fss : List (List AVExpr)} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow (K + D + 1) (caseMotiveBodyAV ℓ w Fss n nIdx D j).erase := by
  refine ⟨?_, ?_⟩
  · have := caseAVAt_below (w := w) (K := K) (Ts := (Fss.map (towerBodyAV w)).drop j)
      (d := D + 1) (kx := .bvar 0)
      (fun T hT => towers_below h T (List.mem_of_mem_drop hT))
      (show (0 : Nat) < K + (D + 1) by omega)
    rwa [show K + (D + 1) = K + D + 1 from by omega] at this
  · refine ⟨?_, ?_⟩
    · have := motAppAV_below (n := n) (nIdx := nIdx) (D' := D + 2) (K := K) hK
      rwa [show K + (D + 2) = K + D + 1 + 1 from by omega] at this
    · have := sumInjAtAV_below (w := w) (K := K) (Fss := Fss) (d := D + 2)
        (tag := succsAV j (.bvar 1)) (payload := .bvar 0) h
        (succsAV_below j (show (1 : Nat) < K + (D + 2) by omega))
        (show (0 : Nat) < K + (D + 2) by omega)
      rwa [show K + (D + 2) = K + D + 1 + 1 from by omega] at this

theorem caseMotiveAV_below {ℓ w n nIdx K : Nat} (hK : nIdx + n < K)
    {Fss : List (List AVExpr)} {D j : Nat}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    VExpr.bvarsBelow (K + D) (caseMotiveAV ℓ w Fss n nIdx D j).erase :=
  ⟨trivial, caseMotiveBodyAV_below hK h⟩

end ConLeche.Semantics
