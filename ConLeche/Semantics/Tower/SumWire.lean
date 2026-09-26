module

public import ConLeche.Semantics.Tower.SumRec
import ConLeche.Semantics.Tower.TowerWire

@[expose] public section

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

open ConLeche.Term

/-! ## The case split -/

theorem natSortMotiveAV_below (w k : Nat) :
    Term.bvarsBelow k (natSortMotiveAV w).erase :=
  ⟨trivial, trivial⟩

theorem natRecAV_below {u : Nat} {M z s kx : AnnotTerm} {k : Nat}
    (hM : Term.bvarsBelow k M.erase) (hz : Term.bvarsBelow k z.erase)
    (hs : Term.bvarsBelow k s.erase) (hk : Term.bvarsBelow k kx.erase) :
    Term.bvarsBelow k (natRecAV u M z s kx).erase :=
  ⟨⟨⟨⟨trivial, hM⟩, hz⟩, hs⟩, hk⟩

/-- The selector at depth `K + d` over spellings bounded at `K`. -/
theorem caseAVAt_below {w K : Nat} :
    ∀ {Ts : List AnnotTerm} {d : Nat} {kx : AnnotTerm},
      (∀ T ∈ Ts, Term.bvarsBelow K T.erase) →
      Term.bvarsBelow (K + d) kx.erase →
      Term.bvarsBelow (K + d) (caseAVAt w Ts d kx).erase
  | [], _, _, _, _ => trivial
  | T :: Ts, d, kx, hT, hk => by
    refine natRecAV_below (natSortMotiveAV_below w _) ?_ ?_ hk
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN d T.erase K 0 (hT T List.mem_cons_self)
    · refine ⟨trivial, trivial, ?_⟩
      have := caseAVAt_below (w := w) (K := K) (Ts := Ts) (d := d + 2) (kx := .bvar 1)
        (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT'))
        (show (1 : Nat) < K + (d + 2) by omega)
      rwa [show K + (d + 2) = K + d + 1 + 1 from by omega] at this

/-! ## The carrier -/

theorem towers_below {w K : Nat} {Fss : List (List AnnotTerm)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    ∀ T ∈ Fss.map (towerBodyAV w), Term.bvarsBelow K T.erase := by
  intro T hT
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
  exact towerBodyAV_below (h Fs hFs)

theorem sumBodyAVPos_below {w K : Nat} {Fss : List (List AnnotTerm)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    Term.bvarsBelow K (sumBodyAVPos w Fss).erase := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_⟩
  have := caseAVAt_below (w := w) (K := K) (Ts := Fss.map (towerBodyAV w)) (d := 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + 1 by omega)
  exact this

theorem sqSumBodyAV_below {K : Nat} {Fss : List (List AnnotTerm)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    Term.bvarsBelow K (sqSumBodyAV Fss).erase := by
  refine ⟨⟨trivial, ⟨?_, trivial⟩⟩, trivial⟩
  have := caseAVAt_below (w := 0) (K := K) (Ts := Fss.map (towerBodyAV 0)) (d := 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + 1 by omega)
  exact this

theorem sumBodyAV_below {w K : Nat} {Fss : List (List AnnotTerm)}
    (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    Term.bvarsBelow K (sumBodyAV w Fss).erase := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_below h
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_below h

/-- **The type-former leaf is bounded.** -/
theorem sumTyAV_below {w : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {Fss : List (List AnnotTerm)} {k : Nat} (hp : DomsBelow k pps)
    (hF : ∀ Fs ∈ Fss, FieldsBelow (k + pps.length) Fs) :
    Term.bvarsBelow k (sumTyAV w pps Fss).erase :=
  mkLamsAV_below hp.mapC (by
    rw [List.length_map]
    exact sumBodyAV_below hF)

/-! ## The constructor -/

theorem sumInjAtAV_below {w K : Nat} {Fss : List (List AnnotTerm)} {d : Nat}
    {tag payload : AnnotTerm} (h : ∀ Fs ∈ Fss, FieldsBelow K Fs)
    (ht : Term.bvarsBelow (K + d) tag.erase) (hp : Term.bvarsBelow (K + d) payload.erase) :
    Term.bvarsBelow (K + d) (sumInjAtAV w Fss d tag payload).erase := by
  refine ⟨⟨⟨⟨trivial, trivial⟩, trivial, ?_⟩, ht⟩, hp⟩
  have := caseAVAt_below (w := w) (K := K) (Ts := Fss.map (towerBodyAV w)) (d := d + 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + (d + 1) by omega)
  rwa [show K + (d + 1) = K + d + 1 from by omega] at this

/-- The point-terminated tupler (graph regime): bounded at the full
field frame. -/
theorem mkTowerGoUPos_below {w : Nat} {E : AnnotTerm} :
    ∀ {Fs : List AnnotTerm} {k : Nat}, FieldsBelow k (Fs ++ [E]) →
      Term.bvarsBelow (k + Fs.length) (mkTowerGoUPos w E Fs).erase
  | [], k, h => by
    have hE : Term.bvarsBelow k E.erase := h.1
    exact ⟨⟨⟨⟨trivial, hE⟩, hE, trivial⟩, trivial⟩, trivial⟩
  | F :: Fs, k, h => by
    simp only [List.cons_append] at h
    have hF : Term.bvarsBelow (k + (Fs.length + 1))
        (F.liftN (Fs.length + 1)).erase := by
      rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1) F.erase k 0 h.1
      exact this
    have hbody : Term.bvarsBelow (k + (Fs.length + 1) + 1)
        ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1).erase := by
      rw [AnnotTerm.erase_liftN]
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1)
        (towerBodyAV w (Fs ++ [E])).erase (k + 1) 1 (towerBodyAV_below h.2)
      rw [show k + 1 + (Fs.length + 1) = k + (Fs.length + 1) + 1
        by omega] at this
      exact this
    have hrec : Term.bvarsBelow (k + (Fs.length + 1))
        (mkTowerGoUPos w E Fs).erase := by
      have := mkTowerGoUPos_below (w := w) (E := E) (Fs := Fs) (k := k + 1) h.2
      rw [show k + 1 + Fs.length = k + (Fs.length + 1) by omega] at this
      exact this
    exact ⟨⟨⟨⟨trivial, hF⟩, hF, hbody⟩,
      show Fs.length < k + (Fs.length + 1) by omega⟩, hrec⟩

/-- The point-terminated tupler, both regimes. -/
theorem mkTowerGoU_below {w : Nat} {Fs : List AnnotTerm} {E : AnnotTerm} {k : Nat}
    (h : FieldsBelow k (Fs ++ [E])) :
    Term.bvarsBelow (k + Fs.length) (mkTowerGoU w Fs E).erase := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; trivial
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_below h

/-- The unit-restricted chains are bounded when the chains are. -/
theorem uChains_below {K : Nat} {Fss : List (List AnnotTerm)} (h : ∀ Fs ∈ Fss, FieldsBelow K Fs) :
    ∀ Fs' ∈ uChains Fss, FieldsBelow K Fs' := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact FieldsBelow_append_idxEq (h Fs hFs) fun _ h => nomatch h

/-- **The constructor leaf is bounded** (`hlen` is the frame
accounting: the field frame ends at the binder tower's). -/
theorem sumMkAV_below {w j : Nat} {ds : List (Nat × Nat × AnnotTerm)}
    {Fs : List AnnotTerm} {Fss : List (List AnnotTerm)} {k nP : Nat} (hd : DomsBelow k ds)
    (hF : FieldsBelow (k + nP) Fs) (hFss : ∀ Fs' ∈ Fss, FieldsBelow (k + nP) Fs')
    (hlen : nP + Fs.length = ds.length) :
    Term.bvarsBelow k (sumMkAV w j ds Fs Fss).erase :=
  mkLamsC_below hd (by
    have hmk := mkTowerGoU_below (w := w) (E := idxEqAV [])
      (FieldsBelow_append_idxEq hF fun _ h => nomatch h)
    have := sumInjAtAV_below (w := w) (K := k + nP) (Fss := Fss) (d := Fs.length)
      (tag := numeralAV j) (payload := mkTowerGoU w Fs (idxEqAV [])) hFss (numeralAV_erase_below j _) hmk
    rwa [show k + nP + Fs.length = k + ds.length from by omega] at this)

end ConLeche.Semantics
