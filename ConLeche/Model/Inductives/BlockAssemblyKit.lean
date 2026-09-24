module

public import ConLeche.Model.Inductives.BlockLeafOk
public section

/-!
# Kit for the uniform block install's assembly (task #315)

`FixAssemblyKit.lean`'s X-chain half at `k` members: the block
functor's whole premise bundle (`BlockChainsOk`,
`Semantics/Tower/BlockFamI.lean`) and the chains' bit-validity, from
the per-member, per-constructor chain facts.  (The closure witness is
no longer the slot operator's: the hole operator's comes from the flat
presentation of the fields with holes, `BlockHoleFlat.lean`.)
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The X-chains of every member's constructors -/

/-- **The block functor's premise and the chains' validity**, from the
per-member, per-constructor chain facts. -/
theorem blockChainsOk_of {k w nP : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {nOf : Nat → Nat} {ksF : Nat → Nat → List RecFieldKind}
    {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}
    (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c))
    (hlenF : ∀ m, m < k → (Fsss m).length = nOf m)
    (hrss : ∀ m, m < k → ∀ j, j < nOf m → (rsss m).getD j [] = rsOf (ksF m j))
    (hC : ∀ m, m < k → ∀ j, j < nOf m →
      ChainFactsB k w nP ((Fsss m).getD j []).length ρp uf Idss m (ksF m j)
        ((tgtsss m).getD j []) ((tlsss m).getD j []) ((Fsss m).getD j [])
        ((Eisss m).getD j []) ((Esss m).getD j []))
    (hCV : ∀ m, m < k → ∀ j, j < nOf m →
      ChainValidFacts nP ((Fsss m).getD j []).length ρp (ksF m j) ((tlsss m).getD j [])
        ((Fsss m).getD j []) ((Eisss m).getD j []) ((Esss m).getD j [])) :
    BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss ∧
    ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ m, m < k →
      ∀ t, t ∈ˢ idxSet (uf m) ρp (Idss m) →
      SumFieldsValid (cons t (cons Y ρp))
        (chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m)
          (Fsss m) (Esss m)) := by
  -- every chain of member `m` is one of its constructors' X-chains
  have hmem : ∀ m, m < k → ∀ chain ∈ chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m)
      (tlsss m) (Eisss m) (Fsss m) (Esss m), ∃ j, j < nOf m ∧
      chain = chainXBI uf Idss (Idss m).length (rsOf (ksF m j)) ((tgtsss m).getD j [])
        ((tlsss m).getD j []) ((Eisss m).getD j []) ((Fsss m).getD j [])
        ((Esss m).getD j []) := by
    intro m hm chain hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    rw [chainsXBI_getElem?] at hj
    split at hj
    · next hjF =>
      have hjn : j < nOf m := by rw [← hlenF m hm]; exact hjF
      refine ⟨j, hjn, ?_⟩
      rw [← hrss m hm j hjn]
      exact (Option.some.inj hj).symm
    · exact nomatch hj
  have hok : BlockChainsOkI k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss := by
    intro Y hY m hm t ht chain hc
    obtain ⟨j, hj, rfl⟩ := hmem m hm chain hc
    exact (blockChain_of hI hm hY ht (hC m hm j hj)).1
  refine ⟨⟨hI, hok, fun Y hY m hm t ht j hj => ?_⟩,
    fun Y hY m hm t ht chain hc => ?_⟩
  · rw [hrss m hm j (by rw [← hlenF m hm]; exact hj)]
    exact (blockChain_of hI hm hY ht (hC m hm j (by rw [← hlenF m hm]; exact hj))).2
  · obtain ⟨j, hj, rfl⟩ := hmem m hm chain hc
    exact blockChainValid_of hI hIV hY (hC m hm j hj) (hCV m hm j hj)


/-! ## The chains read the field list only at the ORDINARY positions -/

/-- An X-chain entry ignores its domain at a RECURSIVE position: there
the entry is the slot at the field's target. -/
theorem xEntryB_congr_ord (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm))
    {F F' : AnnotTerm} {i : Nat} (h : rs.getD i false = false → F = F') :
    xEntryB uf Idss rs tgts tls Eis F i = xEntryB uf Idss rs tgts tls Eis F' i := by
  unfold xEntryB
  by_cases hr : rs.getD i false = true
  · rw [if_pos hr, if_pos hr]
  · have hr' : rs.getD i false = false := by simpa using hr
    rw [if_neg (by rw [hr']; exact Bool.false_ne_true),
      if_neg (by rw [hr']; exact Bool.false_ne_true), h hr']

/-- **`chainXBIGo` reads its field list only at the ORDINARY
positions.** -/
theorem chainXBIGo_congr_ord (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) :
    ∀ (Fs Fs' : List AnnotTerm) (i : Nat), Fs.length = Fs'.length →
      (∀ l, l < Fs.length → rs.getD (i + l) false = false →
        Fs.getD l default = Fs'.getD l default) →
      chainXBIGo uf Idss rs tgts tls Eis Fs i = chainXBIGo uf Idss rs tgts tls Eis Fs' i
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | F :: Fs, F' :: Fs', i, hlen, hord => by
    rw [chainXBIGo_cons, chainXBIGo_cons,
      chainXBIGo_congr_ord uf Idss rs tgts tls Eis Fs Fs' (i + 1) (by simpa using hlen)
        (fun l hl hr => by
          have := hord (l + 1) (by simpa using hl)
            (by rwa [show i + (l + 1) = i + 1 + l from by omega])
          simpa using this),
      xEntryB_congr_ord uf Idss rs tgts tls Eis (F := F) (F' := F')
        (fun hr => by
          have := hord 0 (by simp) (by rwa [Nat.add_zero])
          simpa using this)]

/-- **A member's X-chains read its constructors' field lists only at
the ordinary positions**: the recursive entries are slots, and the
terminating equation reads the lengths. -/
theorem chainsXBI_congr_ord {uf : Nat → Nat} {Idss : Nat → List AnnotTerm} {nIdx : Nat}
    {rss : List (List Bool)} {tgtss : List (List Nat)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)}
    (hlen : Fss.length = Fss'.length)
    (hlenj : ∀ j, j < Fss.length → ((Fss.getD j []).length = (Fss'.getD j []).length))
    (hord : ∀ j, j < Fss.length → ∀ l, l < ((Fss.getD j []).length) →
      (rss.getD j []).getD l false = false →
      (Fss.getD j []).getD l default = (Fss'.getD j []).getD l default) :
    chainsXBI uf Idss nIdx rss tgtss tlss Eiss Fss Ess
      = chainsXBI uf Idss nIdx rss tgtss tlss Eiss Fss' Ess := by
  unfold chainsXBI
  rw [← hlen]
  refine List.map_congr_left fun j hj => ?_
  have hjl : j < Fss.length := by simpa using hj
  unfold chainXBI
  rw [chainXBIGo_congr_ord uf Idss ((rss.getD j [])) ((tgtss.getD j [])) ((tlss.getD j []))
      ((Eiss.getD j [])) ((Fss.getD j [])) ((Fss'.getD j [])) 0 (hlenj j hjl)
      (fun l hl hr => hord j hjl l hl (by rwa [Nat.zero_add] at hr)),
    hlenj j hjl]

/-- **The recursive slots' fit reads the field list only at the
ordinary positions** — the premise `BlockChainsOk.hfit` carries, whose
entries are `xEntryB`'s. -/
theorem slotsFitXB_congr_ord {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {rs : List Bool} {tgts : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {Y t : V} :
    ∀ {Fs Fs' : List AnnotTerm} {i : Nat} {as : List V}, Fs.length = Fs'.length →
      (∀ l, l < Fs.length → rs.getD (i + l) false = false →
        Fs.getD l default = Fs'.getD l default) →
      SlotsFitXB (V := V) k w ρp uf Idss rs tgts tls Eis Y t i as Fs →
      SlotsFitXB k w ρp uf Idss rs tgts tls Eis Y t i as Fs'
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | F :: Fs, F' :: Fs', i, as, hlen, hord, h => by
    have hE : xEntryB uf Idss rs tgts tls Eis F i = xEntryB uf Idss rs tgts tls Eis F' i :=
      xEntryB_congr_ord uf Idss rs tgts tls Eis (fun hr => by
        have := hord 0 (by simp) (by rwa [Nat.add_zero]); simpa using this)
    refine ⟨h.1, fun a ha => ?_⟩
    exact slotsFitXB_congr_ord (Fs := Fs) (Fs' := Fs') (i := i + 1) (as := as ++ [a])
      (by simpa using hlen)
      (fun l hl hr => by
        have := hord (l + 1) (by simpa using hl)
          (by rwa [show i + (l + 1) = i + 1 + l from by omega])
        simpa using this)
      (h.2 a (by rw [hE]; exact ha))

/-- The block operator's fibre reads the fields only at the ordinary
positions. -/
theorem blockStepV_congr_ord {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {rsss : Nat → List (List Bool)}
    {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Fsss' Esss : Nat → List (List AnnotTerm)}
    (hchains : ∀ m, m < k →
      chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) (Esss m)
        = chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss' m)
            (Esss m))
    {m : Nat} (hm : m < k) :
    blockStepV (V := V) w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m
      = blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss' Esss m := by
  funext Y t
  unfold blockStepV blockStepG slotChs
  rw [hchains m hm]

/-- **The block functor's premise bundle transports from the LEAF's
chains to the REAL ones.**  `blockModelAt_of_stages` asks for
`BlockChainsOk` at the members' real field readings, while every stage
supplies it at the dummy former's; they agree because an X-chain reads
a recursive position through its slot (the field's target) and an
ordinary one through the domain itself, which the two readings share
(`hord`). -/
theorem blockChainsOk_congr_ord {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {rsss : Nat → List (List Bool)}
    {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Fsss' Esss : Nat → List (List AnnotTerm)}
    (hlen : ∀ m, m < k → (Fsss m).length = (Fsss' m).length)
    (hlenj : ∀ m, m < k → ∀ j, j < (Fsss m).length →
      ((Fsss m).getD j []).length = ((Fsss' m).getD j []).length)
    (hord : ∀ m, m < k → ∀ j, j < (Fsss m).length → ∀ l, l < ((Fsss m).getD j []).length →
      ((rsss m).getD j []).getD l false = false →
      ((Fsss m).getD j []).getD l default = ((Fsss' m).getD j []).getD l default)
    (h : BlockChainsOk (V := V) k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) :
    BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss' Esss := by
  have hchains : ∀ m, m < k →
      chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) (Esss m)
        = chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss' m)
            (Esss m) :=
    fun m hm => chainsXBI_congr_ord (hlen m hm) (hlenj m hm) (hord m hm)
  refine ⟨h.hI, fun Y hY m hm t ht => ?_, fun Y hY m hm t ht j hj => ?_⟩
  · have := h.hok Y hY m hm t ht
    unfold slotChs at this ⊢
    rw [← hchains m hm]; exact this
  · -- the slots fit: the chain's entries are the same terms
    have hjl : j < (Fsss m).length := by rw [hlen m hm]; exact hj
    have := h.hfit Y hY m hm t ht j hjl
    refine slotsFitXB_congr_ord (hlenj m hm j hjl) ?_ this
    exact fun l hl hr => hord m hm j hjl l hl (by rwa [Nat.zero_add] at hr)

end ConLeche.Model
