module

public import ConLeche.Model.Inductives.BlockLeafOk
import ConLeche.Model.Inductives.BlockWitness
public section

/-!
# Kit for the uniform block install's assembly (task #315 M3)

`FixAssemblyKit.lean`'s X-chain half at `k` members: the block
functor's whole premise bundle (`BlockChainsOk`, lane S's
`Semantics/Tower/BlockFamI.lean`) and the chains' bit-validity, from
the per-member, per-constructor chain facts.

The closure at a `Type`-valued block ((W) at tuples) is
`BlockWitness.blockClosed_of` — the block's container presentation,
shapes = the shadow tuples TAGGED by (component, constructor),
positions = the recursive fields' telescope spines, targets = the
calls' (member, index tuple) pairs — exactly as it is at `k = 1` a
call to `FixWitness.fixClosed_of`.  At a `Prop`-valued block the
closure is free (`blockPhi_closed_zero`).
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
        ((Fsss m).getD j []) ((Eisss m).getD j []) ((Esss m).getD j []))
    :
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
  have hclosed : ∃ L, IsClosedTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) L := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · exact blockPhi_closed_zero_of hok
    · exact blockClosed_of (Nat.pos_iff_ne_zero.mp hw) hI hlenF hrss hC
  refine ⟨⟨hI, hok, fun Y hY m hm t ht j hj => ?_, hclosed⟩,
    fun Y hY m hm t ht chain hc => ?_⟩
  · rw [hrss m hm j (by rw [← hlenF m hm]; exact hj)]
    exact (blockChain_of hI hm hY ht (hC m hm j (by rw [← hlenF m hm]; exact hj))).2
  · obtain ⟨j, hj, rfl⟩ := hmem m hm chain hc
    exact blockChainValid_of hI hIV hY (hC m hm j hj) (hCV m hm j hj)

end ConLeche.Model
