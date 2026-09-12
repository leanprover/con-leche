module

public import ConLeche.Model.Inductives.MutualRecRead
public import ConLeche.Model.Inductives.MutualRecPre2
public section

/-!
# The member recursor's leaf (task #278, M2.3)

Member `mm`'s recursor `T_mm.rec` is the λ-tower over its STORED type's
binder data (`mutualRecDataAV`: parameters, the `k` motives, the `n`
minors, member `mm`'s index telescope, the major) whose body is the
AUXILIARY recursor — the fixpoint route's leaf `nativeRecAVI` at the
auxiliary binder data (`auxRecDataAV`) — applied to the parameters,
the motive dispatch `motDispAV` (the block's `k` motives dispatched on
the tag, `Model/Inductives/MutualDisp.lean`), the minors unchanged,
the tagged tuple `⟨inj mm ⟨ı⃗⟩⟩` of the index variables, and the major.
Its typing and its rule laws are the fixpoint route's laws at that
data, read back through the dispatch's computation law.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- **The auxiliary recursor's leaf** at the block's data (`nativeRecAVI`
at `auxRecDataAV`, elimination level `ℓ`, sort `s`). -/
@[expose] def auxRecAV (m : EnvModel V env) (ψ : Name → Nat) (ℓ W w nP s : Nat) (elimL : Level)
    (pps : List (Nat × Nat × AnnotTerm)) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (FssR Fss₀ Ess' : List (List AnnotTerm)) (mems : Nat → Nat) (tgts : Nat → Nat → Nat)
    (cds : List CtorDatumR) : AnnotTerm :=
  nativeRecAVI ℓ w nP FssR Ess' (auxIds W Idss) rss tlss Eiss'
    (auxRecDataAV m ψ W w nP elimL pps Idss rss tlss Eiss' Fss₀ Ess' mems tgts cds) s

/-- **The member recursor's body** at the frame `(p⃗, M⃗, S⃗, ı⃗, t)`
(`D = k + n + nIdx + 1` binders below the parameters): the auxiliary
recursor at the parameters, the dispatch (its motives at
`bvar (mOff + k - 1 - m')`, `mOff = n + nIdx + 1`), the minors, the
tagged tuple of the index variables, and the major. -/
@[expose] def mutualRecBodyAV (ℓ W w nP k n nIdx mm : Nat) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss₀ Ess' : List (List AnnotTerm))
    (auxLeaf : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (auxLeaf.liftN (k + n + nIdx + 1) 0)
    (paramBvarsAt nP (nP + (k + n + nIdx + 1)) ++
      [motDispAV ℓ W w (k + n + nIdx + 1) (n + nIdx + 1) k Idss rss tlss Eiss' Fss₀ Ess'] ++
      ((List.range n).map fun J => AnnotTerm.bvar (nIdx + 1 + n - 1 - J)) ++
      [tagTupleAV W mm (k + n + nIdx + 1) Idss (idxVarsAV nIdx 1)] ++
      [AnnotTerm.bvar 0])

/-- **Member `mm`'s recursor leaf**: the λ-tower over its stored type's
binder data (bit `b`, the elimination bit) with the body above. -/
@[expose] def mutualRecAVI (m : EnvModel V env) (ψ : Name → Nat) (ℓ W w nP s b : Nat)
    (elimL : Level) (Ls : List AnnotTerm) (nIdxs : List Nat) (pps : List (Nat × Nat × AnnotTerm))
    (ipss : List (List (Nat × Nat × AnnotTerm))) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (FssR Fss₀ Ess' : List (List AnnotTerm))
    (mems : Nat → Nat) (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (mm : Nat) : AnnotTerm :=
  mkLamsC b (mutualRecDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts mm)
    (mutualRecBodyAV ℓ W w nP Ls.length cds.length (nIdxs.getD mm 0) mm Idss rss tlss Eiss' Fss₀ Ess'
      (auxRecAV m ψ ℓ W w nP s elimL pps Idss rss tlss Eiss' FssR Fss₀ Ess' mems tgts cds))

end ConLeche.Model
