module

public import ConLeche.Model.Inductives.MutualDisp
import ConLeche.Model.Inductives.FixRecKFrame
public import ConLeche.Model.Inductives.FixRecPre
import ConLeche.Model.Inductives.FixLeafOk
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only (`PropWhen.never.isNever`). -/
import all ConLeche.Kernel.PropWhen
public section

/-!
# The auxiliary recursor's binder data (task #278, M2.3)

The mutual block's auxiliary family is the fixpoint route's family at
the ONE index `tagTyAV W Idss` (`Semantics/Tower/MutualLeafI.lean`), so
its recursor is the fixpoint route's leaf `nativeRecAVI` at the binder
data the fixpoint route SPELLS from a former leaf and constructor data
(`fixRecDataAVL`, task #278 M2.2).  Here: the auxiliary former's closed
leaf `auxFormerAV` (the fixpoint route's `nativeTyAVI` over the
parameters and the tag binder), the constructors' data at the TAGGED
index expressions (`auxCtorData`: every constructor's index expressions
become the one tagged tuple, every recursive slot's likewise), and the
auxiliary binder data `auxRecDataAV`.  The premise `FixPre` for it is
assembled from `fixPre_ofL` with SEMANTIC premises — there is no stored
auxiliary recursor type to read — the first of which are here: the
former leaf's frame independence (`auxFormer_hleafT`) and the auxiliary
motive's domain reading (`auxMotive_interp`: the auxiliary motive space
of the dispatch, `auxMotSp`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The spellings -/

/-- The tag index datum: the auxiliary family's ONE index binder. -/
@[expose] def tagIps (W : Nat) (Idss : List (List AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  [(W, W, tagTyAV W Idss)]

omit [SetTheory V] in
theorem tagIps_doms (W : Nat) (Idss : List (List AnnotTerm)) :
    (tagIps W Idss).map (·.2.2) = auxIds W Idss := rfl

/-- The auxiliary former's closed leaf: `λ p⃗ (i : tag), aux ⟨i⟩` — the
fixpoint route's former leaf over the parameters and the tag binder. -/
@[expose] def auxFormerAV (W w : Nat) (pps : List (Nat × Nat × AnnotTerm))
    (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss₀ Ess' : List (List AnnotTerm)) : AnnotTerm :=
  nativeTyAVI [] W w (pps ++ tagIps W Idss) (auxIds W Idss) rss tlss Eiss' Fss₀ Ess'

/-- A constructor datum at the tagged index expressions: constructor
`J` of member `mem` with fields `nF` gets the one index expression
`⟨inj mem ⟨e⃗_J⟩⟩` (its expressions scoped `nF` binders below the
parameters), and its recursive slot `i` (targeting member `tgts i`
under a telescope of length `tl_i.length`) the one expression
`⟨inj (tgts i) ⟨e⃗_i⟩⟩` — `mutualEss`/`mutualEiss` per datum. -/
@[expose] def auxCtorDatum (W : Nat) (Idss : List (List AnnotTerm)) (mem : Nat) (tgts : Nat → Nat)
    (cd : CtorDatumR) : CtorDatumR :=
  (cd.1, cd.2.1, cd.2.2.1, [tagTupleAV W mem cd.2.1 Idss cd.2.2.2.1], cd.2.2.2.2.1,
    (List.range cd.2.1).map fun i =>
      [tagTupleAV W (tgts i) (i + (cd.2.2.2.2.2.2.getD i []).length) Idss
        (cd.2.2.2.2.2.1.getD i [])],
    cd.2.2.2.2.2.2)

/-- The block's constructor data at the tagged expressions, in block
order (`mems J` the member of constructor `J`, `tgts J i` the target of
its slot `i`). -/
@[expose] def auxCtorData (W : Nat) (Idss : List (List AnnotTerm)) (mems : Nat → Nat)
    (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) : List CtorDatumR :=
  (List.range cds.length).map fun J => auxCtorDatum W Idss (mems J) (tgts J) (cds.getD J default)

omit [SetTheory V] in
theorem auxCtorData_length (W : Nat) (Idss : List (List AnnotTerm)) (mems : Nat → Nat)
    (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) :
    (auxCtorData W Idss mems tgts cds).length = cds.length := by
  simp [auxCtorData]

omit [SetTheory V] in
theorem auxCtorData_getElem? (W : Nat) (Idss : List (List AnnotTerm)) (mems : Nat → Nat)
    (tgts : Nat → Nat → Nat) (cds : List CtorDatumR) (J : Nat) :
    (auxCtorData W Idss mems tgts cds)[J]?
      = (cds[J]?).map fun cd => auxCtorDatum W Idss (mems J) (tgts J) cd := by
  unfold auxCtorData
  rw [List.getElem?_map]
  by_cases hJ : J < cds.length
  · rw [List.getElem?_range hJ, List.getElem?_eq_getElem hJ]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl

/-- **The auxiliary recursor's binder data**: the fixpoint route's
data at the auxiliary former's leaf, the tag index, and the tagged
constructor data. -/
@[expose] def auxRecDataAV (m : EnvModel V env) (ψ : Name → Nat) (W w nP : Nat) (elimL : Level)
    (pps : List (Nat × Nat × AnnotTerm)) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss₀ Ess' : List (List AnnotTerm)) (mems : Nat → Nat) (tgts : Nat → Nat → Nat)
    (cds : List CtorDatumR) : List (Nat × Nat × AnnotTerm) :=
  fixRecDataAVL m ψ (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') nP 1 elimL pps
    (tagIps W Idss) (auxCtorData W Idss mems tgts cds)

/-! ## The former leaf -/

omit [SetTheory V] in
theorem domsBelow_append {k : Nat} :
    ∀ {ds ds' : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds → DomsBelow (k + ds.length) ds' →
      DomsBelow k (ds ++ ds')
  | [], _, _, h' => by simpa using h'
  | d :: ds, ds', h, h' => by
    refine ⟨h.1, domsBelow_append h.2 ?_⟩
    rw [List.length_cons, show k + (ds.length + 1) = k + 1 + ds.length by omega] at h'
    exact h'

omit [SetTheory V] in
/-- The tag type is bounded at the parameters when every member's index
chain is. -/
theorem tagTyAV_below {W nP : Nat} {Idss : List (List AnnotTerm)}
    (h : ∀ Ids ∈ Idss, FieldsBelow nP Ids) :
    Term.bvarsBelow nP (tagTyAV W Idss).erase := by
  unfold tagTyAV
  refine sumBodyAV_below (fun Fs hFs => ?_) (fun h => absurd rfl h)
  obtain ⟨Ids, hIds, rfl⟩ := List.mem_map.mp hFs
  exact FieldsBelow_append_idxEq (h Ids hIds) (fun e he => nomatch he)

omit [SetTheory V] in
/-- **The auxiliary former's leaf is closed.** -/
theorem auxFormerAV_below {W w nP : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hp : DomsBelow 0 pps) (hlenP : pps.length = nP) (hIds : ∀ Ids ∈ Idss, FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss₀ Ess',
      FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow 0 (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess').erase := by
  unfold auxFormerAV
  have hdrop : (pps ++ tagIps W Idss).drop nP = tagIps W Idss := by
    rw [← hlenP, List.drop_left]
  refine nativeTyAVI_below (nP := nP) (nIdx := 1) ?_ (by simp [hlenP, tagIps]) ?_ hchains ?_
  · refine domsBelow_append hp ?_
    rw [hlenP, Nat.zero_add]
    exact ⟨tagTyAV_below hIds, trivial⟩
  · rw [hdrop]; rfl
  · rw [hdrop]; rfl

/-- **The auxiliary former's leaf is frame-independent** — the
`hleafT` premise of the fixpoint route's K-frame lemmas at the
auxiliary family. -/
theorem auxFormer_hleafT {W w nP : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)}
    (hcl : Term.bvarsBelow 0 (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess').erase)
    (ρp : Nat → V) :
    ∀ σ : Nat → V, interp V σ (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess')
      = interp V (fun k => ρp (k + nP))
          (nativeTyAVI [] W w (pps ++ tagIps W Idss) ((tagIps W Idss).map (·.2.2)) rss tlss Eiss'
            Fss₀ Ess') :=
  fun σ => interp_closed (V := V) hcl σ _

/-! ## The auxiliary motive -/

/-- **The auxiliary motive's domain reads the auxiliary motive space**
`Π (i : tag) (x : aux ⟨i⟩), Sort ℓ` at a parameter valuation. -/
theorem auxMotive_interp {ψ : Name → Nat} {elimL : Level} {ℓ W w nP : Nat}
    (hℓ : elimL.eval ψ = ℓ) {pps : List (Nat × Nat × AnnotTerm)} (hlenP : pps.length = nP)
    {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss₀ Ess' : List (List AnnotTerm)} {ρp : Nat → V}
    (hsatP : Sat V ((pps.map (·.2.2)).reverse) ρp)
    (hT : TagOk W ρp Idss)
    (hX : XChainsOk [] W w ρp (auxIds W Idss) rss tlss Eiss' Fss₀ Ess')
    (hcl : Term.bvarsBelow 0 (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess').erase) :
    interp V ρp (motiveAVIL (auxFormerAV W w pps Idss rss tlss Eiss' Fss₀ Ess') ψ nP 1 elimL
        (tagIps W Idss))
      = auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss₀ Ess' := by
  have hleafT := auxFormer_hleafT (nP := nP) hcl ρp
  have hTv := tagTyAV_facts hT
  unfold motiveAVIL auxMotSp
  rw [ConLeche.Model.interp_mkPisAV_piTele (v := ℓ + 1) (gds := rebit (pwBit ψ PropWhen.never) (tagIps W Idss))
    (fun d hd => by
      rw [mem_rebit hd]
      exact ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ),
        fun h => absurd h (Nat.succ_ne_zero _)⟩)
    (B := fun is' => piR (ℓ + 1)
      (SetTheory.app (auxFamI [] W w ρp Idss rss tlss Eiss' Fss₀ Ess') (tupW W is'))
      fun _ => (univ ℓ : V)) (acc := []) ?_, rebit_map_dom, tagIps_doms]
  · unfold auxIds
    simp only [teleOfFields_cons, teleOfFields_nil, piTele, hTv.1, List.nil_append]
    rfl
  · intro as hsp
    rw [rebit_map_dom, tagIps_doms] at hsp
    have hlenAs : as.length = 1 := by rw [hsp.length_eq]; rfl
    rw [interp_pi, hℓ, List.nil_append]
    have h := fixFamAt_ofL (nIdx := 1) hlenP rfl hsatP hX hleafT hlenAs [] hsp
    rw [consList_nil, List.length_nil, Nat.zero_add] at h
    rw [h, piR_congr_bit (v' := ℓ + 1)
      ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ), fun h => absurd h (Nat.succ_ne_zero _)⟩]
    rfl

end ConLeche.Model
