module

public import ConLeche.Model.Inductives.MutualShadow
public import ConLeche.Model.Inductives.FixRealChains
public import ConLeche.Model.Inductives.FixAssemblyKit
public import ConLeche.Semantics.Tower.MutualLeafFacts
public section

/-!
# The auxiliary family's chains (task #278, M2.4)

The mutual block's members are fibres of ONE fixpoint-route family at
the tag — the tagged union of the members' index towers
(`Semantics/Tower/MutualLeafI.lean`).  This module spells that
family's chain data off the constructors' readings
(`MutualData.lean`) and proves what the fixpoint route's premise
theorem (`fixPre_of`) asks of it:

* the chain data: the REAL chains `mutFss` (constructor `J`'s field
  entries as read at the members' leaves), the X-source chains
  `mutFss0` — the real ones with `Sort 0` at the recursive slots,
  which is all the X-chain ever reads there (`xEntry` replaces a
  recursive slot by `slotXI`), so the X-chains mention no member —
  the recursive positions `mutRss`, the reflexive telescopes
  `mutTlss`, and the TAGGED index expressions `mutEss'`/`mutEiss'`
  (`mutualEss`/`mutualEiss`: a member occurrence `T_{m'} p⃗ e⃗` is the
  auxiliary family at `⟨inj m' ⟨e⃗⟩⟩`);
* the walk's inputs at every constructor (`ChainFacts` at the
  auxiliary family, `mutualChainFacts_at`) and, from them,
  `XChainsOk`, `FixChainsOkI` and `ChainsRealI` for the whole block
  (`mutualChainFacts_of`).

The one new step over the fixpoint route is the TAG: a slot's index
fit is `SpineFit ρp [tagTyAV] [inj m' ⟨e⃗⟩]`, which is the member's
own fit through `tagTuple_mem`, and a tagged tuple's grading is
`tagTupleAV_facts` at the frame the slot is read in.  That the tagged
tuples mention no recursive slot is `NoBVar_liftN`: their head is the
member's tupler lifted past every field read so far.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The chain data -/

variable (nP n : Nat)

/-- Constructor `J`'s REAL field chain: its field entries as read at
the members' leaves. -/
@[expose] def mutFss (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  (List.range n).map fun J => ((dsF J ψ).drop nP).map (·.2.2)

/-- Constructor `J`'s X-SOURCE chain: the real one with `Sort 0` at
the recursive slots — the X-chain reads a recursive slot as the
family's (`xEntry`), so this chain mentions no member. -/
@[expose] def mutFss0 (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  (List.range n).map fun J =>
    shadowFs nP (kindsOf (ksF J)) (nFs J) (((dsF J ψ).drop nP).map (·.2.2))

/-- The recursive positions, per constructor. -/
@[expose] def mutRss (ksF : Nat → List (RecFieldKind × Nat)) : List (List Bool) :=
  (List.range n).map fun J => rsOf (kindsOf (ksF J))

/-- The reflexive telescopes, per constructor. -/
@[expose] def mutTlss (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (ψ : Name → Nat) : List (List (List (Nat × Nat × AnnotTerm))) :=
  (List.range n).map fun J => tssF J ψ

/-- The constructors' OWN index readings, per constructor. -/
@[expose] def mutEss0 (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  (List.range n).map fun J => esF J ψ

/-- The recursive slots' OWN index readings, per constructor. -/
@[expose] def mutEiss0 (eissF : Nat → (Name → Nat) → List (List AnnotTerm)) (ψ : Name → Nat) :
    List (List (List AnnotTerm)) :=
  (List.range n).map fun J => eissF J ψ

/-- Each constructor's own member. -/
@[expose] def mutMems (memF : Nat → Nat) : List Nat := (List.range n).map memF

/-- Each constructor's field count. -/
@[expose] def mutNFs (nFs : Nat → Nat) : List Nat := (List.range n).map nFs

/-- Each constructor's recursive slots' target members. -/
@[expose] def mutTgts (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat) :
    List (List Nat) :=
  (List.range n).map fun J => (List.range (nFs J)).map (tgtAt (ksF J))

variable {nP n}

omit [SetTheory V] in
theorem mutFss_length {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat} :
    (mutFss nP n dsF ψ).length = n := by simp [mutFss]

omit [SetTheory V] in
theorem mutFss_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat}
    {J : Nat} (hJ : J < n) :
    (mutFss nP n dsF ψ).getD J [] = ((dsF J ψ).drop nP).map (·.2.2) := by
  simp [mutFss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutFss0_length {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat} {ψ : Name → Nat} :
    (mutFss0 nP n dsF ksF nFs ψ).length = n := by simp [mutFss0]

omit [SetTheory V] in
theorem mutFss0_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) :
    (mutFss0 nP n dsF ksF nFs ψ).getD J []
      = shadowFs nP (kindsOf (ksF J)) (nFs J) (((dsF J ψ).drop nP).map (·.2.2)) := by
  simp [mutFss0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutRss_getD {ksF : Nat → List (RecFieldKind × Nat)} {J : Nat} (hJ : J < n) :
    (mutRss n ksF).getD J [] = rsOf (kindsOf (ksF J)) := by
  simp [mutRss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutTlss_getD {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ψ : Name → Nat} {J : Nat} (hJ : J < n) :
    (mutTlss n tssF ψ).getD J [] = tssF J ψ := by
  simp [mutTlss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutEss0_length {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} :
    (mutEss0 n esF ψ).length = n := by simp [mutEss0]

omit [SetTheory V] in
theorem mutEss0_getD {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) : (mutEss0 n esF ψ).getD J [] = esF J ψ := by
  simp [mutEss0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutEiss0_length {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} :
    (mutEiss0 n eissF ψ).length = n := by simp [mutEiss0]

omit [SetTheory V] in
theorem mutEiss0_getD {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat}
    {J : Nat} (hJ : J < n) : (mutEiss0 n eissF ψ).getD J [] = eissF J ψ := by
  simp [mutEiss0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutMems_getD {memF : Nat → Nat} {J : Nat} (hJ : J < n) :
    (mutMems n memF).getD J 0 = memF J := by
  simp [mutMems, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutNFs_getD {nFs : Nat → Nat} {J : Nat} (hJ : J < n) :
    (mutNFs n nFs).getD J 0 = nFs J := by
  simp [mutNFs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutTgts_getD {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat} {J i : Nat}
    (hJ : J < n) (hi : i < nFs J) :
    ((mutTgts n ksF nFs).getD J []).getD i 0 = tgtAt (ksF J) i := by
  simp [mutTgts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ,
    List.getElem?_range hi]

/-! ## The tagged index expressions -/

/-- The constructors' TAGGED index expressions. -/
@[expose] def mutEss' (W : Nat) (Idss : List (List AnnotTerm)) (memF nFs : Nat → Nat)
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) : List (List AnnotTerm) :=
  mutualEss W Idss (mutMems n memF) (mutNFs n nFs) (mutEss0 n esF ψ)

/-- The recursive slots' TAGGED index expressions. -/
@[expose] def mutEiss' (W : Nat) (Idss : List (List AnnotTerm))
    (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat)
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm)) (ψ : Name → Nat) :
    List (List (List AnnotTerm)) :=
  mutualEiss W Idss (mutTgts n ksF nFs) (mutTlss n tssF ψ)
    (mutEiss0 n eissF ψ)

omit [SetTheory V] in
theorem mutEss'_getD {W : Nat} {Idss : List (List AnnotTerm)} {memF nFs : Nat → Nat}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} {J : Nat} (hJ : J < n) :
    (mutEss' (n := n) W Idss memF nFs esF ψ).getD J []
      = [tagTupleAV W (memF J) (nFs J) Idss (esF J ψ)] := by
  unfold mutEss' mutualEss
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [mutEss0_length]; exact hJ)]
  simp only [Option.map_some, Option.getD_some]
  rw [mutMems_getD hJ, mutNFs_getD hJ, mutEss0_getD hJ]

omit [SetTheory V] in
theorem mutEss'_length {W : Nat} {Idss : List (List AnnotTerm)} {memF nFs : Nat → Nat}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} :
    (mutEss' (n := n) W Idss memF nFs esF ψ).length = n := by
  unfold mutEss' mutualEss
  rw [List.length_map, List.length_range, mutEss0_length]

omit [SetTheory V] in
theorem mutEiss'_getDJ {W : Nat} {Idss : List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) (hlen : (eissF J ψ).length = nFs J) :
    (mutEiss' (n := n) W Idss ksF nFs tssF eissF ψ).getD J []
      = (List.range (nFs J)).map fun i =>
          [tagTupleAV W (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length) Idss
            ((eissF J ψ).getD i [])] := by
  unfold mutEiss' mutualEiss
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [mutEiss0_length]; exact hJ)]
  simp only [Option.map_some, Option.getD_some]
  rw [mutEiss0_getD hJ, hlen]
  apply List.map_congr_left
  intro i hi
  rw [mutTgts_getD hJ (List.mem_range.mp hi), mutTlss_getD hJ]

omit [SetTheory V] in
theorem mutEiss'_getD {W : Nat} {Idss : List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} {J i : Nat}
    (hJ : J < n) (hi : i < nFs J) (hlen : (eissF J ψ).length = nFs J) :
    ((mutEiss' (n := n) W Idss ksF nFs tssF eissF ψ).getD J []).getD i []
      = [tagTupleAV W (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length) Idss
          ((eissF J ψ).getD i [])] := by
  rw [mutEiss'_getDJ hJ hlen, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

omit [SetTheory V] in
theorem mutEiss'_lengthJ {W : Nat} {Idss : List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) (hlen : (eissF J ψ).length = nFs J) :
    ((mutEiss' (n := n) W Idss ksF nFs tssF eissF ψ).getD J []).length = nFs J := by
  rw [mutEiss'_getDJ hJ hlen, List.length_map, List.length_range]

/-! ## Kit: the shadow chain, application spines, tagged slots -/

omit [SetTheory V] in
theorem shadowFs_getD {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AnnotTerm} {i : Nat}
    (hi : i < nF) :
    (shadowFs nP ks nF Fs).getD i default
      = if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default := by
  rw [List.getD_eq_getElem?_getD, shadowFs_getElem? hi]
  rfl

omit [SetTheory V] in
/-- The shadow chain is its own shadow. -/
theorem shadowFs_shadowFs {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AnnotTerm} :
    shadowFs nP ks nF (shadowFs nP ks nF Fs) = shadowFs nP ks nF Fs := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < nF
  · rw [shadowFs_getElem? hi, shadowFs_getElem? hi, shadowFs_getD hi]
    split <;> rfl
  · rw [List.getElem?_eq_none (by rw [shadowFs_length]; omega),
      List.getElem?_eq_none (by rw [shadowFs_length]; omega)]

omit [SetTheory V] in
/-- An application mentions no excluded slot when its head and its
arguments do not. -/
theorem NoBVar_mkAppN {P : Nat → Prop} {f : AnnotTerm} (hf : NoBVar P f) :
    ∀ (as : List AnnotTerm), (∀ a ∈ as, NoBVar P a) → NoBVar P (AnnotTerm.mkAppN f as)
  | [], _ => hf
  | a :: as, ha => by
    refine NoBVar_mkAppN (f := .app f a) ⟨hf, ha a List.mem_cons_self⟩ as ?_
    intro b hb
    exact ha b (List.mem_cons_of_mem _ hb)

omit [SetTheory V] in
/-- **A tagged tuple mentions no recursive slot below the field it
sits under**: its head is the member's tupler lifted past every field
and telescope binder read so far, and the excluded slots all lie
below that lift. -/
theorem NoBVar_tagTupleAV {P : Nat → Prop} {d W m' : Nat} {Idss : List (List AnnotTerm)}
    {Es : List AnnotTerm} (hP : ∀ j, P j → j < d) (hE : ∀ E ∈ Es, NoBVar P E) :
    NoBVar P (tagTupleAV W m' d Idss Es) :=
  NoBVar_mkAppN (NoBVar_liftN_zero hP _) Es hE

/-! ## The auxiliary family's chain facts at one constructor -/

/-- The family leaf's argument spine, read at a frame: a Pi-tower leaf
applied to the parameter variables and index expressions is graded
only if the expressions' values fit the leaf's index telescope
(`fixChainFacts_of`'s `fitAt`, with the leaf and its telescope
explicit — at a mutual block a recursive slot's leaf is the TARGET
member's). -/
theorem leafSpineFit {L : AnnotTerm} {pps : List (Nat × Nat × AnnotTerm)} {nP nIdx w : Nat}
    {ρp : Nat → V} {σas : List V} {e : Nat} {Eis : List AnnotTerm}
    (hlen : pps.length = nP + nIdx) (hLclosed : Term.bvarsBelow 0 L.erase)
    (hL : ∃ B, L = mkLamsC (w + 1) pps B)
    (he : σas.length = e) (hEl : Eis.length = nIdx)
    (hokA : WellDenoted V (consList σas ρp)
      (AnnotTerm.mkAppN L (paramBvarsAt nP (nP + e) ++ Eis))) :
    (∀ E ∈ Eis, WellDenoted V (consList σas ρp) E) ∧
    SpineFit ρp ((pps.drop nP).map (·.2.2)) (Eis.map (interp V (consList σas ρp))) := by
  obtain ⟨-, hargs⟩ := WellDenoted.mkAppN_inv hokA
  refine ⟨fun E hE => hargs E (List.mem_append_right _ hE), ?_⟩
  obtain ⟨B, hB⟩ := hL
  have hK : Term.bvarsBelow 0 (mkLamsC (w + 1) pps B).erase := by rw [← hB]; exact hLclosed
  have hf : interp V (consList σas ρp) L
      = interp V (fun j => ρp (j + nP)) (mkLamsC (w + 1) pps B) := by
    rw [hB]; exact interp_closed (V := V) hK _ _
  have hlenArgs : (paramBvarsAt nP (nP + e) ++ Eis).length = nP + nIdx := by
    simp [paramBvarsAt, hEl]
  have hfit := spineFit_of_wellDenoted_lams (u := w + 1) (Nat.succ_ne_zero _) (b := B)
    (args := paramBvarsAt nP (nP + e) ++ Eis) (ds := pps)
    (σ := fun j => ρp (j + nP)) (ρ := consList σas ρp) (f := L)
    (by rw [hlenArgs, hlen]; exact Nat.le_refl _) hokA hf
  rw [hlenArgs, List.take_of_length_le (by rw [hlen]; exact Nat.le_refl _),
    ← List.take_append_drop nP pps, List.map_append, List.map_append] at hfit
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv hfit
  have hlen₁ : as₁.length = nP := by
    rw [h1.length_eq, List.length_map, List.length_take, hlen]; omega
  have hps : (paramBvarsAt nP (nP + e)).map (interp V (consList σas ρp))
      = (List.range nP).reverse.map ρp := by
    apply map_paramBvarsAt_interp
    intro j
    rw [← he]; exact consList_apply_add σas ρp j
  obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁]; simp [paramBvarsAt])
  rw [hps, consList_range_reverse] at h2
  exact h2

/-- **A slot's fit at the tag**: a member's slot fit becomes the
auxiliary family's at the ONE tagged index expression. -/
theorem slotFit_tag {u W w : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (hTag : TagOk W ρp Idss) {m' : Nat} {IdsT : List AnnotTerm} (hm : Idss[m']? = some IdsT)
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} {as : List V} {i : Nat}
    (hlen : as.length = i) (h : SlotFit u w ρp IdsT tl Eis as) :
    SlotFit W w ρp (auxIds W Idss) tl [tagTupleAV W m' (i + tl.length) Idss Eis] as := by
  refine ⟨h.1, h.2.1, fun bs hsp => ?_⟩
  obtain ⟨hok, hfit⟩ := h.2.2 bs hsp
  have hlenB : bs.length = tl.length := by rw [hsp.length_eq, List.length_map]
  have hfr : shiftE (i + tl.length) 0 (consList (as ++ bs) ρp) = ρp := by
    rw [← hlen, ← hlenB, ← List.length_append]
    exact shiftE_consList _ ρp
  obtain ⟨hval, hokT⟩ := tagTupleAV_facts hTag hm hfr hok hfit
  refine ⟨fun E hE => by rw [List.mem_singleton] at hE; subst hE; exact hokT, ?_⟩
  rw [List.map_singleton, hval]
  refine ⟨?_, trivial⟩
  rw [(tagTyAV_facts hTag).1]
  exact tagTuple_mem hTag hm hfit

set_option maxHeartbeats 3200000 in
/-- **The walk's inputs at one constructor of a mutual block**
(`fixChainFacts_of` at the auxiliary family): the X-source chain is
the real one with `Sort 0` at the recursive slots, the index
expressions are the TAGGED ones, and the index telescope is the tag's.
`hmem`/`hTgt` are what the block's former stage supplies: the
constructor's own member and every member a field targets are read at
the auxiliary family's tag position, with their leaves the Pi-towers
over their own parameter-and-index data. -/
theorem mutualChainFacts_at (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {members : List (Name × Nat × Nat)} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nF nIdx mem : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₀ : Env} {caps : IndCaps}
    {sorts : List Level} {ks : List (RecFieldKind × Nat)}
    (hCtor : ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) env memberNames T lps nP nIdx
      resSort isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hProp : isProp = true → (Level.isEquiv resSort .zero == some true) = true)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {lvlsAll : (Name → Nat) → List Nat}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll lvlsAll)
    (hleafT : ∀ ψ, ∃ B, mp.base2.acval T ψ = mkLamsC (resSort.eval ψ + 1) (ppsAll ψ) B)
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hD : MutualCtorDataI mp.base2 env₀ members T lps cvCa nP nF nIdx resSort isProp large
      idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    {W : Nat} {Idss : List (List AnnotTerm)} (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp)
    (hTag : TagOk W ρp Idss)
    (hmem : Idss[mem]? = some (((ppsAll ψ).drop nP).map (·.2.2)))
    (hTgt : ∀ i, i < nF → (kindAt ks i = .recursive ∨ kindAt ks i = .reflexive) →
      ∃ (ppsT : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ppsT.length = nP + mutualNIdxOf members (tgtAt ks i) ∧
        mp.base2.acval (mutualNameOf members (tgtAt ks i)) ψ
          = mkLamsC (resSort.eval ψ + 1) ppsT B ∧
        Idss[tgtAt ks i]? = some ((ppsT.drop nP).map (·.2.2))) :
    ChainFacts W (resSort.eval ψ) nP nF ρp (auxIds W Idss) (kindsOf ks) (tss ψ)
      (shadowFs nP (kindsOf ks) nF (((ds ψ).drop nP).map (·.2.2)))
      ((List.range nF).map fun i =>
        [tagTupleAV W (tgtAt ks i) (i + ((tss ψ).getD i []).length) Idss ((Eiss ψ).getD i [])])
      [tagTupleAV W mem nF Idss (Es ψ)] := by
  -- the openings, the opened record
  obtain ⟨crest, hopP, hopX⟩ := hD.opens
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.mutual_ctor_typeWF hCtor
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  have hO : Opened mp.base2 ψ (nP + nF) cvCa.type (fvsP ++ xFvs) xrest
      (((ds ψ).map (·.2.2)).reverse) (ctorBodyAVI mp.base2 T nP nF ψ (Es ψ)) :=
    opened_of_peel hopAll hcf hcb (hD.read ψ) (hD.len ψ) (hD.okTy ψ)
  have hlenDs := hD.len ψ
  have hlenFs : ((((ds ψ).drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  -- the parameter frames identified
  have hiff := (mutualCtorFrames hμ mp hCtor hfT hProp hFD hD.toCtorDataI hleafT).1 ψ ρp
  have hρp' : Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρp := hiff.mp hρp
  -- the shadow gradings
  obtain ⟨hkey, hkeyR⟩ := mutualShadowGrading hμ mp hCtor hProp hD ψ
  -- the tagged index expressions, positionally
  have hEissGet : ∀ i, i < nF →
      ((List.range nF).map fun i =>
        [tagTupleAV W (tgtAt ks i) (i + ((tss ψ).getD i []).length) Idss
          ((Eiss ψ).getD i [])]).getD i []
        = [tagTupleAV W (tgtAt ks i) (i + ((tss ψ).getD i []).length) Idss
            ((Eiss ψ).getD i [])] := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  -- a recursive variable is a leaf of no later domain nor of the residual
  have hrecGet : ∀ i, recAt nP (kindsOf ks) (nP + i) → i < nF → ∃ x, xFvs[i]? = some x ∧
      (∀ y ∈ xFvs.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
      xrest.mentionsFvar (nP + i) = false := by
    intro i hr hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    rcases (recAt_kindsOf hD.ksLen hi).mp hr with hk | hk
    · obtain ⟨-, -, -, -, hlater, hres⟩ := hD.opened.recF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
    · obtain ⟨-, -, -, -, -, -, -, -, -, hlater, hres⟩ := hD.opened.reflF i _ hx hk
      exact ⟨_, hx, hlater, hres⟩
  -- field `i`'s opened domain: scoped, leaf-free of the recursive
  -- variables below it
  have hdom : ∀ i, i < nF → ∃ x, xFvs[i]? = some x ∧ Expr.WScoped (nP + i) x.fvarTypeD ∧
      (∀ l ∈ x.fvarTypeD.fvarLeaves, ¬ (recAt nP (kindsOf ks) l.1 ∧ l.1 < nP + i)) := by
    intro i hi
    have hx : xFvs[i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) :=
      List.getElem?_eq_getElem _
    have hxA : (fvsP ++ xFvs)[nP + i]? = some (xFvs[i]'(by rw [hD.xLen]; exact hi)) := by
      rw [List.getElem?_append_right (by rw [hD.pLen]; omega), hD.pLen, Nat.add_sub_cancel_left]
      exact hx
    obtain ⟨-, hws, -, -, -⟩ := hO.var (nP + i) _ hxA
    refine ⟨_, hx, hws, ?_⟩
    intro l hl ⟨hr, hlt⟩
    have hge := hr.1
    obtain ⟨x', hx', hlater, -⟩ := hrecGet (l.1 - nP)
      (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
    have hmem' : (xFvs[i]'(by rw [hD.xLen]; exact hi)) ∈ xFvs.drop (l.1 - nP + 1) := by
      refine List.mem_of_getElem? (i := i - (l.1 - nP + 1)) ?_
      rw [List.getElem?_drop, show l.1 - nP + 1 + (i - (l.1 - nP + 1)) = i from by omega]
      exact hx
    exact mentionsFvar_false (hlater _ hmem') l hl (by omega)
  -- a reflexive field's opened telescope
  have hreflGet : ∀ i x, xFvs[i]? = some x → kindAt ks i = .reflexive → i < nF →
      ∃ afvs body,
        openPisAtFvars ((tss ψ).getD i []).length x.fvarTypeD (nP + i) = some (afvs, body) ∧
        (∀ k a, afvs[k]? = some a → Expr.WScoped (nP + i + k) a.fvarTypeD ∧
          (∀ l ∈ a.fvarTypeD.fvarLeaves, ¬ (recAt nP (kindsOf ks) l.1 ∧ l.1 < nP + i)) ∧
          denoteMeta mp.base2.acval env ψ (nP + i + k) a.fvarTypeD
            = some (((tss ψ).getD i []).getD k default).2.2) ∧
        Expr.WScoped (nP + i + ((tss ψ).getD i []).length) body ∧
        (∀ l ∈ body.fvarLeaves, ¬ (recAt nP (kindsOf ks) l.1 ∧ l.1 < nP + i)) ∧
        DenoteMetaSpine mp.base2.acval env ψ (nP + i + ((tss ψ).getD i []).length)
          (body.getAppArgs.drop nP) ((Eiss ψ).getD i []) := by
    intro i x hx hk hi
    obtain ⟨afvs, body, hop, -, hdoms, hsp⟩ := hD.reflOpen ψ i x hx hk
    obtain ⟨x', hx', hws, hlf⟩ := hdom i hi
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    have hleaves := openPisAtFvars_leaf_bound hop
    have hwsAll := openPisAtFvars_WScoped _ _ _ hop hws
    refine ⟨afvs, body, hop, fun k a hk' => ⟨openPisAtFvars_typeWScoped _ hop hws k a hk',
      fun l hl ⟨hr, hlt⟩ => ?_, hdoms k a hk'⟩, hwsAll.2, fun l hl ⟨hr, hlt⟩ => ?_, hsp⟩
    · rcases hleaves.1 a (List.mem_of_getElem? hk') l hl with h | h
      · exact hlf l h ⟨hr, hlt⟩
      · omega
    · rcases hleaves.2 l hl with h | h
      · exact hlf l h ⟨hr, hlt⟩
      · omega
  have hQlt : ∀ i q, recAt nP (kindsOf ks) q ∧ q < nP + i → q < nP + i := fun _ _ h => h.2
  have hQrange : ∀ i q, recAt nP (kindsOf ks) q ∧ q < nP + i → nP ≤ q ∧ q < nP + i :=
    fun _ _ h => ⟨h.1.1, h.2⟩
  have hne_refl : ∀ i, kindAt ks i = .recursive → kindAt ks i ≠ .reflexive := by
    intro i hk h
    rw [hk] at h
    cases h
  refine ⟨by rw [kindsOf_length, hD.ksLen], shadowFs_length, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the X-source entries mention no recursive slot below them
    intro i hi
    rw [shadowFs_getD hi]
    split
    · trivial
    · obtain ⟨x, hx, hws, hlf⟩ := hdom i hi
      rw [drop_map_getD hlenDs hi]
      exact noBVar_of_leaf_free mp.base2 (nP + i) x.fvarTypeD hws (hQlt i) hlf
        (hD.domRead ψ i x hx)
  · -- nor do a reflexive field's telescope domains
    intro i hi hr k d hkd
    rcases (recAt_kindsOf hD.ksLen hi).mp hr with hk | hk
    · rw [hD.tssNone ψ i (hne_refl i hk)] at hkd
      exact nomatch hkd
    · obtain ⟨x, hx, -, -⟩ := hrecGet i hr hi
      obtain ⟨afvs, body, hop, hdoms, -, -, -⟩ := hreflGet i x hx hk hi
      have hlenA := openPisAtFvars_length _ hop
      have hk' : k < afvs.length := by
        rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hkd).1
      obtain ⟨hws, hlf, hread⟩ := hdoms k _ (List.getElem?_eq_getElem hk')
      have hd : d.2.2 = (((tss ψ).getD i []).getD k default).2.2 := by
        rw [List.getD_eq_getElem?_getD, hkd]; rfl
      rw [hd]
      exact noBVar_of_leaf_free mp.base2 (nP + i + k) _ hws (fun q h => by have := h.2; omega)
        hlf hread
  · -- nor do the TAGGED index expressions of the recursive slots
    intro i hi hr E hE
    rw [hEissGet i hi, List.mem_singleton] at hE
    subst hE
    have hbase : ∀ E' ∈ (Eiss ψ).getD i [],
        NoBVar (exclP (fun q => recAt nP (kindsOf ks) q ∧ q < nP + i)
          (nP + i + ((tss ψ).getD i []).length)) E' := by
      intro E' hE'
      obtain ⟨x, hx, hws, hlf⟩ := hdom i hi
      rcases (recAt_kindsOf hD.ksLen hi).mp hr with hk | hk
      · rw [hD.tssNone ψ i (hne_refl i hk), List.length_nil, Nat.add_zero]
        obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv (hD.eisRead ψ i x hx hk) E' hE'
        have ha' : a ∈ x.fvarTypeD.getAppArgs := List.mem_of_mem_drop ha
        exact noBVar_of_leaf_free mp.base2 (nP + i) a (WScoped_of_mem_getAppArgs _ a hws ha')
          (hQlt i) (fun l hl => hlf l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl)) hra
      · obtain ⟨afvs, body, hop, -, hwsB, hlfB, hspB⟩ := hreflGet i x hx hk hi
        obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv hspB E' hE'
        have ha' : a ∈ body.getAppArgs := List.mem_of_mem_drop ha
        exact noBVar_of_leaf_free mp.base2 _ a (WScoped_of_mem_getAppArgs _ a hwsB ha')
          (fun q h => by have := h.2; omega)
          (fun l hl => hlfB l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl)) hra
    refine NoBVar_tagTupleAV ?_ hbase
    rintro j ⟨q, hq, -, rfl⟩
    have := hQrange i q hq
    omega
  · -- nor does the residual's TAGGED index expression
    intro E hE
    rw [List.mem_singleton] at hE
    subst hE
    have hbase : ∀ E' ∈ Es ψ,
        NoBVar (exclP (fun q => recAt nP (kindsOf ks) q ∧ q < nP + nF) (nP + nF)) E' := by
      intro E' hE'
      obtain ⟨a, ha, hra⟩ := DenoteMetaSpine.mem_inv (hD.idxRead ψ) E' hE'
      rw [hD.idxEq] at ha
      have ha' : a ∈ xrest.getAppArgs := List.mem_of_mem_drop ha
      refine noBVar_of_leaf_free mp.base2 (nP + nF) a
        (WScoped_of_mem_getAppArgs _ a hO.bodyScoped.1 ha') (hQlt nF) ?_ hra
      intro l hl ⟨hr, hlt⟩
      have hge := hr.1
      obtain ⟨-, -, -, hres⟩ := hrecGet (l.1 - nP)
        (by rw [show nP + (l.1 - nP) = l.1 from by omega]; exact hr) (by omega)
      exact mentionsFvar_false hres l (mem_fvarLeaves_of_getAppArgs _ a ha' l hl) (by omega)
    refine NoBVar_tagTupleAV ?_ hbase
    rintro j ⟨q, hq, -, rfl⟩
    have := hQrange nF q hq
    omega
  · -- the entries, graded at a shadow-fitting spine; the recursive
    -- slots' fit at the TAG
    intro i hi as' hsp'
    rw [shadowFs_shadowFs] at hsp'
    have hlenA : as'.length = i := by
      rw [hsp'.length_eq, List.length_take, shadowFs_length]; omega
    have hsat : Sat V ((shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse)).drop
        (nP + nF - (nP + i))) (consList as' ρp) := by
      rw [shadowCtx_drop_fields hlenDs (Nat.le_of_lt hi)]
      exact sat_of_spineFit hρp' hsp'
    obtain ⟨hokP, hbnd⟩ := hkey (nP + i) (by omega) _ hsat
    rw [reverse_getD_field hlenDs hi] at hokP hbnd
    rw [shadowFs_getD hi]
    refine ⟨?_, ?_, ?_⟩
    · split
      · trivial
      · exact hokP.1
    · intro hnr hw
      rw [if_neg hnr]
      exact hbnd (Nat.le_add_right _ _) hnr hw
    · intro hr
      rw [hEissGet i hi]
      obtain ⟨ppsT, B, hppsTlen, hleafTgt, hIdssTgt⟩ := hTgt i hi
        ((recAt_kindsOf hD.ksLen hi).mp hr)
      have huntag : SlotFit W (resSort.eval ψ) ρp ((ppsT.drop nP).map (·.2.2))
          ((tss ψ).getD i []) ((Eiss ψ).getD i []) as' := by
        rcases (recAt_kindsOf hD.ksLen hi).mp hr with hk | hk
        · -- a finitary field
          rw [hD.tssNone ψ i (hne_refl i hk)]
          have hentry := hD.recEntry ψ i hk hi
          rw [drop_map_getD hlenDs hi, hentry] at hokP
          obtain ⟨hok, hfit⟩ := leafSpineFit hppsTlen (mp.base2.cval_closedL _ ψ)
            ⟨B, hleafTgt⟩ hlenA (hD.eisLen ψ i hk hi) hokP.1
          exact SlotFit.of_fin hok hfit
        · -- a reflexive field
          have hentry := hD.reflEntry ψ i hk hi
          rw [drop_map_getD hlenDs hi, hentry] at hokP
          obtain ⟨hF, hB⟩ := WellDenoted_mkPisAV_inv hokP.1
          refine ⟨?_, fun d hd => hD.tssBits ψ i d hd, fun bs hsp => ?_⟩
          · refine fieldsOkB_of_pointwise fun k hkT bs hbs => ?_
            rw [List.length_map] at hkT
            rw [getD_map_snd hkT]
            have hbs' : SpineFit (consList as' ρp) ((((tss ψ).getD i []).take k).map (·.2.2)) bs := by
              rw [List.map_take]; exact hbs
            refine ⟨?_, fun hw =>
              (mutualTeleBound_of hμ mp hCtor hProp hD ψ hw hi hk hρp' hsp' k hkT bs hbs').2⟩
            have := hF.wellDenoted_at k (by rw [List.length_map]; exact hkT) bs hbs
            rwa [getD_map_snd hkT] at this
          · have hokB := hB bs hsp
            rw [← consList_append] at hokB
            have hlenAB : (as' ++ bs).length = i + ((tss ψ).getD i []).length := by
              rw [List.length_append, hlenA, hsp.length_eq, List.length_map]
            rw [Nat.add_assoc] at hokB
            exact leafSpineFit hppsTlen (mp.base2.cval_closedL _ ψ) ⟨B, hleafTgt⟩ hlenAB
              (hD.eisLenRefl ψ i hk hi) hokB
      exact slotFit_tag hTag hIdssTgt hlenA huntag
  · -- the residual's TAGGED index expression, graded at a
    -- shadow-fitting field spine
    intro as' hsp' E hE
    rw [shadowFs_shadowFs] at hsp'
    rw [List.mem_singleton] at hE
    subst hE
    have hlenA : as'.length = nF := by
      rw [hsp'.length_eq, shadowFs_length]
    have hsat : Sat V (shadowCtx nP (kindsOf ks) (nP + nF) (((ds ψ).map (·.2.2)).reverse))
        (consList as' ρp) := by
      have hh := shadowCtx_drop_fields (ks := kindsOf ks) hlenDs (Nat.le_refl nF)
      rw [Nat.sub_self, List.drop_zero,
        List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hh
      rw [hh]
      exact sat_of_spineFit hρp' hsp'
    have hokR := hkeyR _ hsat
    unfold ctorBodyAVI at hokR
    rw [paramBvars_eq_paramBvarsAt] at hokR
    obtain ⟨hEok, hfit⟩ := leafSpineFit (hFD.len ψ) (mp.base2.cval_closedL _ ψ) (hleafT ψ)
      hlenA (hD.lenE ψ) hokR.1
    have hfr : shiftE nF 0 (consList as' ρp) = ρp := by
      rw [← hlenA]; exact shiftE_consList _ ρp
    exact (tagTupleAV_facts hTag hmem hfr hEok hfit).2

end ConLeche.Model
