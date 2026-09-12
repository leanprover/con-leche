module

import ConLeche.Model.IndRep
public import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Model.Inductives.MutualRecData
import ConLeche.Model.Inductives.MutualStageRec
import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Model.IndRepSwap
public section

/-!
# The mutual block's discharge of the representation clause (task #278, M2.6 part 2)

The fixpoint route's discharge (`Model/Inductives/FixRep.lean`) at a
mutual block: the datum `mutualRepData` is the block's spelling — the
CONTAINER is the auxiliary family over the tag
(`Semantics/Tower/MutualLeafI.lean`), so `IdsC` is `auxIds`, `u` is the
tag's universe `W`, member `m`'s index spine goes to the container's
tuple by `tup ψ m ı⃗ = ⟨inj m ⟨ı⃗⟩⟩`, the functor is `fixFunVI` at the
tagged chain data and the injections are the tagged towers.

**The container's index readings.**  The clause's datum carries the
constructors' index readings TWICE (task #278 M2.6): `esF`/`eissF` as
the stored types read them — at the MEMBERS' leaves, so constructor
`J`'s spine has length `nIdxAt (mems J)` and field `i`'s the length of
its target's — and `essC`/`eissC` as the CONTAINER reads them.  At a
mutual block the second pair is the TAGGED singletons `mutEssC`/
`mutEissC` (`[⟨inj m ⟨e⃗⟩⟩]` over the one-binder tag telescope), which
is what the X-chains and the fibre are spelled from; at a single family
the two pairs coincide and `fixRepData` sets `essC := esF`,
`eissC := eissF`.  So the datum's `cdsC` here IS the auxiliary family's
constructor data (`auxCtorData`, `MutualRecPre.lean`), and the block's
chain facts (`mutualChainFacts_of`) are the clause's `chains`,
`functor` and `fibre` — the X-source chains `Fss₀` reaching the datum's
REAL chains through `AgreeOffRecs` (`hagree`), exactly as on the
fixpoint route.

**The rule-less cons.**  `IndRep.rules` is conditioned on `rules ≠ []`,
so a recursor PROVISIONED before its rules are checked
(`provisionMutualRecs`: a rule mentions the sibling recursors) claims
its block with that clause vacuous; `mutualIndRepsHead_of` serves both
that cons and the store.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  RecRule MutualBlock MutualFormerA MutualCtor)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The kinds, with and without their targets -/

omit [SetTheory V] in
/-- The kinds stripped of their targets, at ANY position: out of range
both sides are `.ordinary`. -/
theorem kindsOf_getD_all (ks : List (RecFieldKind × Nat)) (i : Nat) :
    (kindsOf ks).getD i .ordinary = kindAt ks i := by
  by_cases hi : i < ks.length
  · exact kindsOf_getD hi
  · have h1 : ks.getD i (RecFieldKind.ordinary, 0) = (.ordinary, 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h2 : (kindsOf ks).getD i RecFieldKind.ordinary = .ordinary := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [kindsOf_length]; omega)]
      rfl
    rw [h2, show kindAt ks i = (ks.getD i (RecFieldKind.ordinary, 0)).1 from rfl, h1]

/-! ## The constructor's data, as the fixpoint route's -/

/-- A constructor's data at a result sort with the same values. -/
theorem CtorDataI.congrSort {m : EnvModel V env} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    (h : CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs)
    {resSort' : Level} (hs : ∀ ψ : Name → Nat, resSort'.eval ψ = resSort.eval ψ) :
    CtorDataI m T lps cvC nP nF nIdx resSort' isProp large idxArgs ds Es srcs :=
  { h with
    bits := fun ψ d hd => by rw [hs ψ]; exact h.bits ψ d hd
    srcProp := fun hl ψ h0 ρ hρ => h.srcProp hl ψ (by rw [← hs ψ]; exact h0) ρ hρ }

/-- **A mutual constructor's data IS the fixpoint route's**, at the
per-field target member: the kinds stripped of their targets
(`kindsOf`, read through `kindAt` at every position), the target name
and index count looked up in the block's member table. -/
theorem MutualCtorDataI.toFixCtorDataI {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)} {fvsP xFvs : List Expr}
    {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es
      srcs ks fvsP xFvs xrest Eiss tss)
    {resSort' : Level} (hs : ∀ ψ : Name → Nat, resSort'.eval ψ = resSort.eval ψ)
    {tgtOf : Nat → Name} {nIdxOf : Nat → Nat}
    (htgt : ∀ i, tgtOf i = mutualNameOf members (tgtAt ks i))
    (hnIdx : ∀ i, nIdxOf i = mutualNIdxOf members (tgtAt ks i)) :
    FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort' isProp large idxArgs ds Es srcs
      (kindsOf ks) fvsP xFvs xrest Eiss tss tgtOf nIdxOf where
  toCtorDataI := h.toCtorDataI.congrSort hs
  opened :=
    { residRes := h.opened.residRes
      ord := fun i x hx hk => h.opened.ord i x hx (by rw [← kindsOf_getD_all ks i]; exact hk)
      recF := fun i x hx hk => by
        rw [htgt i, hnIdx i]
        exact h.opened.recF i x hx (by rw [← kindsOf_getD_all ks i]; exact hk)
      reflF := fun i x hx hk => by
        rw [htgt i, hnIdx i]
        exact h.opened.reflF i x hx (by rw [← kindsOf_getD_all ks i]; exact hk)
      kinds := fun i hi => by
        rw [kindsOf_getD_all ks i]; exact h.opened.kinds i hi }
  opens := h.opens
  ksLen := by rw [kindsOf_length]; exact h.ksLen
  xLen := h.xLen
  pLen := h.pLen
  xIdx := h.xIdx
  pIdx := h.pIdx
  idxEq := h.idxEq
  domRead := h.domRead
  eissLen := h.eissLen
  eisRead := fun ψ i x hx hk => h.eisRead ψ i x hx (by rw [← kindsOf_getD_all ks i]; exact hk)
  eisLen := fun ψ i hk hi => by
    rw [hnIdx i]
    exact h.eisLen ψ i (by rw [← kindsOf_getD_all ks i]; exact hk) hi
  recEntry := fun ψ i hk hi => by
    rw [htgt i]
    exact h.recEntry ψ i (by rw [← kindsOf_getD_all ks i]; exact hk) hi
  eissParams := h.eissParams
  eissBelow := h.eissBelow
  ordNone := fun ψ i h1 h2 => h.ordNone ψ i
    (by rw [← kindsOf_getD_all ks i]; exact h1) (by rw [← kindsOf_getD_all ks i]; exact h2)
  tssLen := h.tssLen
  tssNone := fun ψ i h1 => h.tssNone ψ i (by rw [← kindsOf_getD_all ks i]; exact h1)
  tssBits := fun ψ i d hd => by rw [hs ψ]; exact h.tssBits ψ i d hd
  tssPiBits := h.tssPiBits
  tssBelow := h.tssBelow
  tssParams := h.tssParams
  reflOpen := fun ψ i x hx hk => h.reflOpen ψ i x hx (by rw [← kindsOf_getD_all ks i]; exact hk)
  eisLenRefl := fun ψ i hk hi => by
    rw [hnIdx i]
    exact h.eisLenRefl ψ i (by rw [← kindsOf_getD_all ks i]; exact hk) hi
  reflEntry := fun ψ i hk hi => by
    rw [htgt i]
    exact h.reflEntry ψ i (by rw [← kindsOf_getD_all ks i]; exact hk) hi

/-- **A mutual constructor's facts are the fixpoint route's**, at the
per-field target member. -/
theorem MutualCtorFactsAt.toFixCtorFactsAt {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {lps : List Name} {nP : Nat} {isProp large : Bool}
    {Tname : Nat → Name} {nIdxOf mots : Nat → Nat} {resSortOf : Nat → Level}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List (RecFieldKind × Nat)} {fvsPF xFvsF : Nat → List Expr}
    {xrestF : Nat → Expr} {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {J : Nat} {cA : ConstantVal × Nat}
    (h : MutualCtorFactsAt m env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
      idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF J cA)
    {resSort : Level} (hs : ∀ ψ : Name → Nat, resSort.eval ψ = (resSortOf J).eval ψ)
    {tgtOf : Nat → Name} {nIdxOf' : Nat → Nat}
    (htgt : ∀ i, tgtOf i = mutualNameOf members (tgtAt (ksF J) i))
    (hnIdx : ∀ i, nIdxOf' i = mutualNIdxOf members (tgtAt (ksF J) i)) :
    FixCtorFactsAt m env₀ (Tname (mots J)) lps nP (nIdxOf (mots J)) resSort isProp large
      idxF dsF esF srcsF (fun J => kindsOf (ksF J)) fvsPF xFvsF xrestF eissF tssF J cA
      tgtOf nIdxOf' :=
  ⟨h.1, h.2.1, h.2.2.toFixCtorDataI hs htgt hnIdx⟩

/-! ## The block's chain lists, as the datum spells them -/

omit [SetTheory V] in
/-- The datum's REAL field chains are the block's (`mutFss`). -/
theorem mutFss_eq_fssOfR {nP n : Nat}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {ctorsA : List (ConstantVal × Nat)} (hn : ctorsA.length = n) :
    fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) = mutFss nP n dsF ψ := by
  subst hn
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < ctorsA.length
  · rw [fssOfR, List.getElem?_map, fixCtorDataList_getElem?, List.getElem?_eq_getElem hi,
      mutFss, List.getElem?_map, List.getElem?_range hi, Nat.zero_add]
    rfl
  · rw [fssOfR, List.getElem?_map, fixCtorDataList_getElem?,
      List.getElem?_eq_none (by omega), mutFss, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)]
    rfl

omit [SetTheory V] in
/-- The datum's reflexive telescopes are the block's (`mutTlss`). -/
theorem mutTlss_eq_tlssOfR {n : Nat}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {ctorsA : List (ConstantVal × Nat)} (hn : ctorsA.length = n) :
    tlssOfR (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0) = mutTlss n tssF ψ := by
  subst hn
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < ctorsA.length
  · rw [tlssOfR, List.getElem?_map, fixCtorDataList_getElem?, List.getElem?_eq_getElem hi,
      mutTlss, List.getElem?_map, List.getElem?_range hi, Nat.zero_add]
    rfl
  · rw [tlssOfR, List.getElem?_map, fixCtorDataList_getElem?,
      List.getElem?_eq_none (by omega), mutTlss, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)]
    rfl

/-! ## The stored rules name the member's constructors -/

omit [SetTheory V] in
/-- A mutual recursor's stored rules name the constructors they were
generated from, in order. -/
theorem mutualRules_ctors {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ l : List (MutualCtor × Expr),
      (ConLeche.mutualRules find? recName nP mI rP recTy l).map (·.ctor)
        = l.map (·.1.cv.name)
  | [] => rfl
  | c :: rest => by
    simp only [ConLeche.mutualRules, List.map_cons, ConLeche.recRuleBits_ctor]
    rw [mutualRules_ctors rest]

/-! ## The container's index readings -/

/-- **Constructor `J`'s index reading AT THE CONTAINER**: the tagged
singleton `[⟨inj (mots J) ⟨e⃗_J⟩⟩]`, its own readings scoped `nFs J`
binders below the parameters (`mutualEss` per constructor). -/
@[expose] def mutEssC (W : (Name → Nat) → Nat) (Idss : (Name → Nat) → List (List AnnotTerm))
    (mots nFs : Nat → Nat) (esF : Nat → (Name → Nat) → List AnnotTerm) :
    Nat → (Name → Nat) → List AnnotTerm :=
  fun J ψ => [tagTupleAV (W ψ) (mots J) (nFs J) (Idss ψ) (esF J ψ)]

/-- **Constructor `J`'s recursive slots' index readings AT THE
CONTAINER**: slot `i` targeting member `tgtAt (ksF J) i` under its
telescope gets the tagged singleton `[⟨inj (tgts i) ⟨e⃗_i⟩⟩]`
(`mutualEiss` per constructor). -/
@[expose] def mutEissC (W : (Name → Nat) → Nat) (Idss : (Name → Nat) → List (List AnnotTerm))
    (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat)
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm)) :
    Nat → (Name → Nat) → List (List AnnotTerm) :=
  fun J ψ => (List.range (nFs J)).map fun i =>
    [tagTupleAV (W ψ) (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length) (Idss ψ)
      ((eissF J ψ).getD i [])]

omit [SetTheory V] in
/-- The container's result readings, as the block spells them
(`mutEss'`). -/
theorem essOfR_mutEssC {n : Nat} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ksF' : Nat → List RecFieldKind}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissC : Nat → (Name → Nat) → List (List AnnotTerm)}
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {mots nFs : Nat → Nat} {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat}
    {ctorsA : List (ConstantVal × Nat)} (hn : ctorsA.length = n) :
    essOfR (fixCtorDataList dsF (mutEssC W Idss mots nFs esF) ksF' eissC tssF ψ ctorsA 0)
      = mutEss' (n := n) (W ψ) (Idss ψ) mots nFs esF ψ := by
  subst hn
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < ctorsA.length
  · rw [essOfR, List.getElem?_map, fixCtorDataList_getElem?, List.getElem?_eq_getElem hi,
      mutEss', mutualEss, List.getElem?_map,
      List.getElem?_range (show i < (mutEss0 ctorsA.length esF ψ).length from by
        rw [mutEss0_length]; exact hi),
      Nat.zero_add]
    simp only [Option.map_some]
    rw [mutMems_getD hi, mutNFs_getD hi, mutEss0_getD hi]
    rfl
  · rw [essOfR, List.getElem?_map, fixCtorDataList_getElem?, List.getElem?_eq_none (by omega),
      mutEss', mutualEss, List.getElem?_map,
      List.getElem?_eq_none (by rw [List.length_range, mutEss0_length]; omega)]
    rfl

omit [SetTheory V] in
/-- The container's slot readings, as the block spells them
(`mutEiss'`). -/
theorem eissOfR_mutEissC {n : Nat} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ksF' : Nat → List RecFieldKind} {essC : Nat → (Name → Nat) → List AnnotTerm}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat}
    {ctorsA : List (ConstantVal × Nat)} (hn : ctorsA.length = n)
    (hlen : ∀ J, J < n → (eissF J ψ).length = nFs J) :
    eissOfR (fixCtorDataList dsF essC ksF' (mutEissC W Idss ksF nFs tssF eissF) tssF ψ ctorsA 0)
      = mutEiss' (n := n) (W ψ) (Idss ψ) ksF nFs tssF eissF ψ := by
  subst hn
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < ctorsA.length
  · rw [eissOfR, List.getElem?_map, fixCtorDataList_getElem?, List.getElem?_eq_getElem hi,
      Nat.zero_add]
    have hget : (mutEiss' (n := ctorsA.length) (W ψ) (Idss ψ) ksF nFs tssF eissF ψ)[i]?
        = some ((mutEiss' (n := ctorsA.length) (W ψ) (Idss ψ) ksF nFs tssF eissF ψ).getD i []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show i < (mutEiss' (n := ctorsA.length) (W ψ) (Idss ψ) ksF nFs
          tssF eissF ψ).length from by
          unfold mutEiss' mutualEiss
          rw [List.length_map, List.length_range, mutEiss0_length]
          exact hi)]
      rfl
    rw [hget, mutEiss'_getDJ hi (hlen i hi)]
    rfl
  · rw [eissOfR, List.getElem?_map, fixCtorDataList_getElem?, List.getElem?_eq_none (by omega),
      mutEiss', mutualEiss, List.getElem?_map,
      List.getElem?_eq_none (by rw [List.length_range, mutEiss0_length]; omega)]
    rfl

/-! ## The datum -/

/-- **The representation datum of a mutual block** (`fixRepData` at the
block's `k` members): the constructors' readings as they are stored (at
the MEMBERS' leaves, with the per-field target member), the member
table (`k`, the members' names and index counts, each constructor's own
member `mots` and each field's target `tgtAt`), and — the container —
the auxiliary family over the TAG: `IdsC` is `auxIds`, the index-tuple
sort is the tag's `W`, member `m`'s index spine becomes the container's
tuple `⟨inj m ⟨ı⃗⟩⟩`, the functor is the fixpoint route's at the block's
TAGGED chain data and the injections are the tagged towers.

The CONTAINER's index readings `essC`/`eissC` are the tagged
singletons (`mutEssC`/`mutEissC`), so the datum's `cdsC` is the
auxiliary family's constructor data and its derived chains are the
block's; the stored `esF`/`eissF` stay the members' own.

`resSort` is member `mm`'s OWN spelling of the block's one result level
(`IndRep.strip` compares it syntactically with the stored type's), so
the datum is per member; the constructors' own spellings agree with it
by value (`mutualIndRep_of`'s `hsortJ`). -/
@[expose] noncomputable def mutualRepData (env₀ : Env) (nP k : Nat) (resSort : Level)
    (isProp large : Bool) (elim : Name) (ctorsA : List (ConstantVal × Nat)) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List (RecFieldKind × Nat)) (fvsPF xFvsF : Nat → List Expr)
    (xrestF : Nat → Expr) (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (Tname : Nat → Name) (nIdxOf mots nFs : Nat → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (lvlsOf : Nat → (Name → Nat) → List Nat)
    (W : (Name → Nat) → Nat) (Idss : (Name → Nat) → List (List AnnotTerm))
    (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : (Name → Nat) → List (List (List AnnotTerm)))
    (Ess' : (Name → Nat) → List (List AnnotTerm)) : IndRepData V where
  nP := nP
  nIdx := 1
  resSort := resSort
  isProp := isProp
  large := large
  elim := elim
  env₀ := env₀
  ctorsA := ctorsA
  idxF := idxF
  dsF := dsF
  esF := esF
  srcsF := srcsF
  ksF := fun J => kindsOf (ksF J)
  fvsPF := fvsPF
  xFvsF := xFvsF
  xrestF := xrestF
  eissF := eissF
  tssF := tssF
  essC := mutEssC W Idss mots nFs esF
  eissC := mutEissC W Idss ksF nFs tssF eissF
  k := k
  nIdxs := (List.range k).map nIdxOf
  memberNames := (List.range k).map Tname
  mems := mots
  tgts := fun J i => tgtAt (ksF J) i
  ppsM := ppsOf
  lvlsM := lvlsOf
  IdsC := fun ψ => auxIds (W ψ) (Idss ψ)
  u := W
  tup := fun ψ mm is => tupW (W ψ) [inj mm (mkTower (is ++ [pt]))]
  Φ := fun ψ ρp =>
    fixFunVI (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ)) 1 rss (tlss ψ) (Eiss' ψ)
      (mutFss nP ctorsA.length dsF ψ) (Ess' ψ)
  inj := fun ψ J fs => injW (resSort.eval ψ) J (mkTower (fs ++ [pt]))

/-! ## The member's representation -/

/-- **A member of a natively installed mutual block is represented**,
from the facts the block's stages hold at the carrier storing the
formers, the constructors and the recursors.

The container's side is the block's own chain facts
(`mutualChainFacts_of`) at the datum's spellings: `hrssD`/`htlssD`/
`hEissD`/`hEssD` say that the datum's derived chain lists — read off
`cdsC`, the constructor data at the TAGGED index readings — are the
block's, and `hagree` that the X-source chains `Fss₀` agree with the
real ones off the recursive positions, which is what carries
`XChainsOk` from the one to the other (`xChainsOk_congr`) and the
member's leaf from `auxFamI` at `Fss₀` to the datum's functor
(`fixFamI_congr`). -/
theorem mutualIndRep_of {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {lps : List Name} {nP k : Nat} {resSort : Level}
    {isProp large : Bool} {elim : Name} {ctorsA : List (ConstantVal × Nat)} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List (RecFieldKind × Nat)} {fvsPF xFvsF : Nat → List Expr}
    {xrestF : Nat → Expr} {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {Tname : Nat → Name} {nIdxOf mots nFs : Nat → Nat} {resSortOf : Nat → Level}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvlsOf : Nat → (Name → Nat) → List Nat}
    {W : (Name → Nat) → Nat} {Idss : (Name → Nat) → List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : (Name → Nat) → List (List (List AnnotTerm))}
    {Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm)}
    {mm : Nat} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    -- the member table
    (hmm : mm < k)
    (hmots : ∀ J, J < ctorsA.length → mots J < k)
    (htgtLt : ∀ J i, tgtAt (ksF J) i < k)
    (hnames : ∀ t, t < k → Tname t = mutualNameOf members t)
    (hnIdxs : ∀ t, t < k → nIdxOf t = mutualNIdxOf members t)
    -- the stored member
    {bsT : List (Expr × BinderMeta)}
    (hstripT : cvT.type.stripPis (nP + nIdxOf mm) = some (bsT, .sort resSort))
    (hlpsT : cvT.levelParams = lps)
    (hProp : isProp = (Level.isEquiv resSort .zero == some true))
    (hmI : mI = nP + k + ctorsA.length + nIdxOf mm)
    (hrP : rP = nP + k + ctorsA.length)
    (hrules : rules ≠ [] → rules.map (·.ctor)
      = ((ctorsA.zipIdx.filter fun x => mots x.2 == mm).map (·.1)).map (·.1.name))
    (hFD : FormerData m cvT (nP + nIdxOf mm) resSort (ppsOf mm) (lvlsOf mm))
    (hfound : ∀ t, t < k → ∃ (cv : ConstantVal) (caps : IndCaps),
      env.find? (Tname t) = some (.indInfo cv caps))
    -- the constructors, at their own members and with their fields' targets
    (hcf : ∀ J cA, ctorsA[J]? = some cA →
      MutualCtorFactsAt m env₀ members lps nP isProp large Tname nIdxOf mots resSortOf
        idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF J cA)
    (hsortJ : ∀ (J : Nat) (ψ : Name → Nat), resSort.eval ψ = (resSortOf J).eval ψ)
    (hidxRes : ∀ J cA, ctorsA[J]? = some cA → ∀ e ∈ idxF J, e.constsResolve env = true)
    (hUparams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) → W ψ₁ = W ψ₂)
    -- the parameter telescopes: the block's (member `0`'s) is every
    -- member's and every constructor's (`mutualCrossChecks`)
    (hpps0 : ∀ ψ : Name → Nat, nP ≤ (ppsOf 0 ψ).length)
    (hiff : ∀ J cA, ctorsA[J]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF J ψ).take nP).map (·.2.2)).reverse ρ)
    (hiffM : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ppsOf mm ψ).take nP).map (·.2.2)).reverse ρ)
    -- the container: the tag, the chains, the members' index telescopes
    (hTag : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse ρp → TagOk (W ψ) ρp (Idss ψ))
    (hX : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse ρp →
      XChainsOk (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ)) rss (tlss ψ) (Eiss' ψ)
        (Fss₀ ψ) (Ess' ψ))
    (hIdss : ∀ ψ : Name → Nat, (Idss ψ)[mm]? = some (((ppsOf mm ψ).drop nP).map (·.2.2)))
    -- the leaves
    (hleafT : ∀ ψ : Name → Nat, m.acval (Tname mm) ψ
      = mutualTyAVI (W ψ) (resSort.eval ψ) (ppsOf mm ψ) (nIdxOf mm) (Idss ψ) rss (tlss ψ)
          (Eiss' ψ) (Fss₀ ψ) (Ess' ψ) mm)
    (hleafC : ∀ J cA, ctorsA[J]? = some cA → ∀ ψ : Name → Nat, m.acval cA.1.name ψ
      = sumMkAV (resSort.eval ψ) J (dsF J ψ) (((dsF J ψ).drop nP).map (·.2.2))
          (uChains (mutFss nP ctorsA.length dsF ψ)))
    (hokB : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse ρp →
      ∀ J, J < ctorsA.length → FieldsOkB (resSort.eval ψ) ρp ((mutFss nP ctorsA.length dsF ψ).getD J []))
    -- the datum's derived chain lists ARE the block's (`cdsC` is the
    -- auxiliary family's constructor data), and the X-source chains
    -- agree with the real ones off the recursive positions
    (hrssD : rssOfK (fun J => kindsOf (ksF J)) ctorsA.length = rss)
    (htlssD : ∀ ψ : Name → Nat,
      tlssOfR (fixCtorDataList dsF (mutEssC W Idss mots nFs esF) (fun J => kindsOf (ksF J))
        (mutEissC W Idss ksF nFs tssF eissF) tssF ψ ctorsA 0) = tlss ψ)
    (hEissD : ∀ ψ : Name → Nat,
      eissOfR (fixCtorDataList dsF (mutEssC W Idss mots nFs esF) (fun J => kindsOf (ksF J))
        (mutEissC W Idss ksF nFs tssF eissF) tssF ψ ctorsA 0) = Eiss' ψ)
    (hEssD : ∀ ψ : Name → Nat,
      essOfR (fixCtorDataList dsF (mutEssC W Idss mots nFs esF) (fun J => kindsOf (ksF J))
        (mutEissC W Idss ksF nFs tssF eissF) tssF ψ ctorsA 0) = Ess' ψ)
    (hagree : ∀ ψ : Name → Nat, AgreeOffRecs rss (Fss₀ ψ) (mutFss nP ctorsA.length dsF ψ))
    -- the recursor's shape (task #279 M-A′): its name, its absence from
    -- the carrier (the constructors' environment: the rules' readings
    -- are the store's business), and its type's reading
    (hRname : cvR.name = (Tname mm).str "rec") (hnotR : env.find? cvR.name = none)
    (hRread : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvR.type
      = some (mkPisAV (mutualRecDataAV m ψ ((List.range k).map fun t => m.acval (Tname t) ψ) nP
          ((List.range k).map nIdxOf) (ConLeche.structElimLevel elim large) ((ppsOf 0 ψ).take nP)
          ((List.range k).map fun t => (ppsOf t ψ).drop nP)
          (fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0) mots
          (fun J i => tgtAt (ksF J) i) mm)
        (mutualConcAV k ctorsA.length (nIdxOf mm) mm))) :
    IndRep m (Tname mm) cvT cvR mI rP rules
      (mutualRepData env₀ nP k resSort isProp large elim ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF
        xrestF eissF tssF Tname nIdxOf mots nFs ppsOf lvlsOf W Idss rss tlss Eiss' Ess') mm := by
  let d : IndRepData V :=
    mutualRepData env₀ nP k resSort isProp large elim ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF
      xrestF eissF tssF Tname nIdxOf mots nFs ppsOf lvlsOf W Idss rss tlss Eiss' Ess'
  show IndRep m (Tname mm) cvT cvR mI rP rules d mm
  -- the member table, read off the datum
  have hname : ∀ t, t < k → d.memberName t = Tname t := fun t ht =>
    getD_range_map Tname k t ht _
  have hnIdxAt : ∀ t, t < k → d.nIdxAt t = nIdxOf t := fun t ht =>
    getD_range_map nIdxOf k t ht _
  have hparams : ∀ ψ, d.params ψ = ((ppsOf 0 ψ).take nP).map (·.2.2) := fun _ => rfl
  have hIdsM : ∀ ψ, d.IdsM mm ψ = ((ppsOf mm ψ).drop nP).map (·.2.2) := fun _ => rfl
  have hFssD : ∀ (ψ : Name → Nat) (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      (d.Fss ψ).getD J [] = ((dsF J ψ).drop nP).map (·.2.2) :=
    fun ψ J cA hJ => fssOfR_fixCtorDataList_getD hJ
  have hFssL : ∀ ψ, d.Fss ψ = mutFss nP ctorsA.length dsF ψ := fun ψ => mutFss_eq_fssOfR rfl
  have hrssL : d.rss = rss := hrssD
  have htlssL : ∀ ψ, d.tlss ψ = tlss ψ := htlssD
  have hEissL : ∀ ψ, d.Eiss ψ = Eiss' ψ := hEissD
  have hEssL : ∀ ψ, d.Ess ψ = Ess' ψ := hEssD
  -- the functor's premise at the datum's REAL chains
  have hXr : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse ρp →
      XChainsOk (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ)) rss (tlss ψ) (Eiss' ψ)
        (mutFss nP ctorsA.length dsF ψ) (Ess' ψ) :=
    fun ψ ρp hρ => xChainsOk_congr (hX ψ ρp hρ) (hagree ψ)
  have hlenIdsM : ∀ ψ, (d.IdsM mm ψ).length = nIdxOf mm := by
    intro ψ
    rw [hIdsM, List.length_map, List.length_drop, hFD.len ψ]
    omega
  have hlenP0 : ∀ ψ, (d.params ψ).length = nP := by
    intro ψ
    rw [hparams, List.length_map, List.length_take]
    exact Nat.min_eq_left (hpps0 ψ)
  -- the recursor's shape, reduced (task #279 M-A′)
  have hLs : ∀ ψ, d.Ls m ψ = (List.range k).map fun t => m.acval (Tname t) ψ := by
    intro ψ
    unfold IndRepData.Ls
    exact List.map_congr_left fun t ht => by
      rw [show d.memberNames.getD t .anonymous = d.memberName t from rfl,
        hname t (List.mem_range.mp ht)]
  have hcdsR : ∀ ψ, d.cdsR ψ
      = fixCtorDataList dsF esF (fun J => kindsOf (ksF J)) eissF tssF ψ ctorsA 0 := by
    intro ψ
    show fixCtorDataList d.dsF d.esF d.ksR d.eissR d.tssR ψ (ctorsA ++ []) 0 = _
    rw [List.append_nil]
    rfl
  refine {
    member := hname mm hmm
    strip := ⟨bsT, by rw [hnIdxAt mm hmm]; exact hstripT⟩
    isProp := hProp
    rulesRead := fun _ _ h => by rw [hnotR] at h; exact nomatch h
    mI := by rw [hnIdxAt mm hmm]; exact hmI
    rP := hrP
    rules := hrules
    kRealLe := Nat.le_refl _
    memReal := hmm
    recName := by rw [show d.recNames mm = (d.memberName mm).str "rec" from rfl, hname mm hmm]; exact hRname.symm
    tgtsRLt := htgtLt
    membersFound := fun t ht => by rw [hname t ht]; exact hfound t ht
    ctorsCFound := fun _ h => nomatch h
    pinsReal := fun _ _ => ⟨fun _ => rfl, rfl⟩
    recRead := fun _ ψ => by
      rw [hRread ψ]
      unfold IndRepData.recDataAV
      rw [hLs ψ, hcdsR ψ, show d.pinsOf ψ = fun _ => paramBvarsAt nP nP from rfl,
        show d.nP = nP from rfl, show d.nIdxs = (List.range k).map nIdxOf from rfl,
        show d.elimL = ConLeche.structElimLevel elim large from rfl,
        show d.ppsM 0 ψ = ppsOf 0 ψ from rfl,
        show d.ipss ψ = (List.range k).map (fun t => (ppsOf t ψ).drop nP) from rfl,
        show d.mems = mots from rfl, show d.tgtsR = fun J i => tgtAt (ksF J) i from rfl,
        show d.k = k from rfl, show d.nAll = ctorsA.length from rfl, hnIdxAt mm hmm,
        recDataAVP_params]
    former := by rw [hnIdxAt mm hmm]; exact hFD
    ctors := ?_
    memsFound := ?_
    idxRes := hidxRes
    uParams := fun ψ₁ ψ₂ hq => hUparams ψ₁ ψ₂ (fun q hq' => hq q (by rw [hlpsT]; exact hq'))
    paramsIff := hiff
    chains := ?_
    functor := fun ψ ρp hρ =>
      ⟨fixFunVI_mem (hXr ψ ρp hρ).hok, fixFunVI_mono (hXr ψ ρp hρ), fixFunVI_maps (hXr ψ ρp hρ),
        fixFunVI_closed_exists (hXr ψ ρp hρ)⟩
    fibre := ?_
    leaf := ?_
    tupMem := ?_
    ctor := ?_
    mkZero := fun ψ hz J fs => by
      show injW (resSort.eval ψ) J _ = pt
      rw [show resSort.eval ψ = 0 from hz, injW_zero]
    mkInj := ?_ }
  · -- the constructors' readings
    intro J cA hJ
    have hJlt : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have hmJ : d.memberName (d.mems J) = Tname (mots J) := hname _ (hmots J hJlt)
    have hiJ : d.nIdxAt (d.mems J) = nIdxOf (mots J) := hnIdxAt _ (hmots J hJlt)
    have htg : (fun i => d.memberName (d.tgts J i)) = fun i => Tname (tgtAt (ksF J) i) := by
      funext i; exact hname _ (htgtLt J i)
    have htgI : (fun i => d.nIdxAt (d.tgts J i)) = fun i => nIdxOf (tgtAt (ksF J) i) := by
      funext i; exact hnIdxAt _ (htgtLt J i)
    rw [hmJ, hiJ, htg, htgI, hlpsT]
    exact (hcf J cA hJ).toFixCtorFactsAt (hsortJ J)
      (fun i => hnames _ (htgtLt J i)) (fun i => hnIdxs _ (htgtLt J i))
  · -- the block's names are stored
    intro J hJ
    have hmJ : d.memberName (d.mems J) = Tname (mots J) := hname _ (hmots J hJ)
    refine ⟨by rw [hmJ]; exact hfound _ (hmots J hJ), fun i => ?_⟩
    have hti : d.memberName (d.tgts J i) = Tname (tgtAt (ksF J) i) := hname _ (htgtLt J i)
    rw [hti]
    exact hfound _ (htgtLt J i)
  · -- the chains, at the datum's own lists
    intro ψ ρp hρ
    rw [hrssL, htlssL ψ, hEissL ψ, hEssL ψ, hFssL ψ]
    exact xChainsOk_toChainsOk (hXr ψ ρp hρ)
  · -- the container functor's fibre
    intro ψ ρp hρ X hXm t ht x
    have hCF : ∀ (J : Nat) (fs : List V), d.ChainFit ψ ρp X t J fs ↔
        (fs.length = ((mutFss nP ctorsA.length dsF ψ).getD J []).length ∧
          SpineFit (cons t (cons X ρp))
            (chainXIGo (W ψ) (auxIds (W ψ) (Idss ψ)) (rss.getD J []) ((tlss ψ).getD J [])
              ((Eiss' ψ).getD J []) ((mutFss nP ctorsA.length dsF ψ).getD J []) 0) fs ∧
          EqAll (consList fs (cons t (cons X ρp)))
            (eqsXI (auxIds (W ψ) (Idss ψ)).length
              ((mutFss nP ctorsA.length dsF ψ).getD J []).length ((Ess' ψ).getD J []))) := by
      intro J fs
      show (_ ∧ _ ∧ _) ↔ _
      rw [hrssL, htlssL ψ, hEissL ψ, hEssL ψ, hFssL ψ]
      exact Iff.rfl
    have hXs : X ∈ˢ lfpFamSpace V (resSort.eval ψ)
        (idxSet (W ψ) ρp (auxIds (W ψ) (Idss ψ))) := by
      rw [lfpFamSpace_eq]; exact hXm
    have ht' : t ∈ˢ idxSet (W ψ) ρp (auxIds (W ψ) (Idss ψ)) := ht
    show x ∈ˢ app (app (fixFunVI (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ))
      (auxIds (W ψ) (Idss ψ)).length rss (tlss ψ) (Eiss' ψ) (mutFss nP ctorsA.length dsF ψ)
      (Ess' ψ)) X) t ↔ _
    rw [fixFunVI_app hXs, famFI_app ht', fixStepI_iff]
    constructor
    · rintro ⟨J, fs, hJ, hlen, hsp, hall, rfl⟩
      refine ⟨J, fs, ?_, (hCF J fs).mpr ⟨hlen, hsp, hall⟩, rfl⟩
      show J < ctorsA.length
      rw [mutFss_length] at hJ
      exact hJ
    · rintro ⟨J, fs, hJ, hfit, rfl⟩
      obtain ⟨hlen, hsp, hall⟩ := (hCF J fs).mp hfit
      exact ⟨J, fs, by rw [mutFss_length]; exact hJ, hlen, hsp, hall, rfl⟩
  · -- the leaf
    intro ψ ρ as is hsp₁ hsp₂
    have hsat0 : Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse (consList as ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      rw [hparams] at this
      simpa using this
    have hlenTake : (((ppsOf mm ψ).take nP).map (·.2.2)).length = nP := by
      rw [List.length_map, List.length_take, hFD.len ψ]
      omega
    have hsp₁' : SpineFit ρ (((ppsOf mm ψ).take nP).map (·.2.2)) as := by
      refine (spineFit_iff_of_sat_iff (Ds₁ := d.params ψ) ?_ (fun ρ' => ?_) ρ as
        (by rw [hsp₁.length_eq])).mp hsp₁
      · rw [hlenP0 ψ, hlenTake]
      · rw [hparams]; exact hiffM ψ ρ'
    have hspAll : SpineFit ρ ((ppsOf mm ψ).map (·.2.2)) (as ++ is) := by
      have hsplit : (ppsOf mm ψ).map (·.2.2)
          = ((ppsOf mm ψ).take nP).map (·.2.2) ++ ((ppsOf mm ψ).drop nP).map (·.2.2) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsplit]
      exact hsp₁'.append (by rw [← hIdsM]; exact hsp₂)
    have hislen : is.length = nIdxOf mm := by rw [hsp₂.length_eq, hlenIdsM ψ]
    have hframe : consList (as ++ is) ρ = consList is (consList as ρ) := consList_append _ _ _
    have hshift : shiftE (nIdxOf mm) 0 (consList (as ++ is) ρ) = consList as ρ := by
      rw [hframe, ← hislen]; exact shiftE_consList _ _
    have hfr : ConLeche.Semantics.frameIdx (nIdxOf mm) (consList (as ++ is) ρ) = is := by
      rw [hframe, ← hislen]; exact frameIdx_consList' _ _
    have hbase : MutualBaseI (W ψ) (resSort.eval ψ) (consList (as ++ is) ρ) (nIdxOf mm) (Idss ψ)
        rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ) (Ess' ψ) mm := by
      refine ⟨by rw [hshift]; exact hTag ψ _ hsat0, by rw [hshift]; exact (hX ψ _ hsat0).hok,
        ((ppsOf mm ψ).drop nP).map (·.2.2), hIdss ψ, ?_, ?_⟩
      · rw [← hIdsM]; exact hlenIdsM ψ
      · rw [hshift, hfr, ← hIdsM]; exact hsp₂
    have hfold := mutualTyAVI_fold hspAll hbase
    rw [hshift, hfr] at hfold
    rw [hleafT ψ]
    refine hfold.trans ?_
    unfold auxFamI auxTup
    rw [fixFamI_congr (hagree ψ)]
    rfl
  · -- the member's index spine lands in the container's index set
    intro ψ ρp hρ is hsp
    have hmem : inj mm (mkTower (is ++ [pt])) ∈ˢ interp V ρp (tagTyAV (W ψ) (Idss ψ)) := by
      rw [(tagTyAV_facts (hTag ψ ρp (by rw [← hparams]; exact hρ))).1]
      exact tagTuple_mem (hTag ψ ρp (by rw [← hparams]; exact hρ)) (hIdss ψ)
        (by rw [← hIdsM]; exact hsp)
    exact tupW_mem (Ids := auxIds (W ψ) (Idss ψ)) ⟨hmem, trivial⟩
  · -- the constructors
    intro J cA hJ ψ ρ as fs hsp₁ hsp₂
    have hJlt : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have hsat0 : Sat V (((ppsOf 0 ψ).take nP).map (·.2.2)).reverse (consList as ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
      rw [hparams] at this
      simpa using this
    have hlenD : (dsF J ψ).length = nP + cA.2 := (hcf J cA hJ).2.2.len ψ
    have hsp₁' : SpineFit ρ (((dsF J ψ).take nP).map (·.2.2)) as := by
      refine (spineFit_iff_of_sat_iff (Ds₁ := d.params ψ) ?_ (fun ρ' => ?_) ρ as
        (by rw [hsp₁.length_eq])).mp hsp₁
      · rw [hlenP0 ψ, List.length_map, List.length_take, hlenD]
        omega
      · rw [hparams]; exact hiff J cA hJ ψ ρ'
    rw [hleafC J cA hJ ψ]
    have hsplit : dsF J ψ = (dsF J ψ).take nP ++ (dsF J ψ).drop nP :=
      (List.take_append_drop _ _).symm
    by_cases hz : resSort.eval ψ = 0
    · rw [hz, sumMkAV_zero, foldl_app_pt']
      show pt = injW (resSort.eval ψ) J _
      rw [hz, injW_zero]
    · show _ = injW (resSort.eval ψ) J (mkTower (fs ++ [pt]))
      rw [injW_pos hz]
      have hok : SumFieldsOkB (resSort.eval ψ) (consList as ρ)
          (uChains (mutFss nP ctorsA.length dsF ψ)) := by
        refine SumFieldsOkB_uChains fun Fs hFs => ?_
        obtain ⟨J', hJ'⟩ := List.getElem?_of_mem hFs
        have hJ'lt : J' < ctorsA.length := by
          have := (List.getElem?_eq_some_iff.mp hJ').1
          rw [mutFss_length] at this
          exact this
        have := hokB ψ (consList as ρ) hsat0 J' hJ'lt
        rw [List.getD_eq_getElem?_getD, hJ'] at this
        exact this
      have hjU : (uChains (mutFss nP ctorsA.length dsF ψ))[J]?
          = some ((((dsF J ψ).drop nP).map (·.2.2)) ++ [idxEqAV []]) := by
        rw [uChains_getElem?, mutFss, List.getElem?_map, List.getElem?_range hJlt]
        rfl
      rw [hFssD ψ J cA hJ] at hsp₂
      have := sumMkAV_fold (V := V) hz (pds := (dsF J ψ).take nP) (fds := (dsF J ψ).drop nP)
        (Fss := uChains (mutFss nP ctorsA.length dsF ψ)) (ρ := ρ) hsp₁' hsp₂ hok hjU
      rw [← hsplit] at this
      exact this
  · -- the injections are injective
    intro ψ hz J fs J' fs' hJ hJ' hlen hlen' heq
    have heq' : injW (resSort.eval ψ) J (mkTower (fs ++ [pt]))
        = injW (resSort.eval ψ) J' (mkTower (fs' ++ [pt])) := heq
    rw [injW_pos (w := resSort.eval ψ) hz, injW_pos (w := resSort.eval ψ) hz] at heq'
    obtain ⟨rfl, htow⟩ := inj_inj heq'
    refine ⟨rfl, ?_⟩
    have := mkTower_inj (by rw [List.length_append, List.length_append, hlen, hlen']) htow
    exact List.append_cancel_right this

/-! ## The head's obligation, at one recursor's cons -/

/-- **A fresh recursor claims its block**: the clause's head obligation
from the member's representation at the consed carrier.

It serves BOTH conses of the mutual install: the PROVISIONED one
(`provisionMutualRecs`, `rules = []` — `IndRep.rules` is vacuous
there, so `mutualIndRep_of` is instantiated with
`fun h => absurd rfl h`) and the store's (`storeMutualRecs`, the
member's own rules). -/
theorem mutualIndRepsHead_of {c₀ : ConstantInfo} {cvR : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hc₀ : c₀ = .recInfo cvR mI rP rules)
    {T : Name} (hT : cvR.name = T.str "rec")
    {m₂ : EnvModel V ⟨c₀ :: env.consts⟩} {cvT : ConstantVal} {caps : IndCaps}
    {d : IndRepData V} {mm : Nat}
    (hfT : Env.find? ⟨c₀ :: env.consts⟩ T = some (.indInfo cvT caps))
    (hrep : IndRep m₂ T cvT cvR mI rP rules d mm) :
    IndRepsHead env c₀ m₂ := by
  intro cvR' mI' rP' rules' hc T' hT'
  rw [hc₀] at hc
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
  have hTT : T' = T := by
    have := hT.symm.trans hT'
    exact (Name.str.inj this).1.symm
  subst hTT
  exact Or.inl ⟨cvT, caps, d, mm, hfT, hrep⟩

/-! ## The clause at the group store -/

/-- **The clause at the recursors' group store**: every recursor the
store finds is the constructors' environment's — its representation is
the provisioned carrier's, transported across the rule-list swap
(`IndRep.swap`) — or one of the block's `k`, whose representation the
caller supplies (`mutualIndRep_of`).

This is `stageMutualRecsStore`'s `hreps` obligation; `IndReps.swap`
does NOT serve, because its escape for an entry the swap CHANGED is
`ModeledLeaf` alone, and a natively stored group's `k` recursors are
exactly the changed entries. -/
theorem mutualIndReps_of {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} {cvRas : List ConstantVal}
    {envP : Env} {mP : EnvModel V envP}
    {m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂)}
    (hcg : ConLeche.SwapCongr envP
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂))
    (hac : m₃.acval = mP.acval)
    (hprefix : IndReps mP)
    (hin : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c → envP.find? n = some c)
    (hblock : ∀ x ∈ cvRas.zipIdx, ∀ T : Name, x.1.name = T.str "rec" →
      ∃ (cvT : ConstantVal) (caps : IndCaps) (d : IndRepData V) (mm : Nat),
        (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂).find? T
            = some (.indInfo cvT caps) ∧
        IndRep m₃ T cvT x.1 (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix
          (ConLeche.mutualRules env₂.find? x.1.name b.nP
            (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix x.1.type
            (rulesOf.getD x.2 [])) d mm) :
    IndReps m₃ := by
  intro n cvR mI rP rules hf T hn
  rcases storeMutualRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hname⟩
  · -- the constructors' environment's own recursor: the prefix's entry
    rcases hprefix n cvR mI rP rules (hin _ _ h₂) T hn with ⟨cvT, caps, d, mm, hfT, hd⟩ | hmod
    · exact Or.inl ⟨cvT, caps, d, mm,
        hcg.findUp _ _ hfT (fun _ _ _ _ h => nomatch h),
        hd.swap hcg hac (hd.rulesRead_swap hcg hac (by
          rw [show cvR.name = n from ConLeche.Semantics.Env.find?_name h₂]; exact hin _ _ h₂))⟩
    · exact Or.inr (hmod.swap hcg hac)
  · -- one of the block's `k`
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    obtain ⟨cvT, caps, d, mm, hfT, hd⟩ := hblock x hx T (by rw [hname]; exact hn)
    exact Or.inl ⟨cvT, caps, d, mm, hfT, hd⟩

end ConLeche.Model
