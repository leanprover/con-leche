module

public import ConLeche.Model.IndRep
public import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Model.Inductives.MutualRecData
public import ConLeche.Model.Inductives.MutualStageRec
import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Model.IndRepCons
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

**TWO OBSTACLES, reported not worked around** (task #278 M2.6 part 2;
neither is repaired here — `ConLeche/Model/IndRep.lean` is the clause
author's).

1. **`IndRepData` cannot spell a genuinely mutual block's chains.**
   The datum has ONE pair of per-constructor index readings, `esF` and
   `eissF`, and uses it for two different things: `IndRep.ctors` reads
   the constructors' STORED types through them (`FixCtorFactsAt`, so
   `esF j ψ` is constructor `j`'s own index spine at ITS member's leaf,
   of length `nIdxAt (mems j)`, and `eissF j ψ` field `i`'s spine at
   its TARGET member's leaf, of length `nIdxAt (tgts j i)`), while the
   derived `Ess`/`Eiss` — the ones `IndRep.chains` and `IndRep.fibre`
   are stated over — are the CONTAINER's, which at a mutual block are
   the TAGGED singletons `[⟨inj m ⟨e⃗⟩⟩]` over the one-element telescope
   `IdsC = auxIds`.  The two coincide only at a single family (`k = 1`,
   the tag dropped).  So `chains` and `fibre` are, at a block with
   `k > 1`, NOT satisfiable by any choice of the datum's fields:
   `mutualIndRep_of` takes them as hypotheses, named and flagged.
   The repair is one pair of fields — the container's index readings
   `EssC`/`EissC` beside `esF`/`eissF`, with `Ess`/`Eiss` derived from
   them and the single-family instance `EssC := esF`, `EissC := eissF`
   (so `fixRepData` and the pinned data are unchanged).  Every other
   field of `IndRep` is discharged here.
2. **A rule-less recursor cannot claim its block** (the `rules = []`
   question): `IndRep.rules` says the stored rules name the member's
   own constructors, so at `rules = []` it forces `memberCtors mm = []`
   (`indRep_rules_nil`).  The mutual install conses its `k` recursors
   RULE-LESS first (`provisionMutualRecs`: a rule mentions the sibling
   recursors), so the clause — keyed on the RECURSOR — is claimed of
   entries that have no rules yet, and `stageMutualRecProvision`'s
   `hreps` obligation is false for every member with a constructor.
   The claim has to be deferred to the store (`storeMutualRecs`), i.e.
   the clause must exempt a rule-less recursor entry.
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

omit [SetTheory V] in
/-- The datum's recursive positions are the block's (`mutRss`). -/
theorem rssOfK_kindsOf {n : Nat} {ksF : Nat → List (RecFieldKind × Nat)} :
    rssOfK (fun J => kindsOf (ksF J)) n = mutRss n ksF := rfl

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

/-- **A rule-less recursor claims a member with no constructors**: the
clause's `rules` field pins the stored rules to the member's own
constructors, so at `rules = []` the member has none.  This is the
`rules = []` obstacle of the module docstring — the mutual install's
PROVISIONED recursors carry no rules, so they cannot claim their
block. -/
theorem indRep_rules_nil {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat}
    {d : IndRepData V} {mm : Nat} (h : IndRep m T cvT cvR mI rP [] d mm) :
    d.memberCtors mm = [] := by
  have hr := h.rules
  simp only [List.map_nil] at hr
  cases hc : d.memberCtors mm with
  | nil => rfl
  | cons a l => rw [hc] at hr; exact nomatch hr

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

`resSort` is member `mm`'s OWN spelling of the block's one result level
(`IndRep.strip` compares it syntactically with the stored type's), so
the datum is per member; the constructors' own spellings agree with it
by value (`mutualIndRep_of`'s `hsortJ`). -/
@[expose] noncomputable def mutualRepData (env₀ : Env) (nP k : Nat) (resSort : Level)
    (isProp large : Bool) (ctorsA : List (ConstantVal × Nat)) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List (RecFieldKind × Nat)) (fvsPF xFvsF : Nat → List Expr)
    (xrestF : Nat → Expr) (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (Tname : Nat → Name) (nIdxOf mots : Nat → Nat)
    (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (lvlsOf : Nat → (Name → Nat) → List Nat)
    (W : (Name → Nat) → Nat) (Idss : (Name → Nat) → List (List AnnotTerm))
    (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess' : (Name → Nat) → List (List AnnotTerm)) : IndRepData V where
  nP := nP
  nIdx := 1
  resSort := resSort
  isProp := isProp
  large := large
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
    fixFunVI (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ)) 1 rss (tlss ψ) (Eiss' ψ) (Fss₀ ψ)
      (Ess' ψ)
  inj := fun ψ J fs => injW (resSort.eval ψ) J (mkTower (fs ++ [pt]))

/-! ## The member's representation -/

/-- **A member of a natively installed mutual block is represented**,
from the facts the block's stages hold at the carrier storing the
formers, the constructors and the recursors.

**The two flagged hypotheses** `hchains` and `hfibre` are the clause's
`chains` and `fibre` fields verbatim; at a block with more than one
member they are NOT dischargeable, because the datum has no room for
the container's index readings (see the module docstring, obstacle 1).
Every other field is proved here. -/
theorem mutualIndRep_of {m : EnvModel V env} {env₀ : Env}
    {members : List (Name × Nat × Nat)} {lps : List Name} {nP k : Nat} {resSort : Level}
    {isProp large : Bool} {ctorsA : List (ConstantVal × Nat)} {idxF : Nat → List Expr}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List (RecFieldKind × Nat)} {fvsPF xFvsF : Nat → List Expr}
    {xrestF : Nat → Expr} {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {Tname : Nat → Name} {nIdxOf mots : Nat → Nat} {resSortOf : Nat → Level}
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
    (hrules : rules.map (·.ctor)
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
    -- FLAGGED: not dischargeable at `k > 1` (module docstring, obstacle 1)
    (hchains : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
        fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
        Ess').params ψ).reverse ρp →
      ChainsOk ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF
          ksF fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss'
          Fss₀ Ess').u ψ)
        (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ))
        (mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
          fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
          Ess').rss
        ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
          fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
          Ess').tlss ψ)
        ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
          fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
          Ess').Eiss ψ)
        ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
          fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
          Ess').Fss ψ)
        ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
          fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
          Ess').Ess ψ))
    (hfibre : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V ((mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
        fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀
        Ess').params ψ).reverse ρp →
      ∀ X, X ∈ˢ famSpace (resSort.eval ψ) (idxSet (W ψ) ρp (auxIds (W ψ) (Idss ψ))) →
      ∀ t, t ∈ˢ idxSet (W ψ) ρp (auxIds (W ψ) (Idss ψ)) → ∀ x,
        x ∈ˢ app (app (fixFunVI (W ψ) (resSort.eval ψ) ρp (auxIds (W ψ) (Idss ψ)) 1 rss (tlss ψ)
            (Eiss' ψ) (Fss₀ ψ) (Ess' ψ)) X) t ↔
          ∃ J fs, J < ctorsA.length ∧
            (mutualRepData (V := V) env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF
              fvsPF xFvsF xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss'
              Fss₀ Ess').ChainFit ψ ρp X t J fs ∧
            x = injW (resSort.eval ψ) J (mkTower (fs ++ [pt]))) :
    IndRep m (Tname mm) cvT cvR mI rP rules
      (mutualRepData env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF
        xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀ Ess') mm := by
  let d : IndRepData V :=
    mutualRepData env₀ nP k resSort isProp large ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF
      xrestF eissF tssF Tname nIdxOf mots ppsOf lvlsOf W Idss rss tlss Eiss' Fss₀ Ess'
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
  have hlenIdsM : ∀ ψ, (d.IdsM mm ψ).length = nIdxOf mm := by
    intro ψ
    rw [hIdsM, List.length_map, List.length_drop, hFD.len ψ]
    omega
  have hlenP0 : ∀ ψ, (d.params ψ).length = nP := by
    intro ψ
    rw [hparams, List.length_map, List.length_take]
    exact Nat.min_eq_left (hpps0 ψ)
  refine {
    member := hname mm hmm
    strip := ⟨bsT, by rw [hnIdxAt mm hmm]; exact hstripT⟩
    isProp := hProp
    mI := by rw [hnIdxAt mm hmm]; exact hmI
    rP := hrP
    rules := hrules
    former := by rw [hnIdxAt mm hmm]; exact hFD
    ctors := ?_
    memsFound := ?_
    idxRes := hidxRes
    uParams := fun ψ₁ ψ₂ hq => hUparams ψ₁ ψ₂ (fun q hq' => hq q (by rw [hlpsT]; exact hq'))
    paramsIff := hiff
    chains := hchains
    functor := fun ψ ρp hρ =>
      ⟨fixFunVI_mem (hX ψ ρp hρ).hok, fixFunVI_mono (hX ψ ρp hρ), fixFunVI_maps (hX ψ ρp hρ),
        fixFunVI_closed_exists (hX ψ ρp hρ)⟩
    fibre := hfibre
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
    exact hfold
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

At the mutual install this is instantiable only at the STORE: the
install's `provisionMutualRecs` conses the `k` recursors with
`rules = []`, and `indRep_rules_nil` says a rule-less entry claims a
member with no constructors — so `stageMutualRecProvision`'s `hreps`
is false for every member that has one (the module docstring's second
obstacle). -/
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
        hcg.findUp _ _ hfT (fun _ _ _ _ h => nomatch h), hd.swap hcg hac⟩
    · exact Or.inr (hmod.swap hcg hac)
  · -- one of the block's `k`
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    obtain ⟨cvT, caps, d, mm, hfT, hd⟩ := hblock x hx T (by rw [hname]; exact hn)
    exact Or.inl ⟨cvT, caps, d, mm, hfT, hd⟩

end ConLeche.Model
