module

public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Semantics.Tower.FixTuple
public section

/-!
# `IsBlockModel` at `k = 1` reproduces the native route's block model (task #315, M2)

The ONE fixpoint route (`checkNative`, task #210) represents a single
family by the least pre-fixed family of its X-chain functor `fixFunVI`
(`Semantics/Tower/FixLeafI.lean`, `FixFamI.lean`).  This module builds
the uniform block model of that block — `BlockModel.ofNative`: one member,
every field targeting it, the tuple operator the one-member tuple of
`fixFunVI` (`oneTuple`), the injections the tagged point-terminated
towers `injW w j (mkTower (fs ++ [pt]))` — and proves the block model's
SEMANTIC clauses from the native route's own facts, clause by clause:

* `functor`: `MonoTuple`/`MapsTuple`/the closed tuple from
  `fixFunVI_mono`/`_maps`/`_closed_exists` through the one-member
  lemmas (`monoTuple_one_of`, …);
* `fibre`: the native elimination `fixStepI_elim` (and its intro) with
  the syntactic X-chain fit translated into the block model's semantic
  `FitsFrom` (`spineFit_chainXIGo_iff`: entry by entry, `xEntry_rec`
  is the slot and `xEntry_ord` the domain) and the terminator into the
  projection equations (`EqAll_eqsXI_gen`);
* `leaf`: the former's fold `nativeTyAVI_fold` with the carrier read
  as the one-member tuple lfp (`fixFamI_eq_lfpTuple`);
* `ctor`: the constructor's fold `sumMkAV_fold`;
* `mkZero`/`mkInj`: the injections' own laws (`injW_zero`, `inj_inj`,
  `mkTower_inj`).

So the native route's proofs can be re-based on `IsBlockModel` without
loss: every semantic fact they read of the single family is a clause
of the one-member block model.  The syntactic clauses (`former`, `ctors`,
`rules`, …) are the native route's own reading structures
(`FormerData`, `FixCtorFactsAt` through `BlockCtorData.ofFix`), which
`declNative` establishes as it goes; assembling them into a `IsBlockModel`
is the `declBlock` assembly's job (M4), where the block model gets its first
consumer.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The X-chain fit is the semantic fit -/

section Fit

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}

/-- **The syntactic X-chain fit is the semantic fit**: along a
constructor's domains from position `i` at the prefix `as`, a spine
fits the X-chain at the frame `(ρp, X, t)` iff it fits the entries —
the slot `slotSet … X` at a recursive position, the domain's reading
at an ordinary one — at the frame `consList as ρp`.  The recursive
slots' fit (`SlotsFitX`, the functor premise's `hfit`) is what lets
`xEntry_rec` read the slot. -/
theorem spineFit_chainXIGo_iff (hI : IdxOk u ρp Ids) {X t : V} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as fs : List V), as.length = i →
      SlotsFitX u w ρp Ids rs tls Eis X t i as Fs →
      (SpineFit (consList as (cons t (cons X ρp))) (chainXIGo u Ids rs tls Eis Fs i) fs ↔
        FitsFrom rs (fun i ρ => slotSet w u ρ (tls.getD i []) (Eis.getD i []) X) i
          (consList as ρp) Fs fs)
  | [], _, _, [], _, _ => Iff.rfl
  | [], _, _, _ :: _, _, _ => Iff.rfl
  | _ :: _, _, _, [], _, _ => by simp only [chainXIGo]; exact Iff.rfl
  | F :: Fs, i, as, a :: fs, hi, hfit => by
    subst hi
    rw [chainXIGo_cons]
    show a ∈ˢ interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F as.length) ∧
        SpineFit (cons a (consList as (cons t (cons X ρp)))) (chainXIGo u Ids rs tls Eis Fs (as.length + 1)) fs ↔
      a ∈ˢ (if rs.getD as.length false then
          slotSet w u (consList as ρp) (tls.getD as.length []) (Eis.getD as.length []) X
        else interp V (consList as ρp) F) ∧
      FitsFrom rs (fun i ρ => slotSet w u ρ (tls.getD i []) (Eis.getD i []) X) (as.length + 1)
        (cons a (consList as ρp)) Fs fs
    have hhead : interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F as.length)
        = if rs.getD as.length false then
            slotSet w u (consList as ρp) (tls.getD as.length []) (Eis.getD as.length []) X
          else interp V (consList as ρp) F := by
      by_cases hri : rs.getD as.length false = true
      · rw [xEntry_rec hI F as t hri (hfit.1 hri), if_pos hri]
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntry_ord F as t hri', if_neg (by rw [hri']; exact Bool.false_ne_true)]
    rw [hhead, consList_snoc', consList_snoc']
    refine and_congr_right fun ha => ?_
    have ha' : a ∈ˢ interp V (consList as (cons t (cons X ρp))) (xEntry u Ids rs tls Eis F as.length) := by
      rw [hhead]; exact ha
    exact spineFit_chainXIGo_iff hI Fs (as.length + 1) (as ++ [a]) fs (length_snoc' a as)
      (hfit.2 a ha')

end Fit


/-! ## The X-chains ignore a recursive field's domain (task #315 M7-3 s7)

The native route carries TWO constructor-data families — the DUMMY
one, read at the empty-chain former, from which the fixpoint operator's
X-chain fields are built, and the REAL one, read at the fixpoint
former, at which the constructors' data and readings hold — and they
differ exactly at the RECURSIVE and REFLEXIVE fields, whose domains
mention the family.  `xEntry` DISCARDS the domain at such a position
(it returns the slot), so the two give the SAME X-chain, and every
fact the route proves at the dummy fields holds at the real ones.
This is what lets `BlockModel.ofNative` be instantiated at the REAL
data — its `Φ` reads `Fss` only through `chainsXI`. -/

/-- Two constructors' field lists agree where the X-chain reads them:
same length, and equal at every position the recursive flags leave
`false`. -/
@[expose] def FsAgree (rs : List Bool) (Fs Fs' : List AnnotTerm) : Prop :=
  Fs.length = Fs'.length ∧
    ∀ l, l < Fs.length → rs.getD l false = false → Fs.getD l default = Fs'.getD l default

/-- The same, for a whole block's field lists. -/
@[expose] def FssAgree (rss : List (List Bool)) (Fss Fss' : List (List AnnotTerm)) : Prop :=
  Fss.length = Fss'.length ∧
    ∀ j, j < Fss.length → FsAgree (rss.getD j []) (Fss.getD j []) (Fss'.getD j [])

/-- **A recursive entry discards its domain**, so agreeing field lists
give the same X-chain. -/
theorem chainXIGo_congr {u : Nat} {Ids : List AnnotTerm} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} :
    ∀ (Fs Fs' : List AnnotTerm) (i : Nat), Fs.length = Fs'.length →
      (∀ l, l < Fs.length → rs.getD (i + l) false = false →
        Fs.getD l default = Fs'.getD l default) →
      chainXIGo u Ids rs tls Eis Fs i = chainXIGo u Ids rs tls Eis Fs' i
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | F :: Fs, F' :: Fs', i, hlen, hag => by
    show (if rs.getD i false then _ else F.liftN 2 i) :: chainXIGo u Ids rs tls Eis Fs (i + 1)
      = (if rs.getD i false then _ else F'.liftN 2 i) :: chainXIGo u Ids rs tls Eis Fs' (i + 1)
    have hhead : (if rs.getD i false then slotXI u Ids (tls.getD i []) (Eis.getD i []) i
        else F.liftN 2 i)
        = (if rs.getD i false then slotXI u Ids (tls.getD i []) (Eis.getD i []) i
          else F'.liftN 2 i) := by
      by_cases hr : rs.getD i false = true
      · simp only [if_pos hr]
      · simp only [if_neg hr]
        have h0 := hag 0 (Nat.succ_pos _)
          (by rw [Nat.add_zero]; exact Bool.not_eq_true _ ▸ hr)
        simp only [List.getD_cons_zero] at h0
        rw [h0]
    rw [hhead, chainXIGo_congr Fs Fs' (i + 1) (by simpa using hlen) (fun l hl hrl => by
      have := hag (l + 1) (by simpa using hl)
        (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hrl)
      simpa using this)]

/-- One constructor's X-chain is the same at agreeing field lists. -/
theorem chainXI_congr {u : Nat} {Ids : List AnnotTerm} {nIdx : Nat} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    {Fs Fs' Es : List AnnotTerm} (h : FsAgree rs Fs Fs') :
    chainXI u Ids nIdx rs tls Eis Fs Es = chainXI u Ids nIdx rs tls Eis Fs' Es := by
  unfold chainXI
  rw [chainXIGo_congr Fs Fs' 0 h.1 (fun l hl hrl => h.2 l hl (by rwa [Nat.zero_add] at hrl)), h.1]

/-- The whole block's X-chains are the same at agreeing field lists. -/
theorem chainsXI_congr {u : Nat} {Ids : List AnnotTerm} {nIdx : Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Fss' Ess : List (List AnnotTerm)} (h : FssAgree rss Fss Fss') :
    chainsXI u Ids nIdx rss tlss Eiss Fss Ess = chainsXI u Ids nIdx rss tlss Eiss Fss' Ess := by
  unfold chainsXI
  rw [h.1]
  refine List.map_congr_left fun j hj => ?_
  exact chainXI_congr (h.2 j (by rw [h.1]; exact List.mem_range.mp hj))

/-- **The recursive slots fit alike at agreeing field lists**: the fit
reads a field only through `xEntry`, which discards the domain at a
recursive position. -/
theorem slotsFitX_congr {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rs : List Bool}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {X t : V} :
    ∀ (Fs Fs' : List AnnotTerm) (i : Nat) (as : List V), Fs.length = Fs'.length →
      (∀ l, l < Fs.length → rs.getD (i + l) false = false →
        Fs.getD l default = Fs'.getD l default) →
      SlotsFitX (V := V) u w ρp Ids rs tls Eis X t i as Fs →
      SlotsFitX (V := V) u w ρp Ids rs tls Eis X t i as Fs'
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | F :: Fs, F' :: Fs', i, as, hlen, hag, h => by
    have hhead : xEntry u Ids rs tls Eis F i = xEntry u Ids rs tls Eis F' i := by
      unfold xEntry
      by_cases hr : rs.getD i false = true
      · simp only [if_pos hr]
      · simp only [if_neg hr]
        have h0 := hag 0 (Nat.succ_pos _)
          (by rw [Nat.add_zero]; exact Bool.not_eq_true _ ▸ hr)
        simp only [List.getD_cons_zero] at h0
        rw [h0]
    refine ⟨h.1, fun a ha => ?_⟩
    rw [← hhead] at ha
    exact slotsFitX_congr Fs Fs' (i + 1) (as ++ [a]) (by simpa using hlen)
      (fun l hl hrl => by
        have := hag (l + 1) (by simpa using hl)
          (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hrl)
        simpa using this)
      (h.2 a ha)

/-- **The functor's premise survives the exchange**: every clause reads
the fields through `chainsXI` or `xEntry`. -/
theorem xChainsOk_congr {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Fss' Ess : List (List AnnotTerm)}
    (hag : FssAgree rss Fss Fss') (h : XChainsOk (V := V) u w ρp Ids rss tlss Eiss Fss Ess) :
    XChainsOk (V := V) u w ρp Ids rss tlss Eiss Fss' Ess where
  hI := h.hI
  hok := by
    intro X hX t ht
    have := h.hok X hX t ht
    rwa [chainsXI_congr hag] at this
  hfit := by
    intro X hX t ht j hj
    rw [← hag.1] at hj
    exact slotsFitX_congr _ _ 0 [] (hag.2 j hj).1
      (fun l hl hrl => (hag.2 j hj).2 l hl (by rwa [Nat.zero_add] at hrl))
      (h.hfit X hX t ht j hj)
  hclosed := by
    obtain ⟨L, hL⟩ := h.hclosed
    refine ⟨L, ?_⟩
    show IsClosedFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss tlss Eiss Fss' Ess) L
    unfold fixFunVI famFI fixStepI
    rw [← chainsXI_congr (u := u) (Ids := Ids) (nIdx := Ids.length) (tlss := tlss) (Eiss := Eiss)
      (Ess := Ess) hag]
    exact hL

/-- The leaf term is the same at agreeing field lists. -/
theorem nativeTyAVI_congr {u w : Nat} {pps : List (Nat × Nat × AnnotTerm)} {Ids : List AnnotTerm}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss : List (List (List AnnotTerm))} {Fss Fss' Ess : List (List AnnotTerm)}
    (h : FssAgree rss Fss Fss') :
    nativeTyAVI u w pps Ids rss tlss Eiss Fss Ess = nativeTyAVI u w pps Ids rss tlss Eiss Fss' Ess := by
  unfold nativeTyAVI fixBodyAVI fixFunAVI
  rw [chainsXI_congr (u := u) (Ids := Ids) (nIdx := Ids.length) (tlss := tlss) (Eiss := Eiss)
    (Ess := Ess) h]

/-! ## The one-member block model -/

/-- **The uniform block model of a native block**: one member, every field
targeting it, the tuple operator the one-member tuple of `fixFunVI`
at the block model's own lists, the injections the tagged point-terminated
towers (the point at `w = 0`). -/
@[expose] noncomputable def BlockModel.ofNative (nP : Nat) (resSort : Level) (isProp large : Bool)
    (env₀ : Env) (T : Name) (nIdx : Nat) (ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (uAV : (Name → Nat) → Nat) (ctorsA : List (ConstantVal × Nat)) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (ksF : Nat → List RecFieldKind) (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : BlockModel V where
  nP := nP
  k := 1
  resSort := resSort
  isProp := isProp
  large := large
  env₀ := env₀
  memberNames := [T]
  nIdxs := [nIdx]
  ppsM := fun _ => ppsAll
  uM := fun _ => uAV
  ctorsM := fun _ => ctorsA
  idxF := fun _ => idxF
  dsF := fun _ => dsF
  esF := fun _ => esF
  srcsF := fun _ => srcsF
  ksF := fun _ => ksF
  tgts := fun _ _ _ => 0
  fvsPF := fun _ => fvsPF
  xFvsF := fun _ => xFvsF
  xrestF := fun _ => xrestF
  eissF := fun _ => eissF
  tssF := fun _ => tssF
  pins := []
  Φ := fun ψ ρp =>
    let cds := fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0
    let Ids := ((ppsAll ψ).drop nP).map (·.2.2)
    oneTuple (fixFunVI (uAV ψ) (resSort.eval ψ) ρp Ids Ids.length (rssOfK ksF ctorsA.length)
      (tlssOfR cds) (eissOfR cds) (fssOfR nP cds) (essOfR cds))
  pinCar := fun _ _ _ _ => pt
  inj := fun ψ _ j fs => injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))

section One

variable {nP : Nat} {resSort : Level} {isProp large : Bool} {env₀ : Env} {T : Name} {nIdx : Nat}
  {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {uAV : (Name → Nat) → Nat}
  {ctorsA : List (ConstantVal × Nat)} {idxF : Nat → List Expr}
  {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}

local notation "D" => (BlockModel.ofNative (V := V) nP resSort isProp large env₀ T nIdx ppsAll uAV
  ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF)

/-- The one-member block model's index-tuple set is the native one. -/
theorem ofNative_idx (ψ : Name → Nat) (ρp : Nat → V) :
    (D).idx ψ ρp = fun _ => idxSet (uAV ψ) ρp ((D).IdsM 0 ψ) := rfl

/-- The one-member block model's operator applied: the native functor at the
tuple's component `0`. -/
theorem ofNative_Φ (ψ : Name → Nat) (ρp : Nat → V) (X : Nat → V) (mm : Nat) :
    (D).Φ ψ ρp X mm
      = SetTheory.app (fixFunVI (uAV ψ) ((D).w ψ) ρp ((D).IdsM 0 ψ) ((D).IdsM 0 ψ).length ((D).rss 0)
          ((D).tlss 0 ψ) ((D).Eiss 0 ψ) ((D).Fss 0 ψ) ((D).Ess 0 ψ)) (X 0) := rfl

/-- **`functor` at `k = 1`**: from the native functor's laws. -/
theorem ofNative_functor {ψ : Name → Nat} {ρp : Nat → V}
    (hX : XChainsOk (uAV ψ) ((D).w ψ) ρp ((D).IdsM 0 ψ) ((D).rss 0) ((D).tlss 0 ψ) ((D).Eiss 0 ψ)
      ((D).Fss 0 ψ) ((D).Ess 0 ψ)) :
    MonoTuple ((D).w ψ) 1 ((D).idx ψ ρp) ((D).Φ ψ ρp) ∧
    MapsTuple ((D).w ψ) 1 ((D).idx ψ ρp) ((D).Φ ψ ρp) ∧
    ∃ L, IsClosedTuple ((D).w ψ) 1 ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  ⟨monoTuple_one_of (fixFunVI_mono hX), mapsTuple_one_of (fixFunVI_maps hX),
    closedTuple_one_of (fixFunVI_closed_exists hX)⟩

/-- **`fibre` at `k = 1`**: the native elimination and introduction,
the X-chain fit read semantically. -/
theorem ofNative_fibre {ψ : Name → Nat} {ρp : Nat → V}
    (hX : XChainsOk (uAV ψ) ((D).w ψ) ρp ((D).IdsM 0 ψ) ((D).rss 0) ((D).tlss 0 ψ) ((D).Eiss 0 ψ)
      ((D).Fss 0 ψ) ((D).Ess 0 ψ))
    {X : Nat → V} (hXs : InTupleSpace ((D).w ψ) 1 ((D).idx ψ ρp) X) {t : V}
    (ht : t ∈ˢ (D).idx ψ ρp 0) (x : V) :
    x ∈ˢ SetTheory.app ((D).Φ ψ ρp X 0) t ↔
      ∃ j fs, j < ctorsA.length ∧ (D).ChainFit ψ ρp X t 0 j fs ∧ x = (D).inj ψ 0 j fs := by
  have hX0 : X 0 ∈ˢ lfpFamSpace V ((D).w ψ) (idxSet (uAV ψ) ρp ((D).IdsM 0 ψ)) := by
    rw [lfpFamSpace_eq]; exact inTupleSpace_one_iff.mp hXs
  have hlenF : ((D).Fss 0 ψ).length = ctorsA.length := by
    show (fssOfR _ (fixCtorDataList dsF esF ksF eissF tssF ψ ctorsA 0)).length = _
    rw [fssOfR_length, fixCtorDataList_length]
  have ht' : t ∈ˢ idxSet (uAV ψ) ρp ((D).IdsM 0 ψ) := ht
  rw [ofNative_Φ, fixFunVI_app hX0, famFI_app ht']
  -- the fit, translated
  have hfit : ∀ j, j < ctorsA.length → ∀ fs,
      SpineFit (cons t (cons (X 0) ρp))
          (chainXIGo (uAV ψ) ((D).IdsM 0 ψ) (((D).rss 0).getD j []) (((D).tlss 0 ψ).getD j [])
            (((D).Eiss 0 ψ).getD j []) (((D).Fss 0 ψ).getD j []) 0) fs ↔
        FitsFrom (((D).rss 0).getD j []) ((D).slotAt ψ X 0 j) 0 ρp (((D).Fss 0 ψ).getD j []) fs := by
    intro j hj fs
    have := spineFit_chainXIGo_iff (w := (D).w ψ) hX.hI (X := X 0) (t := t)
      (rs := ((D).rss 0).getD j []) (tls := ((D).tlss 0 ψ).getD j []) (Eis := ((D).Eiss 0 ψ).getD j [])
      (((D).Fss 0 ψ).getD j []) 0 [] fs rfl (hX.hfit (X 0) hX0 t ht j (by rw [hlenF]; exact hj))
    exact this
  have hterm : ∀ j fs, fs.length = (((D).Fss 0 ψ).getD j []).length →
      (EqAll (consList fs (cons t (cons (X 0) ρp)))
          (eqsXI ((D).IdsM 0 ψ).length (((D).Fss 0 ψ).getD j []).length (((D).Ess 0 ψ).getD j [])) ↔
        ∀ l, l < ((D).IdsM 0 ψ).length →
          interp V (consList fs ρp) ((((D).Ess 0 ψ).getD j []).getD l default) = projS l t) :=
    fun j fs hlen => EqAll_eqsXI_gen hlen
  by_cases hw : (D).w ψ = 0
  · -- squash regime: the fibre is the point, some constructor fits
    have hw' : resSort.eval ψ = 0 := hw
    rw [hw]
    constructor
    · intro hx
      obtain ⟨rfl, j, fs, hj, hlen, hsp, hall⟩ := fixStepI_zero_elim hx
      refine ⟨j, fs, by rw [← hlenF]; exact hj, ⟨(hfit j (by rw [← hlenF]; exact hj) fs).mp hsp,
        (hterm j fs hlen).mp hall⟩, ?_⟩
      change (pt : V) = injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))
      rw [hw', injW_zero]
    · rintro ⟨j, fs, hj, ⟨hf, hall⟩, rfl⟩
      have hjF : j < ((D).Fss 0 ψ).length := by rw [hlenF]; exact hj
      have hlen : fs.length = (((D).Fss 0 ψ).getD j []).length := hf.length_eq
      change injW (resSort.eval ψ) j (mkTower (fs ++ [pt])) ∈ˢ _
      rw [hw', injW_zero]
      unfold fixStepI
      refine pt_mem_sumSet_zero (i := j) (a := pt) ?_
      unfold sumFibre
      rw [chainsXI_getElem?, if_pos hjF]
      unfold chainXI
      refine pt_mem_tower_teleOfFields (as := fs ++ [pt]) ?_
      exact spineFit_append_idxEq.mpr ⟨fs, rfl, (hfit j hj fs).mpr hf, (hterm j fs hlen).mpr hall⟩
  · -- graph regime: the fibre is the tagged towers of the fitting spines
    have hw' : resSort.eval ψ ≠ 0 := hw
    constructor
    · intro hx
      obtain ⟨j, fs, rfl, hj, hlen, hsp, hall⟩ := fixStepI_elim hw hx
      refine ⟨j, fs, by rw [← hlenF]; exact hj, ⟨(hfit j (by rw [← hlenF]; exact hj) fs).mp hsp,
        (hterm j fs hlen).mp hall⟩, ?_⟩
      change inj j (mkTower (fs ++ [pt])) = injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))
      rw [injW_pos hw']
    · rintro ⟨j, fs, hj, ⟨hf, hall⟩, rfl⟩
      have hjF : j < ((D).Fss 0 ψ).length := by rw [hlenF]; exact hj
      have hlen : fs.length = (((D).Fss 0 ψ).getD j []).length := hf.length_eq
      change injW (resSort.eval ψ) j (mkTower (fs ++ [pt])) ∈ˢ _
      rw [injW_pos hw']
      unfold fixStepI
      refine inj_mem hw ?_
      unfold sumFibre
      rw [chainsXI_getElem?, if_pos hjF]
      unfold chainXI
      refine mkTower_mem hw (fitsS_teleOfFields.mpr ?_)
      exact spineFit_append_idxEq.mpr ⟨fs, rfl, (hfit j hj fs).mpr hf, (hterm j fs hlen).mpr hall⟩

/-- **`leaf` at `k = 1`**: the former's fold, the carrier read as the
one-member tuple lfp. -/
theorem ofNative_leaf {ψ : Name → Nat} {ρ : Nat → V} {as is : List V}
    (hsp : SpineFit ρ ((D).params ψ) as) (hi : SpineFit (consList as ρ) ((D).IdsM 0 ψ) is)
    (hbase : FixBaseI (uAV ψ) ((D).w ψ) (consList (as ++ is) ρ) ((D).IdsM 0 ψ) ((D).rss 0)
      ((D).tlss 0 ψ) ((D).Eiss 0 ψ) ((D).Fss 0 ψ) ((D).Ess 0 ψ)) :
    (as ++ is).foldl SetTheory.app (interp V ρ
        (nativeTyAVI (uAV ψ) ((D).w ψ) (ppsAll ψ) ((D).IdsM 0 ψ) ((D).rss 0) ((D).tlss 0 ψ)
          ((D).Eiss 0 ψ) ((D).Fss 0 ψ) ((D).Ess 0 ψ)))
      = SetTheory.app (lfpTuple ((D).w ψ) 1 ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ)) 0)
          ((D).tup ψ 0 is) := by
  have hspAll : SpineFit ρ ((ppsAll ψ).map (·.2.2)) (as ++ is) := by
    have h := hsp.append hi
    have hpps : (ppsAll ψ).map (·.2.2) = (D).params ψ ++ (D).IdsM 0 ψ := by
      show (ppsAll ψ).map (·.2.2) = ((ppsAll ψ).take nP).map (·.2.2) ++ ((ppsAll ψ).drop nP).map (·.2.2)
      rw [← List.map_append, List.take_append_drop]
    rw [hpps]; exact h
  rw [ConLeche.Semantics.nativeTyAVI_fold hspAll hbase]
  have hlenIs : is.length = ((D).IdsM 0 ψ).length := hi.length_eq
  have hsh : shiftE ((D).IdsM 0 ψ).length 0 (consList (as ++ is) ρ) = consList as ρ := by
    rw [consList_append, ← hlenIs]; exact shiftE_consList is (consList as ρ)
  have hfr : ConLeche.Semantics.frameIdx ((D).IdsM 0 ψ).length (consList (as ++ is) ρ) = is := by
    rw [consList_append, ← hlenIs]; exact ConLeche.Semantics.frameIdx_consList' is (consList as ρ)
  rw [hsh, hfr, fixFamI_eq_lfpTuple]
  rfl

/-- **`ctor` at `k = 1`**: the constructor's fold. -/
theorem ofNative_ctor {ψ : Name → Nat} {ρ : Nat → V} {j : Nat} {as fs : List V} (hw : (D).w ψ ≠ 0)
    (hsp₂ : SpineFit (consList as ρ) (((D).Fss 0 ψ).getD j []) fs)
    (hok : SumFieldsOkB ((D).w ψ) (consList as ρ) (uChains ((D).Fss 0 ψ)))
    (hjF : ((D).Fss 0 ψ)[j]? = some (((dsF j ψ).drop nP).map (·.2.2)))
    (hsp₁ : SpineFit ρ (((dsF j ψ).take nP).map (·.2.2)) as) :
    (as ++ fs).foldl SetTheory.app (interp V ρ
        (sumMkAV ((D).w ψ) j (dsF j ψ) (((dsF j ψ).drop nP).map (·.2.2)) (uChains ((D).Fss 0 ψ))))
      = (D).inj ψ 0 j fs := by
  have hjD : ((D).Fss 0 ψ).getD j [] = ((dsF j ψ).drop nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, hjF]; rfl
  rw [hjD] at hsp₂
  have hsplit : dsF j ψ = (dsF j ψ).take nP ++ (dsF j ψ).drop nP := (List.take_append_drop _ _).symm
  have := sumMkAV_fold (V := V) (j := j) hw (pds := (dsF j ψ).take nP) (fds := (dsF j ψ).drop nP)
    (Fss := uChains ((D).Fss 0 ψ)) hsp₁ hsp₂ hok (by rw [uChains_getElem?, hjF]; rfl)
  rw [← hsplit] at this
  rw [this]
  have hw' : resSort.eval ψ ≠ 0 := hw
  show inj j (mkTower (fs ++ [pt])) = injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))
  rw [injW_pos hw']

/-- **`ctor` at `k = 1`, at a `Prop`-valued block too** (task #315
M7-3 session 7): `IsBlockModel.ctor` carries no `w ≠ 0` premise, and
at `w = 0` the constructor's tower is the point (`sumMkAV_zero`) and so
is the injection (`injW_zero`) — the mutual route's own branch. -/
theorem ofNative_ctor' {ψ : Name → Nat} {ρ : Nat → V} {j : Nat} {as fs : List V}
    (hsp₂ : SpineFit (consList as ρ) (((D).Fss 0 ψ).getD j []) fs)
    (hok : (D).w ψ ≠ 0 → SumFieldsOkB ((D).w ψ) (consList as ρ) (uChains ((D).Fss 0 ψ)))
    (hjF : ((D).Fss 0 ψ)[j]? = some (((dsF j ψ).drop nP).map (·.2.2)))
    (hsp₁ : SpineFit ρ (((dsF j ψ).take nP).map (·.2.2)) as) :
    (as ++ fs).foldl SetTheory.app (interp V ρ
        (sumMkAV ((D).w ψ) j (dsF j ψ) (((dsF j ψ).drop nP).map (·.2.2)) (uChains ((D).Fss 0 ψ))))
      = (D).inj ψ 0 j fs := by
  by_cases hw : (D).w ψ = 0
  · have hw' : resSort.eval ψ = 0 := hw
    show (as ++ fs).foldl SetTheory.app (interp V ρ
        (sumMkAV (resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop nP).map (·.2.2))
          (uChains ((D).Fss 0 ψ))))
      = injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))
    rw [hw', sumMkAV_zero, foldl_app_pt, injW_zero]
  · exact ofNative_ctor hw hsp₂ (hok hw) hjF hsp₁

/-- **`mkZero` at `k = 1`**. -/
theorem ofNative_mkZero (ψ : Name → Nat) (hw : (D).w ψ = 0) (mm j : Nat) (fs : List V) :
    (D).inj ψ mm j fs = pt := by
  show injW (resSort.eval ψ) j (mkTower (fs ++ [pt])) = pt
  have hw' : resSort.eval ψ = 0 := hw
  rw [hw', injW_zero]

/-- **`mkInj` at `k = 1`**: tag disjointness and the tower's
injectivity at equal lengths. -/
theorem ofNative_mkInj (ψ : Name → Nat) (hw : (D).w ψ ≠ 0) {mm j j' : Nat} {fs fs' : List V}
    (hlen : fs.length = (((D).Fss 0 ψ).getD j []).length)
    (hlen' : fs'.length = (((D).Fss 0 ψ).getD j' []).length)
    (h : (D).inj ψ mm j fs = (D).inj ψ mm j' fs') : j = j' ∧ fs = fs' := by
  have hw' : resSort.eval ψ ≠ 0 := hw
  change injW (resSort.eval ψ) j (mkTower (fs ++ [pt])) = injW (resSort.eval ψ) j' (mkTower (fs' ++ [pt])) at h
  rw [injW_pos hw', injW_pos hw'] at h
  obtain ⟨rfl, h2⟩ := inj_inj h
  refine ⟨rfl, ?_⟩
  have := mkTower_inj (by simp [hlen, hlen']) h2
  exact List.append_cancel_right this

end One

end ConLeche.Model
