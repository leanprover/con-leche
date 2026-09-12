module

public import ConLeche.Model.IndRep
public section

/-!
# The representations of the pinned basis blocks (task #280)

The pinned blocks are valued by their direct pins (`pinnedStructT`),
not by the fixpoint route's towers, so their representations are
supplied by hand, one per block: the datum is the block's spelling and
an abstract functor with the pin's own injections.  This module holds
the kit shared by all of them and the zero-constructor case
(`indRep_zeroCtor`: `Empty` at `Type`, `False` at `Prop` — the leaf is
the empty set, the least fixed point of the functor with no chains).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Kit -/

/-- The least fixed point of a functor whose fibres are all empty is
the empty family. -/
theorem lfpFamSet_app_eq_empty {w : Nat} {I F : V}
    (hF : ∀ X, X ∈ˢ famSpace w I → ∀ i, i ∈ˢ I → app (app F X) i = empty)
    {i : V} (hi : i ∈ˢ I) : app (lfpFamSet w I F) i = empty := by
  have hL : IsClosedFam w I F (graph (fun _ => empty) I) := by
    refine ⟨graph_mem_famSpace fun _ _ => empty_mem_univ w, fun i hi x hx => ?_⟩
    rw [hF _ (graph_mem_famSpace fun _ _ => empty_mem_univ w) i hi] at hx
    exact absurd hx (not_mem_empty x)
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => absurd hx (not_mem_empty x))
  have := lfpFamSet_le hL i hi x hx
  rw [app_graph hi] at this
  exact this

/-- The tagged sum of empty fibres is empty. -/
theorem sumSet_of_empty {w : Nat} {f : Nat → V} (hf : ∀ i, f i = empty) : sumSet w f = empty := by
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => absurd hx (not_mem_empty x))
  by_cases hw : w = 0
  · subst hw
    obtain ⟨-, i, a, ha⟩ := sumSet_zero_elim hx
    rw [hf i] at ha
    exact absurd ha (not_mem_empty a)
  · obtain ⟨i, a, ha, -⟩ := sumSet_elim hw hx
    rw [hf i] at ha
    exact absurd ha (not_mem_empty a)

omit [SetTheory V] in
theorem chainsXI_nil (u : Nat) (Ids : List AnnotTerm) (nIdx : Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm)))
    (Ess : List (List AnnotTerm)) : chainsXI u Ids nIdx rss tlss Eiss [] Ess = [] := rfl

/-- The fixpoint route's functor with no chains has empty fibres. -/
theorem fixStepI_nil {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Ess : List (List AnnotTerm)} (X t : V) :
    fixStepI u w ρp Ids Ids.length rss tlss Eiss [] Ess X t = empty := by
  unfold fixStepI
  refine sumSet_of_empty fun i => ?_
  unfold sumFibre
  rw [chainsXI_nil]
  rfl

/-! ## Zero-constructor blocks -/

/-- The datum of a zero-constructor block: no parameters, no indices,
the tagged functor with no chains, the point as (never used)
injection.  One member, the block's own former `T` (task #278 M2.6). -/
@[expose] noncomputable def zeroCtorData (env₀ : Env) (T : Name) (resSort : Level) :
    IndRepData V where
  nP := 0
  nIdx := 0
  resSort := resSort
  isProp := (Level.isEquiv resSort .zero == some true)
  large := true
  env₀ := env₀
  ctorsA := []
  idxF := fun _ => []
  dsF := fun _ _ => []
  esF := fun _ _ => []
  srcsF := fun _ => []
  ksF := fun _ => []
  fvsPF := fun _ => []
  xFvsF := fun _ => []
  xrestF := fun _ => default
  eissF := fun _ _ => []
  essC := fun _ _ => []
  eissC := fun _ _ => []
  tssF := fun _ _ => []
  k := 1
  nIdxs := [0]
  memberNames := [T]
  mems := fun _ => 0
  tgts := fun _ _ => 0
  ppsM := fun _ _ => []
  lvlsM := fun _ _ => []
  IdsC := fun _ => []
  u := fun _ => 0
  tup := fun _ _ is => tupW 0 is
  Φ := fun ψ ρp => fixFunVI 0 (resSort.eval ψ) ρp [] 0 [] [] [] [] []
  inj := fun _ _ _ => pt

/-- **A zero-constructor block is represented**: its stored type is
`Sort resSort`, its recursor has one motive and no rules, and its leaf
denotes the empty set. -/
theorem indRep_zeroCtor (m : EnvModel V env) {T : Name} {cvT cvR : ConstantVal}
    {rules : List RecRule} (resSort : Level)
    (hty : cvT.type = .sort resSort) (hrules : rules = [])
    (hres : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
      resSort.eval ψ₁ = resSort.eval ψ₂)
    (hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (m.acval T ψ) = empty) :
    IndRep m T cvT cvR 1 1 rules (zeroCtorData env T resSort) 0 := by
  let d : IndRepData V := zeroCtorData env T resSort
  show IndRep m T cvT cvR 1 1 rules d 0
  have hidx : ∀ ρp : Nat → V, d.idx (fun _ => 0) ρp = unitSet := fun _ => rfl
  have hIdx : ∀ (ψ : Name → Nat) (ρp : Nat → V), IdxOk (d.u ψ) ρp (d.IdsC ψ) := fun _ _ => ⟨trivial, trivial⟩
  have hX : ∀ (ψ : Name → Nat) (ρp : Nat → V),
      XChainsOk (d.u ψ) (d.w ψ) ρp (d.IdsC ψ) d.rss (d.tlss ψ) (d.Eiss ψ) (d.Fss ψ) (d.Ess ψ) := by
    intro ψ ρp
    refine ⟨hIdx ψ ρp, (fun X _ t _ Fs hFs => nomatch hFs), (fun _ _ _ _ j hj => nomatch hj), ?_⟩
    refine ⟨graph (fun _ => empty) (idxSet 0 ρp []), graph_mem_famSpace fun _ _ => empty_mem_univ _,
      fun i hi x hx => ?_⟩
    rw [fixFunVI_app (by rw [lfpFamSpace_eq]; exact graph_mem_famSpace fun _ _ => empty_mem_univ _),
      famFI_app hi] at hx
    have : fixStepI (d.u ψ) (d.w ψ) ρp (d.IdsC ψ) (d.IdsC ψ).length d.rss (d.tlss ψ) (d.Eiss ψ)
        (d.Fss ψ) (d.Ess ψ) (graph (fun _ => empty) (idxSet 0 ρp [])) i = empty :=
      fixStepI_nil (Ids := []) _ _
    rw [this] at hx
    exact absurd hx (not_mem_empty x)
  have hfibreE : ∀ (ψ : Name → Nat) (ρp : Nat → V) (X t : V), X ∈ˢ famSpace (d.w ψ) (d.idx ψ ρp) →
      t ∈ˢ d.idx ψ ρp → app (app (d.Φ ψ ρp) X) t = empty := by
    intro ψ ρp X t hX ht
    have hX' : X ∈ˢ lfpFamSpace V (resSort.eval ψ) (idxSet 0 ρp []) := by
      rw [lfpFamSpace_eq]; exact hX
    have ht' : t ∈ˢ idxSet 0 ρp [] := ht
    show app (app (fixFunVI 0 (resSort.eval ψ) ρp [] 0 [] [] [] [] []) X) t = empty
    rw [fixFunVI_app hX', famFI_app ht']
    exact fixStepI_nil (Ids := []) X t
  refine {
    member := rfl
    strip := ⟨[], by rw [hty]; rfl⟩
    isProp := rfl
    mI := rfl
    rP := rfl
    rules := fun _ => by rw [hrules]; rfl
    former := ?_
    ctors := fun j cA hj => nomatch hj
    memsFound := fun j hj => absurd hj (Nat.not_lt_zero j)
    idxRes := fun j cA hj => nomatch hj
    uParams := fun _ _ _ => rfl
    paramsIff := fun j cA hj => nomatch hj
    chains := fun ψ ρp _ => xChainsOk_toChainsOk (hX ψ ρp)
    functor := fun ψ ρp _ => ⟨fixFunVI_mem (hX ψ ρp).hok, fixFunVI_mono (hX ψ ρp),
      fixFunVI_maps (hX ψ ρp), fixFunVI_closed_exists (hX ψ ρp)⟩
    fibre := fun ψ ρp _ X hX t ht x => by
      rw [hfibreE ψ ρp X t hX ht]
      exact ⟨fun h => absurd h (not_mem_empty x), fun ⟨j, _, hj, _⟩ => nomatch hj⟩
    leaf := ?_
    tupMem := fun _ ρp _ is hi => by
      show tupW 0 is ∈ˢ idxSet 0 ρp ([] : List AnnotTerm)
      exact tupW_mem hi
    ctor := fun j cA hj => nomatch hj
    mkZero := fun _ _ _ _ => rfl
    mkInj := fun _ _ j _ _ _ hj => nomatch hj }
  · -- the former's data
    refine ⟨fun ψ => ?_, (fun _ => rfl), (fun _ _ h => nomatch h), fun ψ ρ => ?_, (fun _ => trivial),
      (fun ψ₁ ψ₂ h => ⟨rfl, hres ψ₁ ψ₂ h⟩), (fun _ => rfl),
      (fun _ i hi => absurd hi (Nat.not_lt_zero i)), (fun _ _ _ => rfl)⟩
    · rw [hty, denoteMeta_sort]; rfl
    · show WellDenotedV V ρ (AnnotTerm.sort (resSort.eval ψ))
      exact ⟨by rw [WellDenoted_sort]; trivial, by rw [AnnotValid_sort]; trivial⟩
  · -- the leaf
    intro ψ ρ as is hsp₁ hsp₂
    obtain rfl : as = [] := List.length_eq_zero_iff.mp hsp₁.length_eq
    obtain rfl : is = [] := List.length_eq_zero_iff.mp hsp₂.length_eq
    show interp V ρ (m.acval T ψ) = app (lfpFamSet _ (d.idx ψ (consList [] ρ)) (d.Φ ψ (consList [] ρ))) (tupW 0 [])
    rw [hleaf ψ ρ, tupW_zero]
    refine (lfpFamSet_app_eq_empty (fun X hX i hi => hfibreE ψ _ X i hX hi) ?_).symm
    exact pt_mem_unitSet

end ConLeche.Model
