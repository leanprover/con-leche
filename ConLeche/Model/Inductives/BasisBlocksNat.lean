module

public import ConLeche.Model.Inductives.NestedPremise
public section

/-!
# The pinned `Nat` block's block model (task #315, M7-4)

The fourth of the five pinned basis blocks, and the only one whose
operator recurses: one member, no parameters, no indices, TWO
constructors — `Nat.zero` with no fields and `Nat.succ` with one
RECURSIVE field — and no pins.

The carrier is the pinned `ω`, and the whole content of `leaf` is that
**`ω` is the least pre-fixed family of the successor operator**:

* `natStepSet S = {∅} ∪ {n ∪ {n} | n ∈ S}` is the fibre of the tuple
  operator (there is one fibre: the index-tuple set of a family with no
  indices is `{pt}`);
* `⊆` is leastness against the closed tuple `ω` (`omega_inductive`),
* `⊇` is `omega_subset_inductive` at the least pre-fixed tuple, which
  IS an inductive set because `lfpTuple_closed` makes it closed under
  the operator.

The injections are `natzero` and the von Neumann successor, not tagged
towers — the second reason `ContainerModeled.inj` is guarded by
`0 < d.nP` (DESIGN §U.45; `Nat` has no parameters, so `nestedOccOk`
never pins it).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind RecRule
  ContainerInfo ContainerMember IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The successor operator -/

/-- `Nat.zero`'s value is the empty set. -/
theorem natzero_eq : (natzero : V) = empty := by unfold natzero; rfl

/-- **The step set**: zero and the successors of `S` — the fibre of
`Nat`'s block operator. -/
noncomputable def natStepSet (S : V) : V := binUnion (sing natzero) (image vsucc S)

theorem mem_natStepSet {S x : V} :
    x ∈ˢ natStepSet S ↔ x = (natzero : V) ∨ ∃ a, a ∈ˢ S ∧ x = vsucc a := by
  rw [natStepSet, mem_binUnion, mem_sing, mem_image]

/-- The step set is monotone. -/
theorem natStepSet_mono {S S' : V} (h : S ⊆ˢ S') : natStepSet S ⊆ˢ natStepSet S' := by
  intro x hx
  rcases mem_natStepSet.mp hx with rfl | ⟨a, ha, rfl⟩
  · exact mem_natStepSet.mpr (Or.inl rfl)
  · exact mem_natStepSet.mpr (Or.inr ⟨a, h a ha, rfl⟩)

/-- An inductive set is closed under the step. -/
theorem natStepSet_subset_of_inductive {I : V} (hI : Inductive I) : natStepSet I ⊆ˢ I := by
  intro x hx
  rcases mem_natStepSet.mp hx with rfl | ⟨a, ha, rfl⟩
  · rw [natzero_eq]; exact hI.1
  · exact hI.2 a ha

/-- A set closed under the step is inductive. -/
theorem inductive_of_natStepSet_subset {I : V} (h : natStepSet I ⊆ˢ I) : Inductive I := by
  refine ⟨?_, fun n hn => h _ (mem_natStepSet.mpr (Or.inr ⟨n, hn, rfl⟩))⟩
  have := h _ (mem_natStepSet.mpr (Or.inl (rfl : (natzero : V) = natzero)))
  rwa [natzero_eq] at this

theorem natzero_mem_univ_one : (natzero : V) ∈ˢ (univ 1 : V) := by
  rw [natzero_eq]; exact empty_mem_univ 1

/-- The step set stays in the first universe — where `Nat` lives. -/
theorem natStepSet_mem_univ_one {S : V} (hS : S ∈ˢ (univ 1 : V)) :
    natStepSet S ∈ˢ (univ 1 : V) := by
  have hU := univ_isTGUniverse (V := V) (n := 1) (by decide)
  have hy : (univChain 1 : V) ∈ˢ (univ 1 : V) := univChain_one_mem_univ_succ 0
  refine hU.binUnion_mem hy (hU.sing_mem hy natzero_mem_univ_one) (hU.image_mem hS ?_)
  intro x hx
  have hxU : x ∈ˢ (univ 1 : V) := hU.transitive hS hx
  exact hU.binUnion_mem hy hxU (hU.sing_mem hy hxU)

/-- **The successor is injective** — regularity, through the two-cycle
lemma: the injections of a `Type`-valued block have to be. -/
theorem vsucc_inj {a b : V} (h : vsucc a = vsucc b) : a = b := by
  have ha : a ∈ˢ vsucc b := h ▸ self_mem_vsucc a
  have hb : b ∈ˢ vsucc a := h ▸ self_mem_vsucc b
  rcases mem_vsucc.mp ha with ha' | rfl
  · rcases mem_vsucc.mp hb with hb' | hb''
    · exact (no_two_cycle ha' hb').elim
    · exact hb''.symm
  · rfl

/-- `natzero` is no successor. -/
theorem natzero_ne_vsucc (a : V) : (natzero : V) ≠ vsucc a := by
  rw [natzero_eq]
  exact fun h => vsucc_ne_empty a h.symm

/-! ## The block model -/

/-- **`Nat`'s block model**: one member, no parameters, no indices, two
constructors (`Nat.zero` with no fields, `Nat.succ` with one recursive
field), no pins; the operator the step set at the tuple's own fibre,
the injections `natzero` and the von Neumann successor. -/
@[expose] noncomputable def natBlock : BlockModel V where
  nP := 0
  k := 1
  resSort := .succ .zero
  isProp := (Level.isEquiv (.succ .zero) .zero == some true)
  large := true
  env₀ := ⟨[]⟩
  memberNames := [ConLeche.natName]
  nIdxs := [0]
  ppsM := fun _ _ => []
  uM := fun _ _ => 0
  ctorsM := fun _ =>
    [(ConLeche.natZeroA.toConstantVal, 0), (ConLeche.natSuccA.toConstantVal, 1)]
  idxF := fun _ _ => []
  dsF := fun _ j _ => if j = 0 then [] else [(0, 1, AnnotTerm.const .nat [])]
  esF := fun _ _ _ => []
  srcsF := fun _ j => if j = 0 then [] else [none]
  ksF := fun _ j => if j = 0 then [] else [.recursive]
  tgts := fun _ _ _ => 0
  fvsPF := fun _ _ => []
  xFvsF := fun _ j => if j = 0 then [] else [.fvar 0 (.const ConLeche.natName [])]
  xrestF := fun _ _ => .const ConLeche.natName []
  eissF := fun _ j _ => if j = 0 then [] else [[]]
  tssF := fun _ j _ => if j = 0 then [] else [[]]
  pins := []
  Φ := fun _ _ X _ => graph (fun _ => natStepSet (app (X 0) pt)) unitSet
  pinCar := fun _ _ _ _ => pt
  Ψaux := fun _ _ X _ => graph (fun _ => natStepSet (app (X 0) pt)) unitSet
  pinCtors := fun _ => default
  inj := fun _ _ j fs => if j = 0 then natzero else vsucc (fs.getD 0 pt)

namespace natBlock

local notation "D" => (natBlock (V := V))

/-- The index-tuple set is the one-point set at every frame. -/
theorem idx_eq (ψ : Name → Nat) (ρp : Nat → V) (mm : Nat) : (D).idx ψ ρp mm = unitSet := rfl

/-- The result sort is `Type`. -/
theorem w_eq (ψ : Name → Nat) : (D).w ψ = 1 := rfl

/-- The operator's value, spelled at the index-tuple set. -/
theorem Phi_app (ψ : Name → Nat) (ρp X : Nat → V) (mm : Nat) :
    (D).Φ ψ ρp X mm = graph (fun _ => natStepSet (app (X 0) pt)) ((D).idx ψ ρp mm) := rfl

/-- The operator maps the tuple space into itself. -/
theorem maps (ψ : Name → Nat) (ρp : Nat → V) :
    MapsTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) := by
  intro X hX mm hmm
  refine graph_mem_famSpace fun _ _ => natStepSet_mem_univ_one ?_
  exact famSpace_app (hX 0 Nat.one_pos) pt_mem_unitSet

/-- The operator is monotone: the step set is. -/
theorem mono (ψ : Name → Nat) (ρp : Nat → V) :
    MonoTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) := by
  intro X Y _ _ hXY mm hmm i hi x hx
  rw [Phi_app, app_graph hi] at hx ⊢
  exact natStepSet_mono (hXY 0 Nat.one_pos pt pt_mem_unitSet) x hx

/-- **`ω` is a closed tuple** for the step operator. -/
theorem omegaTuple_closed (ψ : Name → Nat) (ρp : Nat → V) :
    IsClosedTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp)
      (fun _ => graph (fun _ => omega) unitSet) := by
  refine ⟨fun _ _ => graph_mem_famSpace fun _ _ => omega_mem_univ_succ 0, ?_⟩
  intro mm hmm i hi x hx
  have hi' : i ∈ˢ (unitSet : V) := hi
  show x ∈ˢ app (graph (fun _ => (omega : V)) unitSet) i
  rw [app_graph hi']
  have hx' : x ∈ˢ natStepSet (app (graph (fun _ => (omega : V)) unitSet) (pt : V)) := by
    have hx2 : x ∈ˢ app (graph
        (fun _ => natStepSet (app (graph (fun _ => (omega : V)) unitSet) pt)) unitSet) i := hx
    rwa [app_graph hi'] at hx2
  rw [app_graph (pt_mem_unitSet (V := V))] at hx'
  exact natStepSet_subset_of_inductive omega_inductive x hx'

theorem closed (ψ : Name → Nat) (ρp : Nat → V) :
    ∃ L, IsClosedTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  ⟨_, omegaTuple_closed ψ ρp⟩

/-- **`ω` IS the least pre-fixed family of the successor operator** —
`leaf`'s whole content: `⊆` is leastness against the closed tuple `ω`,
`⊇` is `omega_subset_inductive` at a carrier `lfpTuple_closed` makes
inductive. -/
theorem lfp_app (ψ : Name → Nat) (ρp : Nat → V) {t : V} (ht : t ∈ˢ (D).idx ψ ρp 0) :
    app (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) 0) t = (omega : V) := by
  have hpt : t = pt := mem_unitSet_iff.mp ht
  have ht' : t ∈ˢ (unitSet : V) := ht
  refine Subset.antisymm (fun x hx => ?_) ?_
  · have hle := lfpTuple_le (omegaTuple_closed ψ ρp) 0 Nat.one_pos t ht x hx
    show x ∈ˢ (omega : V)
    rwa [app_graph ht'] at hle
  · have hcl := lfpTuple_closed (closed (V := V) ψ ρp) (mono (V := V) ψ ρp) 0 Nat.one_pos t ht
    refine omega_subset_inductive (inductive_of_natStepSet_subset (fun x hx => hcl x ?_))
    show x ∈ˢ app ((D).Φ ψ ρp (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp)) 0) t
    rw [Phi_app, app_graph ht]
    rwa [hpt] at hx

/-- The one index tuple is in the index-tuple set. -/
theorem tup_mem (ψ : Name → Nat) (ρp : Nat → V) : (D).tup ψ 0 [] ∈ˢ (D).idx ψ ρp 0 :=
  (D).tupMem (ψ := ψ) (ρp := ρp) (mm' := 0) (is := []) trivial

/-- `Nat.zero`'s field domains are empty. -/
theorem Fss_zero (ψ : Name → Nat) : ((D).Fss 0 ψ).getD 0 [] = ([] : List AnnotTerm) := rfl

/-- `Nat.succ`'s one field domain is the former's leaf. -/
theorem Fss_succ (ψ : Name → Nat) :
    ((D).Fss 0 ψ).getD 1 [] = [AnnotTerm.const .nat []] := rfl

/-- `Nat.succ`'s one field is recursive. -/
theorem rss_succ : ((D).rss 0).getD 1 [] = [true] := rfl

/-- `Nat.succ`'s slot is the tuple's own fibre. -/
theorem slot_succ (ψ : Name → Nat) (X ρ : Nat → V) :
    (D).slotAt ψ X 0 1 0 ρ = app (X 0) pt := rfl

end natBlock

/-! ## The pinned readings -/

/-- `Nat`'s leaf is its pin. -/
theorem acval_nat_eq {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA) (ψ : Name → Nat) :
    m.acval ConLeche.natName ψ = .const .nat [] := by
  have hpd : ConLeche.Verify.pinnedStructT ConLeche.natName ψ
      = some (Term.const .nat []) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  exact acval_basis_pinned hT (by decide) hpd

/-- `Nat.zero`'s leaf is its pin. -/
theorem acval_natZero_eq {env : Env} {m : EnvModel V env}
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA) (ψ : Name → Nat) :
    m.acval ConLeche.natZeroName ψ = .const .natZero [] := by
  have hpd : ConLeche.Verify.pinnedStructT ConLeche.natZeroName ψ
      = some (Term.const .natZero []) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  exact acval_basis_pinned hZ (by decide) hpd

/-- `Nat.succ`'s leaf is its pin. -/
theorem acval_natSucc_eq {env : Env} {m : EnvModel V env}
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA) (ψ : Name → Nat) :
    m.acval ConLeche.natSuccName ψ = .const .natSucc [] := by
  have hpd : ConLeche.Verify.pinnedStructT ConLeche.natSuccName ψ
      = some (Term.const .natSucc []) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  exact acval_basis_pinned hS (by decide) hpd

/-- `Nat`'s value is `ω`. -/
theorem interp_acval_nat {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA) (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.acval ConLeche.natName ψ) = (omega : V) := by
  rw [acval_nat_eq hT ψ]; rfl

/-- The `Nat` leaf reads at every depth. -/
theorem denoteMeta_natConst {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA) (ψ : Name → Nat) (d : Nat) :
    denoteMeta m.acval env ψ d (.const ConLeche.natName [])
      = some (m.acval ConLeche.natName ψ) := by
  rw [denoteMeta_const hT (by rfl)]
  show some (m.acval ConLeche.natName (Level.substFn ψ [] ([].map Level.param))) = _
  rw [Level.substFn_param_self ψ []]

/-! ## The constructors' data -/

/-- **`Nat.zero`'s reading**: no parameters, no fields, no indices —
its stored type IS the former's constant. -/
theorem natBlock_ctorData_zero {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA) :
    BlockCtorFacts m (natBlock (V := V)) [] 0 0 (ConLeche.natZeroA.toConstantVal, 0) := by
  refine ⟨hZ, rfl, ?_⟩
  refine
    { resid := ⟨[], [], rfl, rfl⟩
      read := fun ψ => ?_
      len := fun _ => rfl
      lenE := fun _ => rfl
      idxLen := rfl
      idxRead := fun _ => DenoteMetaSpine.nil
      bits := fun _ _ h => nomatch h
      okTy := fun ψ ρ => ?_
      below := fun _ => trivial
      belowE := fun _ _ h => nomatch h
      params := fun _ _ _ => ⟨rfl, rfl⟩
      srcLen := rfl
      srcBnd := fun _ h => nomatch h
      srcIdx := fun j l h => ?_
      srcProp := fun _ ψ h => ?_
      opened :=
        { residRes := fun e h => ?_
          ord := fun i x h => nomatch h
          recF := fun i x h => nomatch h
          reflF := fun i x h => nomatch h
          nestF := fun i x q h => nomatch h
          nestReflF := fun i x q h => nomatch h
          kinds := fun i h => nomatch h }
      opens := ⟨_, rfl, rfl⟩
      ksLen := rfl
      xLen := rfl
      pLen := rfl
      xIdx := fun k x h => nomatch h
      pIdx := fun k x h => nomatch h
      idxEq := rfl
      domRead := fun _ i x h => nomatch h
      eissLen := fun _ => rfl
      eisRead := fun _ i x h => nomatch h
      eisLen := fun _ i _ _ h => nomatch h
      recEntry := fun _ i _ _ h => nomatch h
      nestEisRead := fun _ i x q h => nomatch h
      nestEisLen := fun _ i q _ _ h => nomatch h
      nestEntry := fun _ i q _ _ h => nomatch h
      eissParams := fun _ _ _ => rfl
      eissBelow := fun _ i E h => nomatch h
      ordNone := fun _ _ _ _ => rfl
      tssLen := fun _ => rfl
      tssNone := fun _ _ _ => rfl
      tssBits := fun _ _ d h => nomatch h
      tssPiBits := fun _ _ d h => nomatch h
      tssBelow := fun _ _ => trivial
      tssParams := fun _ _ _ => rfl
      reflOpen := fun _ i x h => nomatch h
      eisLenRefl := fun _ i _ _ h => nomatch h
      reflEntry := fun _ i _ _ h => nomatch h
      nestReflOpen := fun _ i x q h => nomatch h
      nestEisLenRefl := fun _ i q _ _ h => nomatch h
      nestReflEntry := fun _ i q _ _ h => nomatch h }
  · show denoteMeta m.acval env ψ 0 (.const ConLeche.natName []) = _
    rw [denoteMeta_natConst hT ψ 0]
    rfl
  · show WellDenotedV V ρ (AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) [])
    rw [show AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) [] = m.acval ConLeche.natName ψ
      from rfl, acval_nat_eq hT ψ]
    exact ⟨trivial, trivial⟩
  · exact nomatch h
  · exact nomatch h
  · exact nomatch h

/-- **`Nat.succ`'s reading**: one RECURSIVE field, whose domain is the
former's own leaf — the block's only recursive occurrence, and the one
that makes the operator a fixpoint. -/
theorem natBlock_ctorData_succ {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA) :
    BlockCtorFacts m (natBlock (V := V)) [] 0 1 (ConLeche.natSuccA.toConstantVal, 1) := by
  have hds : ∀ ψ : Name → Nat, (natBlock (V := V)).dsF 0 1 ψ
      = [(0, 1, AnnotTerm.const .nat [])] := fun _ => rfl
  have hnest : ∀ i, (natBlock (V := V)).nestOf 0 1 i = none :=
    fun i => (natBlock (V := V)).nestOf_none (show (0 : Nat) < 1 from Nat.one_pos)
  have hmn : (natBlock (V := V)).memberName 0 = ConLeche.natName := rfl
  refine ⟨hS, rfl, ?_⟩
  refine
    { resid := ⟨[(.const ConLeche.natName [], { pw := .never })], [], rfl, rfl⟩
      read := fun ψ => ?_
      len := fun _ => rfl
      lenE := fun _ => rfl
      idxLen := rfl
      idxRead := fun _ => DenoteMetaSpine.nil
      bits := fun ψ d hd => ?_
      okTy := fun ψ ρ => ?_
      below := fun _ => ⟨trivial, trivial⟩
      belowE := fun _ _ h => nomatch h
      params := fun _ _ _ => ⟨rfl, rfl⟩
      srcLen := rfl
      srcBnd := fun s hs l hl => ?_
      srcIdx := fun j l h => ?_
      srcProp := fun _ ψ h => nomatch h
      opened :=
        { residRes := fun e h => nomatch h
          ord := fun i x hx hk => ?_
          recF := fun i x hx _ _ => ?_
          reflF := fun i x hx _ hk => ?_
          nestF := fun i x q hx hq => nomatch hq
          nestReflF := fun i x q hx hq => nomatch hq
          kinds := fun i hi => by match i, hi with
            | 0, _ => exact Or.inr (Or.inl rfl) }
      opens := ⟨_, rfl, rfl⟩
      ksLen := rfl
      xLen := rfl
      pLen := rfl
      xIdx := fun k x hx => ?_
      pIdx := fun k x h => nomatch h
      idxEq := rfl
      domRead := fun ψ i x hx => ?_
      eissLen := fun _ => rfl
      eisRead := fun _ i x hx _ _ => ?_
      eisLen := fun _ i _ _ _ => ?_
      recEntry := fun ψ i _ _ hi => ?_
      nestEisRead := fun _ i x q hx hq => nomatch hq
      nestEisLen := fun _ i q hq => nomatch (hnest i).symm.trans hq
      nestEntry := fun _ i q hq => nomatch (hnest i).symm.trans hq
      eissParams := fun _ _ _ => rfl
      eissBelow := fun _ i E hE => ?_
      ordNone := fun _ i h₁ h₂ => ?_
      tssLen := fun _ => rfl
      tssNone := fun _ i h => ?_
      tssBits := fun _ i d hd => ?_
      tssPiBits := fun _ i d hd => ?_
      tssBelow := fun _ i => ?_
      tssParams := fun _ _ _ => rfl
      reflOpen := fun _ i x hx _ hk => ?_
      eisLenRefl := fun _ i _ hk hi => by
        obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
        exact nomatch hk
      reflEntry := fun _ i _ hk hi => by
        obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
        exact nomatch hk
      nestReflOpen := fun _ i x q hx hq => nomatch hq
      nestEisLenRefl := fun _ i q hq => nomatch (hnest i).symm.trans hq
      nestReflEntry := fun _ i q hq => nomatch (hnest i).symm.trans hq }
  -- the type's reading: a Π over the former's leaf, ending in it
  · show denoteMeta m.acval env ψ 0
      (.forallE (.const ConLeche.natName []) (.const ConLeche.natName []) { pw := .never }) = _
    rw [denoteMeta_forallE, show (Expr.const ConLeche.natName []).instantiate1
      (Expr.fvar 0 (.const ConLeche.natName [])) = .const ConLeche.natName [] from rfl]
    simp only [denoteMeta_natConst hT, pwBit_never, hmn, ctorBodyAVI, hds, acval_nat_eq hT]
    rfl
  -- the binder's bit is nonzero, as the block's sort is
  · obtain rfl : d = (0, 1, AnnotTerm.const .nat []) := by
      rw [hds ψ] at hd
      exact (List.mem_singleton.mp hd)
    exact Iff.intro (fun h => nomatch h) (fun h => nomatch h)
  -- the type's grading
  · show WellDenotedV V ρ (AnnotTerm.pi 0 1 (AnnotTerm.const .nat [])
      (AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) []))
    rw [show AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) [] = m.acval ConLeche.natName ψ
      from rfl, acval_nat_eq hT ψ]
    exact ⟨⟨trivial, fun _ _ => trivial⟩, ⟨trivial, fun _ _ => trivial, fun h => nomatch h⟩⟩
  · rw [show (natBlock (V := V)).srcsF 0 1 = [none] from rfl] at hs
    obtain rfl : s = none := List.mem_singleton.mp hs
    exact nomatch hl
  · rw [show (natBlock (V := V)).srcsF 0 1 = [none] from rfl] at h
    match j, h with
    | 0, h => exact nomatch h
  -- the field is not ordinary
  · rw [show ((natBlock (V := V)).ksF 0 1).getD i .ordinary = .recursive from ?_] at hk
    · exact nomatch hk
    · match i, hx with
      | 0, _ => rfl
  -- the recursive field's shape
  · match i, hx with
    | 0, hx =>
      obtain rfl : x = Expr.fvar 0 (.const ConLeche.natName []) := (Option.some.inj hx).symm
      refine ⟨rfl, rfl, rfl, ⟨fun e he => (nomatch he), ⟨fun y hy => (nomatch hy), ?_⟩⟩⟩
      show Expr.mentionsFvar 0 (.const ConLeche.natName []) = false
      simp [Expr.mentionsFvar, Expr.fvarLeaves]
  · rw [show ((natBlock (V := V)).ksF 0 1).getD i .ordinary = .recursive from ?_] at hk
    · exact nomatch hk
    · match i, hx with
      | 0, _ => rfl
  · match k, hx with
    | 0, hx => exact ⟨.const ConLeche.natName [], (Option.some.inj hx).symm⟩
  · match i, hx with
    | 0, hx =>
      obtain rfl : x = Expr.fvar 0 (.const ConLeche.natName []) := (Option.some.inj hx).symm
      show denoteMeta m.acval env ψ 0 (.const ConLeche.natName []) = _
      rw [denoteMeta_natConst hT ψ 0, acval_nat_eq hT ψ]
      rfl
  · match i, hx with
    | 0, hx =>
      obtain rfl : x = Expr.fvar 0 (.const ConLeche.natName []) := (Option.some.inj hx).symm
      exact DenoteMetaSpine.nil
  · match i with
    | 0 => rfl
    | _ + 1 => rfl
  · match i, hi with
    | 0, _ =>
      show ((natBlock (V := V)).dsF 0 1 ψ).getD 0 default |>.2.2 = _
      rw [hds ψ]
      show (AnnotTerm.const .nat []) = AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) ([] ++ [])
      rw [acval_nat_eq hT ψ]
      rfl
  · match i, hE with
    | 0, hE => exact nomatch hE
    | _ + 1, hE => exact nomatch hE
  · match i with
    | 0 => exact absurd rfl h₁
    | _ + 1 => rfl
  · match i with
    | 0 => rfl
    | _ + 1 => rfl
  · match i, hd with
    | 0, hd => exact nomatch hd
    | _ + 1, hd => exact nomatch hd
  · match i, hd with
    | 0, hd => exact nomatch hd
    | _ + 1, hd => exact nomatch hd
  · match i with
    | 0 => exact trivial
    | _ + 1 => exact trivial
  · rw [show ((natBlock (V := V)).ksF 0 1).getD i .ordinary = .recursive from ?_] at hk
    · exact nomatch hk
    · match i, hx with
      | 0, _ => rfl

/-! ## The read-back -/

/-- **`Nat`'s group, read back**: the one-member group with the two
constructors, at the environment that stores the pinned block.  Four
`Env.find?` results are the reading's only environment inputs — the
former, the recursor (the parameter count comes off `Nat.zero`'s
record, the motive walk off the recursor's type) and the two rules'
constructors. -/
theorem containerInfo?_natA {env : Env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hR : env.find? (ConLeche.natName.str "rec") = some ConLeche.natRecA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA) :
    ConLeche.containerInfo? env ConLeche.natName
      = some ⟨0, [⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩]⟩ := by
  have hE : ConLeche.natName = Name.anonymous.str "Nat" := rfl
  have hZE : ConLeche.natZeroName = (Name.anonymous.str "Nat").str "zero" := rfl
  have hSE : ConLeche.natSuccName = (Name.anonymous.str "Nat").str "succ" := rfl
  rw [hE] at hT hR
  rw [hZE] at hZ
  rw [hSE] at hS
  have hmot : ConLeche.containerMotiveMember? env 0 0
      (Expr.forallE (.const (Name.anonymous.str "Nat") [])
        (.sort (.param (Name.anonymous.str "u"))) { pw := .never })
      = some (Name.anonymous.str "Nat") := by
    simp +decide [ConLeche.containerMotiveMember?, Expr.piBinders, Expr.getAppFn,
      Expr.getAppArgs, hT]
  have hmot2 : ConLeche.containerMotiveMember? env 0 1
      (Expr.app (.bvar 0) (.const ((Name.anonymous.str "Nat").str "zero") [])) = none := by
    simp [ConLeche.containerMotiveMember?, Expr.piBinders]
  simp +decide [ConLeche.containerInfo?, hT, hR, hZ, hS, ConLeche.natA, ConLeche.natRecA,
    ConLeche.natZeroA, ConLeche.natSuccA, Expr.stripPis,
    ConLeche.containerMembersGo, hmot, hmot2, Option.bind,
    ConLeche.natZeroName, ConLeche.natSuccName, ConLeche.natName]
  rfl

/-! ## The block model's clauses -/

/-- `Nat.succ`'s value at a natural. -/
theorem natsucc_eq_vsucc : (natsucc : V → V) = vsucc := by unfold natsucc; rfl

/-- **`Nat` is represented by its block model**: the syntactic clauses
are the pin's own records (`mI = rP = 3`, two rules, the former a bare
sort), and the semantic ones the step operator — whose least pre-fixed
tuple's fibre IS `ω` (`natBlock.lfp_app`) and whose injections ARE the
pinned `Nat.zero` and `Nat.succ`. -/
theorem natBlock_isBlockModel {env : Env} {m : EnvModel V env} {cvR : ConstantVal}
    {rules : List RecRule}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA)
    (hrules : rules ≠ [] →
      rules.map (·.ctor) = [ConLeche.natZeroName, ConLeche.natSuccName]) :
    IsBlockModel m ConLeche.natName ConLeche.natA.toConstantVal cvR 3 3 rules
      (natBlock (V := V)) 0 where
  memberLt := Nat.one_pos
  member := rfl
  strip := ⟨[], .succ .zero, rfl, fun _ => rfl⟩
  isProp := rfl
  mI := rfl
  rP := rfl
  rules := hrules
  former :=
    { read := fun ψ => by rw [show ConLeche.natA.toConstantVal.type
        = Expr.sort (.succ .zero) from rfl, denoteMeta_sort]; rfl
      len := fun _ => rfl
      bits := fun _ _ h => nomatch h
      okTy := fun _ _ => ⟨trivial, trivial⟩
      below := fun _ => trivial
      params := fun _ _ _ => ⟨rfl, rfl⟩ }
  ctors := fun mm' j cA hmm hj => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.natZeroA.toConstantVal, 0) := (Option.some.inj hj).symm
      exact natBlock_ctorData_zero hT hZ
    | 1, hj =>
      obtain rfl : cA = (ConLeche.natSuccA.toConstantVal, 1) := (Option.some.inj hj).symm
      exact natBlock_ctorData_succ hT hS
  memsFound := fun mm' hmm => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    exact ⟨_, _, hT⟩
  pinsFound := fun _ h => nomatch h
  tgtsLt := fun _ _ _ _ _ _ => Nat.one_pos
  idxRes := fun _ _ _ _ _ _ h => nomatch h
  uParams := fun _ _ _ _ _ => rfl
  paramsIff := fun _ _ _ _ _ _ _ => Iff.rfl
  idxOk := fun _ _ _ _ _ => ⟨trivial, trivial⟩
  functor := fun ψ ρp _ => ⟨natBlock.mono ψ ρp, natBlock.maps ψ ρp, natBlock.closed ψ ρp⟩
  fibre := fun ψ ρp _ X _ mm' hmm t ht x => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    have hpt : t = pt := mem_unitSet_iff.mp ht
    rw [natBlock.Phi_app, app_graph ht, mem_natStepSet]
    constructor
    · rintro (rfl | ⟨a, ha, rfl⟩)
      · exact ⟨0, [], Nat.zero_lt_two, ⟨trivial, fun l hl => (nomatch hl)⟩, rfl⟩
      · refine ⟨1, [a], Nat.one_lt_two, ⟨⟨?_, trivial⟩, fun l hl => (nomatch hl)⟩, rfl⟩
        show a ∈ˢ (natBlock (V := V)).slotAt ψ X 0 1 0 ρp
        rw [natBlock.slot_succ]
        exact ha
    · rintro ⟨j, fs, hj, ⟨hfit, -⟩, rfl⟩
      match j, hj with
      | 0, _ => exact Or.inl rfl
      | 1, _ =>
        have hlen : fs.length = 1 := by
          have := FitsFrom.length_eq hfit
          rwa [natBlock.Fss_succ] at this
        match fs, hlen with
        | [a], _ =>
          refine Or.inr ⟨a, ?_, rfl⟩
          have ha : a ∈ˢ (natBlock (V := V)).slotAt ψ X 0 1 0 ρp := by
            have h1 := hfit
            rw [natBlock.Fss_succ, natBlock.rss_succ] at h1
            exact h1.1
          rwa [natBlock.slot_succ] at ha
  pinShape := fun _ h => nomatch h
  pinMem := fun _ _ _ _ _ _ h => nomatch h
  pinMono := fun _ _ _ _ _ _ _ _ _ h => nomatch h
  auxFunctor := fun ψ ρp _ => ⟨natBlock.mono ψ ρp, natBlock.maps ψ ρp, natBlock.closed ψ ρp⟩
  auxCompose := fun _ _ => composeΦ_zero.symm
  auxPinsCar := fun _ _ _ _ h => nomatch h
  auxPinIdx := fun _ h => nomatch h
  auxFibre := BlockModel.auxFibre_of_noPins _ rfl (fun _ _ => rfl)
    (fun _ _ _ _ _ => Nat.one_pos)
    (fun ψ ρp _ X _ mm' hmm t ht x => by
        obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
        have hpt : t = pt := mem_unitSet_iff.mp ht
        rw [natBlock.Phi_app, app_graph ht, mem_natStepSet]
        constructor
        · rintro (rfl | ⟨a, ha, rfl⟩)
          · exact ⟨0, [], Nat.zero_lt_two, ⟨trivial, fun l hl => (nomatch hl)⟩, rfl⟩
          · refine ⟨1, [a], Nat.one_lt_two, ⟨⟨?_, trivial⟩, fun l hl => (nomatch hl)⟩, rfl⟩
            show a ∈ˢ (natBlock (V := V)).slotAt ψ X 0 1 0 ρp
            rw [natBlock.slot_succ]
            exact ha
        · rintro ⟨j, fs, hj, ⟨hfit, -⟩, rfl⟩
          match j, hj with
          | 0, _ => exact Or.inl rfl
          | 1, _ =>
            have hlen : fs.length = 1 := by
              have := FitsFrom.length_eq hfit
              rwa [natBlock.Fss_succ] at this
            match fs, hlen with
            | [a], _ =>
              refine Or.inr ⟨a, ?_, rfl⟩
              have ha : a ∈ˢ (natBlock (V := V)).slotAt ψ X 0 1 0 ρp := by
                have h1 := hfit
                rw [natBlock.Fss_succ, natBlock.rss_succ] at h1
                exact h1.1
              rwa [natBlock.slot_succ] at ha)
  pinLeaf := fun _ h => nomatch h
  leaf := fun ψ ρ as is hsp hi => by
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hsp)
    obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hi)
    rw [List.append_nil, List.foldl_nil, interp_acval_nat hT,
      natBlock.lfp_app ψ (consList [] ρ) (natBlock.tup_mem ψ (consList [] ρ))]
  ctor := fun mm' j cA hmm hj ψ ρ as fs hsp hsp₂ => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hsp)
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.natZeroA.toConstantVal, 0) := (Option.some.inj hj).symm
      obtain rfl : fs = [] := by
        have := SpineFit.length_eq hsp₂
        rw [natBlock.Fss_zero] at this
        exact List.eq_nil_of_length_eq_zero this
      show ([] ++ []).foldl app (interp V ρ (m.acval ConLeche.natZeroName ψ)) = _
      rw [List.append_nil, List.foldl_nil, acval_natZero_eq hZ ψ]
      rfl
    | 1, hj =>
      obtain rfl : cA = (ConLeche.natSuccA.toConstantVal, 1) := (Option.some.inj hj).symm
      have hlen : fs.length = 1 := by
        have := SpineFit.length_eq hsp₂
        rwa [natBlock.Fss_succ] at this
      match fs, hlen with
      | [a], _ =>
        have ha : a ∈ˢ (omega : V) := by
          have h1 := hsp₂
          rw [natBlock.Fss_succ] at h1
          exact h1.1
        show ([] ++ [a]).foldl app (interp V ρ (m.acval ConLeche.natSuccName ψ)) = _
        rw [acval_natSucc_eq hS ψ]
        show app (natSuccV V) a = _
        rw [natSuccV_app (V := V) ha]
        show natsucc a = vsucc (([a] : List V).getD 0 pt)
        rw [natsucc_eq_vsucc]
        rfl
  mkZero := fun ψ hw => nomatch hw
  mkInj := fun _ _ mm' hmm j fs j' fs' hj hj' hlen hlen' heq => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    match j, hj, j', hj' with
    | 0, _, 0, _ =>
      rw [natBlock.Fss_zero] at hlen hlen'
      exact ⟨rfl, (List.eq_nil_of_length_eq_zero hlen).trans
        (List.eq_nil_of_length_eq_zero hlen').symm⟩
    | 0, _, 1, _ =>
      exact absurd heq (natzero_ne_vsucc _)
    | 1, _, 0, _ =>
      exact absurd heq.symm (natzero_ne_vsucc _)
    | 1, _, 1, _ =>
      rw [natBlock.Fss_succ] at hlen hlen'
      refine ⟨rfl, ?_⟩
      match fs, hlen, fs', hlen' with
      | [a], _, [b], _ =>
        have : vsucc a = vsucc b := heq
        rw [vsucc_inj this]

/-- **`Nat`'s pins' laws**: no pins. -/
theorem natBlock_pinRecLaws {env : Env} {m : EnvModel V env} :
    PinRecLaws m (natBlock (V := V)) (fun _ => default) where
  tgtsLt := fun _ _ _ _ h => nomatch h
  idxOk := fun _ _ _ _ h => nomatch h
  fibre := fun _ _ _ _ _ _ _ h => nomatch h
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ _ _ h => nomatch h
  injW := fun _ _ h => nomatch h
  ind := fun _ _ _ _ _ _ _ _ h => nomatch h

/-- **`Nat`'S OWN-PIN TABLE IS EMPTY** (task #315 M7-3 session 17,
K.49 and DESIGN §U.74).  A pinned basis block installs no MIMIC
recursor, so `containerOwnPinsAt` of its group hands back the empty
table at every instantiation, and the clause `ContainerOwnPinsSyn` —
which is `ContainerModeled.ownPins` — holds vacuously.

That `Nat.rec_1` is absent is a statement about what the environment
does NOT store, which no other record carries; `checkBasisDecl`
certifies it itself (`basisOwnMimicsOk`, the last conjunct of
`DeclBasisRun`), and `hmim` is that Bool at this block's own former,
which is where `containerOwnPinsAt`'s walk starts. -/
theorem natBlock_ownPins {env : Env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hR : env.find? (ConLeche.natName.str "rec") = some ConLeche.natRecA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.natName 0 = true) :
    ContainerOwnPinsSyn (V := V) env (natBlock (V := V)) :=
  ContainerOwnPinsSyn.of_noMimics rfl hmim fun i hi => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (show i < 1 from hi)
    exact ⟨_, _, containerInfo?_natA hT hR hZ hS, rfl, rfl⟩

/-- **`Nat`'s group carries its block model**.  The `inj` clause is
VACUOUS: `Nat` has no parameters, so the guard `0 < d.nP` (task #315
M7-4) is unsatisfiable — which is the point, `ω`'s elements being von
Neumann ordinals and not tagged towers. -/
theorem natBlock_containerModeled {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hR : env.find? (ConLeche.natName.str "rec") = some ConLeche.natRecA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.natName 0 = true) :
    ContainerModeled m ⟨0, [⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩]⟩
      (natBlock (V := V)) where
  k := rfl
  namesLen := rfl
  nP := rfl
  reps := fun c hc => by
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    exact ⟨_, ConLeche.natA.toConstantVal, 3, 3, [],
      natBlock_isBlockModel hT hZ hS (fun h => absurd rfl h)⟩
  typed := fun ψ => by
    refine ⟨fun t ht ρ => ?_, ⟨fun c hc j cA hj ρ => ?_,
      PinsTyped.of_noPins (d := natBlock (V := V)) rfl ψ⟩⟩
    · obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      rw [show (natBlock (V := V)).memberName 0 = ConLeche.natName from rfl,
        interp_acval_nat hT]
      exact omega_mem_univ_succ 0
    · obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
      match j, hj with
      | 0, hj =>
        obtain rfl : cA = (ConLeche.natZeroA.toConstantVal, 0) := (Option.some.inj hj).symm
        show interp V ρ (m.acval ConLeche.natZeroName ψ) ∈ˢ _
        rw [acval_natZero_eq hZ ψ]
        show (natzero : V) ∈ˢ interp V ρ
          (AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) [])
        rw [show AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) [] = m.acval ConLeche.natName ψ
          from rfl, interp_acval_nat hT]
        exact natzero_mem
      | 1, hj =>
        obtain rfl : cA = (ConLeche.natSuccA.toConstantVal, 1) := (Option.some.inj hj).symm
        show interp V ρ (m.acval ConLeche.natSuccName ψ) ∈ˢ _
        rw [acval_natSucc_eq hS ψ]
        show (natSuccV V) ∈ˢ interp V ρ (AnnotTerm.pi 0 1 (AnnotTerm.const .nat [])
          (AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) []))
        rw [show AnnotTerm.mkAppN (m.acval ConLeche.natName ψ) [] = m.acval ConLeche.natName ψ
          from rfl, acval_nat_eq hT ψ]
        exact natSuccV_mem V
  inj := fun h => absurd h (Nat.lt_irrefl 0)
  member := fun i M hM => by
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ M = ⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩ := by
      match i, hM with
      | 0, hM => exact ⟨rfl, (Option.some.inj hM).symm⟩
    exact ⟨rfl, rfl, ConLeche.natA.toConstantVal, 3, 3, [],
      natBlock_isBlockModel hT hZ hS (fun h => absurd rfl h)⟩
  frame := fun _ _ _ _ => Iff.rfl
  ordFree := fun i j l x hi hj hx hk => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    match j, hj with
    | 0, _ => exact nomatch hx
    | 1, _ =>
      match l, hx with
      | 0, _ => exact nomatch hk
  nestMention := fun _ h => nomatch h
  nestArgsMention := fun _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestArgsMentionAbs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestArgsMentionAbsRefl := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestPinSpineAbs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestPinSpineAbsRefl := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  ctorProjFree := fun i j cA hi hj T hT n => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl := List.mem_singleton.mp hT
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.natZeroA.toConstantVal, 0) := (Option.some.inj hj).symm
      simp [ConLeche.natZeroA, ConLeche.ConstantInfo.toConstantVal]
    | 1, hj =>
      obtain rfl : cA = (ConLeche.natSuccA.toConstantVal, 1) := (Option.some.inj hj).symm
      simp [ConLeche.natSuccA, ConLeche.ConstantInfo.toConstantVal]
  pinsNotMembers := fun _ h => nomatch h
  pinNP := fun _ h => nomatch h
  pinConts := fun _ h => nomatch h
  ownPins := natBlock_ownPins hT hR hZ hS hmim
  pinψ := fun _ h => nomatch h
  pinsDistinct := fun _ _ h _ _ => nomatch h
  pinsDistinctAt := fun _ _ _ h _ _ => nomatch h
  pinDsScoped := fun _ h => nomatch h
  pinDsRes := fun _ h => nomatch h
  pinDsRead := fun _ h => nomatch h
  pinParams := fun _ _ _ => ContainerPinParams.of_noPins rfl

/-- **`Nat` carries its block's model** at any assignment that sends
its group to `natBlock`. -/
theorem natBlockAt {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.natName = some ConLeche.natA)
    (hR : env.find? (ConLeche.natName.str "rec") = some ConLeche.natRecA)
    (hZ : env.find? ConLeche.natZeroName = some ConLeche.natZeroA)
    (hS : env.find? ConLeche.natSuccName = some ConLeche.natSuccA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.natName 0 = true)
    {B : ContainerInfo → BlockModel V}
    (hB : B ⟨0, [⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩]⟩
      = natBlock (V := V)) :
    BlockAt m B ⟨0, [⟨ConLeche.natName, [], ConLeche.natA.toConstantVal.type,
        [⟨ConLeche.natZeroName, ConLeche.natZeroA.toConstantVal.type, 0⟩,
         ⟨ConLeche.natSuccName, ConLeche.natSuccA.toConstantVal.type, 1⟩]⟩]⟩ := by
  refine ⟨hB ▸ natBlock_containerModeled hT hR hZ hS hmim, ⟨fun _ => default, ?_, ?_⟩⟩
  · exact hB ▸ natBlock_pinRecLaws
  · rw [hB]; exact fun q hq => nomatch hq

end ConLeche.Model


