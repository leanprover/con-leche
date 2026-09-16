module

public import ConLeche.Model.Inductives.NestedRecCand
import ConLeche.Model.Inductives.BlockRecFrames
import ConLeche.Model.Inductives.BlockRecTyped
public section

/-!
# The nested candidate at a frame (task #315, M7 — lane L-D)

`BlockRecTyped.lean`'s twin at `k + nPins` classes: **`hcand` of
`nestedRecs`** (`NestedRec.lean`, DESIGN §U.25) and the semantic core
of `hceq`.

A fitting spine of class `c`'s RESTORED recursor type is
`(p⃗, M⃗, m⃗, ı⃗_c, t)` — the block's parameters, the `k + nPins`
motives (the members' and the auxiliary ones), the `nCtorsT` minors in
auxiliary order, the class's index spine and the major — and the leaf
there is the class recursor `blockRecAtT` at the frame's motives and
minors, at the class's index tuple and the major (`blockLeafVT_at`).
`ReadingFramesT` is that decomposition, the frame's two semantic
typings (`MotivesTypedT`/`MinorsTypedT`) and the conclusion's reading,
in one predicate: the ONLY readings-facing premise of
`blockCandT_mem`, which types the candidate at its reading — at
`w ψ ≠ 0` by the kit (`blockRecAtT_mem_B`), at a `Prop`-valued block
by `inhabT_all` (every class's motive at every value is an inhabited
truth value, the classes' induction at the frame's minors and the
point).  `hcandT` is `nestedRecs`'s `hcand` verbatim.

`blockRecAtT_iota` is the ι rule at the candidate — a member's rule
and an AUXILIARY one alike: at a value built by class `c`'s
constructor `j` at a fitting field spine the class recursor IS the
frame's minor `minorIdxT c j` folded along the fields and the
inductive hypotheses.  What `hceq` still needs of the readings is
their bookkeeping (DESIGN §U.25 (e) 3).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-- **The extended candidate's leaf at a frame**: at a frame
`(p⃗, M⃗, m⃗, ı⃗_c, t)` with `k + nPins` motives and `nCtorsT` minors,
class `c`'s leaf is the class recursor at the frame's motives and
minors, at the class's index tuple and the major (`blockLeafV_at`'s
twin, DESIGN §U.25). -/
theorem BlockModel.blockLeafVT_at (d : BlockModel V) (pc : Nat → PinCtors V) (ψ : Name → Nat)
    (ℓ c : Nat) (ρ : Nat → V) {ps Msl msl is : List V} (t : V) (hMsl : Msl.length = d.kT)
    (hmsl : msl.length = d.nCtorsT pc) (his : is.length = d.nIdxT c) :
    d.blockLeafVT pc ψ ℓ c (consList (ps ++ Msl ++ msl ++ is ++ [t]) ρ)
      = d.blockRecAtT pc ψ (consList ps ρ) ℓ
          (fun c' => if c' < d.kT then Msl.getD c' pt else pt)
          (fun J => if J < d.nCtorsT pc then msl.getD J pt else pt) c (d.tupT ψ c is) t := by
  unfold BlockModel.blockLeafVT
  have hfr : consList (ps ++ Msl ++ msl ++ is ++ [t]) ρ
      = cons t (consList is (consList msl (consList Msl (consList ps ρ)))) := by
    simp only [consList_append, consList_cons, consList_nil]
  rw [hfr]
  have hsh : shiftE (1 + d.nIdxT c + d.nCtorsT pc + d.kT) 0
      (cons t (consList is (consList msl (consList Msl (consList ps ρ))))) = consList ps ρ := by
    rw [show cons t (consList is (consList msl (consList Msl (consList ps ρ))))
        = consList (Msl ++ msl ++ is ++ [t]) (consList ps ρ) from by
          simp only [consList_append, consList_cons, consList_nil],
      show 1 + d.nIdxT c + d.nCtorsT pc + d.kT = (Msl ++ msl ++ is ++ [t]).length from by
        simp only [List.length_append, List.length_singleton, hMsl, hmsl, his]; omega,
      shiftE_consList]
  have hsh1 : shiftE 1 0 (cons t (consList is (consList msl (consList Msl (consList ps ρ)))))
      = consList is (consList msl (consList Msl (consList ps ρ))) := by
    rw [show cons t (consList is (consList msl (consList Msl (consList ps ρ))))
        = consList [t] (consList is (consList msl (consList Msl (consList ps ρ)))) from rfl,
      show (1 : Nat) = [t].length from rfl, shiftE_consList]
  rw [hsh, hsh1, ← his, frameIdx_consList', his]
  congr 1
  · funext c'
    split
    · next hc' =>
      rw [show 1 + d.nIdxT c + d.nCtorsT pc + (d.kT - 1 - c')
          = (((d.kT - 1 - c') + msl.length) + is.length) + 1 from by rw [hmsl, his]; omega]
      show consList [t] (consList is (consList msl (consList Msl (consList ps ρ))))
        ((((d.kT - 1 - c') + msl.length) + is.length) + [t].length) = _
      rw [consList_apply_add, consList_apply_add, consList_apply_add,
        consList_apply_lt' _ _ (by omega), hMsl,
        show d.kT - 1 - (d.kT - 1 - c') = c' from by omega]
    · rfl
  · funext J
    split
    · next hJ =>
      rw [show 1 + d.nIdxT c + d.nCtorsT pc - 1 - J = ((d.nCtorsT pc - 1 - J) + is.length) + 1
          from by rw [his]; omega]
      show consList [t] (consList is (consList msl (consList Msl (consList ps ρ))))
        (((d.nCtorsT pc - 1 - J) + is.length) + [t].length) = _
      rw [consList_apply_add, consList_apply_add, consList_apply_lt' _ _ (by omega), hmsl,
        show d.nCtorsT pc - 1 - (d.nCtorsT pc - 1 - J) = J from by omega]
    · rfl

/-! ## The `Prop`-valued block: the motives are inhabited -/

/-- **The bound is inhabited at `Prop`** (`ℓ = 0`): at every value of
every class's carrier, the class's motive at the index tuple and the
value is an inhabited truth value — the classes' induction
(`classInd_all`) at that property, its step the frame's minor at the
fields and the POINT for every inductive hypothesis: at level `0` a
hypothesis' domain is a Π-tower of truth values (`hMs` at the target
class, `motiveT_mem`), inhabited by the induction hypothesis
(`pt_mem_piTele_zero_of`).  `inhab_all`'s twin over the classes, read
semantically — the `Prop` half of the candidate's typing. -/
theorem IsBlockModel.inhabT_all {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) (hreps : IsBlockModels m d)
    {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {Ms ms : Nat → V} (hMs : d.MotivesTypedT ψ ρp 0 Ms)
    (hms : d.MinorsTypedT pc ψ ρp 0 Ms ms) :
    ∀ c, c < d.kT → ∀ t x,
      x ∈ˢ app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c) t →
      ∃ y, y ∈ˢ app ((isOfW (d.uT c ψ) (d.nIdxT c) t).foldl app (Ms c)) x := by
  have hLmem := lfpTuple_mem (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)
  have hLu : ∀ c', c' < d.kT → ∀ t', app (d.famAt ψ ρp
      (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c') t' ∈ˢ (univ (d.w ψ) : V) :=
    fun c' hc' t' => app_famSpace_mem_univ (h.famAt_mem hρp hLmem hc') t'
  intro c hc t x hx
  have ht : t ∈ˢ d.idxT ψ ρp c :=
    mem_idx_of_app_famSpace (h.famAt_mem hρp hLmem hc) hx
  refine h.classInd_all hp hρp
    (P := fun c t x => ∃ y, y ∈ˢ app ((isOfW (d.uT c ψ) (d.nIdxT c) t).foldl app (Ms c)) x)
    ?_ c hc t ht x hx
  intro c' hc' t' ht' j hj fs hfit hih
  have htgts : ∀ i, i < ((d.FssT pc ψ c').getD j []).length →
      ((d.rssT pc c').getD j []).getD i false = true → d.tgtsT pc c' j i < d.kT :=
    fun i hi hr => h.tgtsT_lt hp ψ hc' hj hi hr
  refine ⟨_, hms c' hc' j hj t' ht' fs hfit
    (List.replicate (recIdx ((d.rssT pc c').getD j [])
      ((d.FssT pc ψ c').getD j []).length).length pt) List.length_replicate ?_⟩
  intro l hl
  rw [List.length_replicate] at hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_replicate]; exact hl),
    Option.getD_some, List.getElem_replicate]
  have hgetD : (recIdx ((d.rssT pc c').getD j []) ((d.FssT pc ψ c').getD j []).length).getD l 0
      = (recIdx ((d.rssT pc c').getD j []) ((d.FssT pc ψ c').getD j []).length)[l] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  rw [hgetD]
  have hi' : (recIdx ((d.rssT pc c').getD j []) ((d.FssT pc ψ c').getD j []).length)[l]
      ∈ recIdx ((d.rssT pc c').getD j []) ((d.FssT pc ψ c').getD j []).length :=
    List.getElem_mem hl
  refine pt_mem_piTele_zero_of (fun bs hbs => ?_) (fun bs hbs => ?_)
  · rw [fitsS_teleOfFields] at hbs
    rw [List.nil_append, ← univ_zero]
    exact h.motiveT_mem hreps hp hρp hMs (htgts _ (mem_recIdx.mp hi').1 (mem_recIdx.mp hi').2)
      (d.chainFitT_slot_mem pc hLu htgts hfit hi' hbs)
  · rw [fitsS_teleOfFields] at hbs
    rw [List.nil_append]
    exact hih _ hi' bs hbs

/-! ## The candidate typed at a class's reading -/

/-- A class's index tuple reads back its fitting spine (`isOfW_tupW`
at the class's `idxOk`: the member's, the pin's container's). -/
theorem IsBlockModel.isOfW_tupT {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) (hreps : IsBlockModels m d)
    {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {c : Nat} (hc : c < d.kT) {is : List V}
    (hsp : SpineFit (d.frameT c ψ ρp) (d.IdsT c ψ) is) :
    isOfW (d.uT c ψ) (d.nIdxT c) (d.tupT ψ c is) = is := by
  by_cases hck : c < d.k
  · obtain ⟨cvT', cvR', mI', rP', rules', h'⟩ := hreps c hck
    rw [BlockModel.frameT_of_mem hck, BlockModel.IdsT_of_mem hck] at hsp
    rw [BlockModel.tupT, BlockModel.uT_of_mem hck, BlockModel.nIdxT_of_mem hck,
      ← h'.IdsM_length ψ]
    exact isOfW_tupW (h'.idxOk ψ ρp hρp c hck) hsp
  · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
    rw [BlockModel.frameT_of_pin hck, BlockModel.IdsT_of_pin hck] at hsp
    rw [BlockModel.tupT, BlockModel.uT_of_pin hck, BlockModel.nIdxT_of_pin hck,
      ← h.pinIds_length hq ψ]
    exact isOfW_tupW (hp.idxOk ψ ρp hρp _ hq) hsp

/-- **The reading's frames**: every spine fitting class `c`'s RESTORED
recursor type's reading decomposes into the block's parameters, the
`k + nPins` motives, the `nCtorsT` minors in auxiliary order, the
class's index spine and a major of the class's carrier there; the
frame's motives and minors are typed SEMANTICALLY at the parameter
frame, and the reading's conclusion is the class's motive at the index
spine and the major.  What the readings at `k + nPins` must supply
(`spineFit_recData_inv` + `interp_mutualConcAV_at`'s twins, DESIGN
§U.25 (e) 2/3) — the only readings-facing premise of `blockCandT_mem`. -/
@[expose] def BlockModel.ReadingFramesT (d : BlockModel V) (pc : Nat → PinCtors V) (ψ : Name → Nat)
    (ℓ : Nat) (rds : List (Nat × Nat × AnnotTerm)) (conc : AnnotTerm) (c : Nat) (ρ : Nat → V) :
    Prop :=
  ∀ xs, SpineFit ρ (rds.map (·.2.2)) xs →
    ∃ ps Msl msl is t, xs = ps ++ Msl ++ msl ++ is ++ [t] ∧
      Sat V (d.params ψ).reverse (consList ps ρ) ∧
      Msl.length = d.kT ∧ msl.length = d.nCtorsT pc ∧ is.length = d.nIdxT c ∧
      SpineFit (d.frameT c ψ (consList ps ρ)) (d.IdsT c ψ) is ∧
      t ∈ˢ app (d.famAt ψ (consList ps ρ)
          (lfpTuple (d.w ψ) d.k (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ))) c)
        (d.tupT ψ c is) ∧
      d.MotivesTypedT ψ (consList ps ρ) ℓ (fun c' => if c' < d.kT then Msl.getD c' pt else pt) ∧
      d.MinorsTypedT pc ψ (consList ps ρ) ℓ
        (fun c' => if c' < d.kT then Msl.getD c' pt else pt)
        (fun J => if J < d.nCtorsT pc then msl.getD J pt else pt) ∧
      interp V (consList xs ρ) conc = app (is.foldl app (Msl.getD c pt)) t

/-- **THE CANDIDATE IS TYPED AT ITS READING** (`hcand` of `nestedRecs`,
DESIGN §U.25 (c)): class `c`'s candidate — the class recursor over the
extended union at the frame's `k + nPins` motives and `nCtorsT` minors
— lies in its restored recursor type's reading, given the reading's
frames.  At `w ψ ≠ 0` the leaf is typed by the kit (`blockRecAtT_mem_B`
at `kitBT_mem`/`kitStT_mem`, the frame's typings read semantically); at
a `Prop`-valued block the candidate is the point and the reading is a
Π-tower of inhabited truth values (`inhabT_all`). -/
theorem IsBlockModel.blockCandT_mem {env : Env} {m : EnvModel V env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) (hreps : IsBlockModels m d)
    {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ℓ : Nat}
    (hwℓ : d.w ψ = 0 → ℓ = 0) {rds : List (Nat × Nat × AnnotTerm)} {conc : AnnotTerm} {c : Nat}
    (hc : c < d.kT) {ρ : Nat → V} (hne : rds ≠ [])
    (hbits : ∀ e ∈ rds, (ℓ = 0 ↔ e.2.1 = 0)) (hfr : d.ReadingFramesT pc ψ ℓ rds conc c ρ) :
    d.blockCandT pc ψ ℓ rds c ρ ∈ˢ interp V ρ (mkPisAV rds conc) := by
  -- the leaf's facts at every fitting spine
  have hleaf : ∀ xs, SpineFit ρ (rds.map (·.2.2)) xs →
      (d.w ψ ≠ 0 → d.blockLeafVT pc ψ ℓ c (consList xs ρ) ∈ˢ interp V (consList xs ρ) conc) ∧
      (∃ y, y ∈ˢ interp V (consList xs ρ) conc) ∧
      interp V (consList xs ρ) conc ∈ˢ (univ ℓ : V) := by
    intro xs hxs
    obtain ⟨ps, Msl, msl, is, t, rfl, hρp, hMsl, hmsl, hisLen, hsp, ht, hMs, hms, hconc⟩ := hfr xs hxs
    rw [hconc, d.blockLeafVT_at pc ψ ℓ c ρ t hMsl hmsl hisLen]
    have hisOfW : isOfW (d.uT c ψ) (d.nIdxT c) (d.tupT ψ c is) = is :=
      h.isOfW_tupT hreps hp hρp hc hsp
    have hB := h.kitBT_mem hreps hp hρp hMs
    have hidx : d.tupT ψ c is ∈ˢ d.idxT ψ (consList ps ρ) c :=
      mem_idx_of_app_famSpace (h.famAt_mem hρp (lfpTuple_mem _ _ _ _) hc) ht
    have huniv : app (is.foldl app (Msl.getD c pt)) t ∈ˢ (univ ℓ : V) := by
      have hu := h.motiveT_mem hreps hp hρp hMs hc ht
      rw [hisOfW, if_pos hc] at hu
      exact hu
    refine ⟨fun hw => ?_, ?_, huniv⟩
    · have hr := h.blockRecAtT_mem_B hp hρp hw hB (h.kitStT_mem hreps hp hρp hw hB hms) hc hidx ht
      rw [BlockModel.kitBT_tagged, hisOfW, if_pos hc] at hr
      exact hr
    · rcases Classical.em (d.w ψ = 0) with hw0 | hw
      · have hi := h.inhabT_all hreps hp hρp (hwℓ hw0 ▸ hMs) (hwℓ hw0 ▸ hms) c hc _ t ht
        rw [hisOfW, if_pos hc] at hi
        exact hi
      · have hr := h.blockRecAtT_mem_B hp hρp hw hB (h.kitStT_mem hreps hp hρp hw hB hms) hc hidx ht
        rw [BlockModel.kitBT_tagged, hisOfW, if_pos hc] at hr
        exact ⟨_, hr⟩
  rcases Classical.em (d.w ψ = 0) with hw0 | hw
  · -- the `Prop`-valued block: the candidate is the point, the reading inhabited
    have hℓ := hwℓ hw0
    have hpt : d.blockCandT pc ψ ℓ rds c ρ = pt := by
      unfold BlockModel.blockCandT
      cases hd : rds with
      | nil => exact absurd hd hne
      | cons e es =>
        show lamR ℓ _ _ = pt
        rw [hℓ]; exact lamR_zero
    rw [hpt]
    exact pt_mem_mkPisAV_zero_of hne (fun e he => (hbits e he).mp hℓ)
      fun xs hxs => (hleaf xs hxs).2.1
  · unfold BlockModel.blockCandT
    exact lamTower_mem hbits (towerWalk_of fun xs hxs =>
      ⟨(hleaf xs hxs).1 hw, fun h0 => by rw [← univ_zero, ← h0]; exact (hleaf xs hxs).2.2⟩)

/-- **`nestedRecs`'s `hcand`** (`NestedRec.lean`), discharged from the
readings' frames at every frame and class: the candidate tuple's
components are typed at the `k + nPins` restored recursor types'
readings.  Its one open premise is `ReadingFramesT` — the readings'
decomposition and the frame's semantic typings, the stage's
(DESIGN §U.25 (e) 2/3). -/
theorem IsBlockModel.hcandT {env : Env} {m : EnvModel V env} {T : Name} {cvT cvR : ConstantVal}
    {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) (hreps : IsBlockModels m d)
    {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ℓ : (Name → Nat) → Nat}
    (hwℓ : ∀ ψ, d.w ψ = 0 → ℓ ψ = 0)
    {rdsM : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {concM : Nat → AnnotTerm}
    (hne : ∀ c ψ, c < d.kT → rdsM c ψ ≠ [])
    (hbits : ∀ c ψ, c < d.kT → ∀ e ∈ rdsM c ψ, (ℓ ψ = 0 ↔ e.2.1 = 0))
    (hfr : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < d.kT →
      d.ReadingFramesT pc ψ (ℓ ψ) (rdsM c ψ) (concM c) c ρ) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < d.kT →
      d.blockCandT pc ψ (ℓ ψ) (rdsM c ψ) c ρ ∈ˢ interp V ρ (mkPisAV (rdsM c ψ) (concM c)) :=
  fun ψ ρ c hc =>
    h.blockCandT_mem hreps hp (hwℓ ψ) hc (hne c ψ hc) (hbits c ψ hc) (hfr ψ ρ c hc)

/-! ## The ι rule at the candidate -/

/-- **A fitting spine's value is in its class's carrier**: at the
carrier's extended tuple, class `c`'s constructor `j` at a fit lands in
the class's family — a member's by the fixed-point equation and the
block model's `fibre`, a pin's by `PinRecLaws.fibre`. -/
theorem IsBlockModels.injT_mem_famAt {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hreps : IsBlockModels m d) {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) {c : Nat} (hc : c < d.kT) {t : V}
    (ht : t ∈ˢ d.idxT ψ ρp c) {j : Nat} (hj : j < (d.ctorsT pc c).length) {fs : List V}
    (hfit : d.ChainFitT pc ψ ρp (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
      t c j fs) :
    d.injT pc ψ c j fs
      ∈ˢ app (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c) t := by
  by_cases hck : c < d.k
  · obtain ⟨cvT', cvR', mI', rP', rules', h'⟩ := hreps c hck
    rw [d.idxT_of_mem hck] at ht
    rw [d.famAt_of_mem hck, ← h'.carrier_app_eq hρp hck ht, BlockModel.injT_of_mem hck]
    refine (h'.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) c hck t ht _).mpr ⟨j, fs, ?_, ?_, rfl⟩
    · rw [BlockModel.ctorsT_of_mem hck] at hj; exact hj
    · exact d.chainFit_of_chainFitT pc hck hfit
  · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
    rw [d.idxT_of_pin hck] at ht
    rw [d.famAt_of_pin hck, BlockModel.injT_of_pin hck]
    refine (hp.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) (TupleLe.refl _ _ _) _ hq t ht _).mpr ⟨j, fs, ?_, ?_, rfl⟩
    · rw [BlockModel.ctorsT_of_pin hck] at hj; exact hj
    · rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hck)]; exact hfit

/-- **THE ι RULE AT THE CANDIDATE, SEMANTICALLY** — the heart of
`hceq` (DESIGN §U.25 (c)), at a member's rule and an AUXILIARY one
alike: at a value built by class `c`'s constructor `j` at a fitting
field spine, the class recursor is the frame's minor
(`minorIdxT c j`, the auxiliary order) folded along the fields and the
inductive hypotheses.  The recursion equation (`blockRecAtT_eq` at the
kit's two obligations) with the step's decode identified with the
decomposition (`kitStT_tagged` and the class's `mkInj`). -/
theorem IsBlockModel.blockRecAtT_iota {env : Env} {m : EnvModel V env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {d : BlockModel V} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) (hreps : IsBlockModels m d)
    {pc : Nat → PinCtors V} (hp : PinRecLaws m d pc) {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V (d.params ψ).reverse ρp) (hw : d.w ψ ≠ 0) {ℓ : Nat} {Ms ms : Nat → V}
    (hMs : d.MotivesTypedT ψ ρp ℓ Ms) (hms : d.MinorsTypedT pc ψ ρp ℓ Ms ms) {c : Nat}
    (hc : c < d.kT) {t : V} (ht : t ∈ˢ d.idxT ψ ρp c) {j : Nat} (hj : j < (d.ctorsT pc c).length)
    {fs : List V}
    (hfit : d.ChainFitT pc ψ ρp (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
      t c j fs) :
    d.blockRecAtT pc ψ ρp ℓ Ms ms c t (d.injT pc ψ c j fs)
      = (fs ++ d.kitIhsT pc ψ ρp ℓ c j fs
          (graph (fun v => recSel (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms)
              (d.kitStT pc ψ ρp ℓ ms)) v)
            (d.kitPredT pc ψ ρp (tagged c t (d.injT pc ψ c j fs))))).foldl
          app (ms (d.minorIdxT pc c j)) := by
  have hx := hreps.injT_mem_famAt hp hρp hc ht hj hfit
  have hB := h.kitBT_mem hreps hp hρp hMs
  have hst := h.kitStT_mem hreps hp hρp hw hB hms
  rw [h.blockRecAtT_eq hp hρp hw hB hst hc ht hx]
  have hlenfs : fs.length = ((d.FssT pc ψ c).getD j []).length := hfit.1.length_eq
  have hdec : d.DecodesT pc ψ c (d.injT pc ψ c j fs) := ⟨j, fs, hj, hlenfs, rfl⟩
  obtain ⟨j', fs', hj', hlen', hx', heq⟩ := d.kitStT_tagged pc ψ ρp ℓ ms
    (graph (fun v => recSel (recGraph ℓ (d.unionT ψ ρp) (d.kitPredT pc ψ ρp) (d.kitBT ψ Ms)
        (d.kitStT pc ψ ρp ℓ ms)) v)
      (d.kitPredT pc ψ ρp (tagged c t (d.injT pc ψ c j fs)))) hdec
  rw [heq]
  have hjfs : j = j' ∧ fs = fs' := by
    by_cases hck : c < d.k
    · rw [BlockModel.injT_of_mem hck] at hx'
      rw [BlockModel.ctorsT_of_mem hck] at hj hj'
      rw [BlockModel.FssT_of_mem hck] at hlenfs hlen'
      exact h.mkInj ψ hw c hck j fs j' fs' hj hj' hlenfs hlen' hx'
    · have hq : c - d.k < d.nPins := by unfold BlockModel.kT at hc; omega
      rw [BlockModel.injT_of_pin hck] at hx'
      rw [BlockModel.ctorsT_of_pin hck] at hj hj'
      rw [BlockModel.FssT_of_pin hck] at hlenfs hlen'
      exact hp.mkInj ψ hw _ hq j fs j' fs' hj hj' hlenfs hlen' hx'
  obtain ⟨rfl, rfl⟩ := hjfs
  rfl

end ConLeche.Model
