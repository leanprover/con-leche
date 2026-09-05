import Setlec.SetBase.TowerMk

/-!
# The recursor leaf (task #175, stage 3d)

`directRecAV ℓ ds nF = mkLamsC ℓ ds (recBodyAV nF)` — the constant-bit
λ-tower (bit `ℓ`, the elimination level: the body's type is
`motive t : Sort ℓ`) over the recursor type reading's binder data,
whose body is **`towerRec`'s witness `m ∘ projList`, spelled**:

    recBodyAV nF = (.bvar 1) applied along (projAV i (.bvar 0))

— the minor premise applied to the uniform projections of the major.
No constructor, no telescope data, no entry consultation in the body:
`projAV` depends only on the index.

The semantic minor space `minorSp` is the interpreted minor-premise
type (the Π-tower over the field chain ending
`motive (C p⃗ f⃗) = app M (mkTower f⃗)`, with the squash collapse
`app M pt` at `w = 0`); the recursor type reading's minor entry is
pinned to it by O3, and `RecPre` consumes that pin as an equation.
The eta step of `towerRec` — a member is the tower of its own
projections — enters through `towerSet_elim_teleOfFields` in the
conversion `mkTower (projList n t) = t` at the end of
`underTowerOk_of_recPre`'s base; the squash side is
`towerSet_zero_elim`'s `t = pt`.  Subsingleton elimination at squash
instantiations is not a separate law: the same base goes through with
`w = 0`, where every projection reads `pt` and the minor space's
conclusion is `app M pt`.
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- The recursor leaf's body: the minor premise applied along the
uniform projections of the major — `towerRec`'s witness
`m ∘ projList`, spelled. -/
def recBodyAV (nF : Nat) : AVExpr :=
  AVExpr.mkAppN (.bvar 1) ((List.range nF).map fun i => projAV i (.bvar 0))

/-! ## Projection-list arithmetic -/

theorem projList_snoc : ∀ (k : Nat) (x : V),
    projList (k + 1) x = projList k x ++ [projS k x]
  | 0, _ => rfl
  | k + 1, x => by
    show sfst x :: projList (k + 1) (ssnd x)
      = (sfst x :: projList k (ssnd x)) ++ [projS (k + 1) x]
    rw [projList_snoc k (ssnd x)]
    rfl

theorem projList_eq_map_range (n : Nat) (x : V) :
    projList n x = (List.range n).map fun i => projS i x := by
  apply List.ext_getElem
  · rw [projList_length, List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact projList_get n i x (by rwa [projList_length] at h1)

theorem map_range_projS_mkTower {n : Nat} {bs : List V}
    (h : bs.length = n) :
    ((List.range n).map fun i => projS i (mkTower bs)) = bs := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact projS_mkTower i bs h2

/-! ## The projection spine's grading -/

/-- **The uniform projection spelling is graded on tower members**:
each `.proj` node's `AnnotOk2` package is one `sigmaSet w` level of
the carrier, peeled by `mem_sigma_elim` — both regimes (at squash the
subject is `pt` throughout and the tail memberships are `pt`'s). -/
theorem projAV_ok2_tower {w : Nat} :
    ∀ {i : Nat} {Fs : List AVExpr} {ρ : Nat → V} {e : AVExpr}
      {σ : Nat → V},
      AnnotOk2 V σ e →
      interp2 V σ e ∈ˢ towerSet w (teleOfFields ρ Fs) →
      FieldsBound w ρ Fs → i < Fs.length →
      AnnotOk2 V σ (projAV i e)
  | 0, F :: Fs', ρ, e, σ, hok, hx, hbnd, _ => by
    show AnnotOk2 V σ (.proj 0 e)
    rw [AnnotOk2]
    refine ⟨hok, by omega, w, w, interp2 V ρ F,
      fun a => towerSet w (teleOfFields (cons a ρ) Fs'), ?_, hbnd.1,
      fun a ha => towerSet_univ_teleOfFields (hbnd.2 a ha)⟩
    rwa [show Nat.max w w = w from Nat.max_self w]
  | i + 1, F :: Fs', ρ, e, σ, hok, hx, hbnd, hi => by
    obtain ⟨a, b, ha, hb, hz, hpos⟩ :=
      mem_sigma_elim (A := interp2 V ρ F)
        (B := fun a => towerSet w (teleOfFields (cons a ρ) Fs')) hx
    have hok1 : AnnotOk2 V σ (.proj 1 e) := by
      rw [AnnotOk2]
      refine ⟨hok, by omega, w, w, interp2 V ρ F,
        fun a => towerSet w (teleOfFields (cons a ρ) Fs'), ?_, hbnd.1,
        fun a' ha' => towerSet_univ_teleOfFields (hbnd.2 a' ha')⟩
      rwa [show Nat.max w w = w from Nat.max_self w]
    have hmem1 : interp2 V σ (.proj 1 e)
        ∈ˢ towerSet w (teleOfFields (cons a ρ) Fs') := by
      rw [interp2_proj, if_neg Nat.one_ne_zero]
      rcases Nat.eq_zero_or_pos w with rfl | hwpos
      · rw [hz rfl, ssnd_pt]
        rw [(towerSet_zero_elim _ hb).1] at hb
        exact hb
      · rw [hpos (Nat.pos_iff_ne_zero.mp hwpos), ssnd_spair]
        exact hb
    exact projAV_ok2_tower (i := i) (Fs := Fs') (ρ := cons a ρ)
      (e := .proj 1 e) hok1 hmem1 (hbnd.2 a ha)
      (by exact Nat.lt_of_succ_lt_succ hi)

/-! ## The semantic minor space -/

/-- The interpreted minor-premise type: the Π-tower over the field
chain (bit `ℓ` — its codomain chain ends `Sort ℓ`), concluding at the
motive applied to the accumulated tuple (`pt` at squash). -/
noncomputable def minorSp (ℓ w : Nat) (M : V) :
    List AVExpr → (Nat → V) → List V → V
  | [], _, acc => SetTheory.app M (if w = 0 then pt else mkTower acc)
  | F :: Fs, ρf, acc => piR ℓ (interp2 V ρf F)
      fun a => minorSp ℓ w M Fs (cons a ρf) (acc ++ [a])

/-- At elimination level `0` the minor space is a truth value (its
conclusion needs the motive's off/on-domain applications to be truth
values, which the caller supplies from the motive-space inversion). -/
theorem minorSp_zero_univZero {ℓ w : Nat} {M : V} (h0 : ℓ = 0)
    (hM0 : ∀ y : V, SetTheory.app M y ∈ˢ (univZero : V)) :
    ∀ (Fs : List AVExpr) (ρf : Nat → V) (acc : List V),
      minorSp ℓ w M Fs ρf acc ∈ˢ (univZero : V)
  | [], _, _ => hM0 _
  | _ :: _, _, _ => by
    show piR ℓ _ _ ∈ˢ _
    rw [h0]
    exact piR_zero_mem_univZero

/-- `ArgsOkFit σ args Fs ρf`: the argument spine is graded and its
values fit the field chain — the `SpineFit` of the interpreted
arguments, with each argument's own `AnnotOk2` carried. -/
def ArgsOkFit (σ : Nat → V) : List AVExpr → List AVExpr → (Nat → V) → Prop
  | [], [], _ => True
  | a :: args, F :: Fs, ρf => AnnotOk2 V σ a ∧
      interp2 V σ a ∈ˢ interp2 V ρf F ∧
      ArgsOkFit σ args Fs (cons (interp2 V σ a) ρf)
  | _, _, _ => False

theorem ArgsOkFit.toSpineFit :
    ∀ {args Fs : List AVExpr} {σ ρf : Nat → V},
      ArgsOkFit σ args Fs ρf → SpineFit ρf Fs (args.map (interp2 V σ))
  | [], [], _, _, _ => trivial
  | _ :: args, _ :: _, _, _, h => ⟨h.2.1, ArgsOkFit.toSpineFit (args := args) h.2.2⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- **The minor-space spine, graded fold**: applying a graded member
of the minor space along a graded fitting spine yields, in one
induction, the `AnnotOk2` of the application spine AND its membership
in the motive at the accumulated tuple. -/
theorem minorSp_spine {ℓ w : Nat} {M : V}
    (hM0 : ℓ = 0 → ∀ y : V, SetTheory.app M y ∈ˢ (univZero : V)) :
    ∀ {Fs args : List AVExpr} {ρf : Nat → V} {acc : List V}
      {f : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ f →
      interp2 V σ f ∈ˢ minorSp ℓ w M Fs ρf acc →
      ArgsOkFit σ args Fs ρf →
      AnnotOk2 V σ (AVExpr.mkAppN f args) ∧
        interp2 V σ (AVExpr.mkAppN f args)
          ∈ˢ SetTheory.app M (if w = 0 then pt
              else mkTower (acc ++ args.map (interp2 V σ)))
  | [], [], _, acc, f, σ, hokf, hmf, _ => by
    refine ⟨hokf, ?_⟩
    show interp2 V σ f ∈ˢ SetTheory.app M
      (if w = 0 then pt else mkTower (acc ++ []))
    rw [List.append_nil]
    exact hmf
  | [], _ :: _, _, _, _, _, _, _, hfit => hfit.elim
  | _ :: _, [], _, _, _, _, _, _, hfit => hfit.elim
  | F :: Fs, a :: args, ρf, acc, f, σ, hokf, hmf, hfit => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ interp2 V ρf F →
        minorSp ℓ w M Fs (cons x ρf) (acc ++ [x]) ∈ˢ (univZero : V) :=
      fun h0 x _ =>
        minorSp_zero_univZero h0 (hM0 h0) Fs (cons x ρf) (acc ++ [x])
    have happ : SetTheory.app (interp2 V σ f) (interp2 V σ a)
        ∈ˢ minorSp ℓ w M Fs (cons (interp2 V σ a) ρf)
          (acc ++ [interp2 V σ a]) :=
      app_mem_piR hmf hfit.2.1 hB0
    have hoka : AnnotOk2 V σ (.app f a) := by
      rw [AnnotOk2_app]
      exact ⟨hokf, hfit.1,
        ⟨ℓ, interp2 V ρf F, _, hmf, hfit.2.1, hB0⟩⟩
    have hres := minorSp_spine hM0 (Fs := Fs) (args := args)
      (f := .app f a) hoka happ hfit.2.2
    refine ⟨hres.1, ?_⟩
    have hassoc : (acc ++ [interp2 V σ a]) ++ args.map (interp2 V σ)
        = acc ++ (a :: args).map (interp2 V σ) := by
      simp
    rw [hassoc] at hres
    exact hres.2

/-- The projection spine fits the field chain: value `k` is
`projS k t`, its membership is `projS_mem_teleOfFields`, its grading
`projAV_ok2_tower`; the environment steps by `projList_snoc`. -/
theorem argsOkFit_projSpine {w : Nat} {Fs : List AVExpr}
    {ρp : Nat → V} {σ : Nat → V}
    (ht : σ 0 ∈ˢ towerSet w (teleOfFields ρp Fs))
    (hbnd : FieldsBound w ρp Fs) :
    ∀ (m k : Nat), k + m = Fs.length →
      ArgsOkFit σ ((List.range' k m).map fun i => projAV i (.bvar 0))
        (Fs.drop k) (consList (projList k (σ 0)) ρp)
  | 0, k, hk => by
    rw [show k = Fs.length by omega, List.drop_length]
    trivial
  | m + 1, k, hk => by
    have hkn : k < Fs.length := by omega
    rw [List.range'_succ, List.drop_eq_getElem_cons hkn]
    refine ⟨?_, ?_, ?_⟩
    · exact projAV_ok2_tower (by simp) ht hbnd hkn
    · rw [projAV_interp, interp2_bvar]
      exact projS_mem_teleOfFields
        (fun h0 => h0 ▸ hbnd) ht hkn
    · have hstep := argsOkFit_projSpine ht hbnd m (k + 1) (by omega)
      have henv : consList (projList (k + 1) (σ 0)) ρp
          = cons (interp2 V σ (projAV k (.bvar 0)))
              (consList (projList k (σ 0)) ρp) := by
        rw [projList_snoc, consList_append, consList_cons, consList_nil,
          projAV_interp, interp2_bvar]
      rwa [henv] at hstep

/-! ## The recursor leaf -/

/-- The recursor leaf: the constant-bit λ-tower (bit `ℓ`) over the
recursor type reading's binder data, with the projection-fold body. -/
def directRecAV (ℓ : Nat) (ds : List (Nat × Nat × AVExpr))
    (nF : Nat) : AVExpr :=
  mkLamsC ℓ ds (recBodyAV nF)

/-- The recursor's post-parameter phase facts (`RecBase`): the field
chain graded; the motive/minor/major binder entries graded, with their
readings pinned (O3, semantically) to the motive space, the minor
space, and the carrier. -/
def RecBase (ℓ w : Nat) (ρp : Nat → V) (Fs : List AVExpr)
    (dM dm dt : Nat × Nat × AVExpr) : Prop :=
  FieldsOkB w ρp Fs ∧
  AnnotOk2 V ρp dM.2.2 ∧
  interp2 V ρp dM.2.2
    = piR (ℓ + 1) (towerSet w (teleOfFields ρp Fs))
        (fun _ => (univ ℓ : V)) ∧
  ∀ M, M ∈ˢ interp2 V ρp dM.2.2 →
    AnnotOk2 V (cons M ρp) dm.2.2 ∧
    interp2 V (cons M ρp) dm.2.2 = minorSp ℓ w M Fs ρp [] ∧
    ∀ m, m ∈ˢ interp2 V (cons M ρp) dm.2.2 →
      AnnotOk2 V (cons m (cons M ρp)) dt.2.2 ∧
      interp2 V (cons m (cons M ρp)) dt.2.2
        = towerSet w (teleOfFields ρp Fs)

/-- `RecPre`: the recursor leaf's ONE hereditary premise — the
parameter walk ending in `RecBase`. -/
def RecPre (ℓ w : Nat) (ρ : Nat → V) (Fs : List AVExpr)
    (dM dm dt : Nat × Nat × AVExpr) :
    List (Nat × Nat × AVExpr) → Prop
  | [] => RecBase ℓ w ρ Fs dM dm dt
  | d :: pds => AnnotOk2 V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp2 V ρ d.2.2 → RecPre ℓ w (cons a ρ) Fs dM dm dt pds

/-- **The recursor leaf's `UnderTowerOk`** — `towerRec` spelled: the
base folds the minor along the projections (`minorSp_spine`), closes
with eta (`mkTower (projList n t) = t`, `towerSet_elim`) in the graph
regime and with `t = pt` (`towerSet_zero_elim`) at squash. -/
theorem underTowerOk_of_recPre {ℓ w : Nat} {Fs : List AVExpr}
    {dM dm dt : Nat × Nat × AVExpr} :
    ∀ {pds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      RecPre ℓ w ρ Fs dM dm dt pds →
      UnderTowerOk ℓ ρ (recBodyAV Fs.length) (.app (.bvar 2) (.bvar 0))
        (pds ++ [dM, dm, dt])
  | d :: pds, ρ, h =>
    ⟨h.1, fun a ha => underTowerOk_of_recPre (h.2 a ha)⟩
  | [], ρp, h => by
    obtain ⟨hFs, hMok, hMeq, hMcont⟩ := h
    refine ⟨hMok, fun M hM => ?_⟩
    obtain ⟨hmok, hmeq, hrest⟩ := hMcont M hM
    refine ⟨hmok, fun m hm => ?_⟩
    obtain ⟨htok, hteq⟩ := hrest m hm
    refine ⟨htok, fun t ht => ?_⟩
    -- the semantic readings of the three binders
    rw [hMeq] at hM
    rw [hmeq] at hm
    rw [hteq] at ht
    -- the motive's applications are truth values at `ℓ = 0`
    have hM0 : ℓ = 0 → ∀ y : V,
        SetTheory.app M y ∈ˢ (univZero : V) := by
      intro h0 y
      by_cases hy : y ∈ˢ towerSet w (teleOfFields ρp Fs)
      · have hmem := app_mem_piR_pos (Nat.succ_ne_zero ℓ) hM hy
        rw [h0, univ_zero] at hmem
        exact hmem
      · rw [(mem_piR_pos (Nat.succ_ne_zero ℓ) hM).2.2.1 y hy]
        rw [← univ_zero]
        exact empty_mem_univ 0
    -- the spine, graded and folded
    have hspine := minorSp_spine (V := V) hM0
      (Fs := Fs) (args := (List.range Fs.length).map
        fun i => projAV i (.bvar 0))
      (ρf := ρp) (acc := []) (f := .bvar 1)
      (σ := cons t (cons m (cons M ρp)))
      (by simp) hm
      (by
        have hfit := argsOkFit_projSpine (Fs := Fs) (ρp := ρp)
          (σ := cons t (cons m (cons M ρp))) ht hFs.toBound
          Fs.length 0 (Nat.zero_add _)
        rwa [← List.range_eq_range', List.drop_zero] at hfit)
    refine ⟨hspine.1, ?_, ?_⟩
    · -- membership in `⟦motive t⟧`
      have hconv : (if w = 0 then pt
          else mkTower ([] ++ ((List.range Fs.length).map
            fun i => projAV i (.bvar 0)).map
              (interp2 V (cons t (cons m (cons M ρp)))))) = t := by
        have hmap : (((List.range Fs.length).map
            fun i => projAV i (.bvar 0)).map
              (interp2 V (cons t (cons m (cons M ρp)))))
            = projList Fs.length t := by
          rw [List.map_map, projList_eq_map_range]
          apply List.map_congr_left
          intro i _
          show interp2 V _ (projAV i (.bvar 0)) = projS i t
          rw [projAV_interp, interp2_bvar]
          rfl
        rw [List.nil_append, hmap]
        split
        · next h0 => exact ((towerSet_zero_elim _ (h0 ▸ ht)).1).symm
        · next hnz => exact ((towerSet_elim hnz _ ht).2).symm
      have hgoal := hspine.2
      rw [hconv] at hgoal
      exact hgoal
    · -- the base's truth-value condition at `ℓ = 0`
      intro h0
      have hMt := app_mem_piR_pos (Nat.succ_ne_zero ℓ) hM ht
      rw [h0, univ_zero] at hMt
      exact hMt

/-- **The recursor leaf inhabits its type's reading.** -/
theorem directRecAV_mem {ℓ w : Nat} {Fs : List AVExpr} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM dm dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM, dm, dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPre ℓ w ρ Fs dM dm dt pds) :
    interp2 V ρ (directRecAV ℓ (pds ++ [dM, dm, dt]) Fs.length)
      ∈ˢ interp2 V ρ
        (mkPisAV (pds ++ [dM, dm, dt]) (.app (.bvar 2) (.bvar 0))) :=
  mkLamsC_mem hz (underTowerOk_of_recPre hpre)

/-- **The recursor leaf is graded** (`AnnotOk2`). -/
theorem directRecAV_ok2 {ℓ w : Nat} {Fs : List AVExpr} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM dm dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM, dm, dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPre ℓ w ρ Fs dM dm dt pds) :
    AnnotOk2 V ρ (directRecAV ℓ (pds ++ [dM, dm, dt]) Fs.length) :=
  mkLamsC_ok2 hz (underTowerOk_of_recPre hpre)

/-! ## The iota side -/

/-- The body's raw interpretation: the minor slot applied along the
projections of the major slot — no premises (matching the tier's
unconditional-iota discipline). -/
theorem recBodyAV_interp (n : Nat) (σ : Nat → V) :
    interp2 V σ (recBodyAV n)
      = ((List.range n).map fun i => projS i (σ 0)).foldl
          SetTheory.app (σ 1) := by
  rw [recBodyAV, interp2_mkAppN, List.foldl_map, List.foldl_map]
  simp only [projAV_interp, interp2_bvar]

/-- **Iota, spelled**: on a constructor tower the body computes the
minor applied to the fields — `projS_mkTower` pointwise, no typing of
the fields at all. -/
theorem recBodyAV_fold_mk {n : Nat} {bs : List V} (h : bs.length = n)
    (σ : Nat → V) (hmaj : σ 0 = mkTower bs) :
    interp2 V σ (recBodyAV n) = bs.foldl SetTheory.app (σ 1) := by
  rw [recBodyAV_interp, hmaj, map_range_projS_mkTower h]

end Setlec.SetR.Interp2
