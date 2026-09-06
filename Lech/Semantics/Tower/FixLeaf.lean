import Lech.Semantics.Tower.SumLeaf
import Lech.Semantics.Tower.SumMk
import Lech.Semantics.NoBVar
import Lech.SetModel.Iter
import Lech.SetModel.TowerMono

/-!
# The type-former leaf of a direct recursive block (task #188)

The carrier of a directly installed **recursive** inductive type is the
least pre-fixed point (`lfp`, `Lech/SetTheory/Derive/Lfp.lean`) of its
constructor-tower functor: the former's leaf is

    λ p⃗. lfp.{w} (λ (X : Sort w). Σ_k tower_k(X))

where each constructor's tower is spelled over its **X-chain**
(`chainX`): the chain of field domains in which every recursive slot
reads the bound `X` (as `bvar i` at position `i`, the binder for `X`
sitting just above the chain) and every ordinary domain is lifted past
that binder; the trailing unit field of the sum route (`idxEqAV []`,
`uChains`) is kept so that the constructor leaf and the case split of
the sum route apply verbatim.

Semantically the functor is `fixStep`: `X ↦ sumSet w (sumFibre w (cons
X ρp) (chainsX …))`, and the leaf's body reads to `lfpSet w (lamR (w+1)
(univ w) fixStep)`.  The laws established here, all under the one
grading premise `FixChainsOk` (the X-chains are graded at every `X ∈
univ w` — the P tier supplies it from the constructors' readings at a
dummy former plus `NoBVar` transfer):

* the leaf's formation/grading/fold (`directFixTyAV_mem/_ok2/_fold`);
* the functor is monotone (`fixStep_mono`: the tower and the tagged
  union are monotone in their field sets, `Lech/SetModel/TowerMono.lean`,
  and only the recursive slots read `X`) and maps the universe into
  itself (`fixStep_maps`);
* **a closed member exists** — the ω-iterate `iterU fixStep`
  (`Lech/SetModel/Iter.lean`): every member of a finitary tower over
  `iterU` has all its recursive components at some finite stage
  (`fitsX_iter`), so the ω-iterate is closed; hence the fixed-point
  equation (`fixCarrier_eq`) and structural induction
  (`fixCarrier_induction`) hold, and the carrier IS the ω-iterate
  (`fixCarrier_eq_iterU`);
* the identification with the real chains (`fixCarrier_eq_sum`): at
  the carrier itself the X-chains read as the constructors' real field
  chains (the recursive domains `T p⃗` read to the carrier), so the
  carrier is the tagged union of the real towers — the form the sum
  route's constructor leaf and case split consume.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The X-chains -/

/-- The X-chain of one constructor from position `i` on: a recursive
slot reads the functor's bound variable (`bvar i` at position `i`), an
ordinary domain is lifted past that binder. -/
def chainXGo (rs : List Bool) : List AVExpr → Nat → List AVExpr
  | [], _ => []
  | F :: Fs, i => (if rs.getD i false then .bvar i else F.liftN 1 i) :: chainXGo rs Fs (i + 1)

/-- The X-chain of one constructor, unit-terminated (`uChains`). -/
def chainX (rs : List Bool) (Fs : List AVExpr) : List AVExpr :=
  chainXGo rs Fs 0 ++ [idxEqAV []]

/-- The X-chains of all constructors. -/
def chainsX (rss : List (List Bool)) (Fss : List (List AVExpr)) : List (List AVExpr) :=
  List.zipWith chainX rss Fss

theorem chainsX_getElem? (rss : List (List Bool)) (Fss : List (List AVExpr)) (j : Nat) :
    (chainsX rss Fss)[j]? = match rss[j]?, Fss[j]? with
      | some rs, some Fs => some (chainX rs Fs)
      | _, _ => none := by
  simp only [chainsX, List.getElem?_zipWith]
  cases rss[j]? <;> cases Fss[j]? <;> rfl

/-- The functor's λ: `λ (X : Sort w). Σ_k tower_k(X)`. -/
def fixFunAV (w : Nat) (rss : List (List Bool)) (Fss : List (List AVExpr)) : AVExpr :=
  .lam (w + 1) (.sort w) (sumBodyAV w (chainsX rss Fss))

/-- The carrier body: `lfp.{w} (fixFunAV …)`. -/
def fixBodyAV (w : Nat) (rss : List (List Bool)) (Fss : List (List AVExpr)) : AVExpr :=
  .app (.const .lfp [w]) (fixFunAV w rss Fss)

/-- The type-former leaf of a direct recursive block: the λ-tower over
the parameter domains with the fixed-point body. -/
def directFixTyAV (w : Nat) (pps : List (Nat × Nat × AVExpr)) (rss : List (List Bool))
    (Fss : List (List AVExpr)) : AVExpr :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2)) (fixBodyAV w rss Fss)

/-! ## The semantic functor -/

/-- The constructor-tower functor at a parameter frame. -/
noncomputable def fixStep (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (Fss : List (List AVExpr)) (X : V) : V :=
  sumSet w (sumFibre w (cons X ρp) (chainsX rss Fss))

/-- The functor as a set-level function on `univ w`. -/
noncomputable def fixFunV (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (Fss : List (List AVExpr)) : V :=
  lamR (w + 1) (univ w) (fixStep w ρp rss Fss)

/-- The carrier at a parameter frame. -/
noncomputable def fixCarrier (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (Fss : List (List AVExpr)) : V :=
  lfpSet w (fixFunV w ρp rss Fss)

/-- The grading premise: at every `X ∈ univ w` the X-chains are
graded. -/
def FixChainsOk (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (Fss : List (List AVExpr)) : Prop :=
  ∀ X, X ∈ˢ (univ w : V) → SumFieldsOkB w (cons X ρp) (chainsX rss Fss)

theorem fixFunAV_interp {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    interp2 V ρp (fixFunAV w rss Fss) = fixFunV w ρp rss Fss := by
  unfold fixFunAV fixFunV
  rw [interp2_lam, interp2_sort]
  exact lamR_congr fun X hX => sumBodyAV_interp (hok X hX)

theorem fixFunV_mem {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    fixFunV w ρp rss Fss ∈ˢ lfpFunSpace V w :=
  lamR_mem fun X hX => sumSet_univ_of_okB (hok X hX)

theorem fixFunAV_ok2 {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    AnnotOk2 V ρp (fixFunAV w rss Fss) := by
  unfold fixFunAV
  rw [AnnotOk2_lam]
  refine ⟨by simp, fun X hX => sumBodyAV_ok2 (hok X hX),
    ⟨fun _ => univ w, fun X hX => ?_, fun h => absurd h (Nat.succ_ne_zero w)⟩⟩
  rw [sumBodyAV_interp (hok X hX)]
  exact sumSet_univ_of_okB (hok X hX)

theorem fixBodyAV_interp {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    interp2 V ρp (fixBodyAV w rss Fss) = fixCarrier w ρp rss Fss := by
  unfold fixBodyAV fixCarrier
  rw [interp2_app, interp2_const, fixFunAV_interp hok]
  exact lfpV2_app V (fixFunV_mem hok)

theorem fixBodyAV_mem {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    interp2 V ρp (fixBodyAV w rss Fss) ∈ˢ (univ w : V) := by
  rw [fixBodyAV_interp hok]; exact lfpSet_mem_univ w _

theorem fixBodyAV_ok2 {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    AnnotOk2 V ρp (fixBodyAV w rss Fss) := by
  unfold fixBodyAV
  rw [AnnotOk2_app]
  refine ⟨by simp, fixFunAV_ok2 hok, w + 1, lfpFunSpace V w, fun _ => univ w, ?_, ?_,
    fun h => absurd h (Nat.succ_ne_zero w)⟩
  · exact lfpV2_mem V w
  · rw [fixFunAV_interp hok]; exact fixFunV_mem hok

/-! ## The leaf -/

/-- `ParamsOkX`: the leaf's one hereditary premise — the parameter
telescope graded, `FixChainsOk` at the base. -/
def ParamsOkX (w : Nat) (ρ : Nat → V) (rss : List (List Bool)) (Fss : List (List AVExpr)) :
    List (Nat × Nat × AVExpr) → Prop
  | [] => FixChainsOk w ρ rss Fss
  | d :: pps => d.2.1 ≠ 0 ∧ AnnotOk2 V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp2 V ρ d.2.2 → ParamsOkX w (cons a ρ) rss Fss pps

/-- **The leaf inhabits its type's reading.** -/
theorem directFixTyAV_mem {w : Nat} {rss : List (List Bool)} {Fss : List (List AVExpr)} :
    ∀ {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      ParamsOkX w ρ rss Fss pps →
      interp2 V ρ (directFixTyAV w pps rss Fss) ∈ˢ interp2 V ρ (mkPisAV pps (.sort w))
  | [], ρ, h => fixBodyAV_mem h
  | d :: pps, ρ, h => by
    show (lamR (w + 1) (interp2 V ρ d.2.2)
        fun a => interp2 V (cons a ρ)
          (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) (fixBodyAV w rss Fss)))
      ∈ˢ piR d.2.1 (interp2 V ρ d.2.2)
        fun a => interp2 V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamR_mem_zero_agree (iff_of_false (Nat.succ_ne_zero w) h.1)
      (fun a ha => directFixTyAV_mem (h.2.2 a ha))

/-- **The leaf is graded.** -/
theorem directFixTyAV_ok2 {w : Nat} {rss : List (List Bool)} {Fss : List (List AVExpr)} :
    ∀ {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      ParamsOkX w ρ rss Fss pps → AnnotOk2 V ρ (directFixTyAV w pps rss Fss)
  | [], _, h => fixBodyAV_ok2 h
  | d :: pps, ρ, h => by
    show AnnotOk2 V ρ (.lam (w + 1) d.2.2
      (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) (fixBodyAV w rss Fss)))
    rw [AnnotOk2_lam]
    exact ⟨h.2.1, fun a ha => directFixTyAV_ok2 (h.2.2 a ha),
      ⟨fun a => interp2 V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => directFixTyAV_mem (h.2.2 a ha),
       fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩⟩

/-- **The leaf's application fold**: along a fitting parameter spine
the leaf computes the instantiated carrier. -/
theorem directFixTyAV_fold {w : Nat} {rss : List (List Bool)} {Fss : List (List AVExpr)}
    {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hok : FixChainsOk w (consList as ρ) rss Fss) :
    as.foldl SetTheory.app (interp2 V ρ (directFixTyAV w pps rss Fss))
      = fixCarrier w (consList as ρ) rss Fss := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [directFixTyAV,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp',
    fixBodyAV_interp hok]

/-! ## The X-chains at a frame -/

/-- An ordinary entry of the X-chain reads as the domain at the frame
without the `X` slot. -/
theorem interp2_chainX_ordinary {ρp : Nat → V} {X : V} (F : AVExpr) (as : List V) :
    interp2 V (consList as (cons X ρp)) (F.liftN 1 as.length) = interp2 V (consList as ρp) F := by
  rw [interp2_liftN, shiftE_consList_len, shiftE_succ_cons, shiftE_zero_zero]

/-- A recursive entry of the X-chain reads as `X`. -/
theorem interp2_chainX_rec {ρp : Nat → V} {X : V} (as : List V) :
    interp2 V (consList as (cons X ρp)) (.bvar as.length) = X := by
  rw [interp2_bvar]
  have := consList_apply_add as (cons X ρp) 0
  rwa [Nat.zero_add] at this

omit [SetTheory V] in
/-- One more binder under a frame: the value list grows at the end. -/
theorem consList_snoc (a : V) (as : List V) (ρ : Nat → V) :
    cons a (consList as ρ) = consList (as ++ [a]) ρ := by
  rw [consList_append]; rfl

omit [SetTheory V] in
theorem length_snoc (a : V) (as : List V) : (as ++ [a]).length = as.length + 1 := by
  simp

/-- The terminating unit field reads the same at every frame. -/
theorem interp2_idxEqAV_nil (ρ ρ' : Nat → V) :
    interp2 V ρ (idxEqAV []) = interp2 V ρ' (idxEqAV []) := by
  rw [idxEqAV_interp, idxEqAV_interp]
  congr 1
  exact propext ⟨fun _ => EqAll_nil ρ', fun _ => EqAll_nil ρ⟩

/-- **Monotonicity of the X-chain telescope** in `X`. -/
theorem chainXGo_tele_sub {ρp : Nat → V} {X Y : V} (hXY : X ⊆ˢ Y) (rs : List Bool) :
    ∀ (Fs : List AVExpr) (i : Nat) (as : List V), as.length = i →
      TeleS.Sub (teleOfFields (consList as (cons X ρp)) (chainXGo rs Fs i ++ [idxEqAV []]))
        (teleOfFields (consList as (cons Y ρp)) (chainXGo rs Fs i ++ [idxEqAV []]))
  | [], i, as, _ => by
    simp only [chainXGo, List.nil_append, teleOfFields]
    rw [interp2_idxEqAV_nil (consList as (cons X ρp)) (consList as (cons Y ρp))]
    exact .cons (Subset.refl _) fun _ _ => .nil
  | F :: Fs, i, as, hi => by
    subst hi
    simp only [chainXGo, List.cons_append, teleOfFields]
    refine .cons ?_ fun a _ => ?_
    · split
      · rw [interp2_chainX_rec, interp2_chainX_rec]; exact hXY
      · rw [interp2_chainX_ordinary, interp2_chainX_ordinary]; exact Subset.refl _
    · rw [consList_snoc, consList_snoc]
      exact chainXGo_tele_sub (ρp := ρp) hXY rs Fs (as.length + 1) (as ++ [a]) (length_snoc a as)

/-- The functor is monotone. -/
theorem fixStep_mono {w : Nat} {ρp : Nat → V} {rss : List (List Bool)} {Fss : List (List AVExpr)}
    {X Y : V} (hXY : X ⊆ˢ Y) : fixStep w ρp rss Fss X ⊆ˢ fixStep w ρp rss Fss Y := by
  unfold fixStep
  refine sumSet_mono fun j => ?_
  unfold sumFibre
  rw [chainsX_getElem?]
  cases rss[j]? with
  | none => exact Subset.refl _
  | some rs =>
    cases Fss[j]? with
    | none => exact Subset.refl _
    | some Fs =>
      simp only
      refine towerSet_mono ?_
      exact chainXGo_tele_sub (ρp := ρp) hXY rs Fs 0 [] rfl

/-- The functor maps the universe into itself. -/
theorem fixStep_maps {w : Nat} {ρp : Nat → V} {rss : List (List Bool)} {Fss : List (List AVExpr)}
    (hok : FixChainsOk w ρp rss Fss) {X : V} (hX : X ∈ˢ (univ w : V)) :
    fixStep w ρp rss Fss X ∈ˢ (univ w : V) :=
  sumSet_univ_of_okB (hok X hX)

theorem fixFunV_app {w : Nat} {ρp : Nat → V} {rss : List (List Bool)} {Fss : List (List AVExpr)}
    {X : V} (hX : X ∈ˢ (univ w : V)) :
    SetTheory.app (fixFunV w ρp rss Fss) X = fixStep w ρp rss Fss X :=
  app_lamR_pos (Nat.succ_ne_zero w) hX

theorem fixFunV_mono {w : Nat} {ρp : Nat → V} {rss : List (List Bool)} {Fss : List (List AVExpr)} :
    MonoIn w (fixFunV w ρp rss Fss) := by
  intro X Y hX hY hXY
  rw [fixFunV_app hX, fixFunV_app hY]
  exact fixStep_mono hXY

theorem fixFunV_maps {w : Nat} {ρp : Nat → V} {rss : List (List Bool)} {Fss : List (List AVExpr)}
    (hok : FixChainsOk w ρp rss Fss) : MapsIn w (fixFunV w ρp rss Fss) := by
  intro X hX
  rw [fixFunV_app hX]
  exact fixStep_maps hok hX

/-! ## The ω-iterate is closed -/

/-- **Finitarity**: a tuple fitting the X-chain telescope at the
ω-iterate fits it at some finite stage — each recursive component
lies at a finite stage, and the stages are cumulative. -/
theorem fitsX_iter {ρp : Nat → V} {Φ : V → V} (hcum : ∀ m n, m ≤ n → iterF Φ m ⊆ˢ iterF Φ n)
    (rs : List Bool) :
    ∀ (Fs : List AVExpr) (i : Nat) (as bs : List V), as.length = i →
      FitsS (teleOfFields (consList as (cons (iterU Φ) ρp))
        (chainXGo rs Fs i ++ [idxEqAV []])) bs →
      ∃ n, FitsS (teleOfFields (consList as (cons (iterF Φ n) ρp))
        (chainXGo rs Fs i ++ [idxEqAV []])) bs
  | [], i, as, bs, _, hf => by
    refine ⟨0, ?_⟩
    simp only [chainXGo, List.nil_append, teleOfFields] at hf ⊢
    rw [interp2_idxEqAV_nil (consList as (cons (iterF Φ 0) ρp)) (consList as (cons (iterU Φ) ρp))]
    exact hf
  | F :: Fs, i, as, bs, hi, hf => by
    subst hi
    simp only [chainXGo, List.cons_append, teleOfFields] at hf ⊢
    cases bs with
    | nil => exact hf.elim
    | cons b bs =>
      obtain ⟨hb, hrest⟩ := hf
      have hrest : FitsS (teleOfFields (consList (as ++ [b]) (cons (iterU Φ) ρp))
          (chainXGo rs Fs (as.length + 1) ++ [idxEqAV []])) bs := by
        rw [← consList_snoc]; exact hrest
      obtain ⟨n₁, hn₁⟩ := fitsX_iter hcum rs Fs (as.length + 1) (as ++ [b]) bs (length_snoc b as) hrest
      rw [← consList_snoc] at hn₁
      split at hb
      · rw [interp2_chainX_rec] at hb
        obtain ⟨n₀, hn₀⟩ := mem_iterU.mp hb
        refine ⟨max n₀ n₁, ?_⟩
        rw [if_pos ‹_›]
        refine ⟨?_, ?_⟩
        · rw [interp2_chainX_rec]; exact hcum _ _ (Nat.le_max_left _ _) b hn₀
        · show FitsS (teleOfFields (cons b (consList as (cons (iterF Φ (max n₀ n₁)) ρp)))
            (chainXGo rs Fs (as.length + 1) ++ [idxEqAV []])) bs
          refine FitsS.mono ?_ hn₁
          rw [consList_snoc, consList_snoc]
          exact chainXGo_tele_sub (ρp := ρp) (hcum _ _ (Nat.le_max_right n₀ n₁)) rs Fs
            (as.length + 1) (as ++ [b]) (length_snoc b as)
      · refine ⟨n₁, ?_⟩
        rw [if_neg ‹_›]
        refine ⟨?_, ?_⟩
        · rw [interp2_chainX_ordinary] at hb ⊢; exact hb
        · exact hn₁

theorem iterF_fixStep_mem {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    ∀ n, iterF (fixStep w ρp rss Fss) n ∈ˢ (univ w : V)
  | 0 => empty_mem_univ w
  | n + 1 => fixStep_maps hok (iterF_fixStep_mem hok n)

/-- **The ω-iterate of the functor is closed.** -/
theorem fixStep_iterU_closed {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} :
    fixStep w ρp rss Fss (iterU (fixStep w ρp rss Fss)) ⊆ˢ iterU (fixStep w ρp rss Fss) := by
  refine iterU_closed_of fun x hx => ?_
  have hcum : ∀ m n, m ≤ n → iterF (fixStep w ρp rss Fss) m ⊆ˢ iterF (fixStep w ρp rss Fss) n :=
    fun _ _ h => iterF_mono (fun _ _ hXY => fixStep_mono hXY) h
  -- a member of the sum at the ω-iterate: some constructor's tower
  have hx' : x ∈ˢ sumSet w (sumFibre w (cons (iterU (fixStep w ρp rss Fss)) ρp)
      (chainsX rss Fss)) := hx
  clear hx
  show ∃ n, x ∈ˢ sumSet w (sumFibre w (cons (iterF (fixStep w ρp rss Fss) n) ρp)
      (chainsX rss Fss))
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx'
    unfold sumFibre at ha
    rw [chainsX_getElem?] at ha
    cases hr : rss[j]? with
    | none => rw [hr] at ha; exact absurd ha (not_mem_empty _)
    | some rs =>
      cases hF : Fss[j]? with
      | none => rw [hr, hF] at ha; exact absurd ha (not_mem_empty _)
      | some Fs =>
        rw [hr, hF] at ha
        simp only at ha
        obtain ⟨-, bs, hfit⟩ := towerSet_zero_elim _ ha
        obtain ⟨n, hn⟩ := fitsX_iter hcum rs Fs 0 [] bs rfl hfit
        refine ⟨n, pt_mem_sumSet_zero (i := j) (a := pt) ?_⟩
        unfold sumFibre
        rw [chainsX_getElem?, hr, hF]
        exact pt_mem_tower hn
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw' hx'
    unfold sumFibre at ha
    rw [chainsX_getElem?] at ha
    cases hr : rss[j]? with
    | none => rw [hr] at ha; exact absurd ha (not_mem_empty _)
    | some rs =>
      cases hF : Fss[j]? with
      | none => rw [hr, hF] at ha; exact absurd ha (not_mem_empty _)
      | some Fs =>
        rw [hr, hF] at ha
        simp only at ha
        obtain ⟨hfit, heta⟩ := towerSet_elim hw' _ ha
        obtain ⟨n, hn⟩ := fitsX_iter hcum rs Fs 0 [] _ rfl hfit
        refine ⟨n, inj_mem hw' ?_⟩
        unfold sumFibre
        rw [chainsX_getElem?, hr, hF]
        rw [heta]
        exact mkTower_mem hw' hn

/-- **A closed member exists**: the ω-iterate. -/
theorem fixFunV_closed_exists {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    ∃ L, IsClosedIn w (fixFunV w ρp rss Fss) L := by
  refine ⟨iterU (fixStep w ρp rss Fss), iterU_mem_univ (iterF_fixStep_mem hok), ?_⟩
  rw [fixFunV_app (iterU_mem_univ (iterF_fixStep_mem hok))]
  exact fixStep_iterU_closed

/-! ## The carrier's laws -/

theorem fixCarrier_mem_univ (w : Nat) (ρp : Nat → V) (rss : List (List Bool))
    (Fss : List (List AVExpr)) : fixCarrier w ρp rss Fss ∈ˢ (univ w : V) :=
  lfpSet_mem_univ w _

/-- **The fixed-point equation.** -/
theorem fixCarrier_eq {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    fixStep w ρp rss Fss (fixCarrier w ρp rss Fss) = fixCarrier w ρp rss Fss := by
  have := lfpSet_eq (fixFunV_closed_exists hok) fixFunV_mono (fixFunV_maps hok)
  rwa [fixFunV_app (lfpSet_mem_univ w _)] at this

/-- **Structural induction** on the carrier. -/
theorem fixCarrier_induction {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) (P : V → Prop)
    (hP : ∀ x, x ∈ˢ fixStep w ρp rss Fss (sep (fixCarrier w ρp rss Fss) P) → P x) :
    ∀ x, x ∈ˢ fixCarrier w ρp rss Fss → P x := by
  refine lfpSet_induction (fixFunV_closed_exists hok) fixFunV_mono P fun x hx => hP x ?_
  rwa [fixFunV_app (univ_sep_mem (lfpSet_mem_univ w _))] at hx

/-- **The carrier is the ω-iterate.** -/
theorem fixCarrier_eq_iterU {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss) :
    fixCarrier w ρp rss Fss = iterU (fixStep w ρp rss Fss) := by
  refine Subset.antisymm ?_ ?_
  · refine lfpSet_subset ⟨iterU_mem_univ (iterF_fixStep_mem hok), ?_⟩
    rw [fixFunV_app (iterU_mem_univ (iterF_fixStep_mem hok))]
    exact fixStep_iterU_closed
  · have hn : ∀ n, iterF (fixStep w ρp rss Fss) n ⊆ˢ fixCarrier w ρp rss Fss := by
      intro n
      induction n with
      | zero => exact empty_subset _
      | succ n ih =>
        rw [iterF_succ]
        refine Subset.trans (fixStep_mono ih) ?_
        rw [fixCarrier_eq hok]
        exact Subset.refl _
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iterU.mp hx
    exact hn n x hxn

/-! ## The identification with the real chains -/

/-- `ChainReal μ ρp rs i Fs₀ Fs`: the constructor's real field chain
`Fs` (its domains read at the block's environment) against the chain
`Fs₀` the X-chain was spelled from — at a recursive position the real
domain reads to the carrier `μ` at every frame of the right depth, at
an ordinary position the two are the same term. -/
def ChainReal (μ : V) (ρp : Nat → V) (rs : List Bool) :
    Nat → List AVExpr → List AVExpr → Prop
  | _, [], [] => True
  | i, F₀ :: Fs₀, F :: Fs =>
      (if rs.getD i false then ∀ as : List V, as.length = i → interp2 V (consList as ρp) F = μ
       else F = F₀) ∧ ChainReal μ ρp rs (i + 1) Fs₀ Fs
  | _, _, _ => False

/-- The X-chain tower at the carrier is the real chain's tower. -/
theorem towerSet_chainX_eq {w : Nat} {μ : V} {ρp : Nat → V} (rs : List Bool) :
    ∀ (Fs₀ Fs : List AVExpr) (i : Nat) (as : List V), as.length = i → ChainReal μ ρp rs i Fs₀ Fs →
      towerSet w (teleOfFields (consList as (cons μ ρp)) (chainXGo rs Fs₀ i ++ [idxEqAV []]))
        = towerSet w (teleOfFields (consList as ρp) (Fs ++ [idxEqAV []]))
  | [], [], i, as, _, _ => by
    simp only [chainXGo, List.nil_append, teleOfFields]
    rw [interp2_idxEqAV_nil (consList as (cons μ ρp)) (consList as ρp)]
  | [], _ :: _, _, _, _, hc => hc.elim
  | _ :: _, [], _, _, _, hc => hc.elim
  | F₀ :: Fs₀, F :: Fs, i, as, hi, hc => by
    subst hi
    simp only [chainXGo, List.cons_append, teleOfFields, towerSet]
    obtain ⟨hhead, htail⟩ := hc
    have hA : interp2 V (consList as (cons μ ρp))
        (if rs.getD as.length false then AVExpr.bvar as.length else F₀.liftN 1 as.length)
        = interp2 V (consList as ρp) F := by
      split
      · rw [interp2_chainX_rec]; rw [if_pos ‹_›] at hhead; exact (hhead as rfl).symm
      · rw [interp2_chainX_ordinary]; rw [if_neg ‹_›] at hhead; rw [hhead]
    rw [hA]
    congr 1
    funext a
    rw [consList_snoc, consList_snoc]
    exact towerSet_chainX_eq (w := w) (μ := μ) (ρp := ρp) rs Fs₀ Fs (as.length + 1) (as ++ [a])
      (length_snoc a as) htail

/-- `ChainsReal`: `ChainReal` for every constructor. -/
def ChainsReal (μ : V) (ρp : Nat → V) (rss : List (List Bool))
    (Fss₀ Fss : List (List AVExpr)) : Prop :=
  rss.length = Fss.length ∧ Fss₀.length = Fss.length ∧
  ∀ (j : Nat) rs Fs₀ Fs, rss[j]? = some rs → Fss₀[j]? = some Fs₀ → Fss[j]? = some Fs →
    ChainReal μ ρp rs 0 Fs₀ Fs

/-- **The functor at the carrier is the tagged union of the real
towers.** -/
theorem fixStep_eq_sum {w : Nat} {μ : V} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss₀ Fss : List (List AVExpr)} (hreal : ChainsReal μ ρp rss Fss₀ Fss) :
    fixStep w ρp rss Fss₀ μ = sumSet w (sumFibre w ρp (uChains Fss)) := by
  unfold fixStep
  refine sumSet_congr fun j => ?_
  unfold sumFibre
  rw [chainsX_getElem?, uChains_getElem?]
  obtain ⟨hl₁, hl₂, h⟩ := hreal
  cases hF : Fss[j]? with
  | none =>
    have hj : Fss.length ≤ j := List.getElem?_eq_none_iff.mp hF
    rw [List.getElem?_eq_none (by omega)]
    rfl
  | some Fs =>
    have hj : j < Fss.length := (List.getElem?_eq_some_iff.mp hF).1
    obtain ⟨rs, hr⟩ : ∃ rs, rss[j]? = some rs :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨Fs₀, hF₀⟩ : ∃ Fs₀, Fss₀[j]? = some Fs₀ :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [hr, hF₀]
    simp only
    exact towerSet_chainX_eq (w := w) rs Fs₀ Fs 0 [] rfl (h j rs Fs₀ Fs hr hF₀ hF)

/-- **The carrier is the tagged union of the real towers.** -/
theorem fixCarrier_eq_sum {w : Nat} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss₀ Fss : List (List AVExpr)} (hok : FixChainsOk w ρp rss Fss₀)
    (hreal : ChainsReal (fixCarrier w ρp rss Fss₀) ρp rss Fss₀ Fss) :
    fixCarrier w ρp rss Fss₀ = sumSet w (sumFibre w ρp (uChains Fss)) := by
  rw [← fixStep_eq_sum hreal]
  exact (fixCarrier_eq hok).symm

end Lech.Semantics
