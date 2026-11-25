module

public import ConLeche.Model.Env.BlockLfp
import ConLeche.Model.Env.BlockLfpTup
public import ConLeche.Semantics.Inductives.TeleAcc
import ConLeche.SetModel.Access

public section

/-!
# The hole fit is ACCESSIBLE, from its constructors' telescopes (strictly first-order)

The consumer side of accessibility: the hole fit of an lfp datum is
accessible (`LfpDatum.FitAcc`) with ONE set `A` — a set of the level at a
`Type`-valued block — as soon as every constructor's field telescope is
accessible along the ACCESSIBILITY RELATION at the hole frame (`accRel`:
the hole frames of any two tuples of the space), with a telescope bound
(`teleBound`) that reads no hole.

* **First-order set supports (`occOfItem`, `SpineFitEnc`).**
  `teleBound_support` returns a set-level support graph `g ∈ˢ piSet B _ _`
  carrying `occEncItem` items (`HoleAcc.lean`); `fitAcc_holeOp` separates
  fitting member spines via `hasSep_of_defPred` (`SpineFitEnc`) and maps
  them to `occSpace D.N (D.idx ψ ρp) X` via `DefFun`-definable `occOfItem`.
* **Non-fitting spines (`holeFam_foldl_full`, `accRel_ptHitStable`).**
  At every level (including `w = 0`), a `foldl app` spine hitting `pt`
  cannot fit a member's index telescope (`IsTy.ne_pt`), so `holeFam_foldl_nofit`
  gives `pt`-stability (`FrameRel.PtHitStable`) for `AccOn.holeApp`.
-/

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A λ-tower at its full arity -/

theorem foldlApp_empty : ∀ (vs : List V), vs.foldl app (empty : V) = empty
  | [] => rfl
  | v :: vs => by
    show vs.foldl app (app empty v) = empty
    rw [app_empty]
    exact foldlApp_empty vs

theorem foldlApp_pt : ∀ (vs : List V), vs.foldl app (pt : V) = pt
  | [] => rfl
  | v :: vs => by
    show vs.foldl app (app pt v) = pt
    rw [app_pt]
    exact foldlApp_pt vs

/-- **A λ-tower applied to a spine of its full length** computes at a
fitting spine and is junk otherwise: `∅` where a graph is applied off its
domain, the point where a level is (no spine fits its telescope). -/
theorem holeFam_foldl_full :
    ∀ {ρ : Nat → V} {Fs : List Term} {vs : List V} (g : List V → V)
      {hg_def : DefHoleFn Fs.length g},
      vs.length = Fs.length →
      (SpineFit ρ Fs vs ∧ vs.foldl app (holeFam ρ Fs g hg_def) = g vs) ∨
        (¬ SpineFit ρ Fs vs ∧
          (vs.foldl app (holeFam ρ Fs g hg_def) = empty ∨
            vs.foldl app (holeFam ρ Fs g hg_def) = pt))
  | _, [], [], _, _, _ => Or.inl ⟨trivial, by rw [holeFam_nil]; rfl⟩
  | _, [], _ :: _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, h => by simp at h
  | ρ, F :: Fs, a :: vs, g, hg_def, h => by
    rw [List.foldl_cons, holeFam_cons]
    by_cases ha : a ∈ˢ interp V ρ F
    · rw [app_lamV ha]
      rcases holeFam_foldl_full (ρ := cons a ρ) (Fs := Fs) (vs := vs) (fun as => g (a :: as))
          (hg_def := hg_def.cons a) (by simpa using h) with ⟨hf, he⟩ | ⟨hn, he⟩
      · exact Or.inl ⟨⟨ha, hf⟩, he⟩
      · exact Or.inr ⟨fun hf => hn hf.2, he⟩
    · refine Or.inr ⟨fun hf => ha hf.1, ?_⟩
      by_cases hp : lamV (interp V ρ F)
          (fun x => holeFam (cons x ρ) Fs (fun as => g (x :: as)) (hg_def.cons x))
          (holeFam_hasGraph ρ F Fs g hg_def) = pt
      · rw [hp, app_pt]
        exact Or.inr (foldlApp_pt vs)
      · rw [lamV_eq_graph hp, app_graph_of_not_mem ha]
        exact Or.inl (foldlApp_empty vs)

namespace LfpDatum

variable {D : LfpDatum V}

/-! ## The accessibility relation at the hole frame -/

variable (D) in
/-- **The accessibility relation** at the hole frame of `ρp`: the frames of
any two tuples of the space. -/
@[expose] def accRel (ψ : Name → Nat) (ρp : Nat → V) : FrameRel V :=
  fun σ σ' => ∃ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y ∧ σ = D.frame ψ ρp X ∧ σ' = D.frame ψ ρp Y

variable (D) in
/-- **The member holes at their full arity**: member `t`'s hole (position
`k - 1 - t` of the hole frame) at its indices. -/
@[expose] def MemberQ (ψ : Name → Nat) : Nat → Nat → Prop :=
  fun i n => ∃ t, t < D.k ∧ i = D.k - 1 - t ∧ n = (D.ids t ψ).length

theorem memberQ_finQ (ψ : Name → Nat) : FinQ (D.MemberQ ψ) := by
  refine ⟨(List.range D.k).map fun t => (D.k - 1 - t, (D.ids t ψ).length), fun i n => ?_⟩
  simp only [MemberQ, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨t, ht, rfl, rfl⟩

theorem accRel_symm {ψ : Name → Nat} {ρp : Nat → V} : (D.accRel ψ ρp).Symm := by
  rintro _ _ ⟨X, Y, hX, hY, rfl, rfl⟩
  exact ⟨Y, X, hY, hX, rfl, rfl⟩

theorem accRel_refl {ψ : Name → Nat} {ρp X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) :
    D.accRel ψ ρp (D.frame ψ ρp X) (D.frame ψ ρp X) :=
  ⟨X, X, hX, hX, rfl, rfl⟩

/-- The frames agree off the member holes. -/
theorem accRel_agreeOff {ψ : Name → Nat} {ρp : Nat → V} {σ σ' : Nat → V}
    (h : D.accRel ψ ρp σ σ') : ∀ i, D.k ≤ i → σ i = σ' i := by
  obtain ⟨X, Y, -, -, rfl, rfl⟩ := h
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + D.k := ⟨i - D.k, by omega⟩
  rw [frame_param, frame_param]

/-! ## Items and occurrences -/

variable (D) in
/-- **The occurrence of a member-hole item** (encoded in `V` via `occEnc`). -/
@[expose] noncomputable def occOf (ψ : Name → Nat) (o : Occ V) : V :=
  occEnc (D.k - 1 - o.1) (tupW (D.u (D.k - 1 - o.1) ψ) o.2.1) o.2.2

/-- **A held item at a fitting spine is an occurrence in `occSpace`.** -/
theorem inTup_occOf (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp X : Nat → V}
    {o : Occ V} (hQ : Adm (D.MemberQ ψ) o)
    (hfit : SpineFit ρp (D.ids (D.k - 1 - o.1) ψ) o.2.1)
    (hH : Holds (D.frame ψ ρp X) o) : D.occOf ψ o ∈ˢ occSpace D.N (D.idx ψ ρp) X := by
  obtain ⟨i, vs, y⟩ := o
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  unfold Holds at hH
  simp only at hH hlen hfit
  rw [frame_hole ht] at hH
  unfold holeVal at hH
  have ht' : D.k - 1 - (D.k - 1 - t) = t := by omega
  rw [ht'] at hfit
  unfold occOf
  simp only [ht']
  rw [holeFam_app _ hfit] at hH
  exact occEnc_mem_occSpace.mpr ⟨by omega, tupW_mem hfit, hH⟩

/-- **An occurrence held by another tuple holds the item at its frame**
(at a fitting spine). -/
theorem holds_of_inTup {ψ : Name → Nat} {ρp X' : Nat → V} {o : Occ V}
    (hQ : Adm (D.MemberQ ψ) o) (hfit : SpineFit ρp (D.ids (D.k - 1 - o.1) ψ) o.2.1)
    (hin : D.occOf ψ o ∈ˢ occSpace D.N (D.idx ψ ρp) X') : Holds (D.frame ψ ρp X') o := by
  obtain ⟨i, vs, y⟩ := o
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  unfold Holds
  simp only at hlen hfit ⊢
  rw [frame_hole ht]
  unfold holeVal
  have ht' : D.k - 1 - (D.k - 1 - t) = t := by omega
  rw [ht'] at hfit
  obtain ⟨-, -, hy⟩ := occEnc_mem_occSpace.mp (by simpa [occOf, ht'] using hin)
  rw [holeFam_app _ hfit]
  exact hy

/-- **Off a fitting spine an item is held alike at every tuple's frame**:
the hole's value there does not read the tuple (`holeFam_foldl_nofit`;
the tuple's fibres are strict sets or truth values, never the point). -/
theorem holds_of_nofit {ψ : Name → Nat} {ρp X X' : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) (hX' : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X')
    (hkN : D.k ≤ D.N) {o : Occ V} (hQ : Adm (D.MemberQ ψ) o)
    (hn : ¬ SpineFit ρp (D.ids (D.k - 1 - o.1) ψ) o.2.1)
    (hH : Holds (D.frame ψ ρp X) o) : Holds (D.frame ψ ρp X') o := by
  obtain ⟨i, vs, y⟩ := o
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  unfold Holds at hH ⊢
  simp only at hlen hn hH ⊢
  rw [frame_hole ht] at hH ⊢
  unfold holeVal at hH ⊢
  have ht' : D.k - 1 - (D.k - 1 - t) = t := by omega
  rw [ht'] at hn
  have htN : t < D.N := by omega
  have hne : ∀ (Y : Nat → V), InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y →
      ∀ ws, SpineFit ρp (D.ids t ψ) ws → app (Y t) (tupW (D.u t ψ) ws) ≠ pt :=
    fun Y hY ws hws => (IsTy_of_mem_strictU (famSpace_app (hY t htN) (tupW_mem hws))).ne_pt
  rw [holeFam_foldl_nofit (hne X' hX') (hne X hX) hlen hn]
  exact hH

/-! ## Point-free holes and `pt`-stability -/

/-- **The member holes never hold the point** along the accessibility
relation (at a positive level): at a fitting spine a hole's value is a
fibre of the tuple, a strict set; elsewhere it is `∅` or the point,
which is not its own member. -/
theorem accRel_ptFree (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp : Nat → V} (hw : D.w ψ ≠ 0) :
    PtFreeOn (D.MemberQ ψ) (D.accRel ψ ρp) := by
  rintro _ _ ⟨X, Y, hX, -, rfl, -⟩ i vs hQ hpt
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  have htN : t < D.N := by omega
  rw [frame_hole ht] at hpt
  unfold holeVal at hpt
  rcases holeFam_foldl_full (ρ := ρp) (Fs := D.ids t ψ) (vs := vs)
      (fun vs => app (X t) (tupW (D.u t ψ) vs)) hlen with ⟨hf, he⟩ | ⟨-, he | he⟩
  · rw [he] at hpt
    have hs := famSpace_app (hX t htN) (tupW_mem hf)
    exact (((mem_strictU_pos hw).mp hs).2).2 hpt
  · rw [he] at hpt
    exact not_mem_empty _ hpt
  · rw [he] at hpt
    exact not_mem_self _ hpt

/-- **`pt`-stability along `D.accRel`** (`AccOn.holeApp` B1 guard): if a
`foldl app` prefix hits `pt` at `D.frame ψ ρp X`, then `vs` is non-fitting
(fitting spines yield strict sets `≠ pt` by `IsTy.ne_pt`) and
`holeFam_foldl_nofit` keeps the value `pt` at `D.frame ψ ρp Y`. -/
theorem accRel_ptHitStable (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp : Nat → V} :
    (D.accRel ψ ρp).PtHitStable (D.MemberQ ψ) := by
  rintro _ _ ⟨X, Y, hX, hY, rfl, rfl⟩ i vs hQ hnp y hy
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  have htN : t < D.N := by omega
  have hptX : vs.foldl app (D.frame ψ ρp X (D.k - 1 - t)) = pt :=
    foldlApp_eq_pt_of_not_noPtPrefix hnp
  rw [frame_hole ht] at hptX ⊢
  unfold holeVal at hptX ⊢
  have hne : ∀ (Z : Nat → V), InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Z →
      ∀ ws, SpineFit ρp (D.ids t ψ) ws → app (Z t) (tupW (D.u t ψ) ws) ≠ pt :=
    fun Z hZ ws hws => (IsTy_of_mem_strictU (famSpace_app (hZ t htN) (tupW_mem hws))).ne_pt
  have hnfit : ¬ SpineFit ρp (D.ids t ψ) vs := by
    intro hfit
    rw [holeFam_app _ hfit] at hptX
    exact hne X hX vs hfit hptX
  rw [holeFam_foldl_nofit (hg'_def := DefHoleFn.of_app_tupW (X t) (D.u t ψ) (D.ids t ψ).length)
    (hne Y hY) (hne X hX) hlen hnfit, hptX]
  exact hy

/-! ## First-order item decoding and spine separation helpers -/

/-- First-order `SpineFit` check directly on an `encSpineY`-encoded spine. -/
private def SpineFitEnc (ρ : Nat → V) : List Term → V → Prop
  | [], _ => True
  | F :: Fs, s => sfst s ∈ˢ interp V ρ F ∧ SpineFitEnc (cons (sfst s) ρ) Fs (ssnd s)

private theorem spineFitEnc_encSpineY :
    ∀ {Fs : List Term} {ρ : Nat → V} {vs : List V} {y : V},
      vs.length = Fs.length →
      (SpineFitEnc ρ Fs (encSpineY vs y) ↔ SpineFit ρ Fs vs)
  | [], _, [], _, _ => Iff.rfl
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | F :: Fs, ρ, v :: vs, y, hlen => by
    unfold SpineFitEnc SpineFit encSpineY
    rw [sfst_kpair, ssnd_kpair]
    have hrest := spineFitEnc_encSpineY (Fs := Fs) (ρ := cons v ρ) (vs := vs) (y := y)
      (by simpa using hlen)
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hrest.mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hrest.mpr h2⟩⟩

private theorem defRel_spineFitEnc_aux (tail : Nat → V) :
    ∀ (Fs : List Term) (d : Nat),
      DefRel (d + 1) fun v => SpineFitEnc (prepend (ftail v) tail) Fs (v 0)
  | [], d => DefRel.true
  | F :: Fs, d => by
    unfold SpineFitEnc
    have hF : DefFun (d + 1) fun v => interp V (prepend (ftail v) tail) F :=
      ((interp_defFun_prepend tail d F).reIndex fun i => i.succ).congr fun _ => rfl
    have h1 : DefRel (d + 1) fun v =>
        sfst (v 0) ∈ˢ interp V (prepend (ftail v) tail) F :=
      DefRel.mem_apply (DefFun.sfst_apply (DefFun.proj 0)) hF
    have hrec : DefRel ((d + 1) + 1) fun w =>
        SpineFitEnc (prepend (ftail w) tail) Fs (w 0) :=
      defRel_spineFitEnc_aux tail Fs (d + 1)
    let Gs : Fin ((d + 1) + 1) → (Fin (d + 1) → V) → V := fun j v =>
      if hj0 : j.val = 0 then ssnd (v 0)
      else if hj1 : j.val = 1 then sfst (v 0)
      else v ⟨j.val - 1, by omega⟩
    have hGs : ∀ j : Fin ((d + 1) + 1), DefFun (d + 1) (Gs j) := fun j => by
      dsimp only [Gs]
      by_cases hj0 : j.val = 0
      · simp only [hj0, ↓reduceDIte]; exact DefFun.ssnd_apply (DefFun.proj 0)
      · by_cases hj1 : j.val = 1
        · simp only [hj1, ↓reduceDIte]; exact DefFun.sfst_apply (DefFun.proj 0)
        · simp only [hj0, hj1, ↓reduceDIte]; exact DefFun.proj ⟨j.val - 1, by omega⟩
    have h2 : DefRel (d + 1) fun v =>
        SpineFitEnc (cons (sfst (v 0)) (prepend (ftail v) tail)) Fs (ssnd (v 0)) := by
      refine (hrec.comp hGs).congr fun v => ?_
      have h0 : Gs 0 v = ssnd (v 0) := rfl
      have hp : prepend (ftail fun j => Gs j v) tail =
          cons (sfst (v 0)) (prepend (ftail v) tail) := by
        funext k
        cases k with
        | zero => simp [prepend, ftail, Gs]
        | succ k =>
          by_cases hk : k < d
          · have hk1 : k + 1 < d + 1 := by omega
            simp [prepend, ftail, Gs, cons, hk, hk1]
          · have hk1 : ¬ (k + 1 < d + 1) := by omega
            simp only [prepend, cons, hk, hk1, ↓reduceDIte]
            congr 1; omega
      dsimp only
      rw [h0, hp]
    exact DefRel.and h1 h2

private theorem defRel_spineFitEnc (ρ : Nat → V) (Fs : List Term) :
    DefRel 1 fun v => SpineFitEnc ρ Fs (v 0) :=
  (defRel_spineFitEnc_aux ρ Fs 0).congr fun v => by
    have hp : prepend (ftail v) ρ = ρ := funext fun i => by simp [prepend]
    rw [hp]

/-- Encodes an `encSpineY`-encoded spine of fixed length `n` into `mkTower`. -/
private noncomputable def mkTowerEnc (s : V) : Nat → V
  | 0 => empty
  | n + 1 => spair (sfst s) (mkTowerEnc (ssnd s) n)

private theorem mkTowerEnc_encSpineY :
    ∀ {vs : List V} {y : V}, mkTowerEnc (encSpineY vs y) vs.length = mkTower vs
  | [], _ => rfl
  | v :: vs, y => by
    rw [List.length_cons, mkTowerEnc, encSpineY, mkTower, sfst_kpair, ssnd_kpair, mkTowerEnc_encSpineY]

private theorem DefFun.mkTowerEnc_apply {k : Nat} :
    ∀ (n : Nat) {S : (Fin k → V) → V}, DefFun k S →
      DefFun k fun env => mkTowerEnc (S env) n
  | 0, _, _ => DefFun.empty
  | n + 1, _, hS =>
    DefFun.spair_apply (DefFun.sfst_apply hS) (DefFun.mkTowerEnc_apply n (DefFun.ssnd_apply hS))

/-- Encodes an `encSpineY`-encoded spine of length `n` into `tupW u`. -/
private noncomputable def tupWEnc (u n : Nat) (s : V) : V :=
  if u = 0 then pt else mkTowerEnc s n

private theorem tupWEnc_encSpineY (u : Nat) {vs : List V} {y : V} :
    tupWEnc u vs.length (encSpineY vs y) = tupW u vs := by
  unfold tupWEnc
  by_cases hu : u = 0
  · subst hu; rw [ite_eq_left rfl, tupW_zero]
  · rw [ite_eq_right hu, tupW_pos hu, mkTowerEnc_encSpineY]

private theorem DefFun.tupWEnc_apply {k : Nat} (u n : Nat) {S : (Fin k → V) → V}
    (hS : DefFun k S) : DefFun k fun env => tupWEnc u n (S env) := by
  unfold tupWEnc
  by_cases hu : u = 0
  · subst hu; exact DefFun.pt.congr fun _ => by simp
  · exact (DefFun.mkTowerEnc_apply n hS).congr fun _ => by simp [hu]

/-- Maps an encoded hole item `occEncItem (D.k - 1 - t) vs y` (`t < D.k`)
to `occEnc t (tupW (D.u t ψ) vs) y` by finite case analysis over `t < k'`. -/
private noncomputable def occOfAux (D : LfpDatum V) (ψ : Name → Nat) : Nat → V → V
  | 0, _ => empty
  | t + 1, o =>
      open Classical in
      if sfst o = vnat (D.k - 1 - t) then
        occEnc t (tupWEnc (D.u t ψ) (D.ids t ψ).length (ssnd (ssnd o)))
          (lastVal (ssnd (ssnd o)) (D.ids t ψ).length)
      else occOfAux D ψ t o

private theorem defFun_occOfAux (D : LfpDatum V) (ψ : Name → Nat) :
    ∀ k' : Nat, DefFun 1 fun v => occOfAux D ψ k' (v 0)
  | 0 => DefFun.empty
  | t + 1 => by
    unfold occOfAux
    refine DefFun.ite (DefRel.eq_apply (DefFun.sfst_apply (DefFun.proj 0)) (DefFun.const (vnat (D.k - 1 - t))))
      ?_ (defFun_occOfAux D ψ t)
    exact DefFun.occEnc_apply t
      (DefFun.tupWEnc_apply (D.u t ψ) (D.ids t ψ).length
        (DefFun.ssnd_apply (DefFun.ssnd_apply (DefFun.proj 0))))
      (DefFun.lastVal_apply (D.ids t ψ).length
        (DefFun.ssnd_apply (DefFun.ssnd_apply (DefFun.proj 0))))

private theorem occOfAux_eq {D : LfpDatum V} {ψ : Name → Nat} :
    ∀ (k' : Nat), k' ≤ D.k → ∀ {t : Nat} (_htk : t < k') (_htD : t < D.k) {vs : List V} {y : V},
      vs.length = (D.ids t ψ).length →
      occOfAux D ψ k' (occEncItem (D.k - 1 - t) vs y) = occEnc t (tupW (D.u t ψ) vs) y
  | 0, _, _, _htk, _, _, _, _ => absurd _htk (Nat.not_lt_zero _)
  | t' + 1, hk', t, htk, htD, vs, y, hlen => by
    unfold occOfAux
    by_cases heq : t = t'
    · subst heq
      rw [ite_eq_left (by unfold occEncItem; rw [sfst_kpair])]
      unfold occEncItem
      rw [ssnd_kpair, ssnd_kpair, ← hlen, tupWEnc_encSpineY, lastVal_encSpineY]
    · have hne : sfst (occEncItem (D.k - 1 - t) vs y) ≠ vnat (D.k - 1 - t') := by
        unfold occEncItem
        rw [sfst_kpair]
        intro hv
        have := vnat_inj hv
        omega
      rw [ite_eq_right hne]
      exact occOfAux_eq t' (by omega) (by omega) htD hlen

/-! ## The assembly -/

/-- A finite union. -/
noncomputable def finUnion (f : Nat → V) : Nat → V
  | 0 => empty
  | n + 1 => binUnion (finUnion f n) (f n)

theorem subset_finUnion {f : Nat → V} : ∀ {n i : Nat}, i < n → f i ⊆ˢ finUnion f n
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
    intro x hx
    show x ∈ˢ binUnion (finUnion f n) (f n)
    by_cases hin : i = n
    · subst hin; exact mem_binUnion.mpr (Or.inr hx)
    · exact mem_binUnion.mpr (Or.inl (subset_finUnion (by omega) x hx))

theorem finUnion_mem {w' : Nat} (hw : w' ≠ 0) {f : Nat → V} :
    ∀ {n : Nat}, (∀ i, i < n → f i ∈ˢ (tg w' : V)) → finUnion f n ∈ˢ (tg w' : V)
  | 0, _ => empty_mem_tg w'
  | n + 1, h => (tg_isGrothendieck hw).binUnion_mem
      (finUnion_mem hw fun i hi => h i (by omega)) (h n (by omega))

/-- **The hole fit is accessible with ONE bound**, a set of the level at
a `Type`-valued block: strictly first-order, returning set-level support graphs
in `occSpace` via `teleBound_support` and `hasSep_of_defPred`. -/
theorem fitAcc_holeOp {ψ : Name → Nat} {ρp : Nat → V} (hkN : D.k ≤ D.N)
    (ord : Nat → Nat → Nat → Bool) (Af : Nat → Nat → Nat → (Nat → V) → V)
    (hAf : ∀ c, c < D.N → ∀ j, j < D.nctors c →
      ∀ l τ τ', TAgr D.k (ord c j) l τ τ' → Af c j l τ = Af c j l τ')
    (hAf_def : ∀ c, c < D.N → ∀ j, j < D.nctors c →
      ∀ l, DefBound (D.k + l) (Af c j l))
    (hF : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ (i : Nat) (F : Term),
      (D.fields ψ c j)[i]? = some F → ord c j i = true →
        ∀ τ τ', TAgr D.k (ord c j) i τ τ' → interp V τ F = interp V τ' F)
    (htele : ∀ c, c < D.N → ∀ j, j < D.nctors c →
      TeleAccP (D.w ψ) (Af c j) 0 (D.MemberQ ψ) (D.accRel ψ ρp) (D.fields ψ c j))
    (hresC : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ X X',
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X' →
      ∀ fs, SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs →
        SpineFit (D.frame ψ ρp X') (D.fields ψ c j) fs →
        ∀ e ∈ D.resIdx ψ c j,
          interp V (consList fs (D.frame ψ ρp X)) e = interp V (consList fs (D.frame ψ ρp X')) e) :
    ∃ A, SmallAt (D.w ψ) A ∧ D.FitAcc ψ ρp A := by
  let X₀ : Nat → V := AccIter.emptyTup (D.idx ψ ρp)
  have hX₀ : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X₀ :=
    AccIter.emptyTup_mem (w := D.w ψ) (k := D.N) (Is := D.idx ψ ρp)
  let TB : Nat → Nat → V := fun c j =>
    teleBound (D.w ψ) (ord c j) (Af c j) 0 (D.fields ψ c j) (D.frame ψ ρp X₀)
  refine ⟨finUnion (fun c => finUnion (TB c) (D.nctors c)) D.N,
    fun hw => finUnion_mem hw fun c _ => finUnion_mem hw fun j _ => teleBound_mem hw _ _ _ _ _, ?_⟩
  rintro X hX m hm t j fs ⟨hj, hsp, hidx⟩
  have hF0 : ∀ (i : Nat) (F : Term), (D.fields ψ m j)[i]? = some F →
      ord m j (0 + i) = true → ∀ τ τ', TAgr D.k (ord m j) (0 + i) τ τ' →
        interp V τ F = interp V τ' F := by
    intro i F h1 h2 τ τ' h3
    rw [Nat.zero_add] at h2 h3
    exact hF m hm j hj i F h1 h2 τ τ' h3
  obtain ⟨B, g, hB, ⟨U, hg⟩, hitems, hs⟩ :=
    teleBound_support (d0 := D.k) (hAf m hm j hj)
      (fun l' _ => hAf_def m hm j hj l')
      (D.fields ψ m j) 0 (D.MemberQ ψ) (D.accRel ψ ρp) hF0 (htele m hm j hj)
      (D.frame ψ ρp X) (accRel_refl hX) fs hsp
  have hagr : TAgr D.k (ord m j) 0 (D.frame ψ ρp X) (D.frame ψ ρp X₀) := by
    intro i'
    refine ⟨fun h => absurd h (Nat.not_lt_zero _), fun h => ?_⟩
    obtain ⟨i'', rfl⟩ : ∃ i'', i' = i'' + D.k := ⟨i' - D.k, by omega⟩
    rw [frame_param, frame_param]
  have hTB : teleBound (D.w ψ) (ord m j) (Af m j) 0 (D.fields ψ m j) (D.frame ψ ρp X) = TB m j :=
    teleBound_agr (hAf m hm j hj) (D.fields ψ m j) 0 hF0 _ _ hagr
  let P' : V → Prop := fun b =>
    ∃ ti, ti < D.k ∧ ∃ s,
      app g b = kpair (vnat (D.k - 1 - ti)) (kpair (vnat (D.ids ti ψ).length) s) ∧
      SpineFitEnc ρp (D.ids ti ψ) s
  have hSepP' : HasSep B P' := by
    refine hasSep_of_defPred <|
      DefRel.finExists_lt fun ti _ => DefRel.exists_curry (DefRel.and
        (DefRel.eq_apply (DefFun.app_apply (DefFun.const g) (DefFun.proj 1))
          (DefFun.kpair_apply (DefFun.const (vnat (D.k - 1 - ti)))
            (DefFun.kpair_apply (DefFun.const (vnat (D.ids ti ψ).length)) (DefFun.proj 0))))
        ((defRel_spineFitEnc ρp (D.ids ti ψ)).reIndex fun _ => (0 : Fin (1 + 1))))
  let B' := sep B P' hSepP'
  have hg'_def : DefFun 1 fun v => occOfAux D ψ D.k (app g (v 0)) :=
    (defFun_occOfAux D ψ D.k).comp1 (DefFun.app_apply (DefFun.const g) (DefFun.proj 0))
  let g' := graph (fun b => occOfAux D ψ D.k (app g b)) B' (hasGraph_of_defFun1 hg'_def)
  refine ⟨B', g', fun b hb => ?_, graph_mem_piSet fun b hb => ?_, fun X' hX' hheld => ?_⟩
  · have := hB b (sep_subset b hb)
    rw [hTB] at this
    exact subset_finUnion (f := fun c => finUnion (TB c) (D.nctors c)) hm _
      (subset_finUnion hj _ this)
  · obtain ⟨hbB, ti, hti, s, heq_o, hsp_enc⟩ := mem_sep.mp hb
    obtain ⟨⟨i, vs, y, heq1, hq⟩, ⟨i', vs', y', heq2, _, hy⟩⟩ := hitems b hbB
    obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj (heq1.symm.trans heq2)
    obtain ⟨ti', hti', hi_eq, hlen⟩ := hq
    have heq_p : occEncItem i vs y =
        kpair (vnat (D.k - 1 - ti)) (kpair (vnat (D.ids ti ψ).length) s) := heq1.symm.trans heq_o
    unfold occEncItem at heq_p
    obtain ⟨hv_i, hrest⟩ := kpair_inj heq_p
    obtain ⟨hv_len, rfl⟩ := kpair_inj hrest
    have hti_eq : ti = ti' := by
      have := vnat_inj hv_i
      rw [hi_eq] at this
      omega
    subst hti_eq
    have hfit : SpineFit ρp (D.ids ti ψ) vs :=
      (spineFitEnc_encSpineY hlen).mp hsp_enc
    have hocc_eq : occOfAux D ψ D.k (app g b) = D.occOf ψ (i, vs, y) := by
      rw [heq1, hi_eq]
      unfold occOf
      rw [show D.k - 1 - (D.k - 1 - ti) = ti by omega]
      exact occOfAux_eq D.k (Nat.le_refl D.k) hti hti hlen
    rw [hocc_eq]
    subst hi_eq
    exact inTup_occOf hkN ⟨ti, hti, rfl, hlen⟩
      (by simpa [show D.k - 1 - (D.k - 1 - ti) = ti by omega] using hfit) hy
  · have hsp' : SpineFit (D.frame ψ ρp X') (D.fields ψ m j) fs := by
      refine hs (D.frame ψ ρp X') ⟨X, X', hX, hX', rfl, rfl⟩ fun b hb => ?_
      obtain ⟨⟨i, vs, y, heq1, hq⟩, ⟨i', vs', y', heq2, _, hy⟩⟩ := hitems b hb
      obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj (heq1.symm.trans heq2)
      obtain ⟨ti, hti, hi_eq, hlen⟩ := hq
      by_cases hfit : SpineFit ρp (D.ids ti ψ) vs
      · have hb' : b ∈ˢ B' := by
          refine mem_sep.mpr ⟨hb, ti, hti, encSpineY vs y, ?_, (spineFitEnc_encSpineY hlen).mpr hfit⟩
          rw [heq1, hi_eq, ← hlen]
          rfl
        have hheld' := hheld b hb'
        dsimp only [g'] at hheld'
        rw [app_graph hb', heq1, hi_eq, occOfAux_eq D.k (Nat.le_refl D.k) hti hti hlen] at hheld'
        have hholds : Holds (D.frame ψ ρp X') (i, vs, y) := by
          refine holds_of_inTup ⟨ti, hti, hi_eq, hlen⟩ ?_ ?_
          · rw [hi_eq, show D.k - 1 - (D.k - 1 - ti) = ti by omega]; exact hfit
          · unfold occOf
            rw [hi_eq, show D.k - 1 - (D.k - 1 - ti) = ti by omega]
            exact hheld'
        exact ⟨i, vs, y, heq1, hholds⟩
      · have hholdsX : Holds (D.frame ψ ρp X) (i, vs, y) := hy
        have hholdsX' : Holds (D.frame ψ ρp X') (i, vs, y) := by
          refine holds_of_nofit hX hX' hkN ⟨ti, hti, hi_eq, hlen⟩ ?_ hholdsX
          rw [hi_eq, show D.k - 1 - (D.k - 1 - ti) = ti by omega]
          exact hfit
        exact ⟨i, vs, y, heq1, hholdsX'⟩
    refine ⟨hj, hsp', fun l hl => ?_⟩
    obtain ⟨e, he, hev⟩ := hidx l hl
    refine ⟨e, he, ?_⟩
    rw [← hresC m hm j hj X X' hX hX' fs hsp hsp' e (List.mem_of_getElem? he)]
    exact hev

end LfpDatum

end ConLeche.Model
