module

public import ConLeche.Model.Inductives.ContWalk
public import ConLeche.Model.Inductives.NestPosAcc
import ConLeche.Model.Env.LfpAcc
import ConLeche.SetModel.Access
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.FamilyRun
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The container frame's accessibility relation

The twin of `frameRel`/`frameRel_holeRel` (`ContWalk.lean`) for the
accessibility route: a container frame's walk runs along `frameRelA` — the
enclosing relation `R₀` at the key's depth, extended by the reached group's
hole values at ANY tuple of the container's space (comparable frames, no
order) — and `frameRelA` is an accessibility hole relation (`HoleRelA`) of
the frame's walk (`frameRelA_holeRelA`).

A frame hole stands for its member's whole application (it takes no
parameters), and a group member's hole value reads its key frame only
through the index telescope, which reads alike at two frames agreeing off
the holes (N2's `TeleEq`), so a hole value does not move when the
enclosing frame changes off the holes.  The holes never
hold the point: a new hole's value at its full arity is a fibre of the
tuple (a strict set, as in `LfpDatum.accRel_ptFree`) or `∅`; an enclosing
hole is the enclosing relation's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.SetTheory.Tower (projS)
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The admissible items of a frame's walk -/

/-- **The admissible items under a frame**: the new holes (positions below
the group's length, at their members' full arity) and the enclosing ones
moved up. -/
theorem holeQ_frame_iff {ctx : NestCtx} {prog news : List NestHole} {i n : Nat} :
    HoleQ ctx (news.reverse ++ prog) (ctx.hiAt prog.length + news.length) i n ↔
      (∃ (j : Nat) (hk : NestHole), news[j]? = some hk ∧ i = news.length - 1 - j ∧
        n = hk.nIdx) ∨
      (news.length ≤ i ∧ HoleQ ctx prog (ctx.hiAt prog.length) (i - news.length) n) := by
  constructor
  · rintro (⟨t, ht, hlt, rfl, hn⟩ | ⟨j, hk, hj, hlt, rfl, hn⟩)
    · refine Or.inr ⟨by simp only [NestCtx.hiAt]; omega, Or.inl ⟨t, ht, ?_, ?_, hn⟩⟩
      · simp only [NestCtx.hiAt]; omega
      · simp only [NestCtx.hiAt]; omega
    · rw [List.reverse_append, List.reverse_reverse] at hj
      by_cases hjp : j < prog.length
      · rw [List.getElem?_append_left (by simpa using hjp)] at hj
        refine Or.inr ⟨by simp only [NestCtx.hiAt] at hlt ⊢; omega, Or.inr ⟨j, hk, hj, ?_, ?_, hn⟩⟩
        · simp only [NestCtx.hiAt]; omega
        · simp only [NestCtx.hiAt]; omega
      · rw [List.getElem?_append_right (by simpa using hjp), List.length_reverse] at hj
        have hjn := (List.getElem?_eq_some_iff.mp hj).1
        refine Or.inl ⟨j - prog.length, hk, hj, ?_, hn⟩
        simp only [NestCtx.hiAt]; omega
  · rintro (⟨j, hk, hj, rfl, hn⟩ | ⟨hle, ⟨t, ht, hlt, hi, hn⟩ | ⟨j, hk, hj, hlt, hi, hn⟩⟩)
    · have hjn := (List.getElem?_eq_some_iff.mp hj).1
      refine Or.inr ⟨prog.length + j, hk, ?_, ?_, ?_, hn⟩
      · rw [List.reverse_append, List.reverse_reverse,
          List.getElem?_append_right (by simp), List.length_reverse]
        simpa using hj
      · simp only [NestCtx.hiAt]; omega
      · simp only [NestCtx.hiAt]; omega
    · refine Or.inl ⟨t, ht, by omega, ?_, hn⟩
      simp only [NestCtx.hiAt] at hi hlt ⊢; omega
    · have hjp := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_reverse] at hjp
      refine Or.inr ⟨j, hk, ?_, ?_, ?_, hn⟩
      · rw [List.reverse_append, List.reverse_reverse,
          List.getElem?_append_left (by simpa using hjp)]
        exact hj
      · simp only [NestCtx.hiAt]; omega
      · simp only [NestCtx.hiAt] at hi hlt ⊢; omega

/-! ## The relation -/

/-- **The frame relation for accessibility**: the enclosing relation at the
key's depth, extended by the group's hole values at ANY tuple of the
container's space at each side's key frame. -/
@[expose] def frameRelA (R₀ : FrameRel V) (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) (dsa : List Term) (hi : Nat) : FrameRel V :=
  fun σ σ' => ∃ ρ ρ' Y Y', R₀ ρ ρ' ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ)) Y ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ (keyFrame dsa hi ρ')) Y' ∧
    σ = consList (grpVals D ψ grp (keyFrame dsa hi ρ) Y) ρ ∧
    σ' = consList (grpVals D ψ grp (keyFrame dsa hi ρ') Y') ρ'

theorem grpVals_length (D : LfpDatum V) (ψ : Name → Nat) (grp : List (Name × Expr))
    (ρp Y : Nat → V) : (grpVals D ψ grp ρp Y).length = grp.length := by
  simp [grpVals]

theorem grpNews_length (us : List Level) (ds : List Expr) (hi : Nat) (grp : List (Name × Expr)) :
    (grpNews us ds hi grp).length = grp.length := by
  simp [grpNews]

private theorem defHoleFn_cons_list {r n : Nat} {g : List V → V} (hg : DefHoleFn (r + n) g) :
    ∀ (as : List V), as.length = r → DefHoleFn n fun vs => g (as ++ vs) := by
  induction r generalizing g with
  | zero =>
    intro as hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    rw [Nat.zero_add] at hg
    simpa only [List.nil_append] using hg
  | succ r ih =>
    intro as hlen
    cases as with
    | nil => simp at hlen
    | cons a as =>
      rw [Nat.succ_add] at hg
      exact ih (hg.cons a) as (by simpa using hlen)

private theorem defFun_mkTower_ofFn {k : Nat} :
    ∀ {r : Nat} (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefFun k fun env => Tower.mkTower (List.ofFn fun i => As i env)
  | 0, _, _ => DefFun.empty.congr fun _ => by simp [Tower.mkTower]
  | r + 1, As, hAs => by
    have hrest := defFun_mkTower_ofFn (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    exact (DefFun.spair_apply (hAs 0) hrest).congr fun env => by
      simp [List.ofFn_succ, Tower.mkTower]

private theorem defFun_tupW_ofFn (u : Nat) {k r : Nat}
    (As : Fin r → (Fin k → V) → V) (hAs : ∀ i, DefFun k (As i)) :
    DefFun k fun env => tupW u (List.ofFn fun i => As i env) := by
  by_cases hu : u = 0
  · subst hu
    exact DefFun.pt.congr fun _ => (tupW_zero _).symm
  · exact (defFun_mkTower_ofFn As hAs).congr fun _ => (tupW_pos hu _).symm

private theorem holeFam_congr {Fs : List Term} {ρ ρ' : Nat → V} {g g' : List V → V}
    {hg : DefHoleFn Fs.length g} {hg' : DefHoleFn Fs.length g'}
    (hρ : ρ = ρ') (hg_eq : g = g') :
    holeFam ρ Fs g hg = holeFam ρ' Fs g' hg' := by
  subst hρ hg_eq
  rfl

private theorem defFun_holeFam_app_ofFn (u : Nat) (tail : Nat → V) :
    ∀ (Fs : List Term) {k m r : Nat}
      (Xs : Fin m → (Fin k → V) → V) (_ : ∀ i, DefFun k (Xs i))
      (Y : (Fin k → V) → V) (_ : DefFun k Y)
      (As : Fin r → (Fin k → V) → V) (_ : ∀ i, DefFun k (As i)),
      DefFun k fun env =>
        holeFam (Semantics.prepend (fun i => Xs i env) tail) Fs
          (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs)))
          (defHoleFn_cons_list (DefHoleFn.of_app_tupW (Y env) u (r + Fs.length))
            (List.ofFn fun i => As i env) List.length_ofFn)
  | [], k, m, r, Xs, hXs, Y, hY, As, hAs =>
    (DefFun.app_apply hY (defFun_tupW_ofFn u As hAs)).congr fun env => by
      rw [holeFam_nil, List.append_nil]
  | F :: Fs, k, m, r, Xs, hXs, Y, hY, As, hAs => by
    have hF : DefFun k fun env => interp V (Semantics.prepend (fun i => Xs i env) tail) F :=
      (interp_defFun_prepend tail m F).comp hXs
    let Xs' : Fin (m + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if h0 : i.val = 0 then w 0 else Xs ⟨i.val - 1, by omega⟩ (ftail w)
    have hXs' : ∀ i, DefFun (k + 1) (Xs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Xs']
      split
      · exact DefFun.proj 0
      · exact (hXs _).weaken
    let Y' : (Fin (k + 1) → V) → V := fun w => Y (ftail w)
    have hY' : DefFun (k + 1) Y' := hY.weaken
    let As' : Fin (r + 1) → (Fin (k + 1) → V) → V := fun i w =>
      if hi : i.val < r then As ⟨i.val, hi⟩ (ftail w) else w 0
    have hAs' : ∀ i, DefFun (k + 1) (As' i) := fun ⟨i, hi⟩ => by
      dsimp only [As']
      split
      · exact (hAs _).weaken
      · exact DefFun.proj 0
    have hrec := defFun_holeFam_app_ofFn u tail Fs Xs' hXs' Y' hY' As' hAs'
    let hg_all : ∀ env, DefHoleFn (F :: Fs).length
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ vs))) := fun env =>
      defHoleFn_cons_list (DefHoleFn.of_app_tupW (Y env) u (r + (F :: Fs).length))
        (List.ofFn fun i => As i env) List.length_ofFn
    let F_lam : V → (Fin k → V) → V := fun x env =>
      holeFam (cons x (Semantics.prepend (fun i => Xs i env) tail)) Fs
        (fun vs => app (Y env) (tupW u (List.ofFn (fun i => As i env) ++ x :: vs)))
        ((hg_all env).cons x)
    have hrec' : DefFun (k + 1) fun w => F_lam (w 0) (ftail w) := by
      refine hrec.congr fun w => ?_
      have hρ : Semantics.prepend (fun i => Xs' i w) tail =
          cons (w 0) (Semantics.prepend (fun i => Xs i (ftail w)) tail) := by
        funext j
        cases j with
        | zero => simp [Semantics.prepend, Xs']
        | succ j =>
          by_cases hj : j < m
          · have hj1 : j + 1 < m + 1 := by omega
            simp [Semantics.prepend, hj, hj1, Xs', cons]
          · have hj1 : ¬ (j + 1 < m + 1) := by omega
            simp only [Semantics.prepend, hj, hj1, ↓reduceDIte, cons]
            congr 1; omega
      have hA_eq : List.ofFn (fun i => As' i w) =
          List.ofFn (fun i => As i (ftail w)) ++ [w 0] := by
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.length_ofFn] at h1
        simp only [List.getElem_ofFn, As']
        by_cases hj : j < r
        · simp [hj, List.getElem_append_left]
        · have hjr : j = r := by omega
          subst hjr
          simp [List.getElem_append_right]
      have h_fn : (fun vs => app (Y' w) (tupW u (List.ofFn (fun i => As' i w) ++ vs))) =
          (fun vs => app (Y (ftail w)) (tupW u (List.ofFn (fun i => As i (ftail w)) ++ w 0 :: vs))) := by
        funext vs
        change app (Y (ftail w)) (tupW u (List.ofFn (fun i => As' i w) ++ vs)) = _
        rw [hA_eq, List.append_assoc, List.singleton_append]
      exact holeFam_congr hρ h_fn
    have hGraph : ∀ env, HasGraph (interp V (Semantics.prepend (fun i => Xs i env) tail) F)
        (fun x => F_lam x env) := fun env =>
      holeFam_hasGraph (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)
    refine (DefFun.lamV_apply_curry (F := F_lam) (h := hGraph) hrec' hF).congr fun env => ?_
    exact (holeFam_cons (Semantics.prepend (fun i => Xs i env) tail) F Fs _ (hg_all env)).symm

private theorem keyFrame_prepend_eq {dsa : List Term} {hi : Nat} (tail : Nat → V)
    (xs : Fin hi → V) :
    keyFrame dsa hi (Semantics.prepend xs tail) =
      Semantics.prepend (fun j : Fin dsa.length =>
        interp V (Semantics.prepend xs tail) (dsa[dsa.length - 1 - j.val]'(by omega))) tail := by
  funext k
  unfold keyFrame
  have htail : (fun j => Semantics.prepend xs tail (j + hi)) = tail := by
    funext j
    have hge : ¬ (j + hi < hi) := by omega
    simp only [Semantics.prepend, hge, ↓reduceDIte]
    congr 1; omega
  rw [htail]
  by_cases hk : k < dsa.length
  · simp only [Semantics.prepend, hk, ↓reduceDIte]
    have hk' : dsa.length - 1 - k < dsa.length := by omega
    have hpos := consList_getElem_pos (ρ := tail)
      (by simp : (List.map (interp V (Semantics.prepend xs tail)) dsa).length = dsa.length) hk'
    rw [show dsa.length - 1 - (dsa.length - 1 - k) = k by omega] at hpos
    rw [hpos]
    simp [List.getElem_map]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + dsa.length := ⟨k - dsa.length, by omega⟩
    have hm_not : ¬ (m + dsa.length < dsa.length) := by omega
    simp only [Semantics.prepend, hm_not, ↓reduceDIte, Nat.add_sub_cancel]
    have hlen : m + dsa.length = m + (List.map (interp V (Semantics.prepend xs tail)) dsa).length := by simp
    rw [hlen, consList_apply_add]

private theorem grp_idxOf_inj {D : LfpDatum V} {grp : List (Name × Expr)}
    (hnodup : (grp.map (·.1)).Nodup) (hall : ∀ c, c ∈ grp.map (·.1) ↔ c ∈ D.names)
    {j₁ j₂ : Nat} (hj₁ : j₁ < grp.length) (hj₂ : j₂ < grp.length)
    (heq : D.names.idxOf grp[j₁].1 = D.names.idxOf grp[j₂].1) : j₁ = j₂ := by
  have h1 : grp[j₁].1 ∈ D.names := (hall _).mp (List.mem_map.mpr ⟨_, List.getElem_mem hj₁, rfl⟩)
  have h2 : grp[j₂].1 ∈ D.names := (hall _).mp (List.mem_map.mpr ⟨_, List.getElem_mem hj₂, rfl⟩)
  have heq' : grp[j₁].1 = grp[j₂].1 := by
    have hget : D.names[D.names.idxOf grp[j₁].1]? = D.names[D.names.idxOf grp[j₂].1]? := by rw [heq]
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h1),
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h2),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem h1),
      List.getElem_idxOf (List.idxOf_lt_length_of_mem h2)] at hget
    exact Option.some.inj hget
  have hp := List.pairwise_iff_getElem.mp hnodup
  have h1' : j₁ < (grp.map (·.1)).length := by simpa using hj₁
  have h2' : j₂ < (grp.map (·.1)).length := by simpa using hj₂
  by_cases hlt : j₁ < j₂
  · exact absurd (by simpa using heq') (hp j₁ j₂ h1' h2' hlt)
  · by_cases hgt : j₂ < j₁
    · exact absurd (by simpa using heq'.symm) (hp j₂ j₁ h2' h1' hgt)
    · omega

private theorem defRel_holeFrameSide (D : LfpDatum V) (ψ : Name → Nat)
    (grp : List (Name × Expr)) (dsa : List Term) (tail : Nat → V)
    {k hi n : Nat} (hn : grp.length = n)
    (Xs_ρ : Fin hi → (Fin k → V) → V) (hXs_ρ : ∀ i, DefFun k (Xs_ρ i))
    (σ_slot : Fin n → (Fin k → V) → V) (hσ_slot : ∀ i, DefFun k (σ_slot i)) :
    DefRel k fun v =>
      ∀ j : Fin n, ∃ y : V,
        y ∈ˢ famSpace (D.w ψ)
          (D.idx ψ (keyFrame dsa hi (Semantics.prepend (fun i => Xs_ρ i v) tail))
            (D.names.idxOf (grp[j.val]'(by omega)).1)) ∧
        σ_slot ⟨n - 1 - j.val, by omega⟩ v =
          D.holeVal ψ (keyFrame dsa hi (Semantics.prepend (fun i => Xs_ρ i v) tail))
            (fun _ => y) (D.names.idxOf (grp[j.val]'(by omega)).1) := by
  let kf_Xs : Fin dsa.length → (Fin k → V) → V := fun i v =>
    interp V (Semantics.prepend (fun j => Xs_ρ j v) tail) (dsa[dsa.length - 1 - i.val]'(by omega))
  have hkf_Xs : ∀ i, DefFun k (kf_Xs i) := fun i =>
    (interp_defFun_prepend tail hi _).comp hXs_ρ
  refine DefRel.finForall fun j : Fin n => ?_
  let mm := D.names.idxOf (grp[j.val]'(by omega)).1
  refine DefRel.exists_curry (DefRel.and ?_ ?_)
  · have h_idx : DefFun (k + 1) fun w =>
        Tower.towerSet (D.u mm ψ)
          (teleOfFields (Semantics.prepend (fun i => kf_Xs i (ftail w)) tail) (D.ids mm ψ))
          (hasTeleS_teleOfFields (D.u mm ψ)
            (Semantics.prepend (fun i => kf_Xs i (ftail w)) tail) (D.ids mm ψ)) :=
      (DefFun.towerSet_apply (D.u mm ψ)
        (h := fun xs => hasTeleS_teleOfFields (D.u mm ψ) (Semantics.prepend xs tail) (D.ids mm ψ))
        (defTeleS_teleOfFields tail (D.ids mm ψ) dsa.length)).comp (fun i => (hkf_Xs i).weaken)
    refine (DefRel.mem_apply (DefFun.proj 0) (DefFun.famSpace_apply (D.w ψ) h_idx)).congr fun w => ?_
    show (w 0 ∈ˢ famSpace (D.w ψ)
        (idxSet (D.u mm ψ) (Semantics.prepend (fun i => kf_Xs i (ftail w)) tail) (D.ids mm ψ))) ↔ _
    rw [← keyFrame_prepend_eq tail (fun i => Xs_ρ i (ftail w))]
    exact Iff.rfl
  · have h_hole := defFun_holeFam_app_ofFn (D.u mm ψ) tail (D.ids mm ψ)
      (fun i w => kf_Xs i (ftail w)) (fun i => (hkf_Xs i).weaken)
      (fun w => w 0) (DefFun.proj (k := k + 1) 0)
      (fun (_ : Fin 0) (_ : Fin (k + 1) → V) => (empty : V)) (fun i => Fin.elim0 i)
    refine (DefRel.eq_apply (hσ_slot ⟨n - 1 - j.val, by omega⟩).weaken h_hole).congr fun w => ?_
    have heqv : holeFam (Semantics.prepend (fun i => kf_Xs i (ftail w)) tail) (D.ids mm ψ)
          (fun vs => app (w 0) (tupW (D.u mm ψ) (List.ofFn (fun _ : Fin 0 => (empty : V)) ++ vs)))
          (defHoleFn_cons_list (DefHoleFn.of_app_tupW (w 0) (D.u mm ψ) (0 + (D.ids mm ψ).length))
            (List.ofFn fun _ : Fin 0 => (empty : V)) List.length_ofFn) =
        D.holeVal ψ (keyFrame dsa hi (Semantics.prepend (fun i => Xs_ρ i (ftail w)) tail))
          (fun _ => w 0) mm := by
      unfold LfpDatum.holeVal
      exact holeFam_congr (keyFrame_prepend_eq tail (fun i => Xs_ρ i (ftail w))).symm rfl
    rw [heqv]

section Frame

variable (mp : EnvModelM V env) {D : LfpDatum V}
  (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
  (hfind : ∀ n, ctx.find? n = env.find? n) {lps : List Name}
  (hlps : ∀ mm, mm < D.k → ∃ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  (hnd : lps.Nodup) {us : List Level} (hul : us.length = lps.length) {hi : Nat} {ds : List Expr}
  (hds : ∀ x ∈ ds, Expr.WScoped hi x ∧ x.looseBVarsBounded 0 = true) {dsa : List Term}
  (hdsa : DenoteSpine mp.base2.acval env φ hi ds dsa)
  (hlenP : (D.params (Level.substFn φ lps us)).length = ds.length)
  {grp : List (Name × Expr)} (hg : GrpWf env ctx D hi us ds grp)

include hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg

omit hnN hkN hfind hlps hnd hul hds hg in
/-- The members' own parameter telescopes are as long as the key's. -/
theorem parsLen_dsa {mm : Nat} (hmm : mm < D.k) :
    (D.pars mm (Level.substFn φ lps us)).length = dsa.length := by
  obtain ⟨h, -, -, -⟩ := mp.lfp_ok D hD
  rw [h.parsLen mm hmm, hlenP, DenoteSpine.length_eq hdsa]

omit hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg in
/-- **The frame hole's value at full arity** is an occurrence of the tuple
at its member, or `∅`, or the point. -/
theorem grp_hole_full {mm : Nat} (ρp Y : Nat → V) {vs : List V}
    (hlen : vs.length = (D.ids mm (Level.substFn φ lps us)).length) :
    (SpineFit ρp (D.ids mm (Level.substFn φ lps us)) vs ∧
      vs.foldl app (D.holeVal (Level.substFn φ lps us) ρp Y mm)
        = app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) vs)) ∨
      (¬ SpineFit ρp (D.ids mm (Level.substFn φ lps us)) vs ∧
        (vs.foldl app (D.holeVal (Level.substFn φ lps us) ρp Y mm) = empty ∨
          vs.foldl app (D.holeVal (Level.substFn φ lps us) ρp Y mm) = pt)) := by
  unfold LfpDatum.holeVal
  rcases holeFam_foldl_full (ρ := ρp) (Fs := D.ids mm (Level.substFn φ lps us)) (vs := vs)
      (fun vs => app (Y mm) (tupW (D.u mm (Level.substFn φ lps us)) vs)) hlen with h | h
  · exact Or.inl h
  · exact Or.inr h

omit hnd hul hds hdsa hlenP in
/-- A group member's index is in the group. -/
theorem grp_inGrp {p : Name × Expr} (hp : p ∈ grp) : InGrp D grp (D.names.idxOf p.1) := by
  obtain ⟨mm, hmm, hpm, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hg hp
  rw [hidx]
  exact ⟨hmm, by rw [List.contains_iff_mem, List.mem_map]; exact ⟨p, hp, hpm⟩⟩

/-- **The frame relation is an accessibility hole relation** of the
frame's walk (see the module docstring). -/
theorem frameRelA_holeRelA {prog : List NestHole} (hhi : ctx.hiAt prog.length = hi)
    {Δh : List Term} {R₀ : FrameRel V} (hR₀ : HoleRelA mp.base2 φ w ctx prog hi Δh R₀)
    (hin : RulesInputs V mp.base2 φ) (hΔ : Δh.length = hi)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ hi Δh x) (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hkf : ∀ ρ ρ', R₀ ρ ρ' → KeyFit D (Level.substFn φ lps us) dsa hi ρ ∧
      KeyFit D (Level.substFn φ lps us) dsa hi ρ')
    (hwD : ∀ ρ ρ', R₀ ρ ρ' → D.w (Level.substFn φ lps us) = w)
    (harity : ∀ p ∈ grp, ds.length + p.2.piBinders.1.length
      = (D.pars (D.names.idxOf p.1) (Level.substFn φ lps us)).length
        + (D.ids (D.names.idxOf p.1) (Level.substFn φ lps us)).length) :
    HoleRelA mp.base2 φ w ctx ((grpNews us ds hi grp).reverse ++ prog) (hi + grp.length)
      ((grpTys mp.base2 φ hi grp).reverse ++ Δh)
      (frameRelA R₀ D (Level.substFn φ lps us) grp dsa hi) := by
  subst hhi
  have hvl : ∀ ρp Y, (grpVals D (Level.substFn φ lps us) grp ρp Y).length = grp.length :=
    fun _ _ => grpVals_length _ _ _ _ _
  have hnl := grpNews_length us ds (ctx.hiAt prog.length) grp
  have hlen' : ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog).length
      = grp.length + prog.length := by
    rw [List.length_append, List.length_reverse, hnl]
  have hagree : ∀ ρ ρ', R₀ ρ ρ' →
      AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) ρ ρ' :=
    fun ρ ρ' hr => hR₀.agree ρ ρ' hr
  -- a position of the frame: a group hole, or the enclosing frame's
  have hposE : ∀ (ρ ρp Y : Nat → V) (i : Nat), grp.length ≤ i →
      consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ i = ρ (i - grp.length) := by
    intro ρ ρp Y i hi
    have := consList_apply_add (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ (i - grp.length)
    rw [hvl, show i - grp.length + grp.length = i by omega] at this
    exact this
  -- a group hole's position
  have hposG : ∀ (ρ ρp Y : Nat → V) (j : Nat) (hj : j < grp.length),
      consList (grpVals D (Level.substFn φ lps us) grp ρp Y) ρ (grp.length - 1 - j)
        = D.holeVal (Level.substFn φ lps us) ρp Y (D.names.idxOf (grp[j]).1) := by
    intro ρ ρp Y j hj
    rw [consList_getElem_pos (hvl ρp Y) hj]
    simp [grpVals]
  -- the new frames are the group's members at the key
  have hnewj : ∀ (j : Nat) (hk : NestHole), (grpNews us ds (ctx.hiAt prog.length) grp)[j]? = some hk →
      ∃ hj : j < grp.length, hk =
        NestHole.mk ⟨(grp[j]).1, us, ds⟩ (ctx.hiAt prog.length) (grp[j]).2.piBinders.1.length := by
    intro j hk h
    have hj : j < grp.length := by
      have := (List.getElem?_eq_some_iff.mp h).1; rwa [hnl] at this
    refine ⟨hj, ?_⟩
    simp only [grpNews, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
      Option.some.injEq] at h
    exact h.symm
  -- the members' index arities at the group
  have hmm_of : ∀ (j : Nat) (hj : j < grp.length), ∃ mm, mm < D.k ∧
      D.names.idxOf (grp[j]).1 = mm ∧
      (grp[j]).2.piBinders.1.length = (D.ids mm (Level.substFn φ lps us)).length := by
    intro j hj
    have hpi : grp[j] ∈ grp := List.getElem_mem _
    obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hg hpi
    refine ⟨mm, hmm, hidx, ?_⟩
    have h := harity _ hpi
    rw [hidx, parsLen_dsa mp hD hdsa hlenP hmm, ← DenoteSpine.length_eq hdsa] at h
    omega
  -- the admissible positions
  have hQiff := fun (i n : Nat) => holeQ_frame_iff (ctx := ctx) (prog := prog)
    (news := grpNews us ds (ctx.hiAt prog.length) grp) (i := i) (n := n)
  rw [hnl] at hQiff
  refine
    { dom := ?_, agree := ?_, dsScoped := ?_, symm := ?_, ptFree := ?_, lrefl := ?_,
      defRel := ?_, ptHit := ?_ }
  · -- the context
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
    obtain ⟨hk, hk'⟩ := hkf ρ ρ' hr
    exact ⟨sat_of_spineFit h1 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hin
        hΔ hCds hLds _ _ h1 hk hY),
      sat_of_spineFit h2 (grpVals_fit mp hD hnN hkN hfind hlps hnd hul hds hdsa hlenP hg hin
        hΔ hCds hLds _ _ h2 hk' hY')⟩
  · -- agreement off the holes
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, -, -, rfl, rfl⟩ i hi
    rw [hlen'] at hi
    by_cases hig : i < grp.length
    · exfalso; apply hi
      refine ⟨by omega, ?_, ?_⟩ <;> simp only [NestCtx.hiAt] <;> omega
    rw [hposE _ _ _ _ (by omega), hposE _ _ _ _ (by omega)]
    refine hR₀.agree ρ ρ' hr _ fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, by omega, ?_⟩
    simp only [NestCtx.hiAt] at h3 ⊢; omega
  · -- the keys' parameters are scoped
    intro i key hk x hx
    rw [hlen']
    rw [List.reverse_append, List.reverse_reverse] at hk
    refine Expr.WScoped.mono (show ctx.hiAt prog.length ≤ ctx.hiAt (grp.length + prog.length) by
      simp only [NestCtx.hiAt]; omega) ?_
    by_cases hi : i < prog.reverse.length
    · rw [List.getElem?_append_left hi] at hk
      exact hR₀.dsScoped i key hk x hx
    · rw [List.getElem?_append_right (by omega), List.length_reverse] at hk
      have hmem : x ∈ ds := by
        obtain ⟨_, hkey⟩ := hnewj _ key hk
        rw [hkey] at hx
        exact hx
      exact (hds x hmem).1
  · -- symmetric
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩
    exact ⟨ρ', ρ, Y', Y, hR₀.symm ρ ρ' hr, hY', hY, rfl, rfl⟩
  · -- point-free: a new hole's value at its full arity is a fibre of the
    -- tuple (a strict set) or `∅`; an enclosing hole is the enclosing
    -- relation's
    intro hw
    rintro _ _ ⟨ρ, ρ₀, Y, Y₀, hr, hY, hY₀, rfl, rfl⟩ i vs hQ hpt
    have hw' : D.w (Level.substFn φ lps us) ≠ 0 := by rw [hwD ρ ρ₀ hr]; exact hw
    rcases (hQiff i vs.length).mp hQ with ⟨j, hk, hjk, rfl, hn⟩ | ⟨hle, hQ'⟩
    · obtain ⟨hj, rfl⟩ := hnewj _ hk hjk
      obtain ⟨mm, hmm, hidx, har⟩ := hmm_of _ hj
      rw [hposG _ _ _ _ hj, hidx] at hpt
      have hlenv : vs.length = (D.ids mm (Level.substFn φ lps us)).length := by
        simp only at hn; omega
      rcases grp_hole_full (D := D) (lps := lps) (us := us) (φ := φ)
          (keyFrame dsa (ctx.hiAt prog.length) ρ) Y hlenv with ⟨hfv, he⟩ | he
      · rw [he] at hpt
        have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
        exact ((mem_strictU_pos hw').mp (famSpace_app (hY mm hmmN) (tupW_mem hfv))).2.2 hpt
      · rcases he.2 with he | he
        · rw [he] at hpt
          exact not_mem_empty _ hpt
        · rw [he] at hpt
          exact not_mem_self _ hpt
    · rw [hposE _ _ _ _ hle] at hpt
      exact hR₀.ptFree hw ρ ρ₀ hr (i - grp.length) vs hQ' hpt
  · -- left-reflexive
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, -, rfl, rfl⟩
    exact ⟨ρ, ρ, Y, Y, hR₀.lrefl ρ ρ' hr, hY, hY, rfl, rfl⟩
  · -- first-order finite-support definability at depth `ctx.hiAt prog.length + grp.length`
    let hi0 := ctx.hiAt prog.length
    let n := grp.length
    let d := hi0 + n
    let ψ := Level.substFn φ lps us
    refine ⟨?_, fun tail => ?_⟩
    · rintro _ _ ⟨ρ, ρ', Y, Y', hr, -, -, rfl, rfl⟩ j hj
      rw [hposE _ _ _ _ (by omega), hposE _ _ _ _ (by omega)]
      exact hR₀.defRel.1 ρ ρ' hr (j - n) (by omega)
    · let XsL : Fin hi0 → (Fin (d + d) → V) → V := fun i v => v ⟨n + i.val, by omega⟩
      let XsR : Fin hi0 → (Fin (d + d) → V) → V := fun i v => v ⟨d + n + i.val, by omega⟩
      let σL : Fin n → (Fin (d + d) → V) → V := fun i v => v ⟨i.val, by omega⟩
      let σR : Fin n → (Fin (d + d) → V) → V := fun i v => v ⟨d + i.val, by omega⟩
      have hXsL : ∀ i, DefFun (d + d) (XsL i) := fun _ => DefFun.proj _
      have hXsR : ∀ i, DefFun (d + d) (XsR i) := fun _ => DefFun.proj _
      have hσL : ∀ i, DefFun (d + d) (σL i) := fun _ => DefFun.proj _
      have hσR : ∀ i, DefFun (d + d) (σR i) := fun _ => DefFun.proj _
      let re : Fin (hi0 + hi0) → Fin (d + d) := fun i =>
        if hi' : i.val < hi0 then ⟨n + i.val, by omega⟩
        else ⟨d + n + (i.val - hi0), by omega⟩
      have hR_def : DefRel (d + d) fun v =>
          R₀ (Semantics.prepend (fun i => XsL i v) tail)
            (Semantics.prepend (fun i => XsR i v) tail) :=
        ((hR₀.defRel.2 tail).reIndex re).congr fun v => by
          have eL : ftake (fun i => v (re i)) = fun i => XsL i v := by
            funext ⟨i, hi'⟩; simp [ftake, re, hi', XsL]
          have eR : fdrop (fun i => v (re i)) = fun i => XsR i v := by
            funext ⟨i, hi'⟩
            have hge : ¬ (hi0 + i < hi0) := by omega
            simp [fdrop, re, hge, XsR]
          rw [eL, eR]
      have hSideL := defRel_holeFrameSide D ψ grp dsa tail rfl XsL hXsL σL hσL
      have hSideR := defRel_holeFrameSide D ψ grp dsa tail rfl XsR hXsR σR hσR
      refine (DefRel.and hR_def (DefRel.and hSideL hSideR)).congr fun v => ?_
      have h_eq : ∀ (ρ : Nat → V) (Y : Nat → V) (σ_slot : Fin n → V),
          (∀ j : Fin n, σ_slot ⟨n - 1 - j.val, by omega⟩ =
            D.holeVal ψ (keyFrame dsa hi0 ρ) Y (D.names.idxOf (grp[j.val]).1)) →
          ∀ (k : Nat) (hk : k < n), σ_slot ⟨k, hk⟩ = consList (grpVals D ψ grp (keyFrame dsa hi0 ρ) Y) ρ k := by
        intro ρ Y σ_slot h_slot k hk
        let j : Fin n := ⟨n - 1 - k, by omega⟩
        have hkj : n - 1 - j.val = k := by dsimp [j]; omega
        have hpos := hposG ρ (keyFrame dsa hi0 ρ) Y j.val j.isLt
        rw [hkj] at hpos
        dsimp only [ψ] at h_slot ⊢
        rw [hpos]
        simpa [hkj] using h_slot j
      have h_holeVal_pt : ∀ (ρp Y : Nat → V) (mm : Nat),
          D.holeVal ψ ρp Y mm = D.holeVal ψ ρp (fun _ => Y mm) mm := fun _ _ _ => rfl
      constructor
      · rintro ⟨hr0, hL, hR⟩
        let yL : Fin n → V := fun j => Classical.choose (hL j)
        let hyL : ∀ j : Fin n, yL j ∈ˢ famSpace (D.w ψ)
            (D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsL i v) tail))
              (D.names.idxOf grp[j.val].1)) := fun j => (Classical.choose_spec (hL j)).1
        let hσL_eq : ∀ j : Fin n, σL ⟨n - 1 - j.val, by omega⟩ v =
            D.holeVal ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsL i v) tail))
              (fun _ => yL j) (D.names.idxOf grp[j.val].1) := fun j => (Classical.choose_spec (hL j)).2
        let yR : Fin n → V := fun j => Classical.choose (hR j)
        let hyR : ∀ j : Fin n, yR j ∈ˢ famSpace (D.w ψ)
            (D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsR i v) tail))
              (D.names.idxOf grp[j.val].1)) := fun j => (Classical.choose_spec (hR j)).1
        let hσR_eq : ∀ j : Fin n, σR ⟨n - 1 - j.val, by omega⟩ v =
            D.holeVal ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsR i v) tail))
              (fun _ => yR j) (D.names.idxOf grp[j.val].1) := fun j => (Classical.choose_spec (hR j)).2
        let Y : Nat → V := fun m =>
          if h : ∃ j : Fin n, D.names.idxOf grp[j.val].1 = m
          then yL h.choose
          else AccIter.emptyTup (D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsL i v) tail))) m
        let Y' : Nat → V := fun m =>
          if h : ∃ j : Fin n, D.names.idxOf grp[j.val].1 = m
          then yR h.choose
          else AccIter.emptyTup (D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsR i v) tail))) m
        have hY : InTupleSpace (D.w ψ) D.N
            (D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsL i v) tail))) Y := by
          intro m hm
          dsimp only [Y]
          split
          · next hex =>
            have h_in := hyL hex.choose
            rwa [hex.choose_spec] at h_in
          · exact AccIter.emptyTup_mem (w := D.w ψ) (k := D.N)
              (Is := D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsL i v) tail))) m hm
        have hY' : InTupleSpace (D.w ψ) D.N
            (D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsR i v) tail))) Y' := by
          intro m hm
          dsimp only [Y']
          split
          · next hex =>
            have h_in := hyR hex.choose
            rwa [hex.choose_spec] at h_in
          · exact AccIter.emptyTup_mem (w := D.w ψ) (k := D.N)
              (Is := D.idx ψ (keyFrame dsa hi0 (Semantics.prepend (fun i => XsR i v) tail))) m hm
        have hYL_eq : ∀ j : Fin n, Y (D.names.idxOf grp[j.val].1) = yL j := fun j => by
          dsimp only [Y]
          have hex : ∃ j' : Fin n, D.names.idxOf grp[j'.val].1 = D.names.idxOf grp[j.val].1 := ⟨j, rfl⟩
          simp only [hex, ↓reduceDIte]
          have heq := grp_idxOf_inj hg.1 hg.2.1 hex.choose.isLt j.isLt hex.choose_spec
          have hfin : hex.choose = j := Fin.ext heq
          rw [hfin]
        have hYR_eq : ∀ j : Fin n, Y' (D.names.idxOf grp[j.val].1) = yR j := fun j => by
          dsimp only [Y']
          have hex : ∃ j' : Fin n, D.names.idxOf grp[j'.val].1 = D.names.idxOf grp[j.val].1 := ⟨j, rfl⟩
          simp only [hex, ↓reduceDIte]
          have heq := grp_idxOf_inj hg.1 hg.2.1 hex.choose.isLt j.isLt hex.choose_spec
          have hfin : hex.choose = j := Fin.ext heq
          rw [hfin]
        refine ⟨_, _, Y, Y', hr0, hY, hY', ?_, ?_⟩
        · funext k
          by_cases hk : k < n
          · have hkd : k < ctx.hiAt prog.length + grp.length := by change k < d; omega
            simp only [Semantics.prepend, hkd, ↓reduceDIte, ftake]
            exact h_eq _ Y (fun i => σL i v) (fun j => by
              rw [hσL_eq j, h_holeVal_pt _ Y, hYL_eq j]) k hk
          · rw [hposE _ _ _ _ (by omega)]
            by_cases hkd : k < ctx.hiAt prog.length + grp.length
            · have hkhi : k - grp.length < hi0 := by dsimp only [hi0, n] at *; omega
              simp only [Semantics.prepend, hkd, hkhi, ↓reduceDIte, ftake, XsL]
              congr 1; apply Fin.ext; dsimp only [n]; omega
            · have hkhi : ¬ (k - grp.length < hi0) := by dsimp only [hi0, n] at *; omega
              simp only [Semantics.prepend, hkd, hkhi, ↓reduceDIte]
              congr 1; dsimp only [hi0, n]; omega
        · funext k
          by_cases hk : k < n
          · have hkd : k < ctx.hiAt prog.length + grp.length := by change k < d; omega
            simp only [Semantics.prepend, hkd, ↓reduceDIte, fdrop]
            exact h_eq _ Y' (fun i => σR i v) (fun j => by
              rw [hσR_eq j, h_holeVal_pt _ Y', hYR_eq j]) k hk
          · rw [hposE _ _ _ _ (by omega)]
            by_cases hkd : k < ctx.hiAt prog.length + grp.length
            · have hkhi : k - grp.length < hi0 := by dsimp only [hi0, n] at *; omega
              simp only [Semantics.prepend, hkd, hkhi, ↓reduceDIte, fdrop, XsR]
              congr 1; apply Fin.ext; dsimp only [d, n]; omega
            · have hkhi : ¬ (k - grp.length < hi0) := by dsimp only [hi0, n] at *; omega
              simp only [Semantics.prepend, hkd, hkhi, ↓reduceDIte]
              congr 1; dsimp only [hi0, n]; omega
      · rintro ⟨ρ, ρ', Y, Y', hr0, hY, hY', h1, h2⟩
        have hρL : Semantics.prepend (fun i => XsL i v) tail = ρ := by
          funext m
          have hm := congrFun h1 (n + m)
          rw [hposE _ _ _ _ (by omega), show n + m - n = m by omega] at hm
          rw [← hm]
          by_cases hmi : m < hi0
          · have hmd : n + m < ctx.hiAt prog.length + grp.length := by dsimp only [hi0, n] at *; omega
            simp only [Semantics.prepend, hmi, hmd, ↓reduceDIte, ftake, XsL]
          · have hmd : ¬ (n + m < ctx.hiAt prog.length + grp.length) := by dsimp only [hi0, n] at *; omega
            simp only [Semantics.prepend, hmi, hmd, ↓reduceDIte]
            congr 1; dsimp only [hi0, n]; omega
        have hρR : Semantics.prepend (fun i => XsR i v) tail = ρ' := by
          funext m
          have hm := congrFun h2 (n + m)
          rw [hposE _ _ _ _ (by omega), show n + m - n = m by omega] at hm
          rw [← hm]
          by_cases hmi : m < hi0
          · have hmd : n + m < ctx.hiAt prog.length + grp.length := by dsimp only [hi0, n] at *; omega
            simp only [Semantics.prepend, hmi, hmd, ↓reduceDIte, fdrop, XsR]
            congr 1; apply Fin.ext; dsimp only [d, n]; omega
          · have hmd : ¬ (n + m < ctx.hiAt prog.length + grp.length) := by dsimp only [hi0, n] at *; omega
            simp only [Semantics.prepend, hmi, hmd, ↓reduceDIte]
            congr 1; dsimp only [hi0, n]; omega
        rw [hρL, hρR]
        refine ⟨hr0, fun j => ?_, fun j => ?_⟩
        · obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hg (List.getElem_mem j.isLt)
          have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
          refine ⟨Y (D.names.idxOf grp[j.val].1), ?_, ?_⟩
          · rw [hidx]; exact hY mm hmmN
          · have hpos := congrFun h1 (n - 1 - j.val)
            have hkd : n - 1 - j.val < ctx.hiAt prog.length + grp.length := by dsimp only [n]; omega
            simp only [Semantics.prepend, hkd, ↓reduceDIte, ftake] at hpos
            rw [hposG _ _ _ _ j.isLt] at hpos
            exact hpos.trans (h_holeVal_pt _ Y _)
        · obtain ⟨mm, hmm, -, hidx, -⟩ := grpMember mp hD hnN hkN hfind hlps hg (List.getElem_mem j.isLt)
          have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm (mp.lfp_ok D hD).1.kN
          refine ⟨Y' (D.names.idxOf grp[j.val].1), ?_, ?_⟩
          · rw [hidx]; exact hY' mm hmmN
          · have hpos := congrFun h2 (n - 1 - j.val)
            have hkd : n - 1 - j.val < ctx.hiAt prog.length + grp.length := by dsimp only [n]; omega
            simp only [Semantics.prepend, hkd, ↓reduceDIte, fdrop] at hpos
            rw [hposG _ _ _ _ j.isLt] at hpos
            exact hpos.trans (h_holeVal_pt _ Y' _)
  · -- `pt`-stability along admissible holes (`AccOn.holeApp`, B1/B2)
    rintro _ _ ⟨ρ, ρ', Y, Y', hr, hY, hY', rfl, rfl⟩ i vs hQ hnp
    rcases (hQiff i vs.length).mp hQ with ⟨j, hk, hjk, rfl, hn⟩ | ⟨hle, hQ'⟩
    · obtain ⟨hj, rfl⟩ := hnewj _ hk hjk
      obtain ⟨mm, hmm, hidx, har⟩ := hmm_of _ hj
      rw [hposG _ _ _ _ hj, hidx] at hnp ⊢
      have hlenv : vs.length = (D.ids mm (Level.substFn φ lps us)).length := by
        simp only at hn; omega
      have hptX : vs.foldl app (D.holeVal (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ) Y mm) = pt :=
        foldlApp_eq_pt_of_not_noPtPrefix hnp
      obtain ⟨h1, h2⟩ := hR₀.dom ρ ρ' hr
      obtain ⟨hk_f, hk'_f⟩ := hkf ρ ρ' hr
      have hpi : grp[j] ∈ grp := List.getElem_mem hj
      obtain ⟨mm', hmm', hpm', hidx', -, hte⟩ :=
        grp_n2 mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hpi
      have hmm_eq : mm' = mm := hidx'.symm.trans hidx
      subst hmm_eq
      have hG : InGrp D grp mm' := ⟨hmm', by
        rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hpi, hpm'⟩⟩
      have hmmN : mm' < D.N := Nat.lt_of_lt_of_le hmm' (mp.lfp_ok D hD).1.kN
      have hneY : ∀ ws, SpineFit (keyFrame dsa (ctx.hiAt prog.length) ρ)
          (D.ids mm' (Level.substFn φ lps us)) ws →
          app (Y mm') (tupW (D.u mm' (Level.substFn φ lps us)) ws) ≠ pt :=
        fun ws hws => (IsTy_of_mem_strictU (famSpace_app (hY mm' hmmN) (tupW_mem hws))).ne_pt
      have hidx_eq := grp_idx_eq mp hD hnN hkN hfind hlps hds hdsa hlenP hg hin hΔ hCds hLds hG
        (hR₀.agree ρ ρ' hr) h1 h2 hk_f hk'_f
      have hneY' : ∀ ws, SpineFit (keyFrame dsa (ctx.hiAt prog.length) ρ)
          (D.ids mm' (Level.substFn φ lps us)) ws →
          app (Y' mm') (tupW (D.u mm' (Level.substFn φ lps us)) ws) ≠ pt := by
        intro ws hws
        have hmem : tupW (D.u mm' (Level.substFn φ lps us)) ws ∈ˢ
            D.idx (Level.substFn φ lps us) (keyFrame dsa (ctx.hiAt prog.length) ρ) mm' :=
          tupW_mem hws
        rw [hidx_eq] at hmem
        exact (IsTy_of_mem_strictU (famSpace_app (hY' mm' hmmN) hmem)).ne_pt
      have hnfit : ¬ SpineFit (keyFrame dsa (ctx.hiAt prog.length) ρ)
          (D.ids mm' (Level.substFn φ lps us)) vs := by
        intro hfit
        unfold LfpDatum.holeVal at hptX
        rw [holeFam_app _ hfit] at hptX
        exact hneY vs hfit hptX
      unfold LfpDatum.holeVal at hptX ⊢
      rw [← holeFam_of_mkPisAV_eq (hg := DefHoleFn.of_app_tupW (Y' mm')
        (D.u mm' (Level.substFn φ lps us)) (D.ids mm' (Level.substFn φ lps us)).length)
        rfl (hte ρ ρ' (hR₀.agree ρ ρ' hr) h1 h2 hk_f hk'_f)]
      rw [holeFam_foldl_nofit (hg'_def := DefHoleFn.of_app_tupW (Y mm')
        (D.u mm' (Level.substFn φ lps us)) (D.ids mm' (Level.substFn φ lps us)).length)
        hneY' hneY hlenv hnfit, hptX]
      exact Subset.refl _
    · rw [hposE _ _ _ _ hle] at hnp ⊢
      exact hR₀.ptHit ρ ρ' hr (i - grp.length) vs hQ' hnp

end Frame

/-- **A frame hole's full arity is its member's telescope** (the premise
`harity` of `frameRelA_holeRelA`): the kernel's `nestArity` (the member's
stored type's binder count) is the recorded parameter and index count —
the recorded reading ends in a sort, so the type's syntactic tail is no
variable, and `nestInstType` saw a sort there (`instPis_count_of_read`'s
pieces). -/
theorem grp_arity (mp : EnvModelM V env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) (hnN : D.names.Nodup) (hkN : D.names.length = D.k) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {hi : Nat} {us : List Level} {ds : List Expr}
    {grp : List (Name × Expr)} (hg : GrpWf env ctx D hi us ds grp) (ψ : Name → Nat) :
    ∀ p ∈ grp, ds.length + p.2.piBinders.1.length
      = (D.pars (D.names.idxOf p.1) ψ).length + (D.ids (D.names.idxOf p.1) ψ).length := by
  intro p hp
  obtain ⟨-, mm, cv, caps, nI, ty, hmm, hpm, hfc, ⟨F, hrun⟩, hF, -⟩ := hg.2.2 p hp
  have hfC' : env.find? (D.member mm) = some (.indInfo cv caps) := by
    rw [← hfind, ← hpm]; exact hfc
  obtain ⟨-, -, -, hrd⟩ := familyRead mp hD hmm hfC' hrun
  obtain ⟨ab, u, hread, hl, -⟩ := hrd ψ
  obtain ⟨s, hs, -⟩ := hF.sort
  have hc := instPis_count_of_read hread cv.levelParams us hF.inst hs
  have hidx : D.names.idxOf p.1 = mm := by rw [hpm]; exact idxOf_member hnN hkN hmm
  simp only at hc
  rw [hc, hidx, ← List.length_append, hl]

end ConLeche.Model
