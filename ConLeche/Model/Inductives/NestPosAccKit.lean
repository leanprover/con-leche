module

public import ConLeche.Model.Inductives.NestPosAcc
public import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Env.LfpAcc

public section

/-!
# Accessibility hole relations, truncated and extended

The counterparts of `HoleRel.drop`, `HoleRel.dropBase` and `HoleRel.extendEmpty`
(`ContFrame.lean`) for the accessibility hole relation `HoleRelA`:

* `HoleRelA.drop`: the relation seen at a depth at or above every hole
  (a container instance's key depth), the frames kept;
* `HoleRelA.dropBase`: the relation seen at the block's own depth, the
  frames forgotten (a cached instantiation's parameters lie below every
  frame hole);
* `HoleRelA.extendEmpty`: a frameless relation at the block's own depth
  extended by enclosing frames holding `∅` on both sides — their holes are
  blind (`∅` applied is `∅`) and never hold `pt`.

The admissible items move with the positions (`holeQ_shift`,
`holeQ_nil`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level NestCtx NestKey NestHole)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat} {w : Nat}

/-! ## The admissible items, moved -/

/-- The admissible items `k` positions further down. -/
theorem holeQ_shift {ctx : NestCtx} {prog : List NestHole} {d k i n : Nat}
    (h : HoleQ ctx prog d i n) : HoleQ ctx prog (d + k) (i + k) n := by
  rcases h with ⟨t, ht, hlt, rfl, hn⟩ | ⟨j, hk, hj, hlt, rfl, hn⟩
  · exact Or.inl ⟨t, ht, by omega, by omega, hn⟩
  · exact Or.inr ⟨j, hk, hj, by omega, by omega, hn⟩

/-- The member holes are admissible under any frames. -/
theorem holeQ_nil {ctx : NestCtx} {prog : List NestHole} {d i n : Nat}
    (h : HoleQ ctx [] d i n) : HoleQ ctx prog d i n := by
  rcases h with h | ⟨j, hk, hj, -⟩
  · exact Or.inl h
  · simp at hj

/-- An item of the frame `n` positions down is its item `n` positions up. -/
theorem holds_drop {ρ : Nat → V} {n : Nat} {o : Occ V} :
    Holds (fun i => ρ (i + n)) o ↔ Holds ρ (o.1 + n, o.2) := Iff.rfl

/-! ## Truncation -/

private theorem defRel_exists_fin {k : Nat} :
    ∀ (m : Nat) {R : (Fin (m + k) → V) → Prop},
      DefRel (m + k) R → DefRel k fun env => ∃ xs : Fin m → V, R (fappend xs env)
  | 0, R, hR =>
    ((hR.reIndex fun i => ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add k)⟩).congr fun env => by
      have heqv : (fun i : Fin (0 + k) => env ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.zero_add k)⟩) =
          fappend Fin.elim0 env := by
        funext ⟨i, hi⟩
        dsimp
        rw [fappend_ge Fin.elim0 env (Nat.zero_le _)]
        rfl
      rw [heqv]
      exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩)
  | m + 1, R, hR => by
    let re : Fin ((m + 1) + k) → Fin (m + (1 + k)) := fun i =>
      if h0 : i.val = 0 then ⟨m, by omega⟩
      else if hm : i.val < m + 1 then ⟨i.val - 1, by omega⟩
      else ⟨i.val, by omega⟩
    have hsub : DefRel (1 + k) fun v =>
        ∃ xs : Fin m → V, R (fun i => (fappend xs v) (re i)) :=
      defRel_exists_fin m (hR.reIndex re)
    let re2 : Fin (1 + k) → Fin (k + 1) := fun i => ⟨i.val, by omega⟩
    refine ((hsub.reIndex re2).exists_).congr fun env => ?_
    constructor
    · rintro ⟨x, xs, hx⟩
      refine ⟨fcons x xs, ?_⟩
      refine Eq.mp (congrArg R ?_) hx
      funext ⟨i, hi⟩
      by_cases h0 : i = 0
      · subst h0
        simp only [re, dite_true]
        rw [fappend_lt (fcons x xs) env (by dsimp; omega),
          fappend_ge xs (fun j => fcons x env (re2 j)) (by dsimp; omega)]
        have hz : re2 ⟨m - m, by omega⟩ = 0 := Fin.ext (Nat.sub_self m)
        rw [hz, fcons_zero]
        rfl
      · by_cases hm : i < m + 1
        · simp only [re, h0, hm, ↓reduceDIte]
          rw [fappend_lt (fcons x xs) env (by dsimp; omega),
            fappend_lt xs (fun j => fcons x env (re2 j)) (by dsimp; omega)]
          cases i with
          | zero => exact absurd rfl h0
          | succ i => rfl
        · simp only [re, h0, hm, ↓reduceDIte]
          rw [fappend_ge (fcons x xs) env (by dsimp; omega),
            fappend_ge xs (fun j => fcons x env (re2 j)) (by dsimp; omega)]
          have heq : re2 ⟨i - m, by omega⟩ = ⟨(i - (m + 1)) + 1, by omega⟩ := by
            apply Fin.ext; dsimp [re2]; omega
          rw [heq]; rfl
    · rintro ⟨xs, hxs⟩
      refine ⟨xs 0, fun i => xs i.succ, ?_⟩
      refine Eq.mp (congrArg R ?_) hxs
      funext ⟨i, hi⟩
      by_cases h0 : i = 0
      · subst h0
        simp only [re, dite_true]
        rw [fappend_lt xs env (by dsimp; omega),
          fappend_ge (fun i => xs i.succ) (fun j => fcons (xs 0) env (re2 j)) (by dsimp; omega)]
        have hz : re2 ⟨m - m, by omega⟩ = 0 := Fin.ext (Nat.sub_self m)
        rw [hz, fcons_zero]
        rfl
      · by_cases hm : i < m + 1
        · simp only [re, h0, hm, ↓reduceDIte]
          rw [fappend_lt xs env (by dsimp; omega),
            fappend_lt (fun i => xs i.succ) (fun j => fcons (xs 0) env (re2 j)) (by dsimp; omega)]
          cases i with
          | zero => exact absurd rfl h0
          | succ i => rfl
        · simp only [re, h0, hm, ↓reduceDIte]
          rw [fappend_ge xs env (by dsimp; omega),
            fappend_ge (fun i => xs i.succ) (fun j => fcons (xs 0) env (re2 j)) (by dsimp; omega)]
          have heq : re2 ⟨i - m, by omega⟩ = ⟨(i - (m + 1)) + 1, by omega⟩ := by
            apply Fin.ext; dsimp [re2]; omega
          rw [heq]; rfl

private theorem def_drop_add {m h : Nat} {R : FrameRel V} (hdef : R.Def (m + h)) :
    (R.drop m).Def h := by
  refine ⟨fun _ _ ⟨ρ, ρ', hr, h1, h2⟩ j hj => by
    subst h1 h2; exact hdef.1 ρ ρ' hr (j + m) (by omega), fun tail => ?_⟩
  let re : Fin ((m + h) + (m + h)) → Fin (m + (m + (h + h))) := fun i =>
    if hi : i.val < m then ⟨i.val, by omega⟩
    else if hid : i.val < m + h then ⟨m + m + (i.val - m), by omega⟩
    else if hi2 : i.val < (m + h) + m then ⟨m + (i.val - (m + h)), by omega⟩
    else ⟨m + m + h + (i.val - ((m + h) + m)), by omega⟩
  have hre : DefRel (m + (m + (h + h))) fun w =>
      R (Semantics.prepend (fun i : Fin (m + h) => w (re ⟨i.val, by omega⟩)) tail)
        (Semantics.prepend (fun i : Fin (m + h) => w (re ⟨(m + h) + i.val, by omega⟩)) tail) :=
    ((hdef.2 tail).reIndex re).congr fun w => by
      have eL : ftake (fun i => w (re i)) = fun i : Fin (m + h) => w (re ⟨i.val, by omega⟩) := by
        funext ⟨i, hi⟩; simp [ftake]
      have eR : fdrop (fun i => w (re i)) = fun i : Fin (m + h) => w (re ⟨(m + h) + i.val, by omega⟩) := by
        funext ⟨i, hi⟩; simp [fdrop]
      rw [eL, eR]
  refine (defRel_exists_fin m (defRel_exists_fin m hre)).congr fun v => ?_
  have hpL : ∀ xs ys : Fin m → V,
      Semantics.prepend (fun i : Fin (m + h) => (fappend ys (fappend xs v)) (re ⟨i.val, by omega⟩)) tail =
      fun k => if hk : k < m then ys ⟨k, hk⟩ else Semantics.prepend (ftake v) tail (k - m) := by
    intro xs ys
    funext k
    by_cases hk : k < m + h
    · simp only [Semantics.prepend, hk, ↓reduceDIte]
      by_cases hkm : k < m
      · simp only [re, hkm, ↓reduceDIte]
        rw [fappend_lt ys (fappend xs v) hkm]
      · simp only [re, hkm, hk, ↓reduceDIte]
        have hge : m ≤ m + m + (k - m) := by omega
        rw [fappend_ge ys (fappend xs v) hge]
        have heq : (⟨m + m + (k - m) - m, by omega⟩ : Fin (m + (h + h))) =
            ⟨m + (k - m), by omega⟩ := by apply Fin.ext; dsimp; omega
        rw [heq, fappend_ge xs v (by dsimp; omega)]
        have hkmh : k - m < h := by omega
        simp only [hkmh, ↓reduceDIte, ftake]
        congr 1; apply Fin.ext; dsimp; omega
    · have hkm : ¬ (k < m) := by omega
      have hge : ¬ (k - m < h) := by omega
      simp only [Semantics.prepend, hk, hkm, hge, ↓reduceDIte]
      congr 1; omega
  have hpR : ∀ xs ys : Fin m → V,
      Semantics.prepend (fun i : Fin (m + h) => (fappend ys (fappend xs v)) (re ⟨(m + h) + i.val, by omega⟩)) tail =
      fun k => if hk : k < m then xs ⟨k, hk⟩ else Semantics.prepend (fdrop v) tail (k - m) := by
    intro xs ys
    funext k
    by_cases hk : k < m + h
    · simp only [Semantics.prepend, hk, ↓reduceDIte]
      by_cases hkm : k < m
      · have hnotm : ¬ ((m + h) + k < m) := by omega
        have hnotd : ¬ ((m + h) + k < m + h) := by omega
        have hlt2 : (m + h) + k < (m + h) + m := by omega
        simp only [re, hnotm, hnotd, hlt2, ↓reduceDIte]
        rw [fappend_ge ys (fappend xs v) (by dsimp; omega)]
        have heq : (⟨m + ((m + h) + k - (m + h)) - m, by omega⟩ : Fin (m + (h + h))) =
            ⟨k, by omega⟩ := by apply Fin.ext; dsimp; omega
        rw [heq, fappend_lt xs v hkm]
        simp [hkm]
      · have hnotm : ¬ ((m + h) + k < m) := by omega
        have hnotd : ¬ ((m + h) + k < m + h) := by omega
        have hnot2 : ¬ ((m + h) + k < (m + h) + m) := by omega
        simp only [re, hnotm, hnotd, hnot2, ↓reduceDIte]
        rw [fappend_ge ys (fappend xs v) (by dsimp; omega)]
        have heq : (⟨m + m + h + ((m + h) + k - ((m + h) + m)) - m, by omega⟩ : Fin (m + (h + h))) =
            ⟨m + (h + (k - m)), by omega⟩ := by apply Fin.ext; dsimp; omega
        rw [heq, fappend_ge xs v (by dsimp; omega)]
        have hkmh : k - m < h := by omega
        simp only [hkm, hkmh, ↓reduceDIte, fdrop]
        congr 1; apply Fin.ext; dsimp; omega
    · have hkm : ¬ (k < m) := by omega
      have hge : ¬ (k - m < h) := by omega
      simp only [Semantics.prepend, hk, hkm, hge, ↓reduceDIte]
      congr 1; omega
  constructor
  · rintro ⟨xs, ys, hxy⟩
    rw [hpL xs ys, hpR xs ys] at hxy
    refine ⟨_, _, hxy, ?_, ?_⟩ <;>
    · funext i
      have hnot : ¬ (i + m < m) := by omega
      simp [hnot]
  · rintro ⟨ρ, ρ', hr, h1, h2⟩
    refine ⟨fun i => ρ' i.val, fun i => ρ i.val, ?_⟩
    rw [hpL, hpR]
    have e1 : (fun k => if hk : k < m then ρ k else Semantics.prepend (ftake v) tail (k - m)) = ρ := by
      funext k
      by_cases hk : k < m
      · simp [hk]
      · simp only [hk, ↓reduceDIte, h1]
        exact congrArg ρ (Nat.sub_add_cancel (Nat.le_of_not_lt hk))
    have e2 : (fun k => if hk : k < m then ρ' k else Semantics.prepend (fdrop v) tail (k - m)) = ρ' := by
      funext k
      by_cases hk : k < m
      · simp [hk]
      · simp only [hk, ↓reduceDIte, h2]
        exact congrArg ρ' (Nat.sub_add_cancel (Nat.le_of_not_lt hk))
    rw [e1, e2]
    exact hr

private theorem def_drop {d h : Nat} {R : FrameRel V} (hdef : R.Def d) (hle : h ≤ d) :
    (R.drop (d - h)).Def h := by
  have hmd : d - h + h = d := Nat.sub_add_cancel hle
  rw [← hmd] at hdef
  exact def_drop_add hdef

/-- **The accessibility hole relation, truncated** at a depth `h` at or
above every hole: the frame's walk sees the context below `h`. -/
theorem HoleRelA.drop {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List Term}
    {R : FrameRel V} (hR : HoleRelA m φ w ctx prog d Δa R) {h : Nat}
    (_hhi : ctx.hiAt prog.length ≤ h) (hle : h ≤ d) :
    HoleRelA m φ w ctx prog h (Δa.drop (d - h)) (R.drop (d - h)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop h1 _, Sat_drop h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - h)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  dsScoped := hR.dsScoped
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  ptFree hw := by
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ
    have hQ' : HoleQ ctx prog d (i + (d - h)) vs.length := by
      have := holeQ_shift (k := d - h) hQ
      rwa [show h + (d - h) = d by omega] at this
    exact hR.ptFree hw ρ ρ₀ hr (i + (d - h)) vs hQ'
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩
  defRel := def_drop hR.defRel hle
  ptHit := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i vs hQ hnp
    have hQ' : HoleQ ctx prog d (i + (d - h)) vs.length := by
      have := holeQ_shift (k := d - h) hQ
      rwa [show h + (d - h) = d by omega] at this
    exact hR.ptHit ρ ρ' hr (i + (d - h)) vs hQ' hnp

/-- **The accessibility hole relation seen at the block's own depth**, the
frames forgotten. -/
theorem HoleRelA.dropBase {ctx : NestCtx} {prog : List NestHole} {d : Nat} {Δa : List Term}
    {R : FrameRel V} (hR : HoleRelA m φ w ctx prog d Δa R) (hle : ctx.hiAt prog.length ≤ d) :
    HoleRelA m φ w ctx [] (ctx.hiAt 0) (Δa.drop (d - ctx.hiAt 0)) (R.drop (d - ctx.hiAt 0)) where
  dom := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨Sat_drop h1 _, Sat_drop h2 _⟩
  agree := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i hi
    refine hR.agree ρ ρ' hr (i + (d - ctx.hiAt 0)) fun hp => hi ?_
    simp only [holeP, NestCtx.hiAt, List.length_nil] at hp hle ⊢
    omega
  dsScoped := by
    intro i hk h
    simp at h
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  ptFree hw := by
    have hle0 : ctx.hiAt 0 ≤ d := by simp only [NestCtx.hiAt] at hle ⊢; omega
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ
    have hQ' : HoleQ ctx prog d (i + (d - ctx.hiAt 0)) vs.length := by
      have := holeQ_nil (prog := prog) (holeQ_shift (k := d - ctx.hiAt 0) hQ)
      rwa [show ctx.hiAt 0 + (d - ctx.hiAt 0) = d by omega] at this
    exact hR.ptFree hw ρ ρ₀ hr _ vs hQ'
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩
  defRel := def_drop hR.defRel (by simp only [NestCtx.hiAt] at hle ⊢; omega)
  ptHit := by
    have hle0 : ctx.hiAt 0 ≤ d := by simp only [NestCtx.hiAt] at hle ⊢; omega
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i vs hQ hnp
    have hQ' : HoleQ ctx prog d (i + (d - ctx.hiAt 0)) vs.length := by
      have := holeQ_nil (prog := prog) (holeQ_shift (k := d - ctx.hiAt 0) hQ)
      rwa [show ctx.hiAt 0 + (d - ctx.hiAt 0) = d by omega] at this
    exact hR.ptHit ρ ρ' hr _ vs hQ' hnp

/-! ## Empty enclosing frames -/

theorem consList_replicate_lt (n : Nat) (a : V) (σ : Nat → V) {i : Nat} (hi : i < n) :
    consList (List.replicate n a) σ i = a := by
  rw [consList_getD_of_lt _ _ _ (by simpa using hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, List.length_replicate]
  rw [ite_eq_left (by omega)]
  rfl

private theorem noPtPrefix_empty : ∀ (vs : List V), NoPtPrefix (empty : V) vs
  | [] => trivial
  | _ :: vs => ⟨pt_ne_empty.symm, by rw [app_empty]; exact noPtPrefix_empty vs⟩

private theorem def_extendEmpty (d0 n : Nat) {R00 : FrameRel V} (hdef : R00.Def d0) :
    FrameRel.Def (d0 + n) fun σ σ' : Nat → V => ∃ ρ ρ', R00 ρ ρ' ∧
      σ = consList (List.replicate n empty) ρ ∧
      σ' = consList (List.replicate n empty) ρ' := by
  refine ⟨?_, fun tail => ?_⟩
  · rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ j hj
    have ha := consList_apply_add (List.replicate n (empty : V))
    rw [List.length_replicate] at ha
    obtain ⟨m, rfl⟩ : ∃ m, j = m + n := ⟨j - n, by omega⟩
    rw [ha ρ m, ha ρ' m]
    exact hdef.1 ρ ρ' hr m (by omega)
  · have hemp : DefRel ((d0 + n) + (d0 + n)) fun v =>
        ∀ k : Fin n, v ⟨k.val, by omega⟩ = (empty : V) ∧ v ⟨(d0 + n) + k.val, by omega⟩ = empty :=
      DefRel.finForall fun k : Fin n =>
        DefRel.and (DefRel.eq_apply (DefFun.proj ⟨k.val, by omega⟩) DefFun.empty)
          (DefRel.eq_apply (DefFun.proj ⟨(d0 + n) + k.val, by omega⟩) DefFun.empty)
    let re : Fin (d0 + d0) → Fin ((d0 + n) + (d0 + n)) := fun i =>
      if hi : i.val < d0 then ⟨n + i.val, by omega⟩
      else ⟨(d0 + n) + n + (i.val - d0), by omega⟩
    have hR0 : DefRel ((d0 + n) + (d0 + n)) fun v =>
        R00 (Semantics.prepend (fun i : Fin d0 => v ⟨n + i.val, by omega⟩) tail)
          (Semantics.prepend (fun i : Fin d0 => v ⟨(d0 + n) + n + i.val, by omega⟩) tail) :=
      ((hdef.2 tail).reIndex re).congr fun v => by
        have eL : ftake (fun i => v (re i)) = fun i : Fin d0 => v ⟨n + i.val, by omega⟩ := by
          funext ⟨i, hi⟩; simp [ftake, re, hi]
        have eR : fdrop (fun i => v (re i)) =
            fun i : Fin d0 => v ⟨(d0 + n) + n + i.val, by omega⟩ := by
          funext ⟨i, hi⟩
          have hge : ¬ (d0 + i < d0) := by omega
          simp [fdrop, re, hge]
        rw [eL, eR]
    refine (DefRel.and hemp hR0).congr fun v => ?_
    have ha_eq : ∀ (ρ : Nat → V),
        consList (List.replicate n (empty : V)) ρ =
        fun k => if hk : k < n then empty else ρ (k - n) := by
      intro ρ; funext k
      by_cases hk : k < n
      · simp [hk, consList_replicate_lt]
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, by omega⟩
        have heq := consList_apply_add (List.replicate n (empty : V)) ρ m
        rw [List.length_replicate] at heq
        simp [hk, heq]
    constructor
    · rintro ⟨h_emp, hr⟩
      refine ⟨_, _, hr, ?_, ?_⟩
      · rw [ha_eq]
        funext k
        by_cases hk : k < n
        · have hk' : k < d0 + n := by omega
          simp only [hk, ↓reduceDIte, Semantics.prepend, hk', ftake]
          exact (h_emp ⟨k, hk⟩).1
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, by omega⟩
          simp only [hk, ↓reduceDIte, Nat.add_sub_cancel]
          by_cases hm : m < d0
          · have hmn : m + n < d0 + n := by omega
            simp only [Semantics.prepend, hm, hmn, ↓reduceDIte, ftake]
            congr 1; apply Fin.ext; dsimp; omega
          · have hmn : ¬ (m + n < d0 + n) := by omega
            simp only [Semantics.prepend, hm, hmn, ↓reduceDIte]
            congr 1; omega
      · rw [ha_eq]
        funext k
        by_cases hk : k < n
        · have hk' : k < d0 + n := by omega
          simp only [hk, ↓reduceDIte, Semantics.prepend, hk', fdrop]
          exact (h_emp ⟨k, hk⟩).2
        · obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, by omega⟩
          simp only [hk, ↓reduceDIte, Nat.add_sub_cancel]
          by_cases hm : m < d0
          · have hmn : m + n < d0 + n := by omega
            simp only [Semantics.prepend, hm, hmn, ↓reduceDIte, fdrop]
            congr 1; apply Fin.ext; dsimp; omega
          · have hmn : ¬ (m + n < d0 + n) := by omega
            simp only [Semantics.prepend, hm, hmn, ↓reduceDIte]
            congr 1; omega
    · rintro ⟨ρ, ρ', hr, h1, h2⟩
      refine ⟨fun ⟨k, hk⟩ => ?_, ?_⟩
      · have e1 := congrFun h1 k
        have e2 := congrFun h2 k
        have hk' : k < d0 + n := by omega
        simp only [Semantics.prepend, hk', ↓reduceDIte, ftake, fdrop, consList_replicate_lt n _ _ hk] at e1 e2
        exact ⟨e1, e2⟩
      · have hpL : Semantics.prepend (fun i : Fin d0 => v ⟨n + i.val, by omega⟩) tail = ρ := by
          funext m
          by_cases hm : m < d0
          · have hmn : n + m < d0 + n := by omega
            have em := congrFun h1 (n + m)
            simp only [Semantics.prepend, hmn, ↓reduceDIte, ftake] at em
            have ha := consList_apply_add (List.replicate n (empty : V)) ρ m
            rw [List.length_replicate, show m + n = n + m by omega] at ha
            rw [ha] at em
            simpa [Semantics.prepend, hm] using em
          · have hmn : ¬ (n + m < d0 + n) := by omega
            have em := congrFun h1 (n + m)
            simp only [Semantics.prepend, hmn, ↓reduceDIte] at em
            have ha := consList_apply_add (List.replicate n (empty : V)) ρ m
            rw [List.length_replicate, show m + n = n + m by omega] at ha
            rw [ha] at em
            simp only [Semantics.prepend, hm, ↓reduceDIte]
            rw [← em]
            congr 1; omega
        have hpR : Semantics.prepend (fun i : Fin d0 => v ⟨(d0 + n) + n + i.val, by omega⟩) tail = ρ' := by
          funext m
          by_cases hm : m < d0
          · have hmn : n + m < d0 + n := by omega
            have em := congrFun h2 (n + m)
            simp only [Semantics.prepend, hmn, ↓reduceDIte, fdrop] at em
            have ha := consList_apply_add (List.replicate n (empty : V)) ρ' m
            rw [List.length_replicate, show m + n = n + m by omega] at ha
            rw [ha] at em
            simpa [Semantics.prepend, hm, Nat.add_assoc] using em
          · have hmn : ¬ (n + m < d0 + n) := by omega
            have em := congrFun h2 (n + m)
            simp only [Semantics.prepend, hmn, ↓reduceDIte] at em
            have ha := consList_apply_add (List.replicate n (empty : V)) ρ' m
            rw [List.length_replicate, show m + n = n + m by omega] at ha
            rw [ha] at em
            simp only [Semantics.prepend, hm, ↓reduceDIte]
            rw [← em]
            congr 1; omega
        rw [hpL, hpR]
        exact hr

/-- **Empty enclosing frames**: a frameless relation at the block's own
depth, extended by the enclosing frames of `prog` holding `∅` on both
sides (a `Sort 0` entry each). -/
theorem HoleRelA.extendEmpty {ctx : NestCtx} {Δ0 : List Term} {R00 : FrameRel V}
    (hR : HoleRelA m φ w ctx [] (ctx.hiAt 0) Δ0 R00) (prog : List NestHole)
    (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x) :
    HoleRelA m φ w ctx prog (ctx.hiAt prog.length)
      (List.replicate prog.length (.sort 0) ++ Δ0)
      (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧ σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') where
  dom := extendEmpty_dom _ hR.dom
  agree := extendEmpty_agree _ hR.agree
  dsScoped := hsc
  symm := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ', ρ, hR.symm ρ ρ' hr, rfl, rfl⟩
  ptFree hw := by
    rintro _ _ ⟨ρ, ρ₀, hr, rfl, rfl⟩ i vs hQ hpt
    -- an enclosing frame's hole holds nothing
    by_cases hip : i < prog.length
    · rw [consList_replicate_lt _ _ _ hip, foldlApp_empty] at hpt
      exact not_mem_empty _ hpt
    -- an admissible position beyond the enclosing frames is a member hole
    obtain ⟨j, rfl⟩ : ∃ j, i = j + prog.length := ⟨i - prog.length, by omega⟩
    have hQ0 : HoleQ ctx [] (ctx.hiAt 0) j vs.length := by
      rcases hQ with ⟨t, ht, hlt, hi, hn⟩ | ⟨jj, hk, hj, hlt, hi, hn⟩
      · refine Or.inl ⟨t, ht, ?_, ?_, hn⟩
        · simp only [NestCtx.hiAt] at hlt ⊢; omega
        · simp only [NestCtx.hiAt] at hi ⊢; omega
      · have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_reverse] at this
        simp only [NestCtx.hiAt] at hi; omega
    have ea := consList_apply_add (List.replicate prog.length (empty : V)) ρ j
    rw [List.length_replicate] at ea
    rw [ea] at hpt
    exact hR.ptFree hw ρ ρ₀ hr j vs hQ0 hpt
  lrefl := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    exact ⟨ρ, ρ, hR.lrefl ρ ρ' hr, rfl, rfl⟩
  defRel := by
    have hd : ctx.hiAt prog.length = ctx.hiAt 0 + prog.length := by
      simp only [NestCtx.hiAt]; omega
    rw [hd]
    exact def_extendEmpty (ctx.hiAt 0) prog.length hR.defRel
  ptHit := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ i vs hQ hnp
    by_cases hip : i < prog.length
    · rw [consList_replicate_lt _ _ _ hip] at hnp
      exact absurd (noPtPrefix_empty vs) hnp
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + prog.length := ⟨i - prog.length, by omega⟩
      have hQ0 : HoleQ ctx [] (ctx.hiAt 0) j vs.length := by
        rcases hQ with ⟨t, ht, hlt, hi, hn⟩ | ⟨jj, hk, hj, hlt, hi, hn⟩
        · refine Or.inl ⟨t, ht, ?_, ?_, hn⟩
          · simp only [NestCtx.hiAt] at hlt ⊢; omega
          · simp only [NestCtx.hiAt] at hi ⊢; omega
        · have := (List.getElem?_eq_some_iff.mp hj).1
          simp only [List.length_reverse] at this
          simp only [NestCtx.hiAt] at hi; omega
      have ea := consList_apply_add (List.replicate prog.length (empty : V)) ρ j
      have ea' := consList_apply_add (List.replicate prog.length (empty : V)) ρ' j
      rw [List.length_replicate] at ea ea'
      rw [ea] at hnp
      rw [ea']
      exact hR.ptHit ρ ρ' hr j vs hQ0 hnp

end ConLeche.Model
