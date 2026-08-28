import Setlec.SetR.Sound.Motives

/-!
# Soundness — the iota rule (task #148, T4, batch g)

R11, the wide rule: the equality is the fired contract
(`EnvSHyp.rec_rules` — the `iota_sound` + `certs_fit` +
`nested_fire_premise` + `defEqList_values` re-hang), consumed at the
spine with the major rewritten to its rescued constructor form; the
transport is the contract's truthfulness conclusion at the spine's
decomposed truthfulness.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- The head and every argument of a truthful spine are truthful. -/
theorem AnnotOkV_mkAppN_parts {ρ : Nat → V} :
    ∀ {as : List VExpr} {f : VExpr},
      AnnotOkV V ρ (VExpr.mkAppN f as) →
      AnnotOkV V ρ f ∧ ∀ a ∈ as, AnnotOkV V ρ a := by
  intro as
  induction as with
  | nil =>
    intro f h
    exact ⟨h, by simp⟩
  | cons a as ih =>
    intro f h
    rw [VExpr.mkAppN_cons] at h
    obtain ⟨hfa, hrest⟩ := ih h
    rw [AnnotOkV_app] at hfa
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hfa.2.1
    · exact hrest b hb'

/-- Every argument of a truthful spine is truthful. -/
theorem AnnotOkV_mkAppN_args {ρ : Nat → V} {as : List VExpr} {f : VExpr}
    (h : AnnotOkV V ρ (VExpr.mkAppN f as)) : ∀ a ∈ as, AnnotOkV V ρ a :=
  (AnnotOkV_mkAppN_parts h).2

/-- Pointwise reading of a map equality at `getD` slots. -/
theorem map_interp_getD_eq {ρ : Nat → V} {as bs : List VExpr}
    (h : as.map (interp V ρ) = bs.map (interp V ρ))
    {i : Nat} (hi : i < as.length) :
    interp V ρ (as.getD i default) = interp V ρ (bs.getD i default) := by
  have hlen : as.length = bs.length := by
    have := congrArg List.length h
    simpa using this
  have h1 : (as.map (interp V ρ))[i]? = (bs.map (interp V ρ))[i]? := by
    rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)]
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hlen ▸ hi)]
    at h1
  simpa using h1

/-- `getD` through `take`, below the cut. -/
theorem getD_take {as : List VExpr} {k i : Nat} (hi : i < k) :
    (as.take k).getD i default = as.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hi]

/-- `getD` through `drop`. -/
theorem getD_drop (as : List VExpr) (k i : Nat) :
    (as.drop k).getD i default = as.getD (k + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- A list of length `k + 1` splits as its prefix plus its last
element. -/
theorem take_getD_split {as : List VExpr} {k : Nat}
    (h : as.length = k + 1) :
    as = as.take k ++ [as.getD k default] := by
  have hlen : (as.drop k).length = 1 := by
    rw [List.length_drop, h]
    omega
  obtain ⟨a, ha⟩ : ∃ a, as.drop k = [a] := by
    match hd : as.drop k with
    | [a] => exact ⟨a, rfl⟩
    | [] => rw [hd] at hlen; simp at hlen
    | a :: b :: t => rw [hd] at hlen; simp at hlen
  have hget : a = as.getD k default := by
    have h0 : (as.drop k).getD 0 default = a := by rw [ha]; rfl
    rw [getD_drop, Nat.add_zero] at h0
    exact h0.symm
  calc as = as.take k ++ as.drop k := (List.take_append_drop k as).symm
    _ = as.take k ++ [as.getD k default] := by rw [ha, hget]

/-- R11: the iota step. -/
theorem sndRedIota (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {n' : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {rl : RecRule} {cvj : ConstantVal}
    {cnP cnF : Nat} {us usj : List Level}
    {xs ys : List VExpr} {m₀ m TV TVj R restR restC H' : VExpr}
    {cargs : List VExpr}
    (h1 : env.find? n' = some (.recInfo cv mI rP rules))
    (h2 : rules.find? (fun r' => r'.ctor == rl.ctor) = some rl)
    (h3 : rl.fire ≠ .inert)
    (h4 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h5 : rP ≤ mI) (h6 : xs.length = mI + 1)
    (h7 : ys.length = rl.ctorParams + rl.nfields)
    (h8 : us.length = cv.levelParams.length)
    (h9 : usj.length = cvj.levelParams.length)
    (_ : (cv.type.stripPis (mI + 1)).isSome = true)
    (_ : (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome = true)
    (h12 : Level.isEquivList usj
      (recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1
      = some true)
    (h13 : denoteClosed cval env φ
      (cv.type.instantiateLevelParams cv.levelParams us) = some TV)
    (_ : VExpr.Closed TV)
    (h14 : denoteClosed cval env φ
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVj)
    (_ : VExpr.Closed TVj)
    (h15 : denoteClosed cval env φ
      (rl.rhs.instantiateLevelParams cv.levelParams us) = some R)
    (_ : VExpr.Closed R)
    (h16 : m = VExpr.mkAppN
      (cval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys)
    (_ : Red μ env cval φ Δ (xs.getD mI default) m₀)
    (_ : Red μ env cval φ Δ m₀ m)
    (_ : rl.fire = .plain →
      DefEqL μ env cval φ Δ (ys.take rl.ctorParams)
        (xs.take rl.ctorParams))
    (_ : ∀ lvls pins, rl.fire = .nested lvls pins →
      ∀ i, i < rl.ctorParams → ∀ vp : VExpr,
        denote cval env φ rP
          (openRev 0 rP ((pins.getD i default).instantiateLevelParams
            cv.levelParams us)) = some vp →
        VExpr.bvarsBelow rP vp →
        DefEq μ env cval φ Δ (ys.getD i default)
          (VExpr.instRevChain (xs.take rP) vp))
    (_ : Tele μ env cval φ Δ TV (xs.take mI ++ [m]) restR)
    (_ : Tele μ env cval φ Δ TVj ys restC)
    (h23 : restC = VExpr.mkAppN H' cargs)
    (h24 : mI = rP ∨ cargs.length = rl.ctorParams + (mI - rP))
    (_ : DefEqL μ env cval φ Δ (cargs.drop rl.ctorParams)
      ((xs.take mI).drop rP))
    (ih17 : RedS V Δ (xs.getD mI default) m₀)
    (ih18 : RedS V Δ m₀ m)
    (ih19 : ∀ _ : rl.fire = .plain,
      DeqLS V Δ (ys.take rl.ctorParams) (xs.take rl.ctorParams))
    (ih20 : ∀ lvls pins (_ : rl.fire = .nested lvls pins)
      (i : Nat) (_ : i < rl.ctorParams) (vp : VExpr)
      (_ : denote cval env φ rP
        (openRev 0 rP ((pins.getD i default).instantiateLevelParams
          cv.levelParams us)) = some vp)
      (_ : VExpr.bvarsBelow rP vp),
      DeqS V Δ (ys.getD i default)
        (VExpr.instRevChain (xs.take rP) vp))
    (ih21 : TeleS V Δ TV (xs.take mI ++ [m]) restR)
    (ih22 : TeleS V Δ TVj ys restC)
    (ih25 : DeqLS V Δ (cargs.drop rl.ctorParams)
      ((xs.take mI).drop rP)) :
    RedS V Δ
      (VExpr.mkAppN (cval n' (Level.substFn φ cv.levelParams us)) xs)
      (VExpr.mkAppN R (xs.take rP ++ ys.drop rl.ctorParams)) := by
  intro ρ hΔ
  have hrl : rl ∈ rules := List.mem_of_find?_eq_some h2
  obtain ⟨-, hR⟩ := henv.rec_rules n' cv mI rP rules h1 rl hrl h3
  obtain ⟨R', hdR', hfired⟩ := hR us h8
  obtain rfl : R' = R := Option.some.inj (hdR'.symm.trans h15)
  have hxsm : (xs.take mI).length = mI := by
    rw [List.length_take]
    omega
  have htk : (xs.take mI).take rP = xs.take rP := by
    rw [List.take_take, Nat.min_eq_left h5]
  -- fits, from the telescope certificates
  obtain ⟨hfitR, hargsR, -⟩ := ih21 ρ hΔ
  obtain ⟨hfitC, hargsC, -⟩ := ih22 ρ hΔ
  -- the index pin
  have hpin : IotaIndexPinV V ρ restC rl.ctorParams mI rP
      (xs.take mI) := by
    refine ⟨H', cargs, h23, h24, fun i hi => ?_⟩
    have hlen : i < (cargs.drop rl.ctorParams).length := by
      rw [List.length_drop]
      rcases h24 with h | h
      · omega
      · omega
    have h := map_interp_getD_eq (ih25 ρ hΔ) hlen
    rw [getD_drop, getD_drop] at h
    exact h
  -- the fired contract
  have hcontract := hfired cvj cnP cnF h4 usj ρ (xs.take mI) ys TV TVj
    restR restC hxsm h7 h9
    (Level.substFn_congr (Level.isEquivList_sound h12 φ))
    (fun hfire i hi him => by
      have hlen : i < (ys.take rl.ctorParams).length := by
        rw [List.length_take]
        omega
      have h := map_interp_getD_eq (ih19 hfire ρ hΔ) hlen
      rw [getD_take hi, getD_take hi] at h
      rw [getD_take him]
      exact h)
    (fun lvls pins hfire i hi vp hden hbb => by
      have h := ih20 lvls pins hfire i hi vp hden hbb ρ hΔ
      rw [htk]
      exact h)
    hpin h13 h14 (h16 ▸ hfitR) hfitC
  obtain ⟨heq, hannot⟩ := hcontract
  rw [htk] at heq hannot
  -- the subject at the rescued spine
  have hmajor : interp V ρ (xs.getD mI default) = interp V ρ m :=
    (ih17 ρ hΔ).1.trans (ih18 ρ hΔ).1
  have hsubj : interp V ρ
      (VExpr.mkAppN (cval n' (Level.substFn φ cv.levelParams us)) xs)
      = interp V ρ
        (VExpr.mkAppN (cval n' (Level.substFn φ cv.levelParams us))
          (xs.take mI ++ [m])) := by
    have hxseq : VExpr.mkAppN
        (cval n' (Level.substFn φ cv.levelParams us)) xs
        = VExpr.mkAppN (cval n' (Level.substFn φ cv.levelParams us))
            (xs.take mI ++ [xs.getD mI default]) := by
      rw [← take_getD_split h6]
    rw [hxseq, interp_mkAppN_map, interp_mkAppN_map, List.map_append,
      List.map_append]
    simp only [List.map_cons, List.map_nil, hmajor]
  refine ⟨?_, ?_⟩
  · rw [hsubj, h16]
    exact heq
  · intro hs
    have hargs : ∀ a ∈ xs, AnnotOkV V ρ a := AnnotOkV_mkAppN_args hs
    exact hannot
      (fun a ha => hargs a (List.take_subset mI xs ha)) hargsC

end Cases

end Setlec.SetR
