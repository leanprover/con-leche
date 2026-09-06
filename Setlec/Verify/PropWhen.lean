import Setlec.Verify.Level

/-!
# The zero-ness datum: soundness, completeness, substitution laws (task #161)

`PropWhen` is the binder annotation of the validated-annotation
design: the reading of a codomain sort's zero-ness predicate
`Z(l) = {φ | eval φ l = 0}`.  This file proves the design's
load-bearing facts:

* **Soundness of the readout** — `zeronessOf_sound`:
  `(zeronessOf l).holds φ = (eval φ l == 0)`.
* **Soundness and completeness of the comparison** —
  `equiv_iff_holds`: the containment test `PropWhen.equiv` decides
  zero-ness agreement at *every* valuation.  (The design's "checked,
  not proved" pivot made exact: the validation and defeq comparisons
  are complete, so the comparison itself contributes no
  incompleteness decline class.)
* **The substitution pushforward** — `zeronessOf_subst`:
  `zeronessOf (subst ks vs l) = substPW ks vs (zeronessOf l)`, a
  *syntactic* equation (the shape-preserving `bindZ` design).
* **The instantiation laws** — `substPW_self` (identity at a
  declaration's own parameters, unconditional) and `substPW_comp`
  (composition, under the same parameter-definedness hypothesis the
  level side has — `PropWhen.paramsDefined`, folded into
  `Expr.allLevelParamsDefined`).
-/

namespace Setlec.PropWhen

/-! ## `holds` characterizations -/

theorem holds_inter (φ : Name → Nat) (p q : PropWhen) :
    (p.inter q).holds φ = (p.holds φ && q.holds φ) := by
  cases p <;> cases q <;> simp [List.all_append]

theorem holds_bindZ_go (φ : Name → Nat) (f : Name → PropWhen) :
    ∀ ps : List Name,
      (bindZ.go f ps).holds φ = ps.all fun n => (f n).holds φ
  | [] => by rw [bindZ_go_nil, holds_ifAllZero]; rfl
  | n :: rest => by
    simp [bindZ.go, holds_inter, holds_bindZ_go φ f rest]

/-! ## Soundness of the readout -/

private theorem beq_zero_and (x y : Nat) :
    ((x == 0) && (y == 0)) = (Max.max x y == 0) := by
  cases hx : x == 0 <;> cases hy : y == 0 <;> simp_all <;> omega

theorem zeronessOf_sound (φ : Name → Nat) :
    ∀ l : Level, (Level.zeronessOf l).holds φ = (Level.eval φ l == 0)
  | .zero => by simp [Level.zeronessOf, Level.eval]
  | .succ l => by simp [Level.zeronessOf, Level.eval]
  | .param n => by simp [Level.zeronessOf, Level.eval]
  | .max a b => by
    rw [Level.zeronessOf, holds_inter, zeronessOf_sound φ a,
      zeronessOf_sound φ b, beq_zero_and]
    rfl
  | .imax a b => by
    rw [Level.zeronessOf, zeronessOf_sound φ b]
    show _ = ((if Level.eval φ b = 0 then 0
      else Max.max (Level.eval φ a) (Level.eval φ b)) == 0)
    by_cases hb : Level.eval φ b = 0
    · simp [hb]
    · have hm : ¬ Max.max (Level.eval φ a) (Level.eval φ b) = 0 := by
        omega
      have h1 : (Level.eval φ b == 0) = false := by simpa using hb
      have h2 : (Max.max (Level.eval φ a) (Level.eval φ b) == 0) = false :=
        by simpa using hm
      rw [h1, if_neg hb, h2]

/-! ## Completeness of the comparison -/

/-- Membership-equal lists agree on every `all`. -/
private theorem all_eq_of_mem_iff {ps qs : List Name}
    (h : ∀ n, n ∈ ps ↔ n ∈ qs) (f : Name → Bool) :
    ps.all f = qs.all f := by
  cases hq : qs.all f
  · cases hp : ps.all f
    · rfl
    · rw [List.all_eq_true] at hp
      rw [List.all_eq_false] at hq
      obtain ⟨n, hn, hf⟩ := hq
      exact absurd (hp n ((h n).mpr hn)) (by simp [hf])
  · rw [List.all_eq_true] at hq ⊢
    exact fun n hn => hq n ((h n).mp hn)

private theorem mem_of_holds_eq {ps qs : List Name}
    (h : ∀ φ, holds φ (.ifAllZero ps) = holds φ (.ifAllZero qs)) :
    ∀ n, n ∈ ps → n ∈ qs := by
  intro n hin
  by_cases hout : n ∈ qs
  · exact hout
  exfalso
  have hn := h fun m => if m = n then 1 else 0
  simp only [holds_ifAllZero] at hn
  have hbs : (qs.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = true :=
    List.all_eq_true.mpr fun m hm => by
      have hne : m ≠ n := fun he => hout (he ▸ hm)
      simp [hne]
  have has : (ps.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = false :=
    List.all_eq_false.mpr ⟨n, hin, by simp⟩
  rw [has, hbs] at hn
  exact Bool.false_ne_true hn

/-- The containment test decides zero-ness agreement at every
valuation: sound **and** complete.  The separating valuations: the
all-zero valuation separates `never` from every `ifAllZero`, and
`φ n := 1, else 0` separates parameter sets that disagree on `n`. -/
theorem equiv_iff_holds (p q : PropWhen) :
    equiv p q = true ↔ ∀ φ, p.holds φ = q.holds φ := by
  constructor
  · intro h φ
    cases p with
    | never => cases q with
      | never => rfl
      | ifAllZero qs => simp at h
    | ifAllZero ps => cases q with
      | never => simp at h
      | ifAllZero qs =>
        simp only [equiv_ifAllZero, Bool.and_eq_true, List.all_eq_true] at h
        obtain ⟨hpq, hqp⟩ := h
        rw [holds_ifAllZero, holds_ifAllZero]
        exact all_eq_of_mem_iff
          (fun n => ⟨fun hn => by
              simpa [List.contains_iff_mem] using hpq n hn,
            fun hn => by
              simpa [List.contains_iff_mem] using hqp n hn⟩) _
  · intro h
    cases p with
    | never => cases q with
      | never => rfl
      | ifAllZero qs =>
        have := h fun _ => 0
        simp at this
    | ifAllZero ps => cases q with
      | never =>
        have := h fun _ => 0
        simp at this
      | ifAllZero qs =>
        have h1 := mem_of_holds_eq h
        have h2 := mem_of_holds_eq fun φ => (h φ).symm
        rw [equiv_ifAllZero]
        rw [Bool.and_eq_true]
        exact ⟨List.all_eq_true.mpr fun n hn => by
            simpa [List.contains_iff_mem] using h1 n hn,
          List.all_eq_true.mpr fun n hn => by
            simpa [List.contains_iff_mem] using h2 n hn⟩

theorem paramsDefined_inter_of {params : List Name} {p q : PropWhen}
    (hp : p.paramsDefined params = true)
    (hq : q.paramsDefined params = true) :
    (p.inter q).paramsDefined params = true := by
  cases p <;> cases q <;>
    simp_all [List.all_append]

/-- `equiv` is reflexive (the fold's vacuous self-comparison steps). -/
theorem equiv_refl (p : PropWhen) : equiv p p = true :=
  (equiv_iff_holds p p).mpr fun _ => rfl

/-! ## The bit readouts (task #161 P3)

The P3 proofs consume validated annotations only through the *bit* a
datum reads out at a ground valuation.  These are the two named
readout laws: what a passed comparison says (`holds_eq_of_equiv`), and
what a passed validation site says (`holds_of_equiv_zeronessOf` — the
run inversions' `(zeronessOf v).equiv m.pw` conjunct, turned into the
sort's zero bit). -/

/-- Equivalent data read out equal bits at every valuation (the `mp`
direction of `equiv_iff_holds`, named for the P3 API). -/
theorem holds_eq_of_equiv {p q : PropWhen} (h : equiv p q = true)
    (φ : Name → Nat) : p.holds φ = q.holds φ :=
  (equiv_iff_holds p q).mp h φ

/-- **Parameter locality**: a datum reads its valuation only at its
own parameters (the `paramsDefined` footprint) — `denoteP`'s
φ-congruence walk (`denoteP_params_ext`) rides this at every binder.
(Mirror on the canonical side: `ZPropWhen.holds_congr`, via
`parameters`.) -/
theorem holds_ext {ps : List Name} {pw : PropWhen}
    (hdef : pw.paramsDefined ps = true) {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) : pw.holds φ₁ = pw.holds φ₂ := by
  cases pw with
  | never => rfl
  | ifAllZero qs =>
    simp only [paramsDefined_ifAllZero, List.all_eq_true] at hdef
    rw [holds_ifAllZero, holds_ifAllZero]
    induction qs with
    | nil => rfl
    | cons n rest ih =>
      simp only [List.all_cons]
      rw [hφ n (by simpa [List.contains_iff_mem] using hdef n (by simp)),
        ih fun m hm => hdef m (by simp [hm])]

/-- **The establishment law**: a datum the checker validated against a
computed codomain sort reads out that sort's zero bit, at every ground
valuation. -/
theorem holds_of_equiv_zeronessOf {v : Setlec.Level} {pw : PropWhen}
    (h : equiv (Setlec.Level.zeronessOf v) pw = true) (φ : Name → Nat) :
    pw.holds φ = (Setlec.Level.eval φ v == 0) := by
  rw [← holds_eq_of_equiv h φ, zeronessOf_sound]

/-! ## `bindZ` algebra -/

/-- `inter` is associative (the datum is a set union in list
clothing). -/
theorem inter_assoc (a b c : PropWhen) :
    (a.inter b).inter c = a.inter (b.inter c) := by
  cases a <;> cases b <;> cases c <;> simp [List.append_assoc]

/-- The `bindZ` fold over an append splits — the list-level half of
`bindZ_inter`. -/
theorem bindZ_go_append (g : Name → PropWhen) : ∀ ps qs : List Name,
    bindZ.go g (ps ++ qs) = (bindZ.go g ps).inter (bindZ.go g qs)
  | [], qs => (nil_inter (bindZ.go g qs)).symm
  | n :: rest, qs => by
    show (g n).inter (bindZ.go g (rest ++ qs))
      = ((g n).inter (bindZ.go g rest)).inter (bindZ.go g qs)
    rw [bindZ_go_append g rest qs, inter_assoc]

theorem bindZ_inter (g : Name → PropWhen) (p q : PropWhen) :
    (p.inter q).bindZ g = (p.bindZ g).inter (q.bindZ g) := by
  cases p with
  | never => rfl
  | ifAllZero ps =>
    cases q with
    | never => simp
    | ifAllZero qs => simp [bindZ_go_append]

theorem bindZ_congr_names {f g : Name → PropWhen} :
    ∀ {ps : List Name}, (∀ n ∈ ps, f n = g n) →
      bindZ.go f ps = bindZ.go g ps
  | [], _ => rfl
  | n :: rest, h => by
    show (f n).inter _ = (g n).inter _
    rw [h n (by simp), bindZ_congr_names fun m hm => h m (by simp [hm])]

/-- `bindZ` at the unit (`n ↦ ifAllZero [n]`) reproduces the datum —
shape and all. -/
theorem bindZ_unit : ∀ pw : PropWhen,
    pw.bindZ (fun n => .ifAllZero [n]) = pw := by
  intro pw
  cases pw with
  | never => rfl
  | ifAllZero ps => rw [bindZ_ifAllZero]; exact bindZ_unit.go ps
where
  go : ∀ ps : List Name,
      bindZ.go (fun n => PropWhen.ifAllZero [n]) ps = .ifAllZero ps
  | [] => rfl
  | n :: rest => by
    show (PropWhen.ifAllZero [n]).inter _ = _
    rw [go rest, inter_ifAllZero]
    rfl

end Setlec.PropWhen

namespace Setlec.Level

open Setlec.PropWhen

/-- The substitution pushforward, as a syntactic equation: reading
zero-ness commutes with level-parameter substitution. -/
theorem zeronessOf_subst (ks : List Name) (vs : List Level) :
    ∀ l : Level,
      zeronessOf (subst ks vs l) = substPW ks vs (zeronessOf l)
  | .zero => rfl
  | .succ l => rfl
  | .param n => rfl
  | .max a b => by
    show (zeronessOf (subst ks vs a)).inter (zeronessOf (subst ks vs b))
      = substPW ks vs ((zeronessOf a).inter (zeronessOf b))
    rw [zeronessOf_subst ks vs a, zeronessOf_subst ks vs b]
    exact (bindZ_inter _ _ _).symm
  | .imax a b => by
    show zeronessOf (subst ks vs b) = _
    exact zeronessOf_subst ks vs b

/-- `subst.go` at the identity substitution. -/
theorem subst_go_self (ks : List Name) (n : Name) :
    subst.go ks (ks.map Level.param) n = .param n := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    show (if k = n then Level.param k else subst.go ks (ks.map .param) n)
      = _
    by_cases h : k = n
    · simp [h]
    · simp [h, ih]

/-- Instantiating a datum at the declaration's own parameters is the
identity — unconditionally (no canonical-form side condition; the
`bindZ` design is shape-preserving). -/
theorem substPW_self (ks : List Name) (pw : PropWhen) :
    substPW ks (ks.map Level.param) pw = pw := by
  show pw.bindZ _ = pw
  have : pw.bindZ (fun n => zeronessOf (subst.go ks (ks.map .param) n))
      = pw.bindZ (fun n => .ifAllZero [n]) := by
    cases pw with
    | never => rfl
    | ifAllZero ps =>
      rw [bindZ_ifAllZero, bindZ_ifAllZero]
      exact bindZ_congr_names fun n _ => by rw [subst_go_self]; rfl
  rw [this, bindZ_unit]

/-- `subst.go` under a mapped replacement list: a parameter resolved
within the pairing factors through the outer substitution. -/
theorem subst_go_map (σ : Level → Level) :
    ∀ (ps : List Name) (vs : List Level) (n : Name),
      n ∈ ps → vs.length = ps.length →
      subst.go ps (vs.map σ) n = σ (subst.go ps vs n)
  | [], _, n, hn, _ => by simp at hn
  | p :: ps, [], n, _, hl => by simp at hl
  | p :: ps, v :: vs, n, hn, hl => by
    show (if p = n then σ v else subst.go ps (vs.map σ) n) = _
    by_cases h : p = n
    · simp [h, subst.go]
    · have hn' : n ∈ ps := by
        cases hn with
        | head => exact absurd rfl h
        | tail _ h' => exact h'
      have hl' : vs.length = ps.length := by simpa using hl
      simp only [h, if_false]
      rw [subst_go_map σ ps vs n hn' hl']
      show _ = σ (if p = n then v else subst.go ps vs n)
      simp [h]

/-- Composition of datum instantiations, under the same
parameter-definedness the level side's `subst_subst` has: parameters
of the datum are covered by the inner substitution. -/
theorem substPW_comp {ks : List Name} {us : List Level}
    {ps : List Name} {vs : List Level} {pw : PropWhen}
    (hl : vs.length = ps.length)
    (hdef : pw.paramsDefined ps = true) :
    substPW ks us (substPW ps vs pw) =
      substPW ps (vs.map (Level.subst ks us)) pw := by
  cases pw with
  | never => rfl
  | ifAllZero pws =>
    rw [show substPW ps vs (PropWhen.ifAllZero pws)
          = bindZ.go (fun n => zeronessOf (subst.go ps vs n)) pws from
        bindZ_ifAllZero _ _,
      show substPW ps (vs.map (Level.subst ks us)) (PropWhen.ifAllZero pws)
          = bindZ.go
              (fun n => zeronessOf (subst.go ps (vs.map (Level.subst ks us)) n))
              pws from bindZ_ifAllZero _ _]
    show (bindZ.go (fun n => zeronessOf (subst.go ps vs n)) pws).bindZ _
      = bindZ.go (fun n => zeronessOf (subst.go ps (vs.map _) n)) pws
    simp only [PropWhen.paramsDefined_ifAllZero, List.all_eq_true] at hdef
    induction pws with
    | nil => rfl
    | cons n rest ih =>
      show (PropWhen.inter _ _).bindZ _ = PropWhen.inter _ _
      rw [bindZ_inter]
      rw [ih fun m hm => hdef m (by simp [hm])]
      congr 1
      show substPW ks us (zeronessOf (subst.go ps vs n))
        = zeronessOf (subst.go ps (vs.map (subst ks us)) n)
      rw [← zeronessOf_subst ks us (subst.go ps vs n),
        subst_go_map (Level.subst ks us) ps vs n
          (by simpa [List.contains_iff_mem] using hdef n (by simp)) hl]

/-- The parameter footprint of a readout is the level's. -/
theorem zeronessOf_paramsDefined {ps' : List Name} :
    ∀ {l : Level}, l.allParamsDefined ps' = true →
      (zeronessOf l).paramsDefined ps' = true
  | .zero, _ => rfl
  | .succ _, _ => rfl
  | .param n, h => by
    simpa [zeronessOf, allParamsDefined] using h
  | .max a b, h => by
    rw [allParamsDefined, Bool.and_eq_true] at h
    exact PropWhen.paramsDefined_inter_of
      (zeronessOf_paramsDefined h.1) (zeronessOf_paramsDefined h.2)
  | .imax a b, h => by
    rw [allParamsDefined, Bool.and_eq_true] at h
    show (zeronessOf b).paramsDefined ps' = true
    exact zeronessOf_paramsDefined h.2

/-- A parameter resolved within the pairing lands in the replacement
list. -/
theorem subst_go_mem :
    ∀ {ks : List Name} {us : List Level} {n : Name},
      n ∈ ks → us.length = ks.length → subst.go ks us n ∈ us
  | [], _, n, hn, _ => by simp at hn
  | _ :: _, [], n, _, hl => by simp at hl
  | k :: ks, u :: us, n, hn, hl => by
    show (if k = n then u else subst.go ks us n) ∈ u :: us
    by_cases h : k = n
    · simp [h]
    · have hn' : n ∈ ks := by
        cases hn with
        | head => exact absurd rfl h
        | tail _ h' => exact h'
      simp only [h, if_false]
      exact List.mem_cons_of_mem u (subst_go_mem hn' (by simpa using hl))

/-- The pushforward keeps datum parameters within the bound of the
substituted levels — the datum half of
`Level.allParamsDefined_subst`. -/
theorem substPW_paramsDefined {ks : List Name} {us : List Level}
    {ps' : List Name} (hl : us.length = ks.length)
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {pw : PropWhen}, pw.paramsDefined ks = true →
      (substPW ks us pw).paramsDefined ps' = true := by
  intro pw h
  cases pw with
  | never => rfl
  | ifAllZero pws =>
    rw [show substPW ks us (PropWhen.ifAllZero pws)
          = bindZ.go (fun n => zeronessOf (subst.go ks us n)) pws from
        bindZ_ifAllZero _ _]
    simp only [PropWhen.paramsDefined_ifAllZero, List.all_eq_true] at h
    induction pws with
    | nil => rfl
    | cons n rest ih =>
      show (PropWhen.inter _ _).paramsDefined ps' = true
      exact PropWhen.paramsDefined_inter_of
        (zeronessOf_paramsDefined (hus _ (subst_go_mem
          (by simpa [List.contains_iff_mem] using h n (by simp)) hl)))
        (ih fun m hm => h m (by simp [hm]))

/-- **The pushforward's semantic reading** (task #161 P3): the
instantiated datum's bit at `φ` is the datum's bit at the composed
valuation `Level.substFn φ ks vs` — the same composed valuation
`denote2`'s constant clause uses.  The `denoteP` level crossing rides
this where the canonical lane needed the open checker metatheorems
(`SortOfEInstLevels`/`LamSortEInstLevels`,
`Setlec/SetR/Interp2/Step2/Levels.lean`). -/
theorem holds_substPW (φ : Name → Nat) (ks : List Name)
    (vs : List Level) : ∀ pw : PropWhen,
    (substPW ks vs pw).holds φ = pw.holds (substFn φ ks vs) := by
  intro pw
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    rw [show substPW ks vs (PropWhen.ifAllZero ps)
          = PropWhen.bindZ.go (fun n => zeronessOf (subst.go ks vs n)) ps from
        bindZ_ifAllZero _ _,
      holds_bindZ_go, PropWhen.holds_ifAllZero]
    induction ps with
    | nil => rfl
    | cons n rest ih =>
      simp only [List.all_cons, ih]
      rw [zeronessOf_sound, eval_subst_go]

end Setlec.Level
