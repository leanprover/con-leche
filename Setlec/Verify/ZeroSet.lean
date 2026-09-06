import Setlec.Kernel.ZeroSet
import Setlec.Verify.PropWhen

/-!
# The canonical zero-ness datum: the law battery (task #161, P5 candidate)

`Setlec/Kernel/ZeroSet.lean` defines the canonical representation
(`ZeroSet`/`ZPropWhen`) of the binder annotation datum.  This file
proves, law for law, the battery the landed *free* representation has
(`Setlec/Verify/PropWhen.lean`) — against the **same** semantics
(`Level.eval`, `holds`) — plus the payoffs canonicity buys:

* **Extensionality is equality** — `ZeroSet.eq_of_mem_iff`: two
  `ZeroSet`s with the same members *are* the same value.
* **The comparison collapses** — `ZPropWhen.eq_iff_holds`: syntactic
  equality ↔ zero-ness agreement at every valuation.  The landed
  `PropWhen.equiv_iff_holds` becomes an iff with `Eq`, so the mirrored
  `ZPropWhen.equiv` is `==` (`equiv_iff_eq`).
* **`substPW_self` is the identity again** — `substPWZ_self`: the
  amendment-2 counterexample was normalization applied to
  non-canonical input; here inputs are canonical by construction.
* **The composition law keeps its hypothesis** — `substPWZ_comp` under
  `paramsDefined`: that hypothesis is representation-independent (it
  is the level side's own).

The mirrored inventory: `zeronessOfZ_sound` (≙ `zeronessOf_sound`),
`zeronessOfZ_subst` (≙ `zeronessOf_subst`), `substPWZ_self`,
`substPWZ_comp`, `equiv_iff_holds`, `holds_inter`, `inter_nil`,
`inter_never_right`, `bindZ_inter`, `bindZ_congr_names`, `bindZ_unit`,
`paramsDefined_inter_of`, `zeronessOfZ_paramsDefined`,
`substPWZ_paramsDefined`, `substPWZ_eq_self` (≙ the has-param
shortcut's `Level.substPW_eq_self`, `Kernel/ArenaWF.lean`),
`paramsDefined_of_not_hasParams`.

Not mirrored, deliberately: the *interned* twins (`substPWI`,
`zeronessOfLIGo`, `PWMemo`, `Verify/IExpr.lean`).  They belong to the
arena wiring, and this module touches no wiring.

The bridge `toFree`/`ofFree` transports facts both ways, so the
eventual representation swap can be staged: `ofFree_toFree`,
`holds_toFree`, `holds_ofFree`, `toFree_ofFree_equiv`,
`ofFree_eq_iff_equiv`, `eq_iff_equiv_toFree`, `ofFree_zeronessOf`,
`ofFree_substPW`.
-/

namespace Setlec.ZeroSet

/-! ## Membership -/

/-- Membership-equal lists agree on every `all` (the landed battery's
private helper, re-proved here to keep this module self-contained). -/
private theorem all_eq_of_mem_iff {ps qs : List Name}
    (h : ∀ n, n ∈ ps ↔ n ∈ qs) (f : Name → Bool) :
    ps.all f = qs.all f := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun hp n hn => hp n ((h n).mpr hn), fun hq n hn => hq n ((h n).mp hn)⟩

@[simp] theorem mem_iff {s : ZeroSet} {n : Name} :
    s.mem n = true ↔ n ∈ s.names := by
  simp [mem]

@[simp] theorem mem_names_empty {n : Name} : n ∈ empty.names ↔ False := by
  simp

@[simp] theorem mem_names_singleton {m n : Name} :
    n ∈ (singleton m).names ↔ n = m := by
  simp

theorem mem_names_union {a b : ZeroSet} {n : Name} :
    n ∈ (a.union b).names ↔ n ∈ a.names ∨ n ∈ b.names :=
  mem_mergeRaw _ _

@[simp] theorem mem_names_ofList {l : List Name} {n : Name} :
    n ∈ (ofList l).names ↔ n ∈ l := by
  induction l with
  | nil => simp [ofList]
  | cons m rest ih => simp [ofList_cons, ih]

theorem subset_iff {a b : ZeroSet} :
    a.subset b = true ↔ ∀ n, n ∈ a.names → n ∈ b.names := by
  simp [subset, List.all_eq_true]

/-! ## Canonicity: extensionality *is* equality -/

/-- Two strictly ascending lists with the same members are the same
list — the canonical-form theorem the whole module rests on. -/
theorem ascending_ext : ∀ {as bs : List Name}, ascending as = true →
    ascending bs = true → (∀ n, n ∈ as ↔ n ∈ bs) → as = bs
  | [], [], _, _, _ => rfl
  | [], b :: bs, _, _, h => by simpa using (h b).mpr (by simp)
  | a :: as, [], _, _, h => by simpa using (h a).mp (by simp)
  | a :: as, b :: bs, ha, hb, h => by
    rw [ascending_cons] at ha hb
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (by simp)) with hx | hx
      · exact hx
      rcases List.mem_cons.mp ((h b).mpr (by simp)) with hy | hy
      · exact hy.symm
      exact absurd (gtAll_iff.mp hb.1 a hx)
        (by simp [Name.blt_asymm (gtAll_iff.mp ha.1 b hy)])
    subst hab
    have htail : ∀ n, n ∈ as ↔ n ∈ bs := by
      intro n
      constructor
      · intro hn
        rcases List.mem_cons.mp ((h n).mp (by simp [hn])) with rfl | hn'
        · exact absurd rfl (Name.ne_of_blt (gtAll_iff.mp ha.1 n hn)).symm
        · exact hn'
      · intro hn
        rcases List.mem_cons.mp ((h n).mpr (by simp [hn])) with rfl | hn'
        · exact absurd rfl (Name.ne_of_blt (gtAll_iff.mp hb.1 n hn)).symm
        · exact hn'
    rw [ascending_ext ha.2 hb.2 htail]

/-- Extensionality as an **equality**: same members, same value. -/
theorem eq_of_mem_iff {a b : ZeroSet} (h : ∀ n, n ∈ a.names ↔ n ∈ b.names) :
    a = b :=
  eq_of_names (ascending_ext a.asc b.asc h)

theorem ext_iff {a b : ZeroSet} : a = b ↔ ∀ n, n ∈ a.names ↔ n ∈ b.names :=
  ⟨fun h _ => by rw [h], eq_of_mem_iff⟩

/-- Canonicalizing an already-canonical list is the identity. -/
@[simp] theorem ofList_names (s : ZeroSet) : ofList s.names = s :=
  eq_of_mem_iff fun _ => by simp

/-! ## Union algebra (equalities, by canonicity) -/

@[simp] theorem all_mergeRaw (P : Name → Bool) (as bs : List Name) :
    (mergeRaw as bs).all P = (as.all P && bs.all P) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, List.all_eq_true, mem_mergeRaw]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem all_union (P : Name → Bool) (a b : ZeroSet) :
    (a.union b).names.all P = (a.names.all P && b.names.all P) :=
  all_mergeRaw P _ _

@[simp] theorem union_empty (a : ZeroSet) : a.union empty = a :=
  eq_of_mem_iff fun _ => by simp

@[simp] theorem empty_union (a : ZeroSet) : empty.union a = a :=
  eq_of_mem_iff fun _ => by simp

theorem union_comm (a b : ZeroSet) : a.union b = b.union a :=
  eq_of_mem_iff fun _ => by simp [Or.comm]

theorem union_assoc (a b c : ZeroSet) :
    (a.union b).union c = a.union (b.union c) :=
  eq_of_mem_iff fun _ => by simp [or_assoc]

@[simp] theorem union_self (a : ZeroSet) : a.union a = a :=
  eq_of_mem_iff fun _ => by simp

theorem ofList_append (l₁ l₂ : List Name) :
    ofList (l₁ ++ l₂) = (ofList l₁).union (ofList l₂) :=
  eq_of_mem_iff fun _ => by simp

end Setlec.ZeroSet

namespace Setlec.ZPropWhen

open Setlec.ZeroSet

/-! ## `holds` characterizations -/

theorem holds_eq_holdsP (φ : Name → Nat) (p : ZPropWhen) :
    p.holds φ = p.holdsP (fun n => φ n == 0) := by
  cases p <;> rfl

/-- `holds` only reads the assignment at the datum's own parameters. -/
theorem holds_congr {φ₁ φ₂ : Name → Nat} : ∀ {p : ZPropWhen},
    (∀ n ∈ p.parameters, φ₁ n = φ₂ n) → p.holds φ₁ = p.holds φ₂
  | .never, _ => rfl
  | .ifAllZero s, h => by
    show s.names.all _ = s.names.all _
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true]
    exact ⟨fun hp n hn => (h n hn) ▸ hp n hn,
      fun hq n hn => (h n hn).symm ▸ hq n hn⟩

theorem holdsP_congr {P Q : Name → Bool} : ∀ {p : ZPropWhen},
    (∀ n ∈ p.parameters, P n = Q n) → p.holdsP P = p.holdsP Q
  | .never, _ => rfl
  | .ifAllZero s, h => by
    show s.names.all _ = s.names.all _
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true]
    exact ⟨fun hp n hn => (h n hn) ▸ hp n hn,
      fun hq n hn => (h n hn).symm ▸ hq n hn⟩

theorem holdsP_inter (P : Name → Bool) (p q : ZPropWhen) :
    (p.inter q).holdsP P = (p.holdsP P && q.holdsP P) := by
  cases p <;> cases q <;> simp [inter, holdsP]

/-- The `max` law: an intersection holds exactly where both do
(law (f) at the datum level; `holds_union` below is its set form). -/
theorem holds_inter (φ : Name → Nat) (p q : ZPropWhen) :
    (p.inter q).holds φ = (p.holds φ && q.holds φ) := by
  simp only [holds_eq_holdsP, holdsP_inter]

/-- Law (f) in set form: a union of parameter sets is zero exactly
where both sets are. -/
theorem holds_union (φ : Name → Nat) (a b : ZeroSet) :
    (ZPropWhen.ifAllZero (a.union b)).holds φ =
      ((ZPropWhen.ifAllZero a).holds φ && (ZPropWhen.ifAllZero b).holds φ) :=
  holds_inter φ (.ifAllZero a) (.ifAllZero b)

@[simp] theorem inter_never_right (p : ZPropWhen) : p.inter .never = .never := by
  cases p <;> rfl

@[simp] theorem inter_never_left (p : ZPropWhen) : ZPropWhen.never.inter p = .never :=
  rfl

@[simp] theorem inter_nil (p : ZPropWhen) : p.inter (.ifAllZero .empty) = p := by
  cases p <;> simp [inter]

theorem holdsP_bindZ_go (P : Name → Bool) (f : Name → ZPropWhen) :
    ∀ ps : List Name,
      (bindZ.go f ps).holdsP P = ps.all fun n => (f n).holdsP P
  | [] => by simp [bindZ.go, holdsP]
  | n :: rest => by
    simp [bindZ.go, holdsP_inter, holdsP_bindZ_go P f rest]

/-- The bind law: reading a substituted datum is reading the datum
against the substituted predicate. -/
theorem holdsP_bindZ (P : Name → Bool) (f : Name → ZPropWhen) :
    ∀ p : ZPropWhen,
      (p.bindZ f).holdsP P = p.holdsP fun n => (f n).holdsP P
  | .never => rfl
  | .ifAllZero s => holdsP_bindZ_go P f s.names

/-! ## Canonicity: equality decides zero-ness agreement -/

private theorem mem_of_holds_eq {s t : ZeroSet}
    (h : ∀ φ, holds φ (.ifAllZero s) = holds φ (.ifAllZero t)) :
    ∀ n, n ∈ s.names → n ∈ t.names := by
  intro n hin
  by_cases hout : n ∈ t.names
  · exact hout
  exfalso
  have hn := h fun m => if m = n then 1 else 0
  simp only [holds] at hn
  have hbs : (t.names.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = true :=
    List.all_eq_true.mpr fun m hm => by
      have hne : m ≠ n := fun he => hout (he ▸ hm)
      simp [hne]
  have has : (s.names.all fun m => (if m = n then (1 : Nat) else 0) == 0)
      = false :=
    List.all_eq_false.mpr ⟨n, hin, by simp⟩
  rw [has, hbs] at hn
  exact Bool.false_ne_true hn

/-- **The canonicity payoff (b)**: zero-ness agreement at every
valuation *is* equality of the data.  (The landed free-representation
statement is `PropWhen.equiv_iff_holds`, an iff with a containment
test; canonical data replace the test by `Eq`.) -/
theorem eq_iff_holds {p q : ZPropWhen} :
    p = q ↔ ∀ φ, p.holds φ = q.holds φ := by
  constructor
  · rintro rfl _; rfl
  · intro h
    cases p with
    | never => cases q with
      | never => rfl
      | ifAllZero t =>
        have := h fun _ => 0
        simp [holds] at this
    | ifAllZero s => cases q with
      | never =>
        have := h fun _ => 0
        simp [holds] at this
      | ifAllZero t =>
        have h1 := mem_of_holds_eq h
        have h2 := mem_of_holds_eq fun φ => (h φ).symm
        exact congrArg _ (eq_of_mem_iff fun n => ⟨h1 n, h2 n⟩)

theorem eq_of_holds {p q : ZPropWhen} (h : ∀ φ, p.holds φ = q.holds φ) :
    p = q := eq_iff_holds.mpr h

/-- The mirrored comparison is sound **and** complete — and it is
decidable equality, no containment test. -/
theorem equiv_iff_holds (p q : ZPropWhen) :
    equiv p q = true ↔ ∀ φ, p.holds φ = q.holds φ := by
  rw [equiv, beq_iff_eq, eq_iff_holds]

theorem equiv_iff_eq (p q : ZPropWhen) : equiv p q = true ↔ p = q := by
  simp [equiv]

/-! ## `bindZ` algebra -/

theorem bindZ_inter (g : Name → ZPropWhen) (p q : ZPropWhen) :
    (p.inter q).bindZ g = (p.bindZ g).inter (q.bindZ g) :=
  eq_of_holds fun φ => by
    simp only [holds_eq_holdsP, holdsP_bindZ, holdsP_inter]

theorem bindZ_congr_names {f g : Name → ZPropWhen} :
    ∀ {ps : List Name}, (∀ n ∈ ps, f n = g n) →
      bindZ.go f ps = bindZ.go g ps
  | [], _ => rfl
  | n :: rest, h => by
    show (f n).inter _ = (g n).inter _
    rw [h n (by simp), bindZ_congr_names fun m hm => h m (by simp [hm])]

theorem bindZ_congr {f g : Name → ZPropWhen} : ∀ {p : ZPropWhen},
    (∀ n ∈ p.parameters, f n = g n) → p.bindZ f = p.bindZ g
  | .never, _ => rfl
  | .ifAllZero _, h => bindZ_congr_names h

/-- `bindZ` at the unit (`n ↦ ifAllZero {n}`) reproduces the datum. -/
theorem bindZ_unit (pw : ZPropWhen) :
    pw.bindZ (fun n => .ifAllZero (.singleton n)) = pw :=
  eq_of_holds fun φ => by
    have hf : (fun n => (ZPropWhen.ifAllZero (ZeroSet.singleton n)).holdsP
        (fun m => φ m == 0)) = (fun n => φ n == 0) := by
      funext n; simp [holdsP]
    rw [holds_eq_holdsP, holdsP_bindZ, hf, ← holds_eq_holdsP]

/-! ## `paramsDefined` -/

theorem paramsDefined_iff {params : List Name} : ∀ {p : ZPropWhen},
    p.paramsDefined params = true ↔ ∀ n ∈ p.parameters, n ∈ params
  | .never => by simp [paramsDefined, parameters]
  | .ifAllZero s => by
    simp [paramsDefined, parameters, List.all_eq_true]

/-- Parameter-free data are defined under any parameter list (≙
`PropWhen.paramsDefined_of_not_hasParams`). -/
theorem paramsDefined_of_not_hasParams {params : List Name} {pw : ZPropWhen}
    (h : pw.hasParams = false) : pw.paramsDefined params = true := by
  cases pw with
  | never => rfl
  | ifAllZero s =>
    have hs : s.names = [] := by
      simpa [hasParams, ZeroSet.isEmpty, List.isEmpty_iff] using h
    simp [paramsDefined, hs]

theorem paramsDefined_inter_of {params : List Name} {p q : ZPropWhen}
    (hp : p.paramsDefined params = true)
    (hq : q.paramsDefined params = true) :
    (p.inter q).paramsDefined params = true := by
  rw [paramsDefined_iff] at hp hq ⊢
  intro n hn
  cases p with
  | never => simp [inter, parameters] at hn
  | ifAllZero a => cases q with
    | never => simp [inter, parameters] at hn
    | ifAllZero b =>
      rcases mem_names_union.mp hn with h | h
      · exact hp n h
      · exact hq n h

end Setlec.ZPropWhen

namespace Setlec.Level

open Setlec.ZPropWhen Setlec.ZeroSet

/-! ## Soundness of the canonical readout -/

private theorem beq_zero_and (x y : Nat) :
    ((x == 0) && (y == 0)) = (Max.max x y == 0) := by
  cases hx : x == 0 <;> cases hy : y == 0 <;> simp_all <;> omega

/-- The readout is exact: the datum holds at `φ` iff the level
evaluates to zero there (≙ `PropWhen.zeronessOf_sound`). -/
theorem zeronessOfZ_sound (φ : Name → Nat) :
    ∀ l : Level, (zeronessOfZ l).holds φ = (eval φ l == 0)
  | .zero => by simp [zeronessOfZ, ZPropWhen.holds, eval]
  | .succ l => by simp [zeronessOfZ, ZPropWhen.holds, eval]
  | .param n => by simp [zeronessOfZ, ZPropWhen.holds, eval]
  | .max a b => by
    rw [zeronessOfZ, holds_inter, zeronessOfZ_sound φ a,
      zeronessOfZ_sound φ b, beq_zero_and]
    rfl
  | .imax a b => by
    rw [zeronessOfZ, zeronessOfZ_sound φ b]
    show _ = ((if eval φ b = 0 then 0 else Max.max (eval φ a) (eval φ b)) == 0)
    by_cases hb : eval φ b = 0
    · simp [hb]
    · have hm : ¬ Max.max (eval φ a) (eval φ b) = 0 := by omega
      have h1 : (eval φ b == 0) = false := by simpa using hb
      have h2 : (Max.max (eval φ a) (eval φ b) == 0) = false := by simpa using hm
      rw [h1, if_neg hb, h2]

/-! ### The bit readouts (task #161 P3 mirrors)

`holds_substPWZ` below is the third of the P3 bit-readout trio (it
predates them here because canonicity made it this side's primitive);
these two mirror `PropWhen.holds_eq_of_equiv` and
`PropWhen.holds_of_equiv_zeronessOf`. -/

/-- Equivalent data read out equal bits at every valuation (≙
`PropWhen.holds_eq_of_equiv`; here `equiv` is `==`). -/
theorem _root_.Setlec.ZPropWhen.holds_eq_of_equiv {p q : ZPropWhen}
    (h : ZPropWhen.equiv p q = true) (φ : Name → Nat) :
    p.holds φ = q.holds φ :=
  (ZPropWhen.equiv_iff_holds p q).mp h φ

/-- **The establishment law** (≙ `PropWhen.holds_of_equiv_zeronessOf`):
a datum validated against a computed codomain sort reads out that
sort's zero bit at every ground valuation. -/
theorem holds_of_equiv_zeronessOfZ {v : Level} {pw : ZPropWhen}
    (h : ZPropWhen.equiv (zeronessOfZ v) pw = true) (φ : Name → Nat) :
    pw.holds φ = (eval φ v == 0) := by
  rw [← ZPropWhen.holds_eq_of_equiv h φ, zeronessOfZ_sound]

/-! ### The pushforward's defining equations -/

@[simp] theorem substPWZ_never (ks : List Name) (vs : List Level) :
    substPWZ ks vs .never = .never := rfl

theorem substPWZ_ifAllZero (ks : List Name) (vs : List Level) (s : ZeroSet) :
    substPWZ ks vs (.ifAllZero s) =
      ZPropWhen.bindZ.go (fun n => zeronessOfZ (subst.go ks vs n)) s.names :=
  rfl

/-- Parameter-free data are fixed by every substitution (≙
`Level.substPW_eq_self`, the datum half of the has-param shortcut's
soundness). -/
theorem substPWZ_eq_self {ks : List Name} {us : List Level}
    {pw : ZPropWhen} (h : pw.hasParams = false) : substPWZ ks us pw = pw := by
  cases pw with
  | never => rfl
  | ifAllZero s =>
    have hs : s.names = [] := by
      simpa [ZPropWhen.hasParams, ZeroSet.isEmpty, List.isEmpty_iff] using h
    have hse : s = ZeroSet.empty := ZeroSet.eq_of_names (by simp [hs])
    rw [hse]
    rfl

/-- Reading a pushed-forward datum is reading the datum at the
substituted assignment. -/
theorem holds_substPWZ (φ : Name → Nat) (ks : List Name) (vs : List Level)
    (pw : ZPropWhen) :
    (substPWZ ks vs pw).holds φ = pw.holds (substFn φ ks vs) := by
  rw [substPWZ, ZPropWhen.holds_eq_holdsP, holdsP_bindZ,
    ZPropWhen.holds_eq_holdsP]
  refine holdsP_congr fun n _ => ?_
  rw [← ZPropWhen.holds_eq_holdsP, zeronessOfZ_sound, eval_subst_go]

/-! ## The substitution laws -/

/-- The pushforward commutes with reading zero-ness (≙
`Level.zeronessOf_subst`; syntactic on both representations). -/
theorem zeronessOfZ_subst (ks : List Name) (vs : List Level) (l : Level) :
    zeronessOfZ (subst ks vs l) = substPWZ ks vs (zeronessOfZ l) :=
  ZPropWhen.eq_of_holds fun φ => by
    rw [zeronessOfZ_sound, holds_substPWZ, zeronessOfZ_sound, eval_subst]

/-- **The canonicity payoff (c)**: instantiating a datum at the
declaration's own parameters is the identity.  (For a *normalizing*
`substPW` on the free representation this is false — amendment 2's
counterexample, `Verify/InstLevels.lean`'s
`instantiateLevelParams_self` — because free data need not be
canonical.  Here they always are.) -/
theorem substPWZ_self (ks : List Name) (pw : ZPropWhen) :
    substPWZ ks (ks.map Level.param) pw = pw :=
  ZPropWhen.eq_of_holds fun φ => by
    rw [holds_substPWZ]
    exact ZPropWhen.holds_congr fun n _ => substFn_map_param

/-- **Law (d)**: composition of datum instantiations, under the same
parameter-definedness hypothesis the level side has (that hypothesis
is representation-independent — the landed `substPW_comp` needs it
too). -/
theorem substPWZ_comp {ks : List Name} {us : List Level}
    {ps : List Name} {vs : List Level} {pw : ZPropWhen}
    (hl : vs.length = ps.length)
    (hdef : pw.paramsDefined ps = true) :
    substPWZ ks us (substPWZ ps vs pw) =
      substPWZ ps (vs.map (Level.subst ks us)) pw :=
  ZPropWhen.eq_of_holds fun φ => by
    rw [holds_substPWZ, holds_substPWZ, holds_substPWZ]
    refine ZPropWhen.holds_congr fun n hn => ?_
    exact (substFn_map_subst hl (ZPropWhen.paramsDefined_iff.mp hdef n hn)).symm

/-! ## Parameter footprints -/

/-- The parameter footprint of a readout is the level's (≙
`Level.zeronessOf_paramsDefined`). -/
theorem zeronessOfZ_paramsDefined {ps' : List Name} :
    ∀ {l : Level}, l.allParamsDefined ps' = true →
      (zeronessOfZ l).paramsDefined ps' = true
  | .zero, _ => rfl
  | .succ _, _ => rfl
  | .param n, h => by
    simpa [zeronessOfZ, ZPropWhen.paramsDefined, allParamsDefined,
      ZeroSet.singleton] using h
  | .max a b, h => by
    rw [allParamsDefined, Bool.and_eq_true] at h
    exact ZPropWhen.paramsDefined_inter_of
      (zeronessOfZ_paramsDefined h.1) (zeronessOfZ_paramsDefined h.2)
  | .imax a b, h => by
    rw [allParamsDefined, Bool.and_eq_true] at h
    show (zeronessOfZ b).paramsDefined ps' = true
    exact zeronessOfZ_paramsDefined h.2

private theorem paramsDefined_bindZ_go {ps' : List Name}
    {f : Name → ZPropWhen} :
    ∀ {l : List Name}, (∀ n ∈ l, (f n).paramsDefined ps' = true) →
      (ZPropWhen.bindZ.go f l).paramsDefined ps' = true
  | [], _ => rfl
  | n :: rest, h =>
    ZPropWhen.paramsDefined_inter_of (h n (by simp))
      (paramsDefined_bindZ_go fun m hm => h m (by simp [hm]))

/-- The pushforward keeps datum parameters within the bound of the
substituted levels (≙ `Level.substPW_paramsDefined`). -/
theorem substPWZ_paramsDefined {ks : List Name} {us : List Level}
    {ps' : List Name} (hl : us.length = ks.length)
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {pw : ZPropWhen}, pw.paramsDefined ks = true →
      (substPWZ ks us pw).paramsDefined ps' = true := by
  intro pw h
  rw [ZPropWhen.paramsDefined_iff] at h
  cases pw with
  | never => rfl
  | ifAllZero s =>
    show (ZPropWhen.bindZ.go _ s.names).paramsDefined ps' = true
    refine paramsDefined_bindZ_go fun n hn => ?_
    exact zeronessOfZ_paramsDefined
      (hus _ (subst_go_mem (h n hn) hl))

end Setlec.Level

namespace Setlec.ZPropWhen

open Setlec.ZeroSet

/-! ## The bridge to the landed free representation -/

@[simp] theorem holds_toFree (φ : Name → Nat) : ∀ z : ZPropWhen,
    z.toFree.holds φ = z.holds φ
  | .never => rfl
  | .ifAllZero _ => by simp [toFree, holds]

@[simp] theorem paramsDefined_toFree (params : List Name) :
    ∀ z : ZPropWhen, z.toFree.paramsDefined params = z.paramsDefined params
  | .never => rfl
  | .ifAllZero _ => by simp [toFree, paramsDefined]

@[simp] theorem holds_ofFree (φ : Name → Nat) : ∀ p : PropWhen,
    (ofFree p).holds φ = p.holds φ := by
  intro p
  cases p with
  | never => rfl
  | ifAllZero ps =>
    rw [ofFree_ifAllZero, Setlec.PropWhen.holds_ifAllZero]
    show (ofList ps).names.all _ = ps.all _
    exact all_eq_of_mem_iff (fun _ => by simp) _

/-- `ofFree` is a retraction of `toFree`: canonicalizing a canonical
datum's free form gives it back. -/
@[simp] theorem ofFree_toFree : ∀ z : ZPropWhen, ofFree z.toFree = z
  | .never => rfl
  | .ifAllZero s => by simp [toFree, ofFree]

/-- The other composite is the identity up to the free side's own
comparison — which is all the free side can ask for. -/
theorem toFree_ofFree_equiv (p : PropWhen) :
    PropWhen.equiv (ofFree p).toFree p = true :=
  (Setlec.PropWhen.equiv_iff_holds _ _).mpr fun φ => by simp

/-- The comparison collapse, stated across the bridge: free-side
`equiv` is canonical-side `Eq`. -/
theorem ofFree_eq_iff_equiv (p q : PropWhen) :
    ofFree p = ofFree q ↔ PropWhen.equiv p q = true := by
  rw [eq_iff_holds, Setlec.PropWhen.equiv_iff_holds]
  simp

theorem eq_iff_equiv_toFree (a b : ZPropWhen) :
    a = b ↔ PropWhen.equiv a.toFree b.toFree = true := by
  rw [Setlec.PropWhen.equiv_iff_holds, eq_iff_holds]
  simp

/-- The readouts agree across the bridge. -/
theorem ofFree_zeronessOf (l : Level) :
    ofFree (Level.zeronessOf l) = Level.zeronessOfZ l :=
  eq_of_holds fun φ => by
    rw [holds_ofFree, Setlec.PropWhen.zeronessOf_sound,
      Level.zeronessOfZ_sound]

private theorem holds_substPW_free (φ : Name → Nat) (ks : List Name)
    (vs : List Level) : ∀ p : PropWhen,
    (Level.substPW ks vs p).holds φ = p.holds (Level.substFn φ ks vs) :=
  Setlec.Level.holds_substPW φ ks vs

/-- The pushforwards agree across the bridge — so the free-side
substitution battery transfers to the canonical side. -/
theorem ofFree_substPW (ks : List Name) (vs : List Level) (p : PropWhen) :
    ofFree (Level.substPW ks vs p) = Level.substPWZ ks vs (ofFree p) :=
  eq_of_holds fun φ => by
    rw [holds_ofFree, holds_substPW_free, Level.holds_substPWZ, holds_ofFree]

end Setlec.ZPropWhen
