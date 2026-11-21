module

public import ConLeche.IsModel

@[expose] public section

/-!
# `False` and `Eq` in a model of a stream

`IsModel` (`ConLeche/IsModel.lean`) fixes nothing by name.  A stream that declares the
prelude's `False` (`DeclaresFalse`) has `⟦False⟧ = ∅` in every model of it, and one that
declares the prelude's `Eq` (`DeclaresEq`) has `⟦@Eq A a b⟧ = eqv a b`: both follow from the
declarations' own clauses.

* `False.rec` is a member of what its type denotes at the motive `fun _ => ∅` (a family of
  types: `∅` is the false proposition), so `False.rec motive t ∈ ∅` for every `t ∈ ⟦False⟧`.
* `Eq.rec` at the motive `fun b _ => truthVal (a = b)` (into `Prop`) takes the canonical proof
  of `motive a (Eq.refl a) = truthVal (a = a)` to a member of `truthVal (a = b)` at every
  `t ∈ ⟦@Eq A a b⟧`; `Eq.refl a` inhabits `⟦@Eq A a a⟧`; and `Eq`'s own clause makes
  `⟦@Eq A a b⟧` a truth value.
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V] {model : Name → List Nat → V} {R : ConstantInfo → Prop}

/-- A record's membership clause, off `HasConstant`. -/
theorem IsModel.mem_of_hasRecord (h : IsModel V model R) {n : Name} {ps : List LevelParam}
    {T : Expr} (hr : HasConstant R n ps T) (vals : List Nat) (hl : vals.length = ps.length) :
    model n vals ∈ˢ Expr.eval model (Level.assign ps vals) ρ₀ T := by
  obtain ⟨c, hc, hcv⟩ := hr
  have hs := (h c hc vals (by rw [hcv]; exact hl)).1
  have hn : c.name = n := by
    show c.toConstantVal.name = n
    rw [hcv]
  rw [hn, hcv] at hs
  exact hs

/-- **`False` is empty** in every model of a stream declaring the prelude's `False`. -/
theorem IsModel.false_empty (h : IsModel V model R) (hF : DeclaresFalse R) :
    model falseName [] = empty := by
  obtain ⟨p, hr⟩ := hF
  have hm := h.mem_of_hasRecord hr [0] rfl
  simp only [falseRecType, Expr.eval, List.map_nil] at hm
  apply eq_empty
  intro x hx
  have hmot : lamV (model falseName []) (fun _ => (empty : V)) ∈ˢ
      piV (model falseName []) (fun _ => univ (Level.eval (Level.assign [p] [0]) (.param p))) := by
    refine lamV_mem (fun _ _ => empty_mem_univ _) (fun _ _ => IsTy_of_mem_univ (univ_mem_univ _))
  have h1 := app_mem_piV hm hmot
  have h2 := app_mem_piV h1 hx
  simp only [push] at h2
  rw [app_lamV hx] at h2
  exact not_mem_empty _ h2

/-- **`Eq` is equality** in every model of a stream declaring the prelude's `Eq`: at a type
`A` of the universe `k` and two of its members, `@Eq.{k} A a b` denotes `eqv a b`. -/
theorem IsModel.eq_eqv (h : IsModel V model R) (hE : DeclaresEq R) {k : Nat} {A a b : V}
    (hA : A ∈ˢ (univ k : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    app (app (app (model eqName [k]) A) a) b = eqv a b := by
  obtain ⟨⟨pE, hrE⟩, ⟨pR, hrR⟩, ⟨p₁, p, hne, hrC⟩⟩ := hE
  obtain ⟨E, hE'⟩ : ∃ E, model eqName [k] = E := ⟨_, rfl⟩
  rw [hE']
  -- `Eq`'s own clause: `@Eq A a b` is a truth value
  have hEm := h.mem_of_hasRecord hrE [k] rfl
  simp only [eqType, Expr.eval, push, Level.eval, Level.assign, ite_true] at hEm
  rw [hE'] at hEm
  have hT1 := app_mem_piV hEm hA
  have hT2 := app_mem_piV hT1 ha
  have hT : app (app (app E A) a) b ∈ˢ (univ 0 : V) := app_mem_piV hT2 hb
  -- `Eq.refl a` inhabits `@Eq A a a`
  have hRm := h.mem_of_hasRecord hrR [k] rfl
  simp only [eqReflType, eqApp, Expr.eval, push, List.map_cons, List.map_nil, Level.eval,
    Level.assign, ite_true] at hRm
  rw [hE'] at hRm
  have hrefl : ∀ a', a' ∈ˢ A →
      app (app (model eqReflName [k]) A) a' ∈ˢ app (app (app E A) a') a' :=
    fun a' ha' => by
      have hR1 := app_mem_piV hRm hA
      exact app_mem_piV (B := fun x => app (app (app E A) x) x) hR1 ha'
  -- `Eq.rec` at the motive `fun b _ => truthVal (a = b)`
  have hCm := h.mem_of_hasRecord hrC [0, k] rfl
  have hp : Level.assign [p₁, p] [0, k] p = k := by simp [Level.assign, hne]
  have hp₁ : Level.assign [p₁, p] [0, k] p₁ = 0 := by simp [Level.assign]
  simp only [eqRecType, eqApp, Expr.eval, push, List.map_cons, List.map_nil, Level.eval,
    hp, hp₁] at hCm
  rw [hE'] at hCm
  let mot : V := lamV A fun b' => lamV (app (app (app E A) a) b') fun _ => eqv a b'
  have hmot : mot ∈ˢ piV A (fun b' => piV (app (app (app E A) a) b') fun _ => univ 0) := by
    refine lamV_mem (fun b' hb' => ?_) (fun b' hb' => IsTy_piV)
    exact lamV_mem (fun _ _ => eqv_mem_univ a b') (fun _ _ => IsTy_of_mem_univ (univ_mem_univ 0))
  have hmin : (pt : V) ∈ˢ app (app mot a) (app (app (model eqReflName [k]) A) a) := by
    show pt ∈ˢ app (app (lamV A _) a) _
    rw [app_lamV ha, app_lamV (hrefl a ha)]
    exact pt_mem_eqv_self a
  have hC1 := app_mem_piV hCm hA
  have hC2 := app_mem_piV hC1 ha
  have hC3 := app_mem_piV hC2 hmot
  have hall := app_mem_piV hC3 hmin
  have heq : ∀ t, t ∈ˢ app (app (app E A) a) b → a = b := by
    intro t ht
    have h5 := app_mem_piV hall hb
    have h6 := app_mem_piV h5 ht
    show a = b
    have h6' : app (app (app (app (app (app (model (eqName.str "rec") [0, k]) A) a) mot) pt) b) t
        ∈ˢ app (app mot b) t := h6
    rw [show app (app mot b) t = eqv a b by
      show app (app (lamV A _) b) t = _
      rw [app_lamV hb, app_lamV ht]] at h6'
    exact eq_of_mem_eqv h6'
  apply ext
  intro z
  constructor
  · intro hz
    obtain rfl := heq z hz
    have hz' := mem_univZero.mp ((univ_zero (V := V)) ▸ hT) z hz
    rw [mem_unitSet_iff] at hz'
    rw [hz']
    exact pt_mem_eqv_self a
  · intro hz
    obtain rfl := eq_of_mem_eqv hz
    have hz' := mem_univZero.mp (eqv_mem_univZero a a) z hz
    rw [mem_unitSet_iff] at hz'
    have hr := hrefl a ha
    have hr' := mem_univZero.mp ((univ_zero (V := V)) ▸ hT) _ hr
    rw [mem_unitSet_iff] at hr'
    rw [hz', ← hr']
    exact hr

/-- **No model of a stream declaring the prelude's `False` has a theorem of type `False`**, at
any level parameters. -/
theorem IsModel.no_false_record (h : IsModel V model R) (hF : DeclaresFalse R) {t : Name}
    {ps : List LevelParam} (ht : HasConstant R t ps (.const falseName [])) : False := by
  have hm := h.mem_of_hasRecord ht (ps.map fun _ => 0) (by simp)
  have he : Expr.eval model (Level.assign ps (ps.map fun _ => 0)) ρ₀ (.const falseName []) =
      model falseName [] := rfl
  rw [he, h.false_empty hF] at hm
  exact not_mem_empty _ hm

end ConLeche
