module

public import ConLeche.Model.Modular.RestrictAgree
import ConLeche.Model.Harvest
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.PinRen

public section

/-!
# Every model gives a proof the canonical proof

The invariant behind agreement by proof irrelevance (`ConLeche.Modular.Agree.proof`,
`Agree.thm`): in every model of the modular instance, a stored theorem's type reads as a truth
value under the model (`SemPropType`), and a stored theorem's, definition's or axiom's whose type
reads so has the canonical proof `.prf` as its leaf, at every name (`ProofLeaves`).  It is a
property of the model, not of the checker: the step chooses those leaves (`DeclProofLeaf`) and
checks a theorem's type a proposition, and a context's model reads both off its sources'.
Because the condition is the type's reading, it carries between two models that read the type
alike (`SemPropType.of_denote`): that is how an importer's inference over a part of its context
reaches a source's model, and how a theorem's type reaches a copy of its statement.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Cached
open ConLeche.Term (Term)

universe w

variable {V : Type w} [SetTheory V]

variable (V) in
/-- **Every proof's leaf is the canonical proof** (see the module docstring). -/
@[expose] def ProofLeaves (E : Env) (a : Name → (Name → Nat) → Term) : Prop :=
  ∀ n ci, E.find? n = some ci → ci.isStmtKind = true →
    ((∃ cv, ci = .thmInfo cv) → SemPropType V a E ci.toConstantVal.type) ∧
    (SemPropType V a E ci.toConstantVal.type → a n = fun _ => .prf)

theorem ProofLeaves.empty (a : Name → (Name → Nat) → Term) : ProofLeaves V Env.empty a :=
  fun _ _ h => nomatch h

/-- **A theorem's leaf is the canonical proof.** -/
theorem ProofLeaves.thm {E : Env} {a : Name → (Name → Nat) → Term} (h : ProofLeaves V E a)
    {n : Name} {cv : ConstantVal} (hf : E.find? n = some (.thmInfo cv)) : a n = fun _ => .prf :=
  (h n _ hf rfl).2 ((h n _ hf rfl).1 ⟨cv, rfl⟩)

/-- **`Quot.sound`'s leaf is the canonical proof**, in every model storing it: its pin's. -/
theorem quotSound_leaf {E : Env} (mp : EnvModelM V E) {ci : ConstantInfo}
    (hf : E.find? quotSoundName = some ci) : mp.base2.acval quotSoundName = fun _ => .prf :=
  funext fun _ => mp.base2.acval_pinned_free hf (by decide)
    (fun _ => by simp (decide := true) [ConLeche.Verify.pinnedStructT])

/-- **A truth value read alike is a truth value.** -/
theorem SemPropType.of_denote {a₁ a₂ : Name → (Name → Nat) → Term} {E₁ E₂ : Env} {ty : Expr}
    (h : ∀ ψ, denote a₁ E₁ ψ 0 ty = denote a₂ E₂ ψ 0 ty) (hs : SemPropType V a₂ E₂ ty) :
    SemPropType V a₁ E₁ ty :=
  fun ψ Ta hT ρ => hs ψ Ta ((h ψ).symm.trans hT) ρ

/-- **`ProofLeaves` carries between two leaf assignments of one environment that read every
stored type alike and agree on its leaves.** -/
theorem ProofLeaves.of_alike {E : Env} {a a' : Name → (Name → Nat) → Term}
    (h : ProofLeaves V E a)
    (hden : ∀ n ci, E.find? n = some ci → ∀ ψ,
      denote a' E ψ 0 ci.toConstantVal.type = denote a E ψ 0 ci.toConstantVal.type)
    (hleaf : ∀ n, (E.find? n).isSome = true → a' n = a n) : ProofLeaves V E a' :=
  fun n ci hf hk => by
    obtain ⟨h1, h2⟩ := h n ci hf hk
    refine ⟨fun ht => SemPropType.of_denote (hden n ci hf) (h1 ht), fun hs => ?_⟩
    rw [hleaf n (by rw [hf]; rfl)]
    exact h2 (SemPropType.of_denote (fun ψ => (hden n ci hf ψ).symm) hs)

/-! ## Lookups in a filtered environment, resolution by names -/

theorem find?_filter_name {l : List ConstantInfo} {t : List ProjTable} {q : Name → Bool}
    {n : Name} :
    (⟨l.filter fun c => q c.toConstantVal.name, []⟩ : Env).find? n =
      if q n = true then (⟨l, t⟩ : Env).find? n else none := by
  induction l with
  | nil => split <;> rfl
  | cons c l ih =>
    have e1 : ∀ (cs : List ConstantInfo) (ts : List ProjTable),
        (⟨cs, ts⟩ : Env).find? n = cs.find? (·.name == n) := fun _ _ => rfl
    rw [e1] at ih ⊢
    rw [e1, List.filter_cons]
    by_cases hc : c.name = n
    · have hc' : c.toConstantVal.name = n := hc
      by_cases hq : q n = true
      · simp [hc', hq, hc]
      · have hqf : q c.toConstantVal.name = false := by rw [hc']; simpa using hq
        rw [ite_eq_right hq] at ih ⊢
        simpa [hqf] using ih
    · have hc' : (c.name == n) = false := by simpa using hc
      split <;> simp only [List.find?_cons, hc'] <;> exact ih

theorem find?_isSome_of_mem' {E : Env} {ci : ConstantInfo} (h : ci ∈ E.consts) :
    (E.find? ci.name).isSome = true := by
  unfold Env.find?; rw [List.find?_isSome]; exact ⟨ci, h, by simp⟩

/-- **A term resolves where its names are stored.** -/
theorem Expr.constsResolve_of_readNames {R : Env} :
    ∀ {e : Expr}, (∀ c ∈ e.readNames, (R.find? c).isSome = true) → e.constsResolve R = true := by
  intro e
  induction e with
  | lit l => cases l <;> intro h <;> simp_all [Expr.readNames, ConLeche.Expr.constsResolve]
  | _ => intro h; simp_all [Expr.readNames, ConLeche.Expr.constsResolve]

/-- **A term's names are stored where it resolves.** -/
theorem Expr.readNames_of_constsResolve {R : Env} :
    ∀ {e : Expr}, e.constsResolve R = true → ∀ c ∈ e.readNames, (R.find? c).isSome = true := by
  intro e
  induction e with
  | lit l => cases l <;> intro h c hc <;> simp_all [Expr.readNames, ConLeche.Expr.constsResolve] <;>
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  | _ => intro h c hc; simp_all [Expr.readNames, ConLeche.Expr.constsResolve] <;> grind

/-! ## A step from an environment -/

theorem pushChain_find_old {env : Env} {fe : FEnv} (h : PushChain env fe) {x : Name}
    (hx : (env.find? x).isSome = true) : fe.env.find? x = env.find? x := by
  obtain ⟨-, ⟨new, hc, -, hfr⟩, -, -⟩ := h
  unfold Env.find? at *
  rw [hc, List.find?_append]
  have : new.find? (·.name == x) = none := by
    rw [List.find?_eq_none]
    intro c hcm he
    have hcx : c.name = x := by simpa using he
    have := hfr c hcm
    rw [hcx] at this
    rw [this] at hx
    exact nomatch hx
  rw [this]; rfl

theorem pushChain_table_old {env : Env} {fe : FEnv} (h : PushChain env fe) {x : Name}
    (hx : (env.find? x).isSome = true) : fe.env.findTable? x = env.findTable? x := by
  have hf := pushChain_find_old h hx
  obtain ⟨-, -, -, ⟨newQ, hq, hfr⟩⟩ := h
  unfold Env.findTable?
  rw [hf]
  simp only [hx, ↓reduceIte]
  rw [hq, List.find?_append]
  have : newQ.find? (·.structName == x) = none := by
    rw [List.find?_eq_none]
    intro t ht he
    have htx : t.structName = x := by simpa using he
    have := hfr t ht
    rw [htx] at this
    rw [this] at hx
    exact nomatch hx
  rw [this]; rfl

/-- **A step reads the earlier names as before**: a term resolving in `env` reads the same at an
extension's carrier that keeps `env`'s leaves. -/
theorem pushChain_denote_old {env : Env} {fe : FEnv} (h : PushChain env fe)
    {a a' : Name → (Name → Nat) → Term} (hleaf : ∀ n, (env.find? n).isSome = true → a' n = a n)
    {e : Expr} (he : e.constsResolve env = true) (ψ : Name → Nat) :
    denote a' fe.env ψ 0 e = denote a env ψ 0 e :=
  denote_alike (R := env) (fun {x} hx => by
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨c, c, by rw [pushChain_find_old h hx, hc], hc, .inl rfl⟩)
    hleaf (fun hx => pushChain_table_old h hx) ψ 0 e he

theorem atLps_stmtKind (ci : ConstantInfo) (ps : List Name) :
    (ci.atLps ps).isStmtKind = ci.isStmtKind := by
  cases ci <;> rfl

/-- An inductive or quotient record installs no definition, theorem or axiom off the quotient's
`Quot.sound`. -/
theorem stmt_of_record {d : Declaration} {ci : ConstantInfo} (hci : ci ∈ declConstants d)
    (hk : ci.isStmtKind = true) (hq : ci.name ≠ quotSoundName) :
    (∃ cv v h, d = .defnDecl cv v h ∧ ci = .defnInfo cv v h) ∨
      (∃ cv v, d = .thmDecl cv v ∧ ci = .thmInfo cv) ∨
      (∃ cv v, d = .opaqueDecl cv v ∧ ci = .axiomInfo cv) ∨
      (∃ cv, d = .axiomDecl cv ∧ cv.name ≠ sorryAxName ∧ ci = .axiomInfo cv) := by
  cases d with
  | defnDecl cv v h => exact .inl ⟨cv, v, h, rfl, List.mem_singleton.mp hci⟩
  | thmDecl cv v => exact .inr (.inl ⟨cv, v, rfl, List.mem_singleton.mp hci⟩)
  | opaqueDecl cv v => exact .inr (.inr (.inl ⟨cv, v, rfl, List.mem_singleton.mp hci⟩))
  | axiomDecl cv =>
    simp only [declConstants] at hci
    by_cases hs : cv.name = quotSoundName
    · simp only [hs, ↓reduceIte, List.mem_singleton] at hci
      subst hci
      exact absurd (by rw [show (quotAt .sound cv).name = (quotPin .sound).name from
        atLps_name _ _]; rfl) hq
    · simp only [hs, ↓reduceIte] at hci
      by_cases hy : cv.name = sorryAxName
      · simp only [hy, ↓reduceIte] at hci; exact absurd hci List.not_mem_nil
      · simp only [hy, ↓reduceIte, List.mem_singleton] at hci
        exact .inr (.inr (.inr ⟨cv, rfl, hy, hci⟩))
  | quotDecl k cv =>
    simp only [declConstants, List.mem_singleton] at hci
    subst hci
    exfalso
    cases k <;> first
      | exact absurd (by rw [show (quotAt .sound cv).name = (quotPin .sound).name from
          atLps_name _ _]; rfl) hq
      | (unfold quotAt at hk; rw [atLps_stmtKind] at hk; revert hk; decide)
  | indDecl block nP =>
    exfalso
    simp only [declConstants] at hci
    split at hci
    · next p _ =>
      unfold blockConstants blockFormers blockCtors at hci
      simp only [List.mem_append, List.mem_map] at hci
      rcases hci with (⟨_, -, rfl⟩ | ⟨_, -, rfl⟩) | hr
      · exact nomatch hk
      · exact nomatch hk
      · have : ∀ rs, ∀ c ∈ blockRecs p rs, c.isStmtKind = false := by
          intro rs
          induction rs with
          | nil => exact fun _ h => nomatch h
          | cons r rs ih =>
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · rfl
            · exact ih c hc
        rw [this _ _ hr] at hk; exact nomatch hk
    · exact absurd hci List.not_mem_nil

/-- **A theorem a record installs is the theorem record's.** -/
theorem thm_of_record {d : Declaration} {cv : ConstantVal}
    (hci : ConstantInfo.thmInfo cv ∈ declConstants d) : ∃ v, d = .thmDecl cv v := by
  have hq : ∀ k cv', quotAt k cv' ≠ .thmInfo cv := fun k cv' h => by
    cases k <;> cases h
  cases d with
  | defnDecl _ _ _ => cases List.mem_singleton.mp hci
  | thmDecl cv' v => cases List.mem_singleton.mp hci; exact ⟨v, rfl⟩
  | opaqueDecl _ _ => cases List.mem_singleton.mp hci
  | axiomDecl cv' =>
    simp only [declConstants] at hci
    split at hci
    · exact absurd (List.mem_singleton.mp hci).symm (hq _ _)
    · split at hci
      · exact absurd hci List.not_mem_nil
      · cases List.mem_singleton.mp hci
  | quotDecl k cv' =>
    simp only [declConstants, List.mem_singleton] at hci
    exact absurd hci.symm (hq _ _)
  | indDecl block nP => exact nomatch stmtKind_of_ind hci

end ConLeche.Model.Modular
