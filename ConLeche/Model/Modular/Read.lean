module

public import ConLeche.Model.Fold
public import ConLeche.Modular
public import ConLeche.Verify.EnvBound

public section

/-!
# A context read from its sources

The interface between the two halves of the modular theorem's amalgamation, stated without
modules.  A module's context `C` is an environment each of whose constants is read from an
earlier module's own environment: for every name `n` it stores, its **source** environment `E n`
(the own environment of the module the name is read from), and the part `R n` of it the context
reads as that module does (stored in both, under one key: `ConLeche.Modular.readsAlike`).

`CtxRead C E R` is what the local checks give about that (`Modular/Valid.lean` derives it from
`LocalOk`): the context's copy of a name refines its source's (`Refines`: the same constant, or the
statement of a definition or theorem); what the copy's laws read lies in `R n` (`scope`, over a
predicate: `EntryScopedP`); a name read alike has alike copies in the context and the source
(`Alike`: the same constant, or two statements of one statement), with the same table; and an
inductive group arrives whole, so what a group member read alike reads is read alike too (`ctors`,
`deep`); a compiler-trust name is never presented as a statement (`reduce`).  `CtxModel`
(`Model/Modular/Restrict.lean`) builds the context's model from its sources' models, every law of
a context constant read off its source's law.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify

/-! ## Kinds and copies -/

/-- An inductive type former, constructor or recursor: the kinds a context never presents as a
statement. -/
@[expose] def _root_.ConLeche.ConstantInfo.isIndKind : ConstantInfo → Bool
  | .indInfo .. | .ctorInfo .. | .recInfo .. => true
  | _ => false

/-- A definition, theorem or axiom: the kinds whose copies may differ by a value. -/
@[expose] def _root_.ConLeche.ConstantInfo.isStmtKind : ConstantInfo → Bool
  | .defnInfo .. | .thmInfo .. | .axiomInfo .. => true
  | _ => false

/-- **A context copy refines its source's**: the same constant, or the statement (an axiom of
the same name, level parameters and type) of a definition or theorem. -/
@[expose] def Refines (ci ci' : ConstantInfo) : Prop :=
  ci = ci' ∨ (ci = .axiomInfo ci'.toConstantVal ∧ ci'.isStmtKind = true)

/-- **Two alike copies of one constant**: the same constant, or two statement kinds of one
statement. -/
@[expose] def Alike (ci ci' : ConstantInfo) : Prop :=
  ci = ci' ∨
    (ci.toConstantVal = ci'.toConstantVal ∧ ci.isStmtKind = true ∧ ci'.isStmtKind = true)

theorem Refines.alike {ci ci' : ConstantInfo} (h : Refines ci ci') : Alike ci ci' := by
  rcases h with h | ⟨rfl, h⟩
  · exact .inl h
  · exact .inr ⟨rfl, rfl, h⟩

theorem Alike.cv {ci ci' : ConstantInfo} (h : Alike ci ci') :
    ci.toConstantVal = ci'.toConstantVal := by
  rcases h with rfl | ⟨h, -, -⟩
  · rfl
  · exact h

theorem Alike.eq_of_indKind {ci ci' : ConstantInfo} (h : Alike ci ci') :
    ci.isIndKind = true ∨ ci'.isIndKind = true → ci = ci' := by
  rcases h with h | ⟨-, h1, h2⟩
  · exact fun _ => h
  · intro hk
    rcases hk with hk | hk
    · cases ci <;> simp_all [ConstantInfo.isIndKind, ConstantInfo.isStmtKind]
    · cases ci' <;> simp_all [ConstantInfo.isIndKind, ConstantInfo.isStmtKind]

theorem Alike.symm {ci ci' : ConstantInfo} (h : Alike ci ci') : Alike ci' ci := by
  rcases h with rfl | ⟨h, h1, h2⟩
  · exact .inl rfl
  · exact .inr ⟨h.symm, h2, h1⟩

/-! ## What a constant reads, over a predicate on names -/

/-- **Every name an expression reads satisfies `p`**: `constsResolve` with a predicate in place of
the lookup (a literal reads its support names, a projection its structure). -/
@[expose] def Expr.constsAll (p : Name → Prop) : Expr → Prop
  | .bvar _ | .sort _ => True
  | .lit (.natVal _) => p natName ∧ p natZeroName ∧ p natSuccName
  | .lit (.strVal _) =>
    p natName ∧ p natZeroName ∧ p natSuccName ∧ p stringName ∧ p stringOfListName ∧
      p listName ∧ p listNilName ∧ p listConsName ∧ p charName ∧ p charOfNatName
  | .const n _ => p n
  | .fvar _ ty => Expr.constsAll p ty
  | .app f a => Expr.constsAll p f ∧ Expr.constsAll p a
  | .lam ty body | .forallE ty body => Expr.constsAll p ty ∧ Expr.constsAll p body
  | .letE ty val body => Expr.constsAll p ty ∧ Expr.constsAll p val ∧ Expr.constsAll p body
  | .proj s _ e => p s ∧ Expr.constsAll p e

theorem Expr.constsAll_mono {p q : Name → Prop} (h : ∀ n, p n → q n) :
    ∀ {e : Expr}, Expr.constsAll p e → Expr.constsAll q e := by
  intro e
  induction e with
  | bvar _ => exact fun _ => trivial
  | sort _ => exact fun _ => trivial
  | const n _ => exact h n
  | lit l =>
    cases l with
    | natVal _ => exact fun ⟨a, b, c⟩ => ⟨h _ a, h _ b, h _ c⟩
    | strVal _ =>
      exact fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ =>
        ⟨h _ a1, h _ a2, h _ a3, h _ a4, h _ a5, h _ a6, h _ a7, h _ a8, h _ a9, h _ a10⟩
  | fvar _ _ ih => exact ih
  | app _ _ ihf iha => exact fun ⟨a, b⟩ => ⟨ihf a, iha b⟩
  | lam _ _ ih1 ih2 => exact fun ⟨a, b⟩ => ⟨ih1 a, ih2 b⟩
  | forallE _ _ ih1 ih2 => exact fun ⟨a, b⟩ => ⟨ih1 a, ih2 b⟩
  | letE _ _ _ ih1 ih2 ih3 => exact fun ⟨a, b, c⟩ => ⟨ih1 a, ih2 b, ih3 c⟩
  | proj _ _ _ ih => exact fun ⟨a, b⟩ => ⟨h _ a, ih b⟩

/-- `constsResolve` is `constsAll` at "stored". -/
theorem Expr.constsResolve_iff (R : Env) :
    ∀ {e : Expr}, e.constsResolve R = true ↔
      Expr.constsAll (fun n => (R.find? n).isSome = true) e := by
  intro e
  induction e with
  | bvar _ => simp [ConLeche.Expr.constsResolve, Expr.constsAll]
  | sort _ => simp [ConLeche.Expr.constsResolve, Expr.constsAll]
  | const n _ => simp [ConLeche.Expr.constsResolve, Expr.constsAll]
  | lit l =>
    cases l <;> simp [ConLeche.Expr.constsResolve, Expr.constsAll, and_assoc]
  | fvar _ _ ih => simp only [ConLeche.Expr.constsResolve, Expr.constsAll]; exact ih
  | app _ _ ihf iha =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ihf, iha]
  | lam _ _ ih1 ih2 =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ih1, ih2]
  | forallE _ _ ih1 ih2 =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ih1, ih2]
  | letE _ _ _ ih1 ih2 ih3 =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]
    rw [ih1, ih2, ih3, and_assoc]
  | proj _ _ _ ih =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ih]

/-- **`EntryScoped` over a predicate**, with the former's table (its constructor and bodies) in
`C`: what a constant's laws read satisfies `p`. -/
@[expose] def EntryScopedP (p : Name → Prop) (C : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  Expr.constsAll p ci.toConstantVal.type ∧
  (∀ cv v h, ci = .defnInfo cv v h → Expr.constsAll p v) ∧
  (∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
    Expr.constsAll p r.rhs ∧ p r.ctor ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ q ∈ pins, Expr.constsAll p q) ∧
  (∀ cv caps, ci = .indInfo cv caps →
    (∀ m ∈ caps.all, p m) ∧ (caps.eta = true → p caps.etaCtor) ∧
    ∀ t, C.findTable? n = some t → p t.ctor ∧ ∀ b ∈ t.bodies.toList, Expr.constsAll p b) ∧
  ∀ d ∈ pinFootprint n, p d

theorem EntryScopedP.mono {p q : Name → Prop} {C : Env} {n : Name} {ci : ConstantInfo}
    (h : EntryScopedP p C n ci) (hpq : ∀ d, p d → q d) : EntryScopedP q C n ci := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Expr.constsAll_mono hpq h1, fun cv v hh he => Expr.constsAll_mono hpq (h2 cv v hh he),
    fun cv mI rP isK rules he r hr => ?_, fun cv caps he => ?_, fun d hd => hpq d (h5 d hd)⟩
  · obtain ⟨a, b, c⟩ := h3 cv mI rP isK rules he r hr
    exact ⟨Expr.constsAll_mono hpq a, hpq _ b, fun lvls pins hf x hx =>
      Expr.constsAll_mono hpq (c lvls pins hf x hx)⟩
  · obtain ⟨a, c, d⟩ := h4 cv caps he
    exact ⟨fun m hm => hpq m (a m hm), fun he' => hpq _ (c he'),
      fun t ht => ⟨hpq _ (d t ht).1, fun b hb => Expr.constsAll_mono hpq ((d t ht).2 b hb)⟩⟩

/-! ## The reading -/

/-- **A context, read from its sources** (see the module docstring): per stored name `n`, the
source environment `E n` and the part `R n` of it the context reads as the source does. -/
structure CtxRead (C : Env) (E R : Name → Env) : Prop where
  /-- the context stores each name once -/
  nodup : NodupNames C
  /-- the context's copy refines its source's -/
  entry : ∀ n ci, C.find? n = some ci → ∃ ci', (E n).find? n = some ci' ∧ Refines ci ci'
  /-- the part read alike is part of the source, stored in the context -/
  R_sub : ∀ n d ci, (R n).find? d = some ci → (E n).find? d = some ci ∧ (C.find? d).isSome = true
  /-- a stored name is read alike from its own source -/
  self : ∀ n, (C.find? n).isSome = true → ((R n).find? n).isSome = true
  /-- a name read alike has alike copies -/
  alike : ∀ n d, (C.find? n).isSome = true → ((R n).find? d).isSome = true →
    ∃ ciC ciE, C.find? d = some ciC ∧ (E n).find? d = some ciE ∧ Alike ciC ciE
  /-- and the same table -/
  table : ∀ n d, (C.find? n).isSome = true → ((R n).find? d).isSome = true →
    C.findTable? d = (E n).findTable? d
  /-- what a stored constant's laws read is read alike -/
  scope : ∀ n ci, C.find? n = some ci →
    EntryScopedP (fun d => ((R n).find? d).isSome = true) C n ci
  /-- a former read alike has its constructors read alike (they arrive in its record) -/
  ctors : ∀ n d cv caps, (C.find? n).isSome = true → ((R n).find? d).isSome = true →
    C.find? d = some (.indInfo cv caps) → ∀ x ∈ caps.ctors, ((R n).find? x).isSome = true
  /-- what an inductive kind read alike reads is read alike -/
  deep : ∀ n d ci, (C.find? n).isSome = true → ((R n).find? d).isSome = true →
    C.find? d = some ci → ci.isIndKind = true →
    EntryScopedP (fun d' => ((R n).find? d').isSome = true) C d ci
  /-- a constant at a compiler-trust name is its source's (such a record is presented only as
  itself) -/
  reduce : ∀ n ci, C.find? n = some ci → n ∈ reduceOpNames → (E n).find? n = some ci
  /-- every context table is its structure's, and its structure a stored former -/
  tables_mem : ∀ t ∈ C.tables, C.findTable? t.structName = some t ∧
    ∃ cv caps, C.find? t.structName = some (.indInfo cv caps)
  /-- every source table is its structure's, and its structure a stored former -/
  tables_src : ∀ n, ∀ t ∈ (E n).tables, (E n).findTable? t.structName = some t ∧
    ∃ cv caps, (E n).find? t.structName = some (.indInfo cv caps)

/-- **A context's model** at the leaves `aC`: a covered carrier, with the η-family run, the
η-family closure and the `Nat` facts, whose leaf at every stored name is `aC`'s. -/
@[expose] def CtxModel (V : Type w) [SetTheory V] (C : Env)
    (aC : Name → (Name → Nat) → Term.Term) : Prop :=
  ∃ mp : EnvModelM V C, LfpCover mp [] ∧ FamilyRan mp ∧ EtaFamiliesClosed C ∧ NatFacts C ∧
    ∀ n, (C.find? n).isSome = true → mp.base2.acval n = aC n

end ConLeche.Model.Modular
