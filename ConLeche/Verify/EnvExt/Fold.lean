module

public import ConLeche.Verify.EnvExt.Base
public import ConLeche.Kernel.Inductives.BlockTail
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.EnvWF
import ConLeche.Verify.ExceptBind

public section

/-!
# Env extension, part 11: the fold's side of the base facts

`Agree.ofBase` (`Base.lean`) asks of a base environment `B` and a later
one `E` that `E` extends `B` (`Extends`) and adds no in-scope name `B`
lacks (`NoNewInScope`).  Both are facts about how the declaration fold
grows its environment, and this file states them as ONE relation,
`StepOk B E`: every lookup of `B` survives, and every name `E` stores
that `B` lacks is either not of the reserved projection shape
(`Name.isProjFnShape`), or the projection table / projection function of
a name `B` lacks that is not of that shape either — the derived names
are only ever created by the install of the structure they belong to.

`StepOk` is reflexive and transitive (`StepOk.trans`: the second
disjunct is antitone in the base), and a fresh cons of such a name keeps
it (`StepOk.cons`), so every install stage is a run of conses
(`StepOk.consBlockInds`, `…consBlockCtors`, `…consBlockRecsT`,
`…checkBlockTables`); the per-declaration step is in
`Semantics/FoldScope.lean`, where the run records live.

The payoff is `StepOk.noNewInScope`: a base past the prelude
(`PastPrelude`: every fixed name stored) sees no new in-scope name in a
`StepOk` extension — an in-scope name the base lacks is derived
(`InScope.isProjFnShape_of_none`), and a derived name created later
belongs to a name the base lacks, which the base's scope does not hold.
-/

namespace ConLeche.EnvExt

open ConLeche

/-! ## The two name shapes -/

theorem projTableName_inj {T T' : Name} (h : projTableName T = projTableName T') : T = T' := by
  simp only [projTableName, Name.num.injEq, Name.str.injEq] at h
  exact h.1.1

theorem projFnName_inj {T T' : Name} {i j : Nat} (h : projFnName T i = projFnName T' j) :
    T = T' ∧ i = j := by
  simp only [projFnName, Name.num.injEq, Name.str.injEq] at h
  exact ⟨h.1.1, h.2⟩

theorem projFnName_ne_projTableName {T T' : Name} {i : Nat} :
    projFnName T i ≠ projTableName T' := by
  simp [projFnName, projTableName]

@[simp] theorem isProjFnShape_projTableName (T : Name) : (projTableName T).isProjFnShape = true :=
  rfl

@[simp] theorem isProjFnShape_projFnName (T : Name) (i : Nat) :
    (projFnName T i).isProjFnShape = true := rfl

/-! ## The prelude, and what the base's scope holds beyond its store -/

/-- **A base past the prelude**: every fixed name is stored. -/
@[expose] def PastPrelude (B : Env) : Prop := ∀ n ∈ envExtFixedNames, (B.find? n).isSome = true

/-- An in-scope name the base does not store is a derived one. -/
theorem InScope.isProjFnShape_of_none {B : Env} (hB : PastPrelude B) {n : Name}
    (h : InScope B n) (hn : B.find? n = none) : n.isProjFnShape = true := by
  cases h with
  | stored h => rw [hn] at h; exact nomatch h
  | fixed h => have := hB _ h; rw [hn] at this; exact nomatch this
  | table _ => rfl
  | projFn _ _ => rfl

/-- An in-scope name of the ordinary shape is stored. -/
theorem InScope.stored_of_shape {B : Env} (hB : PastPrelude B) {n : Name}
    (h : InScope B n) (hs : n.isProjFnShape = false) : (B.find? n).isSome = true := by
  cases hn : B.find? n with
  | some _ => rfl
  | none => rw [h.isProjFnShape_of_none hB hn] at hs; exact nomatch hs

/-- A projection table in scope but not stored is the table of an
in-scope name. -/
theorem InScope.of_table {B : Env} (hB : PastPrelude B) {T : Name}
    (h : InScope B (projTableName T)) (hn : B.find? (projTableName T) = none) : InScope B T := by
  generalize hx : projTableName T = x at h hn
  cases h with
  | stored h => rw [hn] at h; exact nomatch h
  | fixed h => have := hB _ h; rw [hn] at this; exact nomatch this
  | table h' => rw [projTableName_inj hx.symm] at h'; exact h'
  | projFn j _ => exact absurd hx.symm projFnName_ne_projTableName

/-- A projection function in scope but not stored is one of an in-scope
name. -/
theorem InScope.of_projFn {B : Env} (hB : PastPrelude B) {T : Name} {i : Nat}
    (h : InScope B (projFnName T i)) (hn : B.find? (projFnName T i) = none) : InScope B T := by
  generalize hx : projFnName T i = x at h hn
  cases h with
  | stored h => rw [hn] at h; exact nomatch h
  | fixed h => have := hB _ h; rw [hn] at this; exact nomatch this
  | table _ => exact absurd hx projFnName_ne_projTableName
  | projFn j h' => rw [(projFnName_inj hx.symm).1] at h'; exact h'

/-! ## The fold's extension relation -/

/-- **A name the fold may add on top of `B`**: an ordinary one, or the
projection table / a projection function of an ordinary name `B` lacks
(the structure's own install creates them). -/
@[expose] def NewOk (B : Env) (n : Name) : Prop :=
  n.isProjFnShape = false ∨
    ∃ T, T.isProjFnShape = false ∧ B.find? T = none ∧
      (n = projTableName T ∨ ∃ j, n = projFnName T j)

/-- **The fold's extension relation**: `E` keeps every lookup of `B`, and
every name it adds is one the fold may add. -/
@[expose] def StepOk (B E : Env) : Prop :=
  Extends B E ∧ ∀ {n : Name}, B.find? n = none → (E.find? n).isSome = true → NewOk B n

theorem NewOk.antitone {B E : Env} (hx : Extends B E) {n : Name} (h : NewOk E n) : NewOk B n := by
  rcases h with h | ⟨T, hs, hT, hn⟩
  · exact .inl h
  · refine .inr ⟨T, hs, ?_, hn⟩
    cases hb : B.find? T with
    | none => rfl
    | some ci => rw [hx hb] at hT; exact nomatch hT

theorem StepOk.refl (B : Env) : StepOk B B :=
  ⟨Extends.refl B, fun h h' => by rw [h] at h'; exact nomatch h'⟩

theorem StepOk.extends_ {B E : Env} (h : StepOk B E) : Extends B E := h.1

theorem StepOk.trans {B E E' : Env} (h₁ : StepOk B E) (h₂ : StepOk E E') : StepOk B E' := by
  refine ⟨fun hb => h₂.1 (h₁.1 hb), fun {n} hb hn' => ?_⟩
  cases hE : E.find? n with
  | some _ => exact h₁.2 hb (by rw [hE]; rfl)
  | none => exact (h₂.2 hE hn').antitone h₁.1

/-- **One fresh cons of a name the fold may add.** -/
theorem StepOk.cons {B E : Env} (h : StepOk B E) {c : ConstantInfo}
    (hf : B.find? c.name = none) (hn : NewOk B c.name) : StepOk B ⟨c :: E.consts⟩ := by
  refine ⟨fun {n ci} hb => ?_, fun {n} hb hn' => ?_⟩
  · rw [Env.find?_cons, if_neg (fun he => by rw [he, hb] at hf; exact nomatch hf)]
    exact h.1 hb
  · rw [Env.find?_cons] at hn'
    by_cases he : c.name = n
    · exact he ▸ hn
    · rw [if_neg he] at hn'; exact h.2 hb hn'

/-- A fresh cons of an ordinary name. -/
theorem StepOk.cons_plain {B E : Env} (h : StepOk B E) {c : ConstantInfo}
    (hf : B.find? c.name = none) (hs : c.name.isProjFnShape = false) :
    StepOk B ⟨c :: E.consts⟩ :=
  h.cons hf (.inl hs)

/-- Freshness at a `StepOk` extension is freshness at the base. -/
theorem StepOk.fresh {B E : Env} (h : StepOk B E) {n : Name} (hn : E.find? n = none) :
    B.find? n = none := by
  cases hb : B.find? n with
  | none => rfl
  | some _ => rw [h.1 hb] at hn; exact nomatch hn

/-- The prelude stays stored. -/
theorem StepOk.pastPrelude {B E : Env} (h : StepOk B E) (hB : PastPrelude B) : PastPrelude E := by
  intro n hn
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hB n hn)
  rw [h.1 hci]; rfl

/-- **The payoff**: past the prelude, a `StepOk` extension adds no
in-scope name. -/
theorem StepOk.noNewInScope {B E : Env} (hB : PastPrelude B) (h : StepOk B E) :
    NoNewInScope B E := by
  intro n hs hb
  cases hE : E.find? n with
  | none => rfl
  | some _ =>
    exfalso
    rcases h.2 hb (by rw [hE]; rfl) with hsh | ⟨T, hTs, hT, hn | ⟨j, hn⟩⟩
    · rw [hs.isProjFnShape_of_none hB hb] at hsh; exact nomatch hsh
    · subst hn
      have := (hs.of_table hB hb).stored_of_shape hB hTs
      rw [hT] at this; exact nomatch this
    · subst hn
      have := (hs.of_projFn hB hb).stored_of_shape hB hTs
      rw [hT] at this; exact nomatch this

/-! ## The install stages as runs of conses -/

section Stages

variable {B : Env}

theorem StepOk.consBlockInds {p₁ : BlockShape} {isRec : Bool} :
    ∀ {cvs : List ConstantVal} {i : Nat} {E : Env}, StepOk B E →
      (∀ cv ∈ cvs, B.find? cv.name = none ∧ cv.name.isProjFnShape = false) →
      StepOk B (ConLeche.consBlockInds p₁ isRec cvs i E)
  | [], _, _, h, _ => h
  | cv :: rest, i, E, h, hcv => by
    simp only [ConLeche.consBlockInds]
    have h0 := hcv cv List.mem_cons_self
    exact StepOk.consBlockInds (h.cons_plain (c := .indInfo cv _) h0.1 h0.2)
      (fun cv' hm => hcv cv' (List.mem_cons_of_mem _ hm))

theorem StepOk.consSumCtors {nP : Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {E : Env}, StepOk B E →
      (∀ c ∈ cs, B.find? c.1.name = none ∧ c.1.name.isProjFnShape = false) →
      StepOk B (ConLeche.consSumCtors nP cs E)
  | [], _, h, _ => h
  | c :: rest, E, h, hc => by
    simp only [ConLeche.consSumCtors]
    have h0 := hc c List.mem_cons_self
    exact StepOk.consSumCtors (h.cons_plain (c := .ctorInfo c.1 nP c.2) h0.1 h0.2)
      (fun c' hm => hc c' (List.mem_cons_of_mem _ hm))

theorem StepOk.consBlockCtors {nP : Nat} :
    ∀ {L : List (List (ConstantVal × Nat))} {E : Env}, StepOk B E →
      (∀ A ∈ L, ∀ c ∈ A, B.find? c.1.name = none ∧ c.1.name.isProjFnShape = false) →
      StepOk B (ConLeche.consBlockCtors nP L E)
  | [], _, h, _ => h
  | A :: rest, E, h, hc => by
    simp only [ConLeche.consBlockCtors]
    exact StepOk.consBlockCtors (StepOk.consSumCtors h (hc A List.mem_cons_self))
      (fun A' hm => hc A' (List.mem_cons_of_mem _ hm))

theorem StepOk.consBlockRecsT {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {E : Env}, StepOk B E →
      (∀ o ∈ out, B.find? o.1.name = none ∧ o.1.name.isProjFnShape = false) →
      StepOk B (ConLeche.consBlockRecsT find? res q m out E)
  | _, [], _, h, _ => h
  | m, (cv, M, rhss) :: rest, E, h, ho => by
    simp only [ConLeche.consBlockRecsT]
    have h0 := ho _ List.mem_cons_self
    exact StepOk.consBlockRecsT (h.cons_plain (c := .recInfo cv _ _ _) h0.1 h0.2)
      (fun o hm => ho o (List.mem_cons_of_mem _ hm))

/-- The table stage: one fresh table per structure-like member, at a
member name the base lacks. -/
theorem StepOk.checkBlockTables {q : BlockShape} :
    ∀ {l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))} {E E' : Env},
      StepOk B E →
      (∀ x ∈ l, B.find? x.1.cvT.name = none ∧ x.1.cvT.name.isProjFnShape = false) →
      ConLeche.checkBlockTables (m := CheckM) q l E = .ok E' → StepOk B E'
  | [], E, E', h, _, hr => by
    simp only [ConLeche.checkBlockTables, pure, Except.pure, Except.ok.injEq] at hr
    exact hr ▸ h
  | (ms, ctorsA, sortss) :: rest, E, E', h, hl, hr => by
    unfold ConLeche.checkBlockTables at hr
    obtain ⟨E₁, hE₁, hr⟩ := ConLeche.exceptBind_ok hr
    have hT := hl _ List.mem_cons_self
    have hrest := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    refine StepOk.checkBlockTables ?_ hrest hr
    revert hE₁
    split
    · split
      · intro hh
        obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := ConLeche.checkStructProjTable_inv hh
        exact h.cons (h.fresh hfresh) (.inr ⟨ms.cvT.name, hT.2, hT.1, .inl rfl⟩)
      · intro hh; simp only [pure, Except.pure, Except.ok.injEq] at hh; exact hh ▸ h
    · intro hh; simp only [pure, Except.pure, Except.ok.injEq] at hh; exact hh ▸ h

end Stages

end ConLeche.EnvExt
