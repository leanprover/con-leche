module

public import Fragment.ModularModel

@[expose] public section

/-!
# The main theorem

**What the checker accepts has a model** (`model_exists`): a list of
declarations that checks from the empty environment (`Checks`,
`Modular.lean`) has a model of its constants in every set theory with
libraries (`IsModel`, `IsModel.lean`; `constantsOf`, `Modular.lean`).
The statement reads the input alone: the declarations' constants and
the reading of terms as sets.  The proof builds the model along the
check (`Checks.blockModel`, `ModularModel.lean`): the installation of
every declaration keeps the internal invariant (`EnvModel`,
`BlockModel`) and makes the declaration's constants hold
(`Holds.lean`).

**The consistency corollary** (`IsModel.no_false`): a model of
constants that include the recursor of an empty proposition (the
`falseSpec` shape: no constructors, parameters, indices or level
parameters) has no constant whose type is that proposition.  So no
accepted list of declarations has a theorem — or any other constant —
of type `False` beside `False`'s own recursor (`no_false_constant`).
The emptiness is read off the recursor's membership in its type, not
off how the model was built.  The syntactic form
(`no_empty_prop_inhabitant`): no closed term has the type `False` in
the environment an accepted list ends in.

Con-leche's counterparts: `model_exists` and `IsModel.no_false_record`
(`ConLeche/MainTheorem.lean`, `ConLeche/Semantics/IsModelBasis.lean`).
-/

namespace Fragment
open SetLib IndLib

universe u

variable (V : Type u) [IndLib V] [LevelOracle]

/-- **The main theorem.**  Every list of declarations the checker
accepts from the empty environment has a model of its constants, in
any set theory with libraries. -/
theorem model_exists {ds : List Decl} (h : Checks Env.empty ds) :
    ∃ M : Name → List Nat → V, IsModel V M (constantsOf ds) := by
  obtain ⟨m, -, -, hh⟩ := h.blockModel Env.Scoped.empty (BlockModel.empty (V := V) fun _ _ => pt)
    (fun _ _ hf => by simp at hf) (Holds.empty _)
  exact ⟨m.M, fun n ci ⟨d, hd, hm⟩ => hh n ci (h.find?_of_stores hd hm)⟩

variable {V}

omit [LevelOracle] in
/-- **A model has no constant of an empty proposition's type**: if the
constants `C` include the recursor of the empty proposition
`falseSpec name recName elim`, no constant of `C` has the type
`name`. -/
theorem IsModel.no_false {M : Name → List Nat → V} {C : Name → ConstInfo → Prop}
    (h : IsModel V M C) {name recName elim : Name}
    (hrec : C recName (IndSpec.falseSpec name recName elim).recInfo)
    {t : Name} {ci : ConstInfo} (ht : C t ci) (hty : ci.type = .const name []) : False := by
  have hzero : ∀ ps : List Name, valOf ps (ps.map fun _ => 0) = fun _ => 0 := by
    intro ps; rw [valOf_map]; funext n; split <;> rfl
  have hR := (h recName _ hrec _ (List.length_map (f := fun _ => (0 : Nat)) (as := _))).1
  rw [hzero] at hR
  have hx := (h t ci ht _ (List.length_map (f := fun _ => (0 : Nat)) (as := ci.lparams))).1
  rw [hzero, hty, interp_const, List.map_nil] at hx
  exact empty_of_rec_mem V (S := IndSpec.falseSpec name recName elim) rfl rfl rfl rfl hR hx

include V in
/-- **No accepted list of declarations has a constant of type `False`**:
where its constants include the recursor of the empty proposition
`falseSpec name recName elim`, none has the type `name` — a theorem of
`False` among them. -/
theorem no_false_constant {ds : List Decl} (h : Checks Env.empty ds) {name recName elim : Name}
    (hrec : constantsOf ds recName (IndSpec.falseSpec name recName elim).recInfo)
    {t : Name} {ci : ConstInfo} (ht : constantsOf ds t ci) (hty : ci.type = .const name []) :
    False := by
  obtain ⟨M, hM⟩ := model_exists V h
  exact hM.no_false hrec ht hty

include V in
/-- **No closed term inhabits an empty proposition** that an accepted
list of declarations installs: in the environment the list ends in, no
closed term has the type `name` of the block `falseSpec name recName
elim` (`no_empty_inductive_inhabitant_of_model`, at the model the
check builds). -/
theorem no_empty_prop_inhabitant {ds : List Decl} (h : Checks Env.empty ds) {name recName elim : Name}
    (hrec : (applyAll ds Env.empty).find? recName = some (IndSpec.falseSpec name recName elim).recInfo)
    (e : Expr) : ¬ Infer (applyAll ds Env.empty) [] e (.const name []) := by
  obtain ⟨m, -, -, -⟩ := h.blockModel Env.Scoped.empty (BlockModel.empty (V := V) fun _ _ => pt)
    (fun _ _ hf => by simp at hf) (Holds.empty _)
  exact no_empty_inductive_inhabitant_of_model V m.toEnvModel
    (S := IndSpec.falseSpec name recName elim) rfl rfl rfl rfl hrec e

end Fragment
