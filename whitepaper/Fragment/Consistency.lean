module

public import Fragment.NestInstall
public import Fragment.Sound

@[expose] public section

/-!
# Consistency of the accepted environments

The environments the checker accepts (`Accepted`: the empty one, and
the two steps `DefOk` and `IndOk`) all have a model
(`accepted_model`), by `install_def` and `install_ind`.  With the
soundness of the rules (`closed_infer`, `Sound.lean`) that gives the
consistency statement: **no closed term inhabits an empty inductive
type** (`no_empty_inductive_inhabitant`), in particular an empty
proposition such as `False` (`no_empty_prop_inhabitant`).

The emptiness is read off the **recursor's type law** in an arbitrary
model — not the family's construction: any model's recursor for the
block lies in the set of `∀ (motive : I → Sort ℓ) (t : I), motive t`;
at the motive with the empty fibre, a member of `I` would give a
member of the empty set.  So the corollary needs no knowledge of how
the model was built, only that one exists.

Con-leche's counterparts: `ConLeche/Model/Consistency.lean`.
-/

namespace Fragment
open SetLib IndLib

universe u

variable (V : Type u) [IndLib V] [LevelOracle]

/-- **The environments the checker accepts**: the empty environment,
a definition the definition check passes, an inductive block the
block check passes (con-leche's `addDecl`, `ConLeche/Kernel/Env.lean`,
run to completion). -/
inductive Accepted : Env → Prop
  /-- Nothing is stored. -/
  | empty : Accepted Env.empty
  /-- A definition (`DefOk`, `Decl.lean`). -/
  | defn {env : Env} {c : Name} {ci : ConstInfo} :
      Accepted env → DefOk env c ci → Accepted (env.add c ci)
  /-- An inductive block, plain or nested (`IndOk`, `Decl.lean`). -/
  | ind {env : Env} (S : IndSpec) : Accepted env → IndOk env S → Accepted (S.install env)

omit [IndLib V] in
/-- An accepted environment is closed: its stored terms mention only
stored constants, at their own level parameters. -/
theorem Accepted.scoped : ∀ {env : Env}, Accepted env → Env.Scoped env
  | _, .empty => Env.Scoped.empty
  | _, .defn h hok => h.scoped.add_def hok
  | _, .ind S h hok => h.scoped.install_any hok

/-- **Every accepted environment has a model** (in any `IndLib`) — a
block model, which remembers its blocks for the nestings to come. -/
theorem accepted_model {env : Env} (h : Accepted env) : Nonempty (BlockModel V env) := by
  induction h with
  | empty => exact ⟨BlockModel.empty fun _ _ => pt⟩
  | defn h hok ih =>
    obtain ⟨m⟩ := ih
    obtain ⟨m', -⟩ := install_def' h.scoped m hok
    exact ⟨m'⟩
  | ind S h hok ih =>
    obtain ⟨m⟩ := ih
    obtain ⟨m', -⟩ := install_ind_any h.scoped m hok
    exact ⟨m'⟩

namespace IndSpec

/-- **The empty proposition** as a block: `inductive False : Prop`
with no constructors, and its recursor eliminating into any universe
(`large`: the subsingleton criterion is vacuous). -/
def falseSpec (name recName elim : Name) : IndSpec :=
  ⟨⟨name, [], [], [], .zero, [], recName, true, elim⟩, none⟩

end IndSpec

section Corollaries

/-! The consistency statements are about the syntax alone; the set
library is the proof's device, so it is an explicit parameter of
them: any `IndLib` will do. -/

include V in
/-- **No closed term inhabits an empty inductive type.**  For a block
without constructors, parameters, indices and level parameters whose
recursor the environment stores, no closed term has the type former's
type: in a model, the recursor's set lies in the product over the
motives and the fibre, and at the motive with the empty fibre a
member of the type would be a member of the empty set. -/
theorem no_empty_inductive_inhabitant {env : Env} (hacc : Accepted env) {S : IndSpec}
    (hctors : S.ctors = []) (hparams : S.params = []) (hidx : S.indices = [])
    (hlp : S.lparams = []) (hrec : env.find? S.recName = some S.recInfo) (e : Expr) :
    ¬ Infer env [] e (.const S.name []) := by
  intro he
  obtain ⟨m⟩ := accepted_model V hacc
  -- the recursor at the identity instantiation and the all-zero valuation
  have hR := (m.type_ok S.recName S.recInfo hrec (fun _ => 0) base (S.recLparams.map .param)
    (by simp [IndSpec.recInfo])).2
  simp only [IndSpec.recInfo] at hR
  rw [interp_instL, Level.substVal_self] at hR
  -- the elimination level is zero
  have hℓ : Level.eval (fun _ => 0) S.ℓ = 0 := by
    unfold IndSpec.ℓ
    split <;> rfl
  have hq : S.q.holds (fun _ => 0) = true := by
    rw [S.q_holds, hℓ]
    rfl
  -- the recursor's type, read: `∀ (motive : I → Sort 0) (t : I), motive t`
  simp only [IndSpec.recType, IndSpec.famVars, IndSpec.famAt, IndSpec.indicesAt, IndSpec.minorsCtx,
    IndSpec.motiveTy, IndSpec.n, IndSpec.nI, IndSpec.nP, IndSpec.lvls, hctors, hparams, hidx, hlp,
    Expr.varsAt, List.range_zero, List.map_nil, List.length_nil, Expr.liftCtx_nil, List.reverse_nil,
    List.nil_append, List.append_nil, List.singleton_append, Expr.mkAppN, List.foldl_cons,
    List.foldl_nil, Expr.mkPis, interp_app, interp_bvar,
    interp_pi, interp_sort, interp_const, PropWhen.holds_never, hq, hℓ, Nat.add_zero, cons_zero,
    cons_succ] at hR
  -- the motive with the empty fibre
  have hmo : lamR false (m.M S.name []) (fun _ => truthVal False) ∈ˢ
      piR false (m.M S.name []) fun _ => (univ 0 : V) :=
    lamR_mem (fun _ _ => truthVal_mem_univ_zero _) fun h => nomatch h
  have h₁ := app_mem_piR hR hmo
  -- a member of the type would be a member of the empty set
  have ht := closed_infer m.toEnvModel (fun _ => 0) he base
  simp only [interp_const, List.map_nil] at ht
  have h₂ := app_mem_piR h₁ ht
  rw [app_lamR_false ht] at h₂
  exact of_mem_truthVal h₂

include V in
/-- **No closed term inhabits an empty proposition**: the block
`inductive False : Prop`, installed in an accepted environment, has
no closed inhabitant. -/
theorem no_empty_prop_inhabitant {env : Env} (hacc : Accepted env) {name recName elim : Name}
    (hrec : env.find? recName = some (IndSpec.falseSpec name recName elim).recInfo) (e : Expr) :
    ¬ Infer env [] e (.const name []) :=
  no_empty_inductive_inhabitant V hacc (S := IndSpec.falseSpec name recName elim) rfl rfl rfl rfl
    hrec e

end Corollaries

end Fragment
