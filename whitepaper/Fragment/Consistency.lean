module

public import Fragment.NestInstall
public import Fragment.Sound
public import Fragment.InstallThm

@[expose] public section

/-!
# The empty proposition

What makes an inductive type without constructors empty in a model:
its **recursor's membership in its type** (`empty_of_rec_mem`), not
the family's construction.  Any set in the recursor's type lies in the
set of `∀ (motive : I → Sort ℓ) (t : I), motive t`; at the motive with
the empty fibre, a member of `I` would give a member of the empty set.
So the consistency corollaries need no knowledge of how a model was
built, only that one exists: over the input's constants
(`IsModel.no_false`, `Main.lean`), and over the internal invariant
with the soundness of the rules (`no_empty_inductive_inhabitant_of_model`,
by `closed_infer`, `Sound.lean`: no closed term has the type).

`falseSpec` is the empty proposition as a block.

Con-leche's counterparts: `ConLeche/Semantics/IsModelBasis.lean`
(`IsModel.no_false_record`) and `ConLeche/Model/Capstone.lean`.
-/

namespace Fragment
open SetLib IndLib

universe u

variable (V : Type u) [IndLib V] [LevelOracle]

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

omit [LevelOracle] in
/-- **The recursor of an empty inductive type empties it**: for a block
without constructors, parameters, indices and level parameters, a set
in the recursor's type at the all-zero valuation makes the type
former's set empty — at the motive with the empty fibre, a member of
the type would give a member of the empty set.  Any assignment `M`:
nothing about how the model was built is read. -/
theorem empty_of_rec_mem {M : Name → List Nat → V} {S : IndSpec}
    (hctors : S.ctors = []) (hparams : S.params = []) (hidx : S.indices = [])
    (hlp : S.lparams = []) {r : V} (hR : r ∈ˢ interp M (fun _ => 0) base S.recType)
    {x : V} (hx : x ∈ˢ M S.name []) : False := by
  -- the elimination level is zero
  have hℓ : Level.eval (fun _ => 0) S.ℓ = 0 := by
    unfold IndSpec.ℓ
    split <;> rfl
  -- the recursor's type, read: `∀ (motive : I → Sort 0) (t : I), motive t`
  simp only [IndSpec.recType, IndSpec.famVars, IndSpec.famAt, IndSpec.indicesAt, IndSpec.minorsCtx,
    IndSpec.motiveTy, IndSpec.n, IndSpec.nI, IndSpec.nP, IndSpec.lvls, hctors, hparams, hidx, hlp,
    Expr.varsAt, List.range_zero, List.map_nil, List.length_nil, Expr.liftCtx_nil, List.reverse_nil,
    List.nil_append, List.append_nil, List.singleton_append, Expr.mkAppN, List.foldl_cons,
    List.foldl_nil, Expr.mkPis, interp_app, interp_bvar,
    interp_pi, interp_sort, interp_const, hℓ, Nat.add_zero, cons_zero,
    cons_succ] at hR
  -- the motive with the empty fibre
  have hmo : lamV (M S.name []) (fun _ => truthVal False) ∈ˢ
      piV (M S.name []) fun _ => (typeU 0 : V) :=
    lamV_mem (fun _ _ => mem_typeU_zero.mpr (truthVal_mem_univ_zero _)) fun _ _ => IsTy_typeU 0
  have h₁ := app_mem_piV hR hmo
  have h₂ := app_mem_piV h₁ hx
  rw [app_lamV hx] at h₂
  exact of_mem_truthVal h₂

/-- **No closed term inhabits an empty inductive type**, in any
environment with a model.  For a block
without constructors, parameters, indices and level parameters whose
recursor the environment stores, no closed term has the type former's
type (`empty_of_rec_mem`). -/
theorem no_empty_inductive_inhabitant_of_model {env : Env} (m : EnvModel V env) {S : IndSpec}
    (hctors : S.ctors = []) (hparams : S.params = []) (hidx : S.indices = [])
    (hlp : S.lparams = []) (hrec : env.find? S.recName = some S.recInfo) (e : Expr) :
    ¬ Infer env [] e (.const S.name []) := by
  intro he
  -- the recursor at the identity instantiation and the all-zero valuation
  have hR := (m.type_ok S.recName S.recInfo hrec (fun _ => 0) base (S.recLparams.map .param)
    (by simp [IndSpec.recInfo])).2.2
  simp only [IndSpec.recInfo] at hR
  rw [interp_instL, Level.substVal_self] at hR
  have ht := closed_infer m (fun _ => 0) he base
  simp only [interp_const, List.map_nil] at ht
  exact empty_of_rec_mem V hctors hparams hidx hlp hR ht

end Corollaries

end Fragment
