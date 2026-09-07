--#export Dep.use

/- End-to-end control for a CROSS-BLOCK dependency: `Box` is a
   structure, `Dep` a two-constructor sum whose `wrap` field is a
   `Box`, and both install on the fixpoint route (task #210).

   Until task #219 this fixture was about something else: the export
   carried the preprocessor's `Box._model` and `Dep._model` families,
   `Dep`'s model was built OUT OF `Box`'s, and the point was that a
   model generator's skip rule has to be dependency-aware.  Its
   negative twin `direct_nested_dep_broken.ndjson` — this export with
   the `Box._model` family head deleted, so a surviving artifact
   referenced an undeclared constant — was deleted with the concept:
   models come from the in-process modeller now
   (`ConLeche/Frontend/InModel/*`), a stream `_model` record is an
   ordinary declaration, and there is no skip rule to get wrong.

   (Measured on the init-prelude stream when it still mattered:
   exactly one of 149 inductive blocks — `Trans` — had a model that
   referenced another block's model, namely `LT`'s.) -/

structure Box (α : Type) where
  val : α

inductive Dep (α : Type) where
  | wrap : Box α → Dep α
  | none : Dep α

def Dep.get {α : Type} (d : Dep α) (fallback : α) : α :=
  match d with
  | .wrap b => b.val
  | .none => fallback

theorem Dep.use (a b : Nat) :
    Eq (Dep.get (Dep.wrap (Box.mk a)) b) a := rfl
