--#export Dep.use

/- End-to-end control for the cross-dependency constraint the direct
   install introduces (task #82).

   `Box` is a direct-class simple structure; `Dep` is a *modeled*
   inductive (two constructors) whose constructor mentions `Box`, so
   the modeller builds `Dep._model` **out of** `Box._model`.

   This is the POSITIVE control of the pair: the export keeps `Box`'s
   artifacts, so `Box` goes modeled (artifact presence wins under the
   direct path's `directNoModel` gating) and everything checks.

   The NEGATIVE half, `direct_nested_dep_broken.ndjson`, is this very
   export with the `Box._model` *family head* deleted, so a surviving
   artifact (`Box.mk._model`) references a constant that is no longer
   declared.  Expected: a clean **reject** (exit 1) naming the missing
   constant — "unknown constant Box._model [at def Box.mk._model]".
   That is the failure mode a dependency-*unaware* skip rule in a
   model generator would produce, and it pins that it fails
   *safe*: the checker never accepts a stream whose artifacts reference
   models that were not generated.  See DESIGN.md, "The endgame:
   ind-models' skip rule must be dependency-aware".

   (Measured on the init-prelude stream: exactly one of 149 inductive
   blocks — `Trans` — has a model that references another block's
   model, namely `LT`'s.  So cross-block model dependencies are rare
   but real, and the skip rule has to compute them.) -/

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
