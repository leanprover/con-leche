module

public import ConLeche.Verify.Inductives.BlockOneInstall
public import ConLeche.Verify.Fueled

public section

/-!
# The fueled family is lawful (milestone M1)

`FueledM` is a monotone family of pure `Except` computations
(`ConLeche/Verify/Fueled.lean`), so it is a lawful monad whose `throw`
short-circuits a `bind` — which is what lets the uniform install's
one-member bridge (`checkBlock_one`) be read at the fuel-indexed monad
the cached bridges compare against.
-/

namespace ConLeche

instance : LawfulMonad FueledM :=
  LawfulMonad.mk'
    (m := FueledM)
    (id_map := fun x => Subtype.ext (funext fun F => by
      show (x.val F >>= fun a => pure a) = x.val F
      cases x.val F <;> rfl))
    (pure_bind := fun a f => Subtype.ext (funext fun F => rfl))
    (bind_assoc := fun x f g => Subtype.ext (funext fun F => by
      show ((x.val F >>= fun a => (f a).val F) >>= fun b => (g b).val F)
        = (x.val F >>= fun a => ((f a).val F >>= fun b => (g b).val F))
      cases x.val F <;> rfl))

instance : ThrowBindM FueledM where
  throw_bind _ _ := Subtype.ext (funext fun _ => rfl)

end ConLeche
