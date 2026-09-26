--#export Foo.ok Foo Foo._model

/- Regression: **`_model` names are not special**.

   There is no `_model` reservation of any kind.

   This fixture is the negative control: a plain `def Foo` followed by
   a plain `def Foo._model`.  It is a perfectly ordinary stream, the
   reference kernels accept it, and it must keep being **accepted**
   (exit 0).  Any reservation or shadow check on the `_model` suffix
   sneaking back in would reject it.

   Committed as a *raw* lean4export result.  Nothing in the frontend or
   the install looks at the name: a record called `Foo._model`
   installs, or does not, on its own merits alone.
-/

def Foo : Nat := Nat.zero

def Foo._model : Nat := Nat.zero

theorem Foo.ok : Eq Foo Foo._model := rfl
