--#export Foo.ok Foo Foo._model

/- Regression: **`_model` names are not special**.

   There is no `_model` reservation of any kind: the public↔`_model`
   identification is group-local to a modeled block's install
   derivation (task #83), the environment carries no linkage, and the
   former model-family guard (`modelFamilyTaken`) is deleted.

   This fixture is the negative control: a plain `def Foo` followed by
   a plain `def Foo._model`.  It is a perfectly ordinary stream, the
   reference kernels accept it, and it must keep being **accepted**
   (exit 0).  Any reservation or shadow check on the `_model` suffix
   sneaking back in would reject it.

   Committed as a *raw* lean4export result and run with
   `LECH_INDUCTIVE_MODELS=/nonexistent` (the `raw` marker in
   `tests/e2e-expected.txt`), so no preprocessor invents a `_model`
   declaration of its own.
-/

def Foo : Nat := Nat.zero

def Foo._model : Nat := Nat.zero

theorem Foo.ok : Eq Foo Foo._model := rfl
