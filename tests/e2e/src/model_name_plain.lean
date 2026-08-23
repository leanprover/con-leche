--#export Foo.ok Foo Foo._model

/- Regression: **`_model` names are not special**.

   The direct simple-structure install carries a *model-family guard*
   (`modelFamilyTaken`, `Setlec/Kernel/Direct.lean`) that refuses a
   `_model` companion appearing *after* the constant it would be linked
   to.  That guard is keyed on exactly the environment invariant's
   linkage clauses — a stored non-reserved inductive-kind type former or
   constructor, or a stored projection function — and on nothing wider.

   This fixture is the negative control: a plain `def Foo` followed by a
   plain `def Foo._model`, neither of them inductive-kind and no
   projection function in sight.  It is a perfectly ordinary stream, the
   reference kernels accept it, setlec accepted it before the direct
   path existed, and it must keep being **accepted** (exit 0).  A
   blanket reservation of the `_model` suffix would reject it.

   Committed as a *raw* lean4export result and run with
   `SETLEC_INDUCTIVE_MODELS=/nonexistent` (the `raw` marker in
   `tests/e2e-expected.txt`), so no preprocessor invents a `_model`
   declaration of its own.
-/

def Foo : Nat := Nat.zero

def Foo._model : Nat := Nat.zero

theorem Foo.ok : Eq Foo Foo._model := rfl
