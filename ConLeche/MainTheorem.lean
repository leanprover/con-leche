module

import ConLeche.Verify.Cached.MainC
public import ConLeche.Denotes
public import ConLeche.Accepts
import ConLeche.Model.Denotes
import ConLeche.Verify.Cached.StreamThm
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.Frontend.Chunks
public section

/-!
# The main theorem and the main corollary

What the checker accepts has a model; hence a file that declares a
theorem of type `False` is not accepted at all — the form a reader can
check without knowing what an `Env` is.  Those two theorems are all
this file holds.  The steps between them are imported: the parser
reads such a file into a list holding a theorem record of type `False`
(`Frontend.parseExportD_hasProofOfFalse`), the preparation the driver
runs before the fold keeps every parsed record
(`Frontend.mem_preparePrelude`), and a stream holding such a record is
never accepted (`no_False_theorem_accepted`: the record is installed
under its own name with its declared type, and in the model of the
main theorem that type is the empty set).  The statements, with a
plain-words account of every name in them, are in
`ConLeche/Challenge.lean`; the reading of terms and the notion of
model — and `Denotes_functional`, which says a term has at most one
denotation — in `ConLeche/Denotes.lean`.

* `checkDecls` (`ConLeche/Cached/Installed.lean`) is the declaration
  fold: it installs every parsed declaration — a definition, theorem
  or opaque annotated and pushed with its check recorded, everything
  else checked in full as it is installed — and then checks every
  recorded declaration against the prefix of the environment it was
  installed at.  The binary's driver (`Main.lean`) runs this fold with a
  heartbeat between the steps and returns its environment together
  with the proof that `checkDecls` returns it
  (`Cached.fullyChecked_checkDecls`), so the success line is printed
  from an accept of `checkDecls` and from nothing else.
* `Declaration` is a parsed declaration; `Env` is the environment the checker
  builds; `env.consts` are the constants it accepted; `.verified` is the
  default mode.
* `hasProofOfFalse` and `pipelineAccepts` (`ConLeche/Accepts.lean`)
  are the file-level vocabulary: the string template of a file that
  declares a theorem of type `False`, and the driver's accept path as
  pure content — the built-in prelude parses, the file parses, and
  `checkDecls` accepts the parsed list prepared with the prelude.
* `False` and `Eq` are built in: the checker installs them from its own
  pins, and a stream that declares them differently is rejected.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : List Declaration) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

/-- **The main corollary.**  A file that declares a theorem of type
`False` is never accepted: the parse reads the template's four lines
into a theorem record of type `False`, the preparation keeps the
record, and a stream holding it is never accepted. -/
theorem no_False_declaration (V : Type w) [SetTheory V] (s : String)
    (h : hasProofOfFalse s) : ¬ pipelineAccepts s := by
  rintro ⟨pre, r, env, -, hparse, hcheck⟩
  obtain ⟨cv, vl, hty, hmem⟩ := Frontend.parseExportD_hasProofOfFalse h hparse
  exact no_False_theorem_accepted V _ cv vl (Frontend.mem_preparePrelude hmem) hty env hcheck

/-- The same, for the chunks the binary reads: a result of the
streaming parse is the wholesale parse of their concatenation. -/
theorem no_False_declaration_streaming (V : Type w) [SetTheory V] (s : String)
    (chunks : List ByteArray) (h : hasProofOfFalse s)
    (hcs : s.toUTF8 = Frontend.concatBytes chunks) (hne : ∀ c ∈ chunks, c.isEmpty = false) :
    ¬ streamingAccepts chunks := by
  rintro ⟨pre, r, env, hpre, hparse, hcheck⟩
  exact no_False_declaration V s h
    ⟨pre, r, env, hpre, Frontend.parseChunks_ok_parseExportD hcs hne hparse, hcheck⟩

end ConLeche
