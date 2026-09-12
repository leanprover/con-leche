module

public import ConLeche.Verify.Cached.MainC
public import ConLeche.Denotes
import ConLeche.Model.Denotes
import ConLeche.Verify.Cached.StreamThm
public section

/-!
# The main theorem, and the main corollary it implies

What the checker accepts has a model; hence it contains no constant of
type `False`.  Those two theorems are all this file holds.  The
statements, with a plain-words account of every name in them, are in
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
* `DeclC` is a parsed declaration; `Env` is the environment the checker
  builds; `env.consts` are the constants it accepted; `.verified` is the
  default mode.
* `False` and `Eq` are built in: the checker installs them from its own
  pins, and a stream that declares them differently is rejected.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (DeclC ExprC checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

/-- **The main corollary.**  An accepted stream never yields a
constant of type `False`: its type would denote the empty set, and
`Model.mem` puts the constant inside it. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] := by
  rintro ⟨c, hc, hty⟩
  obtain ⟨m⟩ := model_exists V ds env accepted
  obtain ⟨T, hT, hmem⟩ := m.mem c hc (fun _ => 0) (fun _ => empty)
  rw [hty] at hT
  rw [m.false_empty _ _ _ hT] at hmem
  exact not_mem_empty _ hmem

/-- **The main corollary, at the stream.**  A stream that declares a
theorem of type `False` is never accepted: the record is installed
under its own name with its declared type, that constant survives the
run, and the main corollary forbids it. -/
theorem no_False_theorem_accepted (V : Type w) [SetTheory V]
    (ds : List DeclC) (cv : ConstantVal) (v : ExprC)
    (hmem : DeclC.thmDecl cv v ∈ ds) (hty : cv.type = .const falseName []) :
    ∀ env, checkDecls .verified ds ≠ .ok env := by
  intro env accepted
  exact no_proof_of_False V ds env accepted
    (Cached.checkDecls_thmDecl_const hty hmem accepted)

end ConLeche
