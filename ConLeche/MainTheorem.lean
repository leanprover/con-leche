module

public import ConLeche.Verify.Cached.MainC
public import ConLeche.Denotes
import ConLeche.Model.Denotes
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
open ConLeche.Cached (DeclC checkDecls)

universe w

/-! ## At an arbitrary `Nat.div`/`Nat.mod` pin list

The fold's third argument is the list of pin variants its
`Nat.div`/`Nat.mod` install gate tries (task #285); the shipped
`checkDecls .verified ds` is the fold at `natOpPinSets`, the variants
this toolchain committed.  Nothing in the consistency argument reads
that list — the model's certificate conversion is over an arbitrary
variant, because what it consumes is the certificates' verdict in the
accepted environment and not where the variant came from — so both
theorems hold at **every** list, and the two shipped statements are
their instances at `natOpPinSets`.  The generalised forms are what a
downstream refinement proof about a differently pinned checker is
stated against. -/

/-- **The main theorem, at an arbitrary pin list.**  `model_exists` is
this at `natOpPinSets`. -/
theorem model_exists_with (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds pins = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

/-- **The main corollary, at an arbitrary pin list.**
`no_proof_of_False` is this at `natOpPinSets`. -/
theorem no_proof_of_False_with (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds pins = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] := by
  rintro ⟨c, hc, hty⟩
  obtain ⟨m⟩ := model_exists_with V pins ds env accepted
  obtain ⟨T, hT, hmem⟩ := m.mem c hc (fun _ => 0) (fun _ => empty)
  rw [hty] at hT
  rw [m.false_empty _ _ _ hT] at hmem
  exact not_mem_empty _ hmem

/-! ## The two shipped statements -/

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    Nonempty (Model V env) :=
  model_exists_with V natOpPinSets ds env accepted

/-- **The main corollary.**  An accepted stream never yields a
constant of type `False`: its type would denote the empty set, and
`Model.mem` puts the constant inside it. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName [] :=
  no_proof_of_False_with V natOpPinSets ds env accepted

end ConLeche
