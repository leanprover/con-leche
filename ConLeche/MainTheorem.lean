module

public import ConLeche.Verify.Cached.MainC
public import ConLeche.Denotes
import ConLeche.Model.Denotes
public section

/-!
# The main theorem, and the main corollary it implies

What the checker accepts has a model; hence it contains no constant of
type `False`.  The statements, with a plain-words account of every
name in them, are in `ConLeche/Challenge.lean`; the reading of terms
and the notion of model in `ConLeche/Denotes.lean`.

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
* `False` is built in: the checker installs it from its own pin, and a
  stream that declares `False` or `False.rec` differently is rejected.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (DeclC checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : List DeclC) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

/-- A term has at most one denotation. -/
theorem Denotes_functional {V : Type w} [SetTheory V]
    {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {e : Expr} {v w : V}
    (hv : Denotes cval env φ ρ e v) (hw : Denotes cval env φ ρ e w) :
    v = w := by
  induction hv generalizing w with
  | bvar => cases hw; rfl
  | sort => cases hw; rfl
  | const hf _ =>
    cases hw with
    | const hf' _ => rw [hf] at hf'; cases hf'; rfl
  | app _ _ ihf iha =>
    cases hw with
    | app hf' ha' => rw [ihf hf', iha ha']
  | lam _ _ _ ihA ihF =>
    cases hw with
    | lam hA' hF' _ =>
      obtain rfl := ihA hA'
      exact ConLeche.SetModel.lamR_congr fun x hx => ihF x hx (hF' x hx)
  | pi _ _ _ ihA ihB =>
    cases hw with
    | pi hA' hB' _ =>
      obtain rfl := ihA hA'
      exact ConLeche.SetModel.piR_congr fun x hx => ihB x hx (hB' x hx)
  | proj_table ht _ ih =>
    cases hw with
    | proj_table ht' he' => rw [ht] at ht'; cases ht'; rw [ih he']
    | proj_fst ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_snd ht' _ => rw [ht] at ht'; exact nomatch ht'
  | proj_fst ht _ ih =>
    cases hw with
    | proj_table ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_fst _ he' => rw [ih he']
  | proj_snd ht _ ih =>
    cases hw with
    | proj_table ht' _ => rw [ht] at ht'; exact nomatch ht'
    | proj_snd _ he' => rw [ih he']
  | natLit _ ih =>
    cases hw with
    | natLit h' => exact ih h'
  | strLit _ ih =>
    cases hw with
    | strLit h' => exact ih h'

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

end ConLeche
