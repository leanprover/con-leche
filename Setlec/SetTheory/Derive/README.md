# Deriving `SetTheory` from the minimal `TG` core

Goal: `instance [TG V] : SetTheory V` (`Setlec/SetTheory/Instance.lean`),
with `TG` (`Setlec/SetTheory/Core.lean`) axiomatizing only membership,
extensionality, pairing, union, power set, regularity, Lean-level
replacement, and Tarski's Axiom A with the transitivity clause
(nanodatg's eight set axioms; choice is inherited from Lean's
`Classical.choice` rather than asserted — see Core.lean's module doc).

Reference blueprints: `_tmp/nanodatg/kernel/README.md` (axiom
itemization) and `_tmp/nanodatg/derived/src/*` (module docs).

## Status

- [x] `Core.lean` — the `TG` class (7 asserted axioms + `nonempty`),
  `Equinumerous`, `IsTGUniverse`, subset notation.
- [x] `Derive/Empty.lean` — empty set from Tarski transitivity +
  regularity; `not_mem_self`, `no_two_cycle`.
- [x] `Derive/Sep.lean` — separation from replacement (classical
  witness default); `image_congr`.
- [x] `Derive/Pair.lean` — singletons, binary union, Kuratowski pairs,
  `kpair_inj`, pair-members-nonempty.
- [x] `Derive/Universe.lean` — the diagonal lemma
  `IsTGUniverse.covered_mem` (nanodatg `cantor::image_in_universe`)
  and the closure laws: power, pairing, replacement image, `⋃` of a
  member, family unions; `guniv` via choice.
- [x] `Derive/Pt.lean` — `pt = {∅}`, `unitSet = {pt}`,
  `univZero = power unitSet`, `truthVal`, `eqv`, propositional
  extensionality; `pt` is never a Kuratowski pair.
- [x] `Derive/Graphs.lean` — `graph`, tagged `app` (`app pt a = pt`),
  `sigmaPairs`, `piSet`; beta on graphs, eta, domain determination,
  universe membership.
- [x] `Derive/Pi.lean` — level-truncated `pi`/`lam` (`pi 0` a truth
  value, `lam 0 = pt`) with all `SetTheory`-shaped laws (`v = 0`
  fibre premises phrased as `v = 0 → … ∈ᵗ univZero`).
- [x] `Derive/Omega.lean` — von Neumann naturals: `omega` separated
  from the inductive universe `guniv empty`, `vnat : Nat → V`
  (injective), `mem_omega_iff`; `omega ∈ U` for any universe with a
  universe member.
- [x] `Derive/Natrec.lean` — recursion on `omega` through the
  meta-level `Nat` (each member of `omega` is a unique `vnat k`).
- [x] `Derive/Univ.lean` — the tower `univ 0 = univZero`,
  `univ (n+1) = guniv {univ n, guniv empty}`; cumulativity,
  `univ_mem_univ`, `omega ∈ univ (n+1)`, closure transport.
- [x] `Derive/Sigma.lean` — `sigmaSet` (level-0 truth value /
  `sigmaPairs`), `spair := kpair`, classical `sfst`/`ssnd` with `pt`
  defaults; all `SetTheory` sigma laws.
- [x] `Derive/Quot.lean` — quotients: equivalence closure of the
  `R`-inhabitation relation on `A`, classes by separation, `quotSet`
  (level-0 collapse to `image (fun _ => pt) A`), `quotLift` via a
  choice of representatives; sound/surjective/lift laws matching the
  quot fields of the *mainline* `Basic.lean`.
- [x] `Derive/Choice.lean` — global `schoice` from `Classical.choice`;
  the Jech-form set-level choice function as a *theorem* (the "eighth
  axiom", derived).
- [x] `Instance.lean` — `noncomputable instance [TG V] : SetTheory V`.

## Notes for the merger

- Nothing outside `Setlec/SetTheory/Core.lean`,
  `Setlec/SetTheory/Derive/*`, `Setlec/SetTheory/Instance.lean` was
  touched; wire imports (e.g. in `Setlec.lean`) as desired.
- This branch's `Setlec/SetTheory/Basic.lean` predates the mainline
  quot/prop_ext/schoice extension.  `Instance.lean` therefore fills
  the fields present here; the extra mainline fields are already
  proved as standalone theorems (`Derive/Quot.lean` for
  `quotSet`/`quotClass`/`quotLift` laws, `Derive/Pt.lean`
  `univZero_ext` for `prop_ext`, `Derive/Choice.lean` for
  `schoice`/`schoice_mem`), so extending the instance is a few-line
  mechanical step — see the comment at the end of `Instance.lean`.
