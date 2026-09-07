# Deriving the operator interface from the `SetTheory` core

Goal: every operator and law of the checker's set-theoretic interface
(surfaced by `ConLeche/SetTheory/Basic.lean`) as a theorem over the
minimal `SetTheory` class (`ConLeche/SetTheory/Core.lean`), which
axiomatizes only membership, extensionality, pairing, union, power set,
regularity, Lean-level replacement, and an ω-chain of Grothendieck
universes `univChain` (universehood as Tarski's Axiom A matrix with
transitivity) — the consistency strength of the `OmegaInaccessibles`
hypothesis of Mario Carneiro, *The Type Theory of Lean*, master's
thesis, Carnegie Mellon University, 2019, §1.2;
choice is inherited from Lean's `Classical.choice` rather than
asserted — see Core.lean's module doc.

## Status

- [x] `Core.lean` — the `SetTheory` class (6 ZF⁻ axioms + the
  ω-chain `univChain`/`univChain_mem`/`univChain_tg`),
  `Equinumerous`, `IsTGUniverse`, subset notation.
- [x] `Derive/Empty.lean` — empty set from universe transitivity +
  regularity at `univChain 1`; `not_mem_self`, `no_two_cycle`.
- [x] `Derive/Sep.lean` — separation from replacement (classical
  witness default); `image_congr`.
- [x] `Derive/Pair.lean` — singletons, binary union, Kuratowski pairs,
  `kpair_inj`, pair-members-nonempty.
- [x] `Derive/Universe.lean` — the diagonal lemma
  `IsTGUniverse.covered_mem` (Cantor) and the closure laws: power,
  pairing, replacement image, `⋃` of a member, family unions;
  `univChain_mem_of_lt`.
- [x] `Derive/Pt.lean` — `pt = {∅}`, `unitSet = {pt}`,
  `univZero = power unitSet`, `truthVal`, `eqv`, propositional
  extensionality; `pt` is never a Kuratowski pair.
- [x] `Derive/Graphs.lean` — `graph`, tagged `app` (`app pt a = pt`),
  `sigmaPairs`, `piSet`; beta on graphs, eta, domain determination,
  universe membership.
- [x] `Derive/Pi.lean` — level-truncated `pi`/`lam` (`pi 0` a truth
  value, `lam 0 = pt`) with the interface laws (`v = 0` fibre
  premises phrased as `v = 0 → … ∈ˢ univZero`).
- [x] `Derive/Omega.lean` — von Neumann naturals: `omega` separated
  from the inductive universe `univChain 1`, `vnat : Nat → V`
  (injective), `mem_omega_iff`; `omega ∈ U` for any universe with
  `univChain 1` as a member.
- [x] `Derive/Natrec.lean` — recursion on `omega` through the
  meta-level `Nat` (each member of `omega` is a unique `vnat k`).
- [x] `Derive/Univ.lean` — the tower `univ 0 = univZero`,
  `univ (n+1) = univChain (n+2)` (shifted so `univChain 1`, the first
  chain member known inductive, is a member of every positive level);
  cumulativity, `univ_mem_univ`, `omega ∈ univ (n+1)`, closure
  transport.
- [x] `Derive/Sigma.lean` — `sigmaSet` (level-0 truth value /
  `sigmaPairs`), `spair := kpair`, classical `sfst`/`ssnd` with `pt`
  defaults; all interface sigma laws.
- [x] `Derive/Quot.lean` — quotients: equivalence closure of the
  `R`-inhabitation relation on `A`, classes by separation, `quotSet`
  (level-0 collapse to `image (fun _ => pt) A`), `quotLift` via a
  choice of representatives; sound/surjective/lift laws.
- [x] `Derive/Choice.lean` — global `schoice` from `Classical.choice`;
  the Jech-form set-level choice function as a *theorem*.
- [x] `Basic.lean` — the interface surface: re-exports the derivation
  and supplies the remaining interface-shaped statements (`natzero`/
  `natsucc`/`natrec_*`, `app_mem`/`app_lam`, `mem_univ_zero`,
  `prop_ext`, …).

## Conventions

- Interface operators are `@[irreducible]` once their laws are proved
  (end of each file): consumers reason only through the laws, exactly
  as they did against the former class projections.
- Interface operators also carry `@[implemented_by]` stubs (unsafe,
  never executed) so that consumer definitions mentioning them stay
  compilable; the stubs have no logical content.
