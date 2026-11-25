# Deriving the operator interface from the `SetTheory` core

Goal: every operator and law of the checker's set-theoretic interface
(surfaced by `ConLeche/SetTheory/Basic.lean`) as a theorem over the
strictly first-order `SetTheory` class (`ConLeche/SetTheory/Core.lean`),
which axiomatizes membership, extensionality, pairing, union, power set,
regularity, the first-order replacement schema over `Formula`
(`ConLeche/SetTheory/Formula.lean`), Jech-form internal choice
(`IsChoiceFn`), and an ω-chain of SGA4 Grothendieck universes
`univChain` (`IsGrothendieck`).  Its consistency strength is that of
ZFC plus `n` inaccessible cardinals for every `n`; it has a model under
the `OmegaInaccessibles` hypothesis of Mario Carneiro, *The Type Theory
of Lean*, master's thesis, Carnegie Mellon University, 2019, §1.2.

## Status

- [x] `Formula.lean` — countable deep embedding `Formula : Nat → Type`
  (`mem`, `eq`, `not`, `and`, `exists_`), `Formula.eval`, `rename`,
  `fcons`/`ftail`/`fappend`, and `ExistsUnique`.
- [x] `Core.lean` — strictly first-order `SetTheory` class
  (extensionality, `upair`, `sUnion`, `power`, `regularity`,
  first-order `replacement`, Jech-form `choice`, `univChain` with
  `IsGrothendieck`), relational Kuratowski helpers (`IsUpair`,
  `IsKPair`, `IsFunGraph`, `IsChoiceFn`), and proof-carrying, zero-junk
  `image` (`HasImage f a`).
- [x] `Derive/Empty.lean` — empty set from `univChain_grothendieck 1`
  transitivity + regularity; `not_mem_self`, `no_two_cycle`,
  `hasImage_empty`.
- [x] `Definable.lean` — `DefRel`, `DefFun`, `DefPredOn`, `DefFunOn`,
  full compositional closure combinators, `hasImage_of_def` via
  `SetTheory.replacement`, and the pure-core `fo_def` tactic macro
  (`solve_by_elim`, zero `import Lean`).
- [x] `Derive/Sep.lean` — proof-carrying, zero-junk `sep` (`HasSep a p`)
  derived from `SetTheory.replacement` via `hasSep_of_def`,
  `DefFun.sep_apply`.
- [x] `Derive/Pair.lean` — singletons, binary union, Kuratowski pairs,
  `kpair_inj`, pair-members-nonempty, bridges to `IsUpair`/`IsKPair`,
  `DefFun` closure.
- [x] `Derive/Universe.lean` — SGA4 `IsGrothendieck` closure laws:
  `transitive`, `upair_mem`, `power_mem`, `mem_of_subset_mem`,
  `sUnion_mem`, `famUnion_mem`, `image_mem` (with `HasGraph` witness),
  `univChain_mem_of_lt`.
- [x] `Derive/Pt.lean` — `pt = {ptTag}`, `unitSet = {pt}`,
  `univZero = power unitSet`, `truthVal`, `eqv`, propositional
  extensionality; `pt` is never a Kuratowski pair; the point laws
  (`pt ∉ univZero`, at most one member, no pair a member); `DefFun`
  closure.
- [x] `Derive/Omega.lean` — von Neumann naturals: `omega` separated
  from the inductive universe `univChain 1`, internal induction
  `omega_ind`, `vsucc_inj`, ordinal laws (`omega_transitive`,
  `omega_cases`, `vsucc_mem_vsucc_of_mem_omega`), and `vnat : Nat → V`.
- [x] `Derive/Graphs.lean` — proof-carrying, zero-junk `graph`
  (`HasGraph A F`), tagged total `app` (`app pt a = pt`),
  `sigmaPairs` (`HasSigmaPairs A B`), `prod`, `piSet`; beta on graphs,
  eta, domain determination, SGA4 `IsGrothendieck` universe membership,
  `DefFun` closure.
- [x] `Derive/Choice.lean` — `choiceFn` from `SetTheory.choice` and
  dependent `piSet_choose` via disjoint Kuratowski-tagged slices.
- [x] `Derive/Natrec.lean` — internal Dedekind recursion on `ω` via
  attempt graphs `IsAttempt`: proof-carrying `omegaRec`, `natrec`, and
  `DefFun` closure (`DefFun.omegaRec_apply`, `DefFun.natrec_apply`).
- [x] `Derive/Tg.lean` — the axiomatic tower `tg 0 = univZero`,
  `tg (n+1) = univChain (n+2)` (shifted so `univChain 1` is a member of
  every positive level); cumulativity, `tg_mem_tg`, `tg_isGrothendieck`,
  `omega ∈ tg (n+1)`.
- [x] `Derive/TypeU.lean` — strict sets and types (task #342):
  `Strict`, `IsTy`, `Fib`; the strict universe `strictU` (truth values
  at `0`, the strict members of `tg n` above: the least fixed points'
  fibre space) and the cumulative universe of types `tyU` (the members
  of `tg n` that are types), with their laws; `pt ∉ ω`.
- [x] `Derive/Univ.lean` — `univ`, what `Sort n` means: `tyU`, with its
  corollaries (cumulativity, size bounds through `tg`) and `univChoiceFn`
  from `choiceFn`.
- [x] `Derive/Sigma.lean` — proof-carrying `sigmaSet` (level-0 truth
  value / `sigmaPairs` with `HasSigmaPairs`), `spair := kpair`,
  classical `sfst`/`ssnd` with `pt` defaults, `unitSetAt`/`unitAt`,
  `sigma_mem_univ`, `DefFun` closure.
- [x] `Derive/Quot.lean` — quotients: bounded first-order intersection
  `QuotRel` over `power (prod A A)`, `qclass` by separation, tagged as
  `kpair ∅ class` above `Prop`, choice-free `quotSet` / `quotClass`,
  `app_eq_of_rel`, `DefRel`/`DefFun` closure.
- [x] `Derive/Lfp.lean`, `Derive/LfpFam.lean`, `Derive/LfpTuple.lean` —
  least pre-fixed sets, families (`famOf`, `lfpFamIn`, extensional
  `DefFun.lfpFamIn_apply`), and `k`-ary tuples (`DefTupleOp`,
  `lfpTuple`, extensional `defFun_lfpTuple`, `HasSep`/`HasGraph`-guarded
  `lfpTuple_induction` and `lfpTuple_induction_of_def`).
- [x] `Basic.lean` — the interface surface: re-exports the derivation
  and supplies the remaining interface-shaped statements (`natzero`/
  `natsucc`/`natrec_*`, `mem_univ_zero`, `prop_ext`, …).

## Conventions

- Every module uses `module` + `@[expose] public section` with zero
  `import Lean`, zero `sorry`, zero `axiom`, and zero `unsafe` stubs.
- Derived set formers (`image`, `sep`, `graph`, `sigmaPairs`, `piSet`,
  `sigmaSet`, `famOf`, `omegaRec`, `lfpTuple`) are proof-carrying and
  zero-junk (`HasImage`, `HasSep`, `HasGraph`, `HasSigmaPairs`,
  `DefTupleOp`), paired with compositional `DefRel`/`DefFun` closure
  lemmas and `fo_def`.
- Interface operators are marked `@[irreducible]` once their laws are
  proved: consumers reason only through the exported laws and `DefFun`
  combinators.
