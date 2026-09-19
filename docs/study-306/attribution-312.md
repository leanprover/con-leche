# Where sokonanoda's speed comes from — the raw tables (task #312)

Measurement study on sokonanoda's own code (`_tmp/ref/sokonanoda`, HEAD `28c03d0`,
history deepened to 108 commits), nanoda_lib `4c544ed` (the arena's `nanoda`), and
con-leche master's shipped binary; 2026-09-19, worktree `agent/attrib-312`.  The
analysis is the `## TASK #312` record in `DESIGN.md`; this file holds the tables.

**Protocol.**  `perf stat -e instructions:u`, ONE run per cell (repeats reproduce
to ≤ 0.1 %: three `init-full` runs of HEAD 47.695 / 47.690 / 47.685 G), single
thread everywhere (`--jobs=1`; `num_threads: 1`; the arena's 4-thread recipe was
also run for `init-full`, `mathlib-prefix`, `grind-ring-5`), `timeout` on every run.
Memory: con-leche under `ulimit -v 16000000` (22 GB at Mathlib scale); the Rust
checkers were first run WITHOUT a limit (sokonanoda reserves 2 GiB stacks per
thread) — after one ablation run (`no-probe` on `init-full`, in a subagent's leg)
reached ~40 GB and had to be killed by hand, every remaining run was put under
`ulimit -v 22000000` (sokonanoda tolerates it: exit 0 on `init-full` at 22 GB and
at 8 GB, and with 4 threads under 22 GB), peak RSS captured with `time -v`, and
Mathlib-scale runs and Rust builds serialised through one `flock`.  Toolchain:
`nix shell nixpkgs#cargo nixpkgs#rustc` (rustc 1.97.1, cargo 1.97.0; `nix shell`
worked at the first try).  sokonanoda HEAD was built twice: plain
`cargo build --release` and the arena's recipe (`-C target-cpu=native` + PGO on
`init-prelude`, `llvm-profdata` from the system); nanoda_lib plain (the arena
builds it plain).  Both Rust checkers read lean4export NDJSON 3.1.x, the format
of every stream here — no conversion was needed.  Streams: the `init-full` and
Mathlib-prefix exports of the #307 record (`lean4export` of `Init` at v4.33.0,
57 977 declarations, 348 MB; the `Mathlib.Order.Filter.Basic` cone at `6f1ef4e5`,
131 902 declarations, 591 MB) and the arena tarball's fixtures.  Scratch:
`_tmp/attrib-312/_tmp/{run,prof,counts,ablate,bisect}`, the three instrumentation
patches `_tmp/soko-instr.patch`, `_tmp/nanoda-instr.patch`,
`_tmp/cl-count-instrumentation.diff` (the last also as branch `agent/count-312`,
commit `8ff7298c`, throwaway), the ablation patch `_tmp/soko-ablate.patch`.

## T1. Local confirmation of the arena (instructions:u, one run per cell, `--jobs=1` / `num_threads: 1`)

| stream | soko plain | **soko PGO** | nanoda | cl `--trusted` | cl `--verified` | arena soko / nanoda / cl | cl-v ÷ soko | nanoda ÷ soko | cl-v ÷ nanoda |
|---|---|---|---|---|---|---|---|---|---|
| `app-lam` | 5.66 | **5.55** | 27.09 | 157.29 | 157.30 | 5.8 / 26 / 167.8 | 28.4× | 4.9× | 5.81× |
| `beta-ladder` | 48.33 | **48.52** | 7.90 | 39.94 | 39.94 | 50.5 / 7.6 / 42.8 | 0.8× | 0.2× | 5.06× |
| `let-ladder` | 0.81 | **0.80** | 4.35 | 8.06 | 8.06 | 0.9 / 4.2 / 8.6 | 10.1× | 5.4× | 1.85× |
| `fueled-chain` | 0.06 | **0.06** | 0.86 | 1.08 | 1.09 | 0.1 / 0.9 / 1.2 | 18.1× | 14.3× | 1.26× |
| `init-prelude` | 0.27 | **0.26** | 0.87 | 3.04 | 3.20 | 0.2 / 0.9 / 3.4 | 12.5× | 3.4× | 3.67× |
| `grind-ring-5` | 2.38 | **2.25** | 8.41 | 21.47 | 22.61 | 2 / 8.3 / 24.3 | 10.0× | 3.7× | 2.69× |
| `magma-list-pair-n21` | 53.18 | **49.55** | 86.85 | 194.28 | 199.17 | 43.5 / 85.6 / 213.8 | 4.0× | 1.8× | 2.29× |
| `magma-list-deep-n36` | 33.49 | **31.48** | 218.98 | 316.51 | 324.55 | 27.9 / 218.7 / 348.2 | 10.3× | 7.0× | 1.48× |
| `init-full` | 47.68 | **45.07** | 230.77 | 567.25 | 585.83 | 38.9 / 206.3 / 579.4 | 13.0× | 5.1× | 2.54× |
| `mathlib-prefix` | 73.29 | **69.33** | 321.83 | 816.82 | 848.52 | – / – / – | 12.2× | 4.6× | 2.64× |

All cells in G = 10⁹ instructions; every run exited 0.  Arena column: `docs/study-306/arena-2026-09-19.txt` (4 threads; `init` there is the v4.29.1 export, 6.06 M lines, against the local v4.33.0 `init-full`, 6.49 M lines, 57 977 declarations).

Thread-count check (same binaries, `num_threads: 4`): soko-pgo-4thr `grind-ring-5` 2.29 G; nanoda-4thr `init-full` 230.56 G; soko-pgo-4thr `init-full` 47.59 G; soko-plain-4thr `init-full` 50.23 G; nanoda-4thr `mathlib-prefix` 320.81 G; soko-pgo-4thr `mathlib-prefix` 72.58 G; soko-plain-4thr `mathlib-prefix` 76.78 G.

Peak RSS (MB, `time -v`): `app-lam` soko 297 / nanoda 2108 / cl 2721; `beta-ladder` soko 1424 / nanoda 607 / cl 752; `let-ladder` soko 89 / nanoda 305 / cl 231; `fueled-chain` soko 59 / nanoda 17 / cl 25; `init-prelude` soko 85 / nanoda 7 / cl 29; `grind-ring-5` soko 450 / nanoda 146 / cl 220; `magma-list-pair-n21` soko 11917 / nanoda 4150 / cl 5345; `magma-list-deep-n36` soko 7873 / nanoda 2507 / cl 7348; `init-full` soko 553 / nanoda 356 / cl 468; `mathlib-prefix` soko 923 / nanoda 618 / cl 914.

Parse-only (`"parse_only": true`) sokonanoda: `init-full` 2.23 G; `mathlib-prefix` 3.95 G; `grind-ring-5` 0.08 G.  nanoda_lib has no `parse_only` option (the key is ignored; the "parse-only" run retired the full count), so its parse share is only known from the profile (T2, ~10 %).

## T2. Profiles of the two Rust checkers (`perf record -e instructions:u`, `--no-children`, self time, top symbols)

**sokonanoda HEAD, plain build, `init-full` (-F 499)**

| % | symbol |
|---|---|
| 15.4 | `TypeChecker::eval` |
| 10.6 | `TypeChecker::intern_frame` |
| 9.9 | `TypeChecker::neutral_app` |
| 8.3 | `TypeChecker::env_extend` |
| 7.8 | `TypeChecker::infer_value` |
| 6.5 | `TypeChecker::eval_no_cache` |
| 4.3 | `TypeChecker::prune_env_cold` |
| 3.2 | `hashbrown rehash<((usize, usize), &sokonanoda::value::Env)…>` |
| 3.0 | `TypeChecker::canonicalize_for_spine` |
| 2.9 | `hashbrown rehash<((usize, sokonanoda::util::ExprPtr), &sokonanoda::value::Env…>` |
| 2.0 | `TypeChecker::unify_general::<true>` |
| 1.8 | `__memmove_avx512_unaligned_erms` |
| 1.6 | `hashbrown rehash<&sokonanoda::value::Env…>` |
| 1.5 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::do_app` |
| 1.5 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::run_over` |
| 1.4 | `TypeChecker::apply` |
| 1.1 | `TypeChecker::unfold_value_go` |
| 1.0 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::other_line` |
| 0.9 | `<sokonanoda::util::LevelInterner>::get` |
| 0.9 | `TypeChecker::const_head_type` |
| 0.8 | `TypeChecker::sig_of` |
| 0.8 | `TypeChecker::unify_no_cache::<true>` |

**sokonanoda, `grind-ring-5` (-F 199)**

| % | symbol |
|---|---|
| 15.0 | `TypeChecker::eval` |
| 12.3 | `TypeChecker::env_extend` |
| 10.4 | `TypeChecker::eval_no_cache` |
| 10.3 | `TypeChecker::intern_frame` |
| 9.9 | `TypeChecker::neutral_app` |
| 5.7 | `TypeChecker::spine_apps` |
| 5.2 | `hashbrown rehash<((usize, usize), &sokonanoda::value::Env)…>` |
| 3.7 | `TypeChecker::infer_value` |
| 3.6 | `TypeChecker::apply` |
| 3.0 | `TypeChecker::apply_closure` |
| 2.7 | `TypeChecker::prune_env_cold` |
| 2.4 | `hashbrown rehash<((usize, sokonanoda::util::ExprPtr), &sokonanoda::value::Env…>` |
| 1.8 | `hashbrown rehash<&sokonanoda::value::Env…>` |
| 1.7 | `TypeChecker::global_key` |
| 1.6 | `_mi_theap_realloc_zero` |
| 1.5 | `TypeChecker::iota_value` |
| 1.4 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::other_line` |
| 0.9 | `TypeChecker::value_has_free_bvar` |
| 0.9 | `<sokonanoda::util::TcCtx>::simplify` |
| 0.8 | `TypeChecker::unify_no_cache::<true>` |

**sokonanoda, Mathlib prefix (-F 199)**

| % | symbol |
|---|---|
| 16.1 | `TypeChecker::eval` |
| 9.0 | `TypeChecker::neutral_app` |
| 8.7 | `TypeChecker::intern_frame` |
| 8.2 | `TypeChecker::infer_value` |
| 7.6 | `TypeChecker::eval_no_cache` |
| 7.5 | `TypeChecker::env_extend` |
| 4.3 | `TypeChecker::prune_env_cold` |
| 3.2 | `TypeChecker::canonicalize_for_spine` |
| 2.6 | `hashbrown rehash<((usize, sokonanoda::util::ExprPtr), &sokonanoda::value::Env…>` |
| 2.6 | `__memmove_avx512_unaligned_erms` |
| 2.0 | `hashbrown rehash<((usize, usize), &sokonanoda::value::Env)…>` |
| 1.7 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::run_over` |
| 1.7 | `TypeChecker::apply` |
| 1.6 | `hashbrown rehash<&sokonanoda::value::Env…>` |
| 1.5 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::other_line` |
| 1.5 | `TypeChecker::unify_general::<true>` |
| 1.2 | `<sokonanoda::parser::Parser<std::io::buffered::bufreader::BufReader<std::io::stdio::Stdin>>>::do_app` |
| 1.0 | `TypeChecker::unfold_value_go` |
| 1.0 | `TypeChecker::store_lookup` |
| 0.9 | `TypeChecker::const_head_type` |
| 0.9 | `mi_malloc_aligned` |
| 0.9 | `<hashbrown::map::HashMap<(usize, usize), (), core::hash::BuildHasherDefault<rustc_hash::FxHasher>>>::insert` |
| 0.8 | `<sokonanoda::value::Spine>::to_vec` |

**nanoda `4c544ed`, `init-full` (-F 499)**

| % | symbol |
|---|---|
| 20.6 | `util::TcCtx::alloc_expr` |
| 9.1 | `util::TcCtx::inst_aux` |
| 7.2 | `<indexmap::map::IndexMap<nanoda_lib::expr::Expr, (), core::hash::BuildHasherDefault<nanoda_lib::unique_hasher::UniqueHas` |
| 6.9 | `util::TcCtx::mk_app` |
| 6.4 | `util::TcCtx::unfold_apps` |
| 4.9 | `tc::TypeChecker::whnf_no_unfolding_aux` |
| 3.3 | `<serde::private::de::content::ContentVisitor as serde_core::de::DeserializeSeed>::deserialize::<&mut serde_json::de::Des` |
| 3.2 | `serde_json::de::from_trait::<serde_json::read::StrRead, nanoda_lib::parser::ExportJsonObject>` |
| 3.0 | `hashbrown rehash<usize…>` |
| 3.0 | `util::TcCtx::subst_aux` |
| 2.7 | `<hashbrown::map::HashMap<(nanoda_lib::util::Ptr<&nanoda_lib::expr::Expr>, u16), nanoda_lib::util::Ptr<&nanoda_lib::expr:` |
| 2.7 | `tc::TypeChecker::infer` |
| 2.3 | `<hashbrown::map::HashMap<nanoda_lib::util::Ptr<&nanoda_lib::expr::Expr>, nanoda_lib::util::Ptr<&nanoda_lib::expr::Expr>,` |
| 1.8 | `<<nanoda_lib::parser::ExportJsonVal as serde_core::de::Deserialize>::deserialize::__Visitor as serde_core::de::Visitor>:` |
| 1.6 | `<hashbrown::map::HashMap<(nanoda_lib::util::Ptr<&nanoda_lib::expr::Expr>, nanoda_lib::util::Ptr<&alloc::sync::Arc<[nanod` |
| 1.4 | `<indexmap::inner::Core<nanoda_lib::util::Ptr<&nanoda_lib::name::Name>, nanoda_lib::env::Declar>>::get_index_of::<nanoda_` |
| 1.2 | `tc::TypeChecker::unfold_def` |
| 1.1 | `_int_malloc` |
| 1.1 | `malloc` |
| 0.8 | `cfree@GLIBC_2.2.5` |

Bucket sums (`_tmp/prof/bucket.py`, symbol-name regexes; "interning" = `intern_frame`, `env_extend`, `neutral_app`, `*_hc`, `canonicalize`, `prune*`, `alloc_expr`, `mk_*`; "hash-tables" = the `hashbrown`/`indexmap` symbols not inside those; "eval" = `eval*`, `apply*`, `force*`, `unfold*`, `whnf*`, `iota*`; "alloc" = malloc/free/memmove):

| profile | interning | hash-tables | eval | conv | infer | subst walks | parser | alloc | other |
|---|---|---|---|---|---|---|---|---|---|
| sokonanoda `init-full` | 38.7 | 8.4 | 26.4 | 5.6 | 8.7 | 0.0 | 4.2 | 3.3 | 3.3 |
| sokonanoda `grind-ring-5` | 37.5 | 9.4 | 34.2 | 6.5 | 3.7 | 0.0 | 1.4 | 2.4 | 4.9 |
| sokonanoda Mathlib prefix | 35.6 | 7.3 | 28.5 | 3.8 | 9.1 | 0.0 | 4.7 | 4.8 | 4.7 |
| nanoda `init-full` | 29.1 | 19.8 | 13.3 | 1.1 | 2.7 | 12.7 | 10.1 | 6.8 | 2.7 |

## T4. sokonanoda step counters (`_tmp/soko-instr.patch`, 168 atomic counters, +1.7–2.0 % instructions; `SOKO_COUNTS=1`, single thread)

| counter | `app-lam` | `beta-ladder` | `let-ladder` | `fueled-chain` | `init-prelude` | `grind-ring-5` | `magma-pair-n21` | `magma-deep-n36` | `init-full` | `mathlib-prefix` |
|---|---|---|---|---|---|---|---|---|---|---|
| β (closure applied: `apply` + unrolled `eval` App + `apply_many`) | 110 | 2 081 | 83 | 3 787 | 31 511 | 1 226 637 | 30 678 845 | 27 582 191 | 15 903 301 | 21 170 339 |
| closure bodies opened (`apply_closure`: fresh bvar OR Pi-codomain instantiation) | 915 | 126 434 | 454 | 37 593 | 86 724 | 329 445 | 98 007 | 37 647 | 13 906 018 | 22 080 267 |
| δ (`Unfold.forced` computed) | 11 | 4 | 4 | 522 | 3 796 | 114 069 | 3 066 173 | 2 611 965 | 2 454 042 | 3 297 158 |
| δ memo hit (`forced` already set) | 0 | 0 | 0 | 28 | 877 | 67 331 | 1 883 | 7 558 065 | 439 480 | 679 805 |
| definition bodies evaluated, once per (name, levels) | 9 | 2 | 2 | 94 | 1 166 | 2 679 | 253 | 464 | 155 821 | 326 434 |
| ι: recursor rule fired | 3 | 3 | 3 | 45 | 1 222 | 141 326 | 816 979 | 851 293 | 546 435 | 711 264 |
| ι: `Nat.rec` on a literal | 0 | 0 | 0 | 0 | 206 | 22 124 | 204 267 | 845 817 | 79 197 | 102 994 |
| ι: projection of a constructor | 0 | 0 | 0 | 109 | 775 | 4 302 | 572 | 6 755 | 307 041 | 446 862 |
| Nat literal ops | 0 | 2 000 | 0 | 4 | 372 | 16 854 | 195 400 | 11 721 | 26 766 | 61 779 |
| K-rescues | 0 | 0 | 0 | 0 | 90 | 24 | 4 | 4 | 556 | 3 478 |
| struct-η rescues | 0 | 0 | 0 | 0 | 417 | 412 | 0 | 2 | 20 869 | 33 337 |
| quotient ι | 0 | 0 | 0 | 2 | 0 | 2 | 0 | 0 | 178 | 311 |
| ι memo hits | 0 | 0 | 0 | 0 | 445 | 128 824 | 9 | 5 034 984 | 77 425 | 142 847 |
| `eval` entries (cache misses: real evaluation) | 2 491 | 9 563 | 1 491 | 48 309 | 287 896 | 2 516 505 | 83 171 211 | 33 568 145 | 50 885 791 | 80 708 364 |
| `eval` closed-term cache hits | 20 550 | 264 283 | 12 351 | 23 741 | 69 156 | 675 735 | 2 991 297 | 75 504 | 14 152 296 | 20 982 921 |
| `eval` (pruned env, term) cache hits | 208 | 124 | 125 | 32 707 | 46 134 | 750 072 | 9 246 462 | 15 288 869 | 19 812 963 | 27 523 651 |
| `unify` entries | 17 010 | 6 534 | 10 548 | 43 147 | 104 910 | 498 797 | 18 849 | 42 908 | 19 453 642 | 30 429 831 |
|   of which `ptr::eq` | 8 637 | 4 331 | 10 337 | 22 118 | 63 153 | 252 856 | 11 660 | 26 282 | 9 815 600 | 15 541 558 |
|   pos-cache hits | 4 027 | 14 | 15 | 5 354 | 3 379 | 29 771 | 536 | 1 117 | 1 488 518 | 2 185 533 |
|   neg-cache hits | 0 | 0 | 0 | 0 | 1 | 284 | 1 | 3 | 22 032 | 33 817 |
|   cacheable misses | 4 237 | 129 | 135 | 6 655 | 25 273 | 127 934 | 3 927 | 6 971 | 3 953 387 | 6 118 585 |
|   Sort/Sort | 103 | 54 | 55 | 8 341 | 11 444 | 76 829 | 2 261 | 7 745 | 3 218 430 | 4 939 725 |
|   same rigid head (ctor/ind/axiom) | 6 | 2 006 | 6 | 671 | 1 560 | 10 118 | 382 | 648 | 892 505 | 1 513 116 |
|   Pi/Pi opened | 261 | 105 | 110 | 4 560 | 20 868 | 30 275 | 2 792 | 5 035 | 960 558 | 1 954 467 |
|   Pi/Pi pointer fast path | 3 936 | 0 | 0 | 2 | 36 | 12 | 3 | 5 | 444 | 2 535 |
|   Lam/Lam opened | 30 | 19 | 20 | 758 | 1 214 | 5 253 | 363 | 486 | 337 075 | 578 217 |
|   Unfold/Unfold same head | 1 | 0 | 0 | 998 | 194 | 3 963 | 93 | 204 | 406 276 | 587 478 |
|     probe decided equal | 1 | 0 | 0 | 465 | 152 | 2 659 | 59 | 160 | 209 994 | 293 658 |
|     probe decided unequal | 0 | 0 | 0 | 4 | 22 | 233 | 17 | 21 | 11 090 | 14 325 |
|     unfold both | 0 | 0 | 0 | 86 | 72 | 1 411 | 46 | 74 | 91 227 | 132 684 |
|   Unfold/Unfold different heads | 0 | 0 | 0 | 182 | 129 | 5 479 | 82 | 172 | 390 293 | 500 714 |
|     unfold left | 0 | 0 | 0 | 88 | 51 | 2 289 | 29 | 77 | 111 713 | 148 089 |
|     unfold right | 0 | 0 | 0 | 12 | 30 | 2 121 | 26 | 44 | 207 237 | 248 532 |
|   Unfold vs other (L) | 4 | 2 | 2 | 61 | 1 315 | 29 214 | 237 | 456 | 522 608 | 763 788 |
|   Unfold vs other (R) | 3 | 1 | 1 | 58 | 800 | 7 484 | 234 | 407 | 939 822 | 1 208 112 |
|   rec/quot vs other (L) | 2 | 2 | 2 | 12 | 520 | 43 095 | 44 | 78 | 91 500 | 132 904 |
|   rec/quot vs other (R) | 0 | 0 | 0 | 16 | 163 | 1 450 | 50 | 75 | 249 256 | 308 139 |
|   proof irrelevance tried | 96 | 57 | 60 | 787 | 6 536 | 94 277 | 1 312 | 2 360 | 2 507 459 | 3 433 170 |
|     vetoed statically | 9 | 6 | 7 | 303 | 1 672 | 87 063 | 553 | 1 001 | 2 227 421 | 2 890 057 |
|     succeeded | 0 | 0 | 0 | 2 | 8 | 30 | 11 | 14 | 1 784 | 2 682 |
|   λ-η | 0 | 0 | 0 | 2 | 0 | 21 | 0 | 0 | 1 657 | 4 390 |
|   struct-η tried | 0 | 0 | 0 | 4 | 32 | 2 057 | 24 | 37 | 155 381 | 211 107 |
|     succeeded | 0 | 0 | 0 | 0 | 3 | 14 | 0 | 0 | 1 213 | 2 060 |
|   final `false` | 0 | 0 | 0 | 4 | 29 | 2 043 | 24 | 37 | 154 433 | 210 779 |
| `unify_spine` entries | 9 | 2 009 | 9 | 3 685 | 3 643 | 34 683 | 1 387 | 1 744 | 3 253 599 | 5 098 871 |
|   spine `ptr::eq` | 6 | 2 006 | 6 | 1 206 | 1 622 | 12 504 | 440 | 738 | 1 139 253 | 1 882 900 |
|   positions skipped by `Sig` | 0 | 0 | 0 | 3 | 284 | 353 | 278 | 208 | 33 056 | 48 503 |
| `infer_value` Check | 33 166 | 14 744 | 18 768 | 43 649 | 135 053 | 474 336 | 23 376 | 54 737 | 16 983 661 | 27 890 761 |
| `infer_value` InferOnly | 181 | 252 046 | 84 | 3 617 | 14 113 | 23 670 | 2 270 | 3 859 | 707 530 | 1 458 275 |
| type cache hits | 4 229 | 109 | 2 117 | 14 942 | 22 467 | 120 049 | 3 740 | 10 227 | 4 793 488 | 7 054 617 |
| type cache misses | 12 467 | 258 200 | 6 308 | 11 472 | 49 709 | 128 390 | 8 148 | 17 554 | 4 266 730 | 7 536 462 |
| `env_extend` hits | 502 | 2 300 | 308 | 32 009 | 59 128 | 718 862 | 4 996 484 | 10 282 150 | 16 210 802 | 23 102 984 |
| `env_extend` new | 4 843 | 128 409 | 2 430 | 14 860 | 88 983 | 886 877 | 25 784 756 | 17 351 100 | 14 677 041 | 22 495 434 |
| `intern_frame` hits | 256 | 111 | 165 | 11 378 | 39 805 | 437 752 | 8 799 220 | 12 698 968 | 9 102 506 | 13 221 197 |
| `intern_frame` new | 694 | 2 691 | 483 | 17 766 | 97 977 | 1 023 909 | 39 286 784 | 19 277 544 | 18 588 017 | 28 139 867 |
| `neutral_app` hits | 226 | 150 | 141 | 10 880 | 41 701 | 522 467 | 12 597 835 | 3 552 500 | 14 488 279 | 20 989 201 |
| `neutral_app` new | 278 | 198 | 182 | 10 040 | 50 066 | 921 835 | 18 693 939 | 16 310 249 | 16 027 550 | 23 509 939 |
| `key_env` prunes | 2 471 | 8 078 | 1 504 | 90 349 | 303 204 | 2 629 217 | 69 299 495 | 40 883 078 | 60 617 459 | 91 374 385 |
| whnf store lookups | 21 079 | 134 719 | 10 690 | 35 187 | 113 930 | 597 641 | 1 432 589 | 83 701 | 15 830 156 | 25 456 513 |
|   hits (128-bit verified) | 3 | 0 | 0 | 120 | 400 | 68 342 | 388 972 | 12 959 | 336 271 | 468 986 |
|   admissions | 1 | 0 | 0 | 6 | 54 | 4 903 | 5 094 | 93 | 23 762 | 31 028 |
| arena sessions | 2 | 2 | 2 | 1 | 2 | 6 | 2 | 2 | 271 | 427 |
| declarations checked | 34 | 20 | 22 | 194 | 2 059 | 2 432 | 324 | 588 | 59 433 | 137 584 |

Zero on every stream: `unify_entries_lax`, `unify_cold_nonrigid` (the `RIGID=false` `unify` is never instantiated — dead code), `unfold_const_hit` (the per-(name, levels) map is written and never hit; the sharing is the `Unfold` node's `OnceCell` via `const_head_value_cache`), `probe_budget_exhausted`, `spine_probe_exhausted`, `conv_cache_negprobe_*` (the 2 048-step probe budget never fires), `store_lookup_verify_fail`, `lam_hc_hit`, `pi_hc_hit`, `delta_forced_no_body`.

## T5. con-leche shipped core, step counters (throwaway counting build on branch `agent/count-312`, commit `8ff7298c`; `--verified --jobs=1`; check + install phase totals)

| counter | `app-lam` | `beta-ladder` | `let-ladder` | `fueled-chain` | `init-prelude` | `grind-ring-5` | `magma-pair-n21` | `magma-deep-n36` | `init-full` | `mathlib-prefix` |
|---|---|---|---|---|---|---|---|---|---|---|
| β binders consumed | 121 | 2 115 | 115 | 4 655 | 45 101 | 1 702 320 | 26 287 649 | 33 368 664 | 36 582 525 | 44 275 979 |
| β peel groups (= bulk substitutions) | 60 | 2 054 | 54 | 2 209 | 16 843 | 555 012 | 9 642 498 | 11 139 264 | 11 907 440 | 14 440 094 |
|   β certificates skipped by the `.never` gate | 121 | 2 115 | 115 | 4 555 | 44 511 | 1 699 366 | 26 287 633 | 33 368 514 | 36 558 170 | 44 181 837 |
| δ unfoldings performed | 21 | 14 | 14 | 1 188 | 6 812 | 165 366 | 2 871 979 | 10 161 839 | 7 293 473 | 8 811 707 |
|   in the whnf loop | 8 | 4 | 4 | 554 | 2 146 | 98 400 | 2 870 548 | 10 158 036 | 3 405 327 | 4 076 205 |
|   lazy-δ: only left is a definition | 7 | 7 | 7 | 61 | 1 846 | 11 930 | 419 | 795 | 1 622 672 | 1 919 030 |
|   lazy-δ: only right | 6 | 3 | 3 | 79 | 1 931 | 35 528 | 491 | 1 209 | 943 696 | 1 194 868 |
|   lazy-δ: by hint, left | 0 | 0 | 0 | 9 | 107 | 3 530 | 70 | 236 | 341 878 | 393 596 |
|   lazy-δ: by hint, right | 0 | 0 | 0 | 97 | 178 | 3 358 | 103 | 287 | 149 138 | 200 320 |
|   lazy-δ: both (equal hints) | 0 | 0 | 0 | 192 | 284 | 6 216 | 161 | 601 | 412 555 | 509 814 |
|   lazy-δ: same-head spine compare failed → both | 0 | 0 | 0 | 2 | 18 | 94 | 13 | 37 | 2 826 | 4 030 |
|   of which `HAdd.hAdd` | 0 | 0 | 0 | 0 | 87 | 4 524 | 54 | 5 550 | 267 697 | 312 451 |
| `constValAt` memo hits | 9 | 8 | 8 | 990 | 3 886 | 149 150 | 2 871 171 | 10 160 251 | 6 432 839 | 7 610 123 |
| `constValAt` misses (bodies instantiated) | 12 | 6 | 6 | 198 | 2 926 | 16 216 | 808 | 1 588 | 860 634 | 1 201 584 |
| ι: recursor rule fired | 7 | 7 | 7 | 61 | 2 360 | 195 842 | 1 021 547 | 1 697 915 | 1 581 099 | 1 894 622 |
|   of which `Quot.lift`/`Quot.ind` | 0 | 0 | 0 | 2 | 0 | 2 | 0 | 0 | 211 | 350 |
| ι: projection of a constructor | 2 | 2 | 2 | 481 | 1 120 | 24 913 | 11 233 | 44 661 | 1 757 654 | 2 106 191 |
| K-rescues | 0 | 0 | 0 | 0 | 49 | 19 | 2 | 2 | 280 | 2 062 |
| struct-η rescues | 0 | 0 | 0 | 0 | 9 | 52 | 0 | 4 | 2 580 | 4 577 |
| Nat `succ` folds | 0 | 0 | 0 | 0 | 148 | 925 | 52 | 106 | 31 720 | 38 304 |
| Nat binary ops | 0 | 2 000 | 0 | 1 | 278 | 19 131 | 195 421 | 11 804 | 159 974 | 218 660 |
| `whnfCore` steps | 450 | 6 316 | 336 | 10 171 | 78 997 | 1 167 369 | 16 603 676 | 15 571 334 | 29 434 303 | 37 820 806 |
|   memo hits | 81 | 4 073 | 73 | 5 065 | 25 664 | 933 414 | 11 671 263 | 21 280 555 | 22 868 717 | 27 733 123 |
|   bodies run | 381 | 4 253 | 273 | 7 420 | 58 674 | 391 602 | 5 928 398 | 2 689 494 | 14 188 110 | 19 379 899 |
| `whnf` steps | 211 | 4 105 | 129 | 2 227 | 20 937 | 209 913 | 3 877 322 | 10 205 708 | 5 434 218 | 7 034 777 |
|   memo hits | 8 190 | 10 106 | 2 125 | 6 130 | 31 714 | 240 858 | 620 586 | 1 746 980 | 3 493 545 | 5 367 931 |
|   bodies run | 203 | 2 102 | 125 | 1 672 | 18 379 | 92 341 | 811 306 | 35 799 | 1 890 127 | 2 772 197 |
| `infer` bodies (full grade) | 16 453 | 8 250 | 4 303 | 10 024 | 64 107 | 168 215 | 11 904 | 28 022 | 5 282 547 | 9 725 996 |
| `infer` bodies (io grade) | 64 | 4 033 | 37 | 1 633 | 10 601 | 20 994 | 2 655 | 4 298 | 419 447 | 928 336 |
|   full-grade memo hits | 16 232 | 6 141 | 12 158 | 23 603 | 55 347 | 281 359 | 13 250 | 41 780 | 9 245 371 | 14 078 056 |
|   full-grade memo misses | 16 414 | 8 231 | 4 282 | 9 672 | 59 436 | 160 292 | 10 961 | 26 415 | 5 111 196 | 9 332 221 |
| `defeq` steps (past the pair memo) | 172 | 114 | 126 | 4 568 | 33 363 | 154 610 | 7 516 | 16 829 | 7 068 899 | 10 192 756 |
|   pair memo hits | 16 133 | 6 097 | 10 104 | 22 271 | 44 681 | 285 378 | 12 013 | 39 173 | 10 142 511 | 15 120 181 |
|   `beq` early exit | 106 | 55 | 69 | 2 003 | 17 499 | 49 349 | 3 225 | 6 978 | 1 889 311 | 3 246 767 |
|   equal after whnfCore | 18 | 15 | 15 | 671 | 3 552 | 14 260 | 1 055 | 2 293 | 384 140 | 672 975 |
|   proof-irrelevance probes | 11 | 10 | 8 | 771 | 2 705 | 21 418 | 930 | 2 311 | 1 253 928 | 1 735 040 |
|     decided | 0 | 0 | 0 | 0 | 29 | 75 | 20 | 37 | 10 266 | 14 239 |
|     reached inference | 0 | 0 | 0 | 0 | 46 | 98 | 26 | 54 | 1 280 | 1 985 |
|   same-head spine compares | 0 | 0 | 0 | 107 | 208 | 3 173 | 123 | 488 | 269 450 | 330 153 |
|     succeeded | 0 | 0 | 0 | 105 | 190 | 3 079 | 110 | 451 | 266 624 | 326 123 |
|   Sort/Sort | 4 | 4 | 4 | 57 | 875 | 1 244 | 119 | 227 | 43 973 | 95 902 |
|   ∀/∀ | 27 | 24 | 24 | 618 | 5 545 | 12 257 | 1 218 | 2 366 | 226 609 | 561 132 |
|   λ/λ | 0 | 0 | 0 | 173 | 134 | 940 | 66 | 199 | 22 763 | 41 328 |
|   app/app congruence | 4 | 5 | 4 | 475 | 1 011 | 10 970 | 382 | 949 | 667 578 | 874 182 |
|   η tried | 0 | 0 | 0 | 2 | 0 | 18 | 0 | 0 | 1 054 | 2 121 |
|   struct-η tried | 0 | 0 | 0 | 2 | 25 | 81 | 10 | 11 | 3 292 | 4 899 |
|     succeeded | 0 | 0 | 0 | 0 | 3 | 0 | 0 | 0 | 830 | 1 293 |
|   unit-like tried | 0 | 0 | 0 | 2 | 43 | 136 | 15 | 33 | 3 565 | 6 027 |
|   final false | 0 | 0 | 0 | 2 | 43 | 144 | 15 | 34 | 4 485 | 7 099 |
| `instantiate1` calls | 65 | 2 050 | 2 051 | 2 111 | 13 232 | 31 383 | 3 167 | 6 301 | 570 012 | 1 370 993 |
| bulk `instantiateList` calls | 60 | 2 054 | 54 | 2 315 | 17 754 | 558 623 | 9 642 530 | 11 139 456 | 11 948 985 | 14 575 103 |
|   memo hits | 0 | 0 | 0 | 539 | 1 136 | 152 004 | 856 458 | 71 837 | 1 738 399 | 2 078 729 |
|   memo misses (walks) | 52 | 2 046 | 46 | 1 426 | 14 807 | 397 828 | 8 776 125 | 10 221 284 | 9 839 629 | 11 955 588 |
| `instListRev` calls (telescope openings, unmemoised) | 32 695 | 16 411 | 12 481 | 34 497 | 132 073 | 467 628 | 27 528 | 73 068 | 15 016 954 | 24 877 740 |
| `annotate` memo hits | 16 198 | 6 126 | 8 144 | 11 796 | 46 848 | 194 645 | 10 416 | 27 653 | 6 883 641 | 10 826 985 |
| `annotate` memo misses | 24 484 | 10 286 | 6 337 | 15 151 | 88 257 | 304 852 | 18 164 | 42 874 | 11 069 694 | 18 672 593 |

`--trusted` (init-full / grind-ring-5): β binders 36 530 256 / 1 698 520 (0.999× verified), io-grade infer bodies 53 767 / 2 742 (0.13×), `HAdd.hAdd` unfolds 267 416 / **4 487** (the #307/#310 figure reproduces exactly on the trusted core; the verified core unfolds it 4 524 times), everything else within 1 %.

## T6. nanoda `4c544ed`, step counters (`_tmp/nanoda-instr.patch`, 101 counters, +0.9–1.3 % instructions; single thread)

| counter | `app-lam` | `beta-ladder` | `let-ladder` | `fueled-chain` | `init-prelude` | `grind-ring-5` | `magma-pair-n21` | `magma-deep-n36` | `init-full` | `mathlib-prefix` |
|---|---|---|---|---|---|---|---|---|---|---|
| β binders consumed | 51 | 2 043 | 43 | 79 230 | 35 142 | 1 512 063 | 26 691 741 | 34 985 140 | 37 456 895 | 45 553 055 |
| β peels (one `inst` each) | 34 | 2 026 | 26 | 38 204 | 12 528 | 438 044 | 9 212 661 | 9 415 307 | 11 730 307 | 14 360 570 |
| ζ | 0 | 0 | 0 | 3 158 | 0 | 853 | 0 | 5 439 | 21 440 | 31 651 |
| `inst` calls (substitution walks) | 64 988 | 16 654 | 14 680 | 145 243 | 146 275 | 987 005 | 9 237 439 | 9 479 068 | 30 215 632 | 45 040 163 |
|   nodes visited | 80 054 943 | 24 021 998 | 14 025 017 | 1 593 213 | 650 703 | 10 671 633 | 158 082 135 | 227 015 631 | 270 591 642 | 364 089 309 |
| δ unfoldings | 12 | 4 | 4 | 17 229 | 5 404 | 161 101 | 2 871 272 | 10 158 784 | 7 149 236 | 8 695 215 |
|   in the whnf loop | 4 | 1 | 1 | 7 115 | 2 568 | 120 067 | 2 870 417 | 10 157 215 | 3 425 832 | 4 124 816 |
|   lazy-δ both | 0 | 0 | 0 | 4 940 | 143 | 6 125 | 100 | 188 | 434 308 | 563 989 |
|   of which `HAdd.hAdd` | 0 | 0 | 0 | 0 | 14 | 4 200 | 25 | 5 286 | 256 740 | 302 033 |
| ι: recursor rule fired | 3 | 3 | 3 | 46 | 1 757 | 169 519 | 1 021 322 | 1 697 231 | 1 664 509 | 1 982 004 |
|   major was a Nat literal | 0 | 0 | 0 | 0 | 438 | 22 941 | 204 316 | 845 905 | 124 384 | 149 996 |
| ι: projection of a constructor | 0 | 0 | 0 | 8 956 | 814 | 24 269 | 215 295 | 883 043 | 1 802 834 | 2 177 526 |
| K | 0 | 0 | 0 | 0 | 45 | 19 | 2 | 2 | 505 | 2 164 |
| quotient | 0 | 0 | 0 | 2 | 0 | 2 | 0 | 0 | 274 | 437 |
| Nat literal ops | 0 | 2 000 | 0 | 1 | 341 | 19 693 | 195 444 | 11 803 | 173 411 | 234 920 |
| `whnf` entries | 4 345 | 6 200 | 2 215 | 34 098 | 40 418 | 319 879 | 1 633 433 | 2 616 538 | 7 106 575 | 10 303 223 |
|   cache hits | 4 123 | 2 083 | 2 088 | 28 266 | 22 973 | 208 395 | 822 472 | 1 743 645 | 5 129 503 | 7 361 612 |
| `whnf_core` entries | 321 | 6 194 | 200 | 124 568 | 48 359 | 1 046 200 | 14 330 656 | 22 217 546 | 32 882 134 | 41 634 509 |
|   cache hits | 0 | 0 | 0 | 4 687 | 464 | 42 842 | 39 | 7 561 575 | 1 132 109 | 1 331 637 |
| `def_eq` entries | 32 403 | 6 284 | 10 287 | 85 337 | 65 351 | 389 411 | 13 377 | 39 766 | 15 437 771 | 23 557 382 |
|   pointer-equal | 24 348 | 6 238 | 10 242 | 60 786 | 57 112 | 328 693 | 11 472 | 34 820 | 12 214 068 | 18 820 024 |
|   eq-cache hits | 4 | 2 | 2 | 3 093 | 687 | 14 659 | 153 | 408 | 818 921 | 1 105 767 |
|   fail-cache hits | 0 | 0 | 0 | 0 | 1 | 69 | 1 | 1 | 3 721 | 5 280 |
|   proof irrelevance tried | 10 | 7 | 5 | 11 497 | 2 051 | 26 674 | 723 | 2 693 | 1 895 918 | 2 554 902 |
|     succeeded | 0 | 0 | 0 | 0 | 7 | 55 | 9 | 12 | 11 386 | 16 675 |
|   lazy-δ decided | 7 | 3 | 2 | 3 624 | 1 129 | 7 912 | 272 | 550 | 532 079 | 762 869 |
|   lazy-δ exhausted | 3 | 4 | 3 | 7 873 | 915 | 18 707 | 442 | 2 131 | 1 352 453 | 1 775 358 |
|   app congruence ok | 3 | 4 | 3 | 2 961 | 470 | 10 119 | 136 | 1 583 | 669 939 | 915 526 |
|   final false | 0 | 0 | 0 | 2 | 14 | 189 | 14 | 18 | 14 038 | 18 967 |
| same-head const-app compares | 0 | 0 | 0 | 3 501 | 69 | 2 712 | 57 | 116 | 279 840 | 358 766 |
|   succeeded | 0 | 0 | 0 | 3 499 | 59 | 2 633 | 47 | 105 | 276 165 | 353 651 |
| `infer` entries | 32 657 | 14 430 | 18 449 | 81 772 | 107 906 | 501 481 | 20 366 | 53 749 | 19 739 338 | 30 653 145 |
|   cache misses | 16 445 | 8 278 | 6 297 | 25 791 | 59 687 | 184 668 | 10 547 | 23 188 | 6 638 302 | 11 516 419 |
| `alloc_expr` (interner) calls | 40 013 532 | 12 014 274 | 6 007 297 | 1 241 054 | 703 019 | 8 394 290 | 113 715 051 | 213 847 349 | 275 601 077 | 372 002 856 |
|   new nodes | 40 007 414 | 12 002 925 | 6 001 922 | 220 029 | 272 563 | 3 332 689 | 64 768 799 | 45 889 503 | 87 265 226 | 117 583 865 |
| `mk_app` calls | 31 997 423 | 8 009 053 | 4 007 019 | 1 008 185 | 391 388 | 6 883 968 | 101 888 606 | 192 391 799 | 219 918 558 | 289 398 191 |

## T7. The decomposition (from `_tmp/run/decomp.py`)

| stream | cl β | soko β | β ratio | cl δ | soko δ | δ ratio | cl ι+proj+nat | soko ι+proj+nat | ι ratio | cl defeq steps (past beq/memo) | soko unify (past ptr-eq) | ratio | cl infer bodies | soko infer_value | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `app-lam` | 121 | 110 | 1.10× | 21 | 11 | 1.91× | 9 | 3 | 3.00× | 172 | 8 373 | 0.02× | 16 517 | 33 347 | 0.50× |
| `beta-ladder` | 2 115 | 2 081 | 1.02× | 14 | 4 | 3.50× | 2 009 | 2 003 | 1.00× | 114 | 2 203 | 0.05× | 12 283 | 266 790 | 0.05× |
| `let-ladder` | 115 | 83 | 1.39× | 14 | 4 | 3.50× | 9 | 3 | 3.00× | 126 | 211 | 0.60× | 4 340 | 18 852 | 0.23× |
| `fueled-chain` | 4 655 | 3 787 | 1.23× | 1 188 | 522 | 2.28× | 545 | 160 | 3.41× | 4 568 | 21 029 | 0.22× | 11 657 | 47 266 | 0.25× |
| `init-prelude` | 45 101 | 31 511 | 1.43× | 6 812 | 3 796 | 1.79× | 3 964 | 3 082 | 1.29× | 33 363 | 41 757 | 0.80× | 74 708 | 149 166 | 0.50× |
| `grind-ring-5` | 1 702 320 | 1 226 637 | 1.39× | 165 366 | 114 069 | 1.45× | 240 884 | 185 044 | 1.30× | 154 610 | 245 941 | 0.63× | 189 209 | 498 006 | 0.38× |
| `magma-list-pair-n21` | 26 287 649 | 30 678 845 | 0.86× | 2 871 979 | 3 066 173 | 0.94× | 1 228 255 | 1 217 222 | 1.01× | 7 516 | 7 189 | 1.05× | 14 559 | 25 646 | 0.57× |
| `magma-list-deep-n36` | 33 368 664 | 27 582 191 | 1.21× | 10 161 839 | 2 611 965 | 3.89× | 1 754 492 | 1 715 592 | 1.02× | 16 829 | 16 626 | 1.01× | 32 320 | 58 596 | 0.55× |
| `init-full` | 36 582 525 | 15 903 301 | 2.30× | 7 293 473 | 2 454 042 | 2.97× | 3 533 518 | 981 042 | 3.60× | 7 068 899 | 9 638 042 | 0.73× | 5 701 994 | 17 691 191 | 0.32× |
| `mathlib-prefix` | 44 275 979 | 21 170 339 | 2.09× | 8 811 707 | 3 297 158 | 2.67× | 4 264 766 | 1 360 025 | 3.14× | 10 192 756 | 14 888 273 | 0.68× | 10 654 332 | 29 349 036 | 0.36× |

| stream | instr cl-v | instr soko (PGO) | **instr ratio** | steps cl (β+δ+ι) | steps soko | **steps ratio** | instr/step cl | instr/step soko | **per-step ratio** | check = steps × per-step | instr/β cl | instr/β soko |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `app-lam` | 157.30 G | 5.55 G | **28.4×** | 0.00 M | 0.00 M | **1.22×** | 1 041 694 648 | 44 730 552 | **23.3×** | 28.4× | 1 299 966 049 | 50 423 531 |
| `beta-ladder` | 39.94 G | 48.52 G | **0.8×** | 0.00 M | 0.00 M | **1.01×** | 9 652 771 | 11 869 132 | **0.8×** | 0.8× | 18 885 658 | 23 316 200 |
| `let-ladder` | 8.06 G | 0.80 G | **10.1×** | 0.00 M | 0.00 M | **1.53×** | 58 398 347 | 8 881 112 | **6.6×** | 10.1× | 70 078 016 | 9 630 122 |
| `fueled-chain` | 1.09 G | 0.06 G | **18.1×** | 0.01 M | 0.00 M | **1.43×** | 170 807 | 13 496 | **12.7×** | 18.1× | 234 397 | 15 927 |
| `init-prelude` | 3.20 G | 0.26 G | **12.5×** | 0.06 M | 0.04 M | **1.46×** | 57 209 | 6 653 | **8.6×** | 12.5× | 70 879 | 8 105 |
| `grind-ring-5` | 22.61 G | 2.25 G | **10.0×** | 2.11 M | 1.53 M | **1.38×** | 10 725 | 1 476 | **7.3×** | 10.0× | 13 284 | 1 837 |
| `magma-list-pair-n21` | 199.17 G | 49.55 G | **4.0×** | 30.39 M | 34.96 M | **0.87×** | 6 554 | 1 417 | **4.6×** | 4.0× | 7 576 | 1 615 |
| `magma-list-deep-n36` | 324.55 G | 31.48 G | **10.3×** | 45.28 M | 31.91 M | **1.42×** | 7 167 | 987 | **7.3×** | 10.3× | 9 726 | 1 141 |
| `init-full` | 585.83 G | 45.07 G | **13.0×** | 47.41 M | 19.34 M | **2.45×** | 12 357 | 2 330 | **5.3×** | 13.0× | 16 014 | 2 834 |
| `mathlib-prefix` | 848.52 G | 69.33 G | **12.2×** | 57.35 M | 25.83 M | **2.22×** | 14 795 | 2 685 | **5.5×** | 12.2× | 19 164 | 3 275 |

Trusted mode and parse-free variants (init-full, grind-ring-5, mathlib-prefix): 
  `grind-ring-5` verified: cl 22.6 G / 2.11 M steps = 10 725 per step; soko (parse removed) 2.2 G / 1.53 M = 1 425; instr ratio 10.4× = steps 1.38× × per-step 7.5×
  `grind-ring-5` trusted: cl 21.5 G / 2.10 M steps = 10 207 per step; soko (parse removed) 2.2 G / 1.53 M = 1 425; instr ratio 9.9× = steps 1.38× × per-step 7.2×
  `init-full` verified: cl 585.8 G / 47.41 M steps = 12 357 per step; soko (parse removed) 42.8 G / 19.34 M = 2 215; instr ratio 13.7× = steps 2.45× × per-step 5.6×
  `init-full` trusted: cl 567.2 G / 47.34 M steps = 11 982 per step; soko (parse removed) 42.8 G / 19.34 M = 2 215; instr ratio 13.2× = steps 2.45× × per-step 5.4×
  `mathlib-prefix` verified: cl 848.5 G / 57.35 M steps = 14 795 per step; soko (parse removed) 65.4 G / 25.83 M = 2 532; instr ratio 13.0× = steps 2.22× × per-step 5.8×
mathlib-prefix trusted n/a list.index(x): x not in list

| stream | β cl / nanoda / soko | δ cl / nanoda / soko | ι+proj+nat cl / nanoda / soko | steps cl / nanoda / soko (M) | instr cl-v / nanoda / soko (G) | per step cl / nanoda / soko | **cl→nanoda: steps × per-step** | **nanoda→soko: steps × per-step** |
|---|---|---|---|---|---|---|---|---|
| `app-lam` | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 157.3 / 27.1 / 5.55 | 1 041 694 648 / 410 407 088 / 44 730 552 | 5.81× = 2.29× × 2.54× | 4.88× = 0.53× × 9.18× |
| `beta-ladder` | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 39.9 / 7.9 / 48.52 | 9 652 771 / 1 951 013 / 11 869 132 | 5.06× = 1.02× × 4.95× | 0.16× = 0.99× × 0.16× |
| `let-ladder` | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 0.00 / 0.00 / 0.00 | 8.1 / 4.4 / 0.80 | 58 398 347 / 87 098 620 / 8 881 112 | 1.85× = 2.76× × 0.67× | 5.45× = 0.56× × 9.81× |
| `fueled-chain` | 0.00 / 0.08 / 0.00 | 0.00 / 0.02 / 0.00 | 0.00 / 0.01 / 0.00 | 0.01 / 0.11 / 0.00 | 1.1 / 0.9 / 0.06 | 170 807 / 8 190 / 13 496 | 1.26× = 0.06× × 20.86× | 14.32× = 23.60× × 0.61× |
| `init-prelude` | 0.05 / 0.04 / 0.03 | 0.01 / 0.01 / 0.00 | 0.00 / 0.00 / 0.00 | 0.06 / 0.04 / 0.04 | 3.2 / 0.9 / 0.26 | 57 209 / 20 031 / 6 653 | 3.67× = 1.28× × 2.86× | 3.41× = 1.13× × 3.01× |
| `grind-ring-5` | 1.70 / 1.51 / 1.23 | 0.17 / 0.16 / 0.11 | 0.24 / 0.21 / 0.19 | 2.11 / 1.89 / 1.53 | 22.6 / 8.4 / 2.25 | 10 725 / 4 459 / 1 476 | 2.69× = 1.12× × 2.41× | 3.73× = 1.24× × 3.02× |
| `magma-list-pair-n21` | 26.29 / 26.69 / 30.68 | 2.87 / 2.87 / 3.07 | 1.23 / 1.43 / 1.22 | 30.39 / 31.00 / 34.96 | 199.2 / 86.8 / 49.55 | 6 554 / 2 802 / 1 417 | 2.29× = 0.98× × 2.34× | 1.75× = 0.89× × 1.98× |
| `magma-list-deep-n36` | 33.37 / 34.99 / 27.58 | 10.16 / 10.16 / 2.61 | 1.75 / 2.59 / 1.72 | 45.28 / 47.74 / 31.91 | 324.6 / 219.0 / 31.48 | 7 167 / 4 587 / 987 | 1.48× = 0.95× × 1.56× | 6.96× = 1.50× × 4.65× |
| `init-full` | 36.58 / 37.46 / 15.90 | 7.29 / 7.15 / 2.45 | 3.53 / 3.65 / 0.98 | 47.41 / 48.25 / 19.34 | 585.8 / 230.8 / 45.07 | 12 357 / 4 783 / 2 330 | 2.54× = 0.98× × 2.58× | 5.12× = 2.50× × 2.05× |
| `mathlib-prefix` | 44.28 / 45.55 / 21.17 | 8.81 / 8.70 / 3.30 | 4.26 / 4.41 / 1.36 | 57.35 / 58.65 / 25.83 | 848.5 / 321.8 / 69.33 | 14 795 / 5 487 / 2 685 | 2.64× = 0.98× × 2.70× | 4.64× = 2.27× × 2.04× |

Steps = β binders + δ unfoldings + (ι fires + projection reductions + K + struct-η + Nat ops), per checker; instructions = the T1 cells (`--verified`; sokonanoda PGO). "parse removed" subtracts sokonanoda's parse-only count.

## T8. Ablations of sokonanoda HEAD (`_tmp/soko-ablate.patch`; one binary, `SOKO_ABLATE=` env; baseline = same binary, no flag, 0–3 % above the plain build; G instructions and Δ % vs baseline)

| ablation | grind-ring-5 | init-full | mathlib-prefix | magma-list-deep-n36 | beta-ladder |
|---|---|---|---|---|---|
| `baseline` | 2.4G +0.0% | 49.1G +0.0% | 75.5G +0.0% | 34.0G +0.0% | 48.3G +0.0% |
| `eager-delta` | 11577.9G +474342.8% [x143] | - | - | - | - |
| `no-conv-cache` | 2.6G +5.8% | 330.7G +573.7% | 231.8G +207.0% [x134] | 34.0G +0.0% | 48.3G +0.0% |
| `no-eval-cache` | 4.4G +78.3% | 152.2G +210.0% | 206.3G +173.3% | 406.5G +1095.0% [x134] | 48.7G +0.8% |
| `no-hc` | 3.2G +29.5% | 64.6G +31.5% | 95.4G +26.4% | 76.2G +124.0% | 48.7G +0.7% |
| `no-nat-defer` | 2.4G +0.1% | 292.4G +495.6% [x137] | 68.6G -9.1% [x134] | 34.0G -0.0% | 48.3G +0.0% |
| `no-probe` | 3.2G +31.6% | 283.0G +476.6% [x143] | 109.3G +44.8% [x134] | 34.2G +0.5% | 48.3G +0.0% |
| `no-prune` | 2.6G +6.1% | 67.6G +37.8% | 12.4G -83.5% [x1] | 53.9G +58.3% [x134] | 0.2G -99.6% |
| `no-relevance` | 2.4G -0.0% | 49.4G +0.7% | - | - | - |
| `no-static-veto` | 2.7G +11.6% | 56.5G +15.1% | 84.7G +12.2% | 34.0G +0.0% | 48.3G +0.0% |
| `no-store` | 2.4G -2.7% | 54.1G +10.2% | 81.9G +8.5% | 34.0G -0.0% | 48.3G -0.0% |
| `no-type-cache` | 33.8G +1283.3% | 353.2G +619.5% | 420.9G +457.6% | 34.3G +1.0% | 48.3G -0.0% |
| `no-unfold-cache` | 2.4G +0.1% | 49.1G -0.0% | - | - | - |
| `probe-cap-1e6` | 2.4G +0.1% | 49.1G +0.0% | - | - | - |
| `probe-cap-64` | 2.4G -0.9% | 123.5G +151.5% | 155.6G +106.1% | 34.0G +0.0% | 48.3G +0.0% |
| `session-1` | 2.6G +4.5% | 58.6G +19.4% | 85.2G +12.9% | 34.0G +0.0% | 48.3G +0.0% |
| `session-1024` | 2.4G -1.0% | 40.8G -16.9% | 66.0G -12.6% | 34.0G +0.0% | 48.3G +0.0% |

`[x134]` = aborted at the 22 GB address-space cap (a lower bound); `[x143/137]` = killed by hand.  Peak RSS (MB): Mathlib prefix baseline 923, `no-store` 915, `no-hc` 919; `magma-list-deep-n36` baseline 7 885, `no-hc` 17 930; `init-full` baseline 570, `no-hc` 572; `session-1024` 1.6–1.9 GB on init-full/Mathlib prefix.

## T9. The bisect: every first-parent commit of `intgrah/sokonanoda` that parses the stream (`init-full`, plain `cargo build --release --locked`, no PGO, no `target-cpu=native`, single thread)

| hash | date | author | subject | init-full G | Δ % | grind G | Mathlib prefix G | class | evidence |
|---|---|---|---|---|---|---|---|---|---|
| `7e0c273` | 2025-12-16 | ammkrn | chore: add temp. note about Q4 upstream issues | exit 1: Error: unrecognized configuration options: ["unsafe_permit_a | – | | | | |
| `90c2b70` | 2026-02-18 | Chris | Merge pull request #7 from ammkrn/json_string | 270.89 | – |  |  |  |  |
| `b6e3c8a` | 2026-02-19 | Chris | Merge pull request #8 from nomeata/proj-from-prop-test | 270.90 | +0.0 |  |  |  |  |
| `e753956` | 2026-02-19 | Chris | Merge pull request #9 from ammkrn/nat_string_opt | 270.99 | +0.0 |  |  |  |  |
| `93bf604` | 2026-02-21 | ammkrn | fix: remedy remaining arena test suite cases | 271.06 | +0.0 |  |  |  |  |
| `1283899` | 2026-03-04 | ammkrn | fix: leq_core(imax, imax) case, rec_rule cmp ck | 270.67 | -0.1 |  |  |  |  |
| `053b4f5` | 2026-03-04 | ammkrn | feat: make inductive more robust to uparam names | 271.15 | +0.2 |  |  |  |  |
| `68d5ca9` | 2026-03-04 | ammkrn | chore: even more misc. bounds checks | 271.23 | +0.0 |  |  |  |  |
| `224b7c1` | 2026-03-24 | Chris | Merge pull request #13 from robsimmons/patch-1 | 271.23 | +0.0 |  |  |  |  |
| `d5f6c8d` | 2026-04-08 | Chris | Merge pull request #11 from lucab/ups/truncating-casts | 271.23 | +0.0 | 9.42 | 376.4 |  |  |
| `6d2f037` | 2026-04-08 | Chris | Merge pull request #14 from eisbaw/master | 232.43 | -14.3 | 8.46 | 325.2 | R | `util.rs:36-77`: `Ptr` packed into one `u32` (bit 31 = dag tag); layout |
| `2baf957` | 2026-04-16 | Paul | less prop defeq checks | 232.14 | -0.1 |  |  |  |  |
| `03ec31d` | 2026-04-16 | Paul | Revert "less prop defeq checks" | 232.43 | +0.1 |  |  |  |  |
| `c61c1ca` | 2026-04-19 | Paul | even less defeq checks | 232.10 | -0.1 |  |  |  |  |
| `d142c75` | 2026-04-19 | Paul | revert to conservative approach | 232.14 | +0.0 |  |  |  |  |
| `9e4ee39` | 2026-04-19 | Paul | rename flag | 232.14 | +0.0 |  |  |  |  |
| `866e539` | 2026-04-20 | Paul | update readme | 232.14 | -0.0 | 8.45 | 324.8 |  |  |
| `22e5940` | 2026-04-20 | Paul | fix caching problem | 318.18 | +37.1 | 8.67 | 417.6 | A | `tc.rs:971`: def-eq successes under a skipped Prop check no longer enter the eq-cache (a cache narrowed for soundness) — the one regression |
| `16b099c` | 2026-04-24 | ammkrn | fix: forward `flag` parameter in infer_proj | 318.25 | +0.0 | 8.68 | 418.6 |  |  |
| `289d48d` | 2026-04-25 | Schrodinger | Add local-first expr allocation cache | 299.35 | -5.9 | 8.23 | 396.7 | R | `util.rs:453`: `alloc_expr` probes the thread-local interner first (`entry` API); the 5 % of the README |
| `06a07b7` | 2026-04-26 | Schrodinger | update | 299.35 | -0.0 | 8.23 | 396.7 |  |  |
| `7c74b01` | 2026-06-12 | IntGrah | NbE | 183.76 | -38.6 | 5.84 | 267.0 | M | `tc.rs` −596, `value.rs` +249, `eval.rs` +1593: NbE — closures instead of substitution (A) over a `bumpalo` value arena with address identity (R); the 35 % of the README |
| `70bd739` | 2026-06-13 | IntGrah | fix possible hash collision unsoundness | 181.00 | -1.5 |  |  |  |  |
| `33f6754` | 2026-06-13 | IntGrah | fix: reduce string literal to constructor before iota | 181.00 | +0.0 |  |  |  |  |
| `f1c4b12` | 2026-06-13 | IntGrah | chore: Update README.md | 181.00 | +0.0 |  |  |  |  |
| `3e93ed2` | 2026-06-14 | IntGrah | Redundant Arc clone | 181.04 | +0.0 |  |  |  |  |
| `a6e72ae` | 2026-06-17 | IntGrah | perf: walk spines in place | 180.12 | -0.5 |  |  |  |  |
| `698c744` | 2026-06-17 | IntGrah | perf: remove unnecessary clones | 180.04 | -0.0 |  |  |  |  |
| `a214ff3` | 2026-06-21 | IntGrah | fix(parser): tolerate out-of-order and sparse export indices | 180.33 | +0.2 |  |  |  |  |
| `c8dcb27` | 2026-06-23 | IntGrah | perf: borrow closures | 180.33 | +0.0 | 5.70 | 262.3 |  |  |
| `fd05f02` | 2026-06-23 | IntGrah | perf: stumpalo allocator | 168.90 | -6.3 | 5.35 | 245.6 | R | `Cargo.toml:33-37`, `util.rs:262-312`: `stumpalo` arena + `hashbrown` interners, pointers with address equality replace `Arc`/index dags |
| `d245a52` | 2026-07-10 | IntGrah | fix: k-rec bug Thread the proper depth | 170.02 | +0.7 |  |  |  |  |
| `90b05dc` | 2026-07-24 | IntGrah | fix: proof irrelevance under bvar | 169.90 | -0.1 |  |  |  |  |
| `7821e5d` | 2026-07-24 | IntGrah | Add test | 169.90 | -0.0 | 5.38 | 246.9 |  |  |
| `6e2dd3f` | 2026-07-24 | IntGrah | Optimisations | 136.26 | -19.8 | 4.33 | 191.0 | R | `Cargo.toml:13,36`, `main.rs:6-7`: `overflow-checks=false`, `mimalloc` global allocator; `parser.rs` +912: byte-level NDJSON fast path |
| `b5cd46f` | 2026-07-24 | IntGrah | More | 136.09 | -0.1 |  |  |  |  |
| `8212fd5` | 2026-07-27 | IntGrah | fix: more struct and inductive checks | 136.12 | +0.0 | 4.33 | 190.7 |  |  |
| `d2a0be0` | 2026-08-02 | IntGrah | wip | 101.99 | -25.1 | 3.43 | 139.1 | M | `tc.rs` −882 → `infer.rs` +270, `quote.rs` +167, `inductive.rs` +1073: inference on syntax under a VALUE environment (A: no instantiation of codomains) plus the deferred infer-closure (structural) |
| `ce1180f` | 2026-08-02 | IntGrah | wip | 101.19 | -0.8 | 3.43 | 138.2 |  |  |
| `7cb1703` | 2026-08-04 | IntGrah | proj | 99.05 | -2.1 | 3.36 | 135.3 | R | `eval.rs:13-38,221-243`: BMI2 `pext` slot selection for environment materialisation |
| `88506dc` | 2026-08-04 | IntGrah | unfold key narrowing | 98.40 | -0.7 |  |  |  |  |
| `8eaaf4b` | 2026-08-04 | IntGrah | interners on the thread | 98.35 | -0.1 | 3.34 | 134.3 |  |  |
| `efaba38` | 2026-08-04 | IntGrah | more stuff | 95.16 | -3.2 | 3.21 | 130.2 | R | `value.rs:143-283`, `eval.rs:346`: a `canonical` flag on values/spines, set at construction; `canonicalize_for_spine` returns at once when set (interior mutability) |
| `7401fe5` | 2026-08-04 | IntGrah | wip | 83.46 | -12.3 | 3.26 | 117.0 | A | `value.rs` +219 content digests, `eval.rs:978-1050`: the persistent cross-declaration whnf store keyed by a 64/128-bit content digest (ablation `no-store` at HEAD: +10 %) |
| `c293178` | 2026-08-04 | IntGrah | union find stuff | 84.06 | +0.7 |  |  |  |  |
| `9e7e528` | 2026-08-04 | IntGrah | fix tests | 84.07 | +0.0 |  |  |  |  |
| `333fe75` | 2026-08-04 | IntGrah | fix test string | 84.05 | -0.0 | 3.29 | 117.9 |  |  |
| `4f0bc57` | 2026-08-05 | IntGrah | Much better algorithm for proof irrelevance in spines | 73.33 | -12.8 | 3.00 | 105.3 | A | `relevance.rs` +126, `conv.rs:328-405`: per-constant `Sig`; the win is the `prop_result` VETO of proof-irrelevance inference (ablation `no-static-veto` +15 %), not the spine skip (`no-relevance` +0.7 %) |
| `4ed825a` | 2026-08-05 | IntGrah | pointer-equality for levels | 71.60 | -2.4 | 2.97 | 102.5 | R | `level.rs:243-262`: pointer-equality early returns in `leq`/`eq_antisymm` (address identity of interned levels) |
| `ba5814a` | 2026-08-05 | IntGrah | pointer-equality on spines | 71.56 | -0.1 |  |  |  |  |
| `0668a6f` | 2026-08-05 | IntGrah | Update README | 71.55 | -0.0 | 2.97 | 102.4 |  |  |
| `13a9760` | 2026-08-05 | IntGrah | Parser stuff | 69.16 | -3.3 | 2.88 | 98.6 | R | `Cargo.toml:15` `codegen-units=1`; `parser.rs` +280: SWAR digit scanning, presized back-ref vectors |
| `84023dd` | 2026-08-12 | IntGrah | Parser streaming to reduce peak memory | 69.11 | -0.1 |  |  |  |  |
| `b38b875` | 2026-08-12 | IntGrah | probe caps | 69.34 | +0.3 | 2.89 | 99.0 |  |  |
| `9ad006e` | 2026-08-13 | IntGrah | Entry | 67.50 | -2.7 | 2.79 | 96.4 | R | `eval.rs:258-300`: `HashMap::entry` — one probe per hash-cons instead of two |
| `247021b` | 2026-08-13 | IntGrah | tweak inline hints | 67.49 | -0.0 |  |  |  |  |
| `0fab887` | 2026-08-13 | IntGrah | Smallvec | 66.94 | -0.8 | 2.78 | 95.7 |  |  |
| `9b4ea12` | 2026-08-14 | IntGrah | eagerness in some places | 63.78 | -4.7 | 2.70 | 90.9 | M | `eval.rs:562-600`: thunks deleted, arguments evaluated eagerly (evaluation strategy — #310 measured strict vs lazy at 1.00× in Lean); `infer.rs:177` apply the codomain closure to the domain when the body ignores its binder; `absent_arg` (ablation: 0) |
| `49b0e9c` | 2026-08-15 | IntGrah | binder optimisations | 63.81 | +0.0 |  |  |  |  |
| `792a5f9` | 2026-08-15 | IntGrah | ignore *.profdata | 63.81 | +0.0 | 2.70 | 90.9 |  |  |
| `7b51784` | 2026-09-05 | IntGrah | port over fixes | 56.95 | -10.8 | 2.52 | 83.7 | M | `conv.rs:99-120`: the positive conv cache goes from a union-find to a hash set (R, data structure); Lam/Lam unifies the domains first (A); nested-inductive checks |
| `ceaabb5` | 2026-09-07 | IntGrah | delete binder names and plicity | 56.77 | -0.3 |  |  |  |  |
| `fe8edcc` | 2026-09-12 | IntGrah | sparse environments | 57.51 | +1.3 | 2.59 | 84.5 |  |  |
| `28c03d0` | 2026-09-12 | IntGrah | share more work | 47.70 | -17.1 | 2.38 | 73.3 | M | `eval.rs:836` `neutral_app` and `:83` `env_extend`: hash-consed spine extension and environment cons keyed by the addresses of the parts — more `ptr::eq` hits in `unify` (A in effect, R in mechanism; #310 ported content-keyed value sharing: nothing at scale) |

## T10. The bisect per class (init-full; the product of the per-commit ratios; the gain of a class = 1/product; share = its log against the whole 90c2b70 → HEAD log-gain of 5.68×)

| class | commits | factor | share of the log-gain |
|---|---|---|---|
| RUNTIME (cheaper steps) | `6d2f037` -14.3 %, `289d48d` -5.9 %, `fd05f02` -6.3 %, `6e2dd3f` -19.8 %, `7cb1703` -2.1 %, `efaba38` -3.2 %, `4ed825a` -2.4 %, `13a9760` -3.3 %, `9ad006e` -2.7 % | 1.90× | 37 % |
| MIXED | `7c74b01` -38.6 %, `d2a0be0` -25.1 %, `9b4ea12` -4.7 %, `7b51784` -10.8 %, `28c03d0` -17.1 % | 3.08× | 65 % |
| ALGORITHMIC (fewer steps) | `7401fe5` -12.3 %, `4f0bc57` -12.8 % | 1.31× | 15 % |
| ALGORITHMIC regression (`22e5940`) | `22e5940` +37.1 % | 0.73× | -18 % |
| commits under 2 % (net) | the other 45 measurable commits, each within ±2 % (the largest: `70bd739` −1.5 %, `fe8edcc` +1.3 %) | 1.02× | 1 % |

The MIXED class split by commit: `7c74b01` NbE 1.63×, `d2a0be0` inference on values 1.34×, `28c03d0` hash-consed spines/environments 1.21×, `7b51784` 1.12×, `9b4ea12` 1.05×.  From the NbE commit's predecessor `06a07b7` (299.4 G) to HEAD (47.7 G) the gain is 6.28×; from the last nanoda-lineage commit `6d2f037` (232.4 G) it is 4.87× — and nanoda_lib's own master `4c544ed` measures 230.8 G on the same stream.
