# The whitepaper

A self-contained account of the core proof idea of ConLeche
(task #323; the shared brief is [`PLAN.md`](./PLAN.md)). One Typst
source — `main.typ`, `sections/NN-name.typ`, the macro library
`lib.typ`, `style.css` — rendered to PDF and HTML by the same compiler.

## Building

    cd whitepaper && direnv allow     # once: the dev shell from flake.nix
    ./build.sh                        # or, from the repo root, without direnv:
    nix develop ./whitepaper -c whitepaper/build.sh

Output: `whitepaper/_build/whitepaper.pdf` and `whitepaper/_build/index.html`
(gitignored), copied to `_out/whitepaper/` at the repo root for reading.
`build.sh` fails on any typst warning.

## Writing

Read the usage comment at the top of [`lib.typ`](./lib.typ): `#ann[...]`
for the one annotation colour (also inside math), `#rule(...)`,
`#theorem[...]`/`#lemma[...]`/`#definition[...]`/`#proof[...]`,
`#src("path", a, b)[the phrase]` for a source link — the phrase itself,
dotted-underlined, is the link (label required; in HTML it shows the
cited lines on hover), `#overview(7)` for a link to a section
of `OVERVIEW.md`, `#lean[...]` for code names. Never branch on the output target in a section: the
macros do. A `;` right after a `#src(...)` call is swallowed by the
parser — write `\;`; the other traps are the "Typst notes" atop `lib.typ`.

## Gates

* `whitepaper/links-gate.sh` — every `src("path", a, b)` call and every
  literal `blob/master/...#L..` link has its cited lines snapshotted in
  `links-expected.txt`; a diff means a citation moved or changed.
  `--update` regenerates. Run from `tests/arena.sh` and CI.
* `build.sh` — the document compiles warning-free in both formats.
* `.github/workflows/whitepaper.yml` — both of the above on every PR
  touching `whitepaper/`, and on `master` the HTML goes to GitHub Pages.
