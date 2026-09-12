#!/usr/bin/env python3
"""scripts/dead-census.py — the per-constant liveness census (task #221).

The instrument task #210 Part C built in `_tmp` and did not keep,
committed so that the next census is a re-run rather than a
re-derivation.  `scripts/dead-census.lean` dumps the constant
dependency graph of an imported environment; this driver runs it over
the two executable environments (`Main.lean` and `PinDump.lean` both
declare `main`, so they cannot be imported into one environment),
chooses the seeds, walks the graph, and classifies what is left against
the sources.

    scripts/dead-census.py [--out DIR] [--skip-lean]

## LIVE = the union of

* the **seven capstone roots** of `tests/ProofDeps.lean` — the
  statements the project exists to make;
* the **executable closure**: `main`, in each of the two environments;
* everything the **test suite** (`ConLecheTests*`), the **Challenge**
  module and the **pin certificates** (`ConLeche.PinGen.Certs`, read by
  name out of the built olean at pin-generation time — no static walk
  can see that) declare;
* every **`@[csimp]`** theorem (reached by nothing, and what makes a
  fast twin reachable at all) and, through the graph's own extra edges,
  the `@[implemented_by]` targets;
* every **registered** declaration — `syntax`, `macro`, `elab`,
  `notation`, `instance`, `@[command_elab]`, `@[extern]` — and every
  declaration of a module that declares a **command elaborator**
  (`Kernel/BasisGen.lean`, `PinGen.lean`, `PinGen/Dump.lean`): its
  helpers are reached only through the command.  These are
  invoked by registration, never by name, so no dependency walk reaches
  them, and neither does one reach the private helpers under them.

## WHAT THE CENSUS CANNOT SEE — the two findings of #210 Part C

1. *syntactic-only uses*: a `simp`/`rw` argument the tactic did not end
   up needing leaves no trace in the proof term, so it reads dead.  The
   text filter below is the compensation and the build is the arbiter:
   cut, build, restore what the build demands, record each restore.
2. *results that are not corollaries*: a top-level theorem no capstone
   is a corollary of is itself the deliverable (`AgreeFloor`'s
   agreement floor, `BridgeDecl`'s `checkDeclsPure_datF`), and reads dead.
   Only a reader can tell those apart; #209's rule stands — "imported
   by nothing" is not a dead-code criterion in a verification tree.

## OUTPUT (default `_tmp/deadcode/`)

    census.tsv     name / module / kind / live       (the joined passes)
    hard.txt       dead, a source declaration, carries no attribute,
                   and its name occurs in NO other file of the tree
    soft.txt       dead and a source declaration, but the name still
                   occurs elsewhere (a `simp` argument, a doc mention,
                   a fixture) — the (1) class, each needs reading
    attributed.txt dead by the walk but carrying an attribute
                   (`@[simp]` above all): deleting one changes what a
                   tactic can reach, so the build must confirm each
    generated.txt  dead names that are not source declarations
                   (equation lemmas, `.rec`, match auxiliaries,
                   anonymous instances)
    modules.txt    modules with no live declaration at all
    summary.txt    the counts
"""

import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

TEXT_EXT = (".lean", ".sh", ".py", ".md", ".toml", ".json", ".txt")
SKIP_DIRS = {".lake", ".git", "_tmp", "perf-data", "pins", "bridge", "_probe"}

MODIFIERS = (r"(?:public\s+|private\s+|protected\s+|partial\s+|noncomputable\s+"
             r"|unsafe\s+|scoped\s+|local\s+|nonrec\s+)*")
DECL_RE = re.compile(
    r"^\s*" + MODIFIERS +
    r"(theorem|def|abbrev|instance|structure|inductive|class|opaque|axiom|lemma)"
    r"\s+([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")
REGISTERED_RE = re.compile(
    r"^\s*" + MODIFIERS +
    r"(?:syntax|macro|elab|notation|instance|macro_rules|declare_syntax_cat)\b"
    r"(?:\s*\(name\s*:=\s*([A-Za-z_][A-Za-z0-9_'!?.]*)\))?")
# A module that declares a COMMAND elaborator is elaboration machinery:
# its private helpers are reached only through the command, which no
# dependency walk sees.  (A module that merely defines a *tactic* macro
# is not: its ordinary declarations are ordinary.)
ELAB_MODULE_RE = re.compile(
    r"^@\[command_elab\b|^elab\s+\"[^\"]*\"[^\n]*:\s*command\b", re.M)
ATTR_RE = re.compile(r"^\s*@\[([^\]]*)\]")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")

# attributes that make a declaration reachable by REGISTRATION.  `simp`
# is deliberately not among them: a simp lemma that never fires is dead,
# and the build is what says whether it fires.
SEED_ATTRS = {"command_elab", "term_elab", "tactic", "builtin_command_elab",
              "builtin_term_elab", "macro", "app_unexpander", "delab",
              "instance", "extern", "export", "init", "builtin_init",
              "implemented_by"}

CAPSTONES = [
    "ConLeche.no_False_theorem_accepted",
    "ConLeche.Cached.no_proof_of_False_cached",
    "ConLeche.Model.no_proof_of_False_pure",
    "ConLeche.Cached.no_proof_of_Empty_cached",
    "ConLeche.Cached.checkDecls_sound",
    "ConLeche.Cached.fullyChecked_checkDecls",
    "ConLeche.Cached.no_proof_of_False_checked",
    "ConLeche.Model.no_proof_of_Empty_pure",
]
SEED_MODULE_PREFIXES = ("ConLecheTests", "ConLeche.Challenge",
                        "ConLeche.PinGen.Certs")


def lean_modules():
    mods = ["ConLeche"]
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "ConLeche")):
        dirnames.sort()
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), ROOT)
                mods.append(rel[:-5].replace("/", "."))
    return mods


def run_lean(mods, out_path):
    cmd = ["lake", "env", "lean", "--run", "scripts/dead-census.lean"] + mods
    with open(out_path, "w") as fh:
        r = subprocess.run(cmd, cwd=ROOT, stdout=fh, stderr=subprocess.PIPE)
    if r.returncode != 0:
        sys.stderr.write(r.stderr.decode())
        sys.exit(1)


def read_pass(path):
    """-> (graph, info, csimp theorem names)"""
    graph, info, csimp = {}, {}, set()
    with open(path) as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if parts[0] == "#csimp":
                csimp.add(parts[1])
                continue
            if len(parts) != 4:
                continue
            name, mod, kind, deps = parts
            graph[name] = deps.split() if deps else []
            info[name] = (mod, kind)
    return graph, info, csimp


def module_file(mod):
    return mod.replace(".", "/") + ".lean"


def suffixes(name):
    parts = name.split(".")
    return [".".join(parts[i:]) for i in range(len(parts))]


def source_index():
    """decls[suffix] -> {file}; attrs[(suffix, file)] -> {attribute};
       registered[suffix] -> {file}; elab_files -> {file};
       tokens[token][file] -> occurrence count.

    The count matters: a name used only inside its own file — a tactic
    macro's syntax quotation, say — has two occurrences there, and a
    name nothing mentions has one (its declaration)."""
    decls = defaultdict(set)
    attrs = defaultdict(set)
    registered = defaultdict(set)
    elab_files = set()
    tokens = defaultdict(dict)
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames
                       if d not in SKIP_DIRS and not d.startswith(".")]
        for fn in filenames:
            if not fn.endswith(TEXT_EXT):
                continue
            path = os.path.relpath(os.path.join(dirpath, fn), ROOT)
            try:
                text = open(os.path.join(ROOT, path), errors="replace").read()
            except OSError:
                continue
            if fn.endswith(".lean"):
                if ELAB_MODULE_RE.search(text):
                    elab_files.add(path)
                pending = set()
                for line in text.splitlines():
                    a = ATTR_RE.match(line)
                    if a:
                        for piece in a.group(1).split(","):
                            pending.add(piece.strip().split()[0]
                                        if piece.strip() else "")
                        line = line[a.end():]
                        if not line.strip():
                            continue
                        line = " " + line
                    m = DECL_RE.match(line)
                    if m:
                        decls[m.group(2)].add(path)
                        if pending:
                            attrs[(m.group(2), path)] |= pending
                        pending = set()
                        continue
                    r = REGISTERED_RE.match(line)
                    if r:
                        if r.group(1):
                            registered[r.group(1)].add(path)
                        pending = set()
                        continue
                    if line.strip() and not line.lstrip().startswith("--"):
                        pending = set()
            counts = defaultdict(int)
            for tok in TOKEN_RE.findall(text):
                counts[tok] += 1
            for tok, c in counts.items():
                tokens[tok][path] = c
    return decls, attrs, registered, elab_files, tokens


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="_tmp/deadcode")
    ap.add_argument("--skip-lean", action="store_true",
                    help="reuse the two raw passes already in --out")
    args = ap.parse_args()
    out = os.path.join(ROOT, args.out)
    os.makedirs(out, exist_ok=True)

    p1 = os.path.join(out, "pass-main.tsv")
    p2 = os.path.join(out, "pass-pindump.tsv")
    if not args.skip_lean:
        run_lean(lean_modules() + ["Main", "ConLecheTests", "ConLeche.Challenge"], p1)
        run_lean(lean_modules() + ["PinDump"], p2)

    graph, info, csimp = read_pass(p1)
    g2, i2, c2 = read_pass(p2)
    for n, ds in g2.items():
        if n in graph:
            graph[n] = sorted(set(graph[n]) | set(ds))
        else:
            graph[n], info[n] = ds, i2[n]
    csimp |= c2

    decls, attrs, registered, elab_files, tokens = source_index()

    # ---- seeds -------------------------------------------------------
    seeds = set(CAPSTONES) | csimp
    seeds.add("main")
    for n, (mod, _kind) in info.items():
        own = module_file(mod)
        if mod.startswith(SEED_MODULE_PREFIXES) or own in elab_files:
            seeds.add(n)
            continue
        for s in suffixes(n):
            if own in registered.get(s, ()) or attrs.get((s, own), set()) & SEED_ATTRS:
                seeds.add(n)
                break
            if s in decls:
                break
    seeds &= set(graph)

    # ---- closure -----------------------------------------------------
    live, todo = set(), list(seeds)
    while todo:
        n = todo.pop()
        if n in live:
            continue
        live.add(n)
        todo.extend(graph.get(n, ()))

    with open(os.path.join(out, "census.tsv"), "w") as fh:
        for name in sorted(info):
            mod, kind = info[name]
            fh.write(f"{name}\t{mod}\t{kind}\t{1 if name in live else 0}\n")

    # ---- classification of the dead ----------------------------------
    hard, soft, attributed, generated = [], [], [], []
    for name in sorted(info):
        if name in live:
            continue
        mod, kind = info[name]
        own = module_file(mod)
        src = None
        for s in suffixes(name):
            if s in decls:
                src = s
                break
        if src is None:
            generated.append((name, mod, kind, []))
            continue
        if attrs.get((src, own)):
            attributed.append((name, mod, kind,
                               sorted(attrs[(src, own)])))
            continue
        short = name.split(".")[-1]
        occ = tokens.get(short, {})
        elsewhere = sorted(f for f, c in occ.items()
                           if f != own or c > 1)
        (soft if elsewhere else hard).append((name, mod, kind, elsewhere))

    def dump(fn, rows, extra=False):
        with open(os.path.join(out, fn), "w") as fh:
            for name, mod, kind, xs in rows:
                tail = "\t" + ",".join(xs[:6]) if extra else ""
                fh.write(f"{name}\t{mod}\t{kind}{tail}\n")

    dump("hard.txt", hard)
    dump("soft.txt", soft, extra=True)
    dump("attributed.txt", attributed, extra=True)
    dump("generated.txt", generated)

    per_mod_live = defaultdict(int)
    per_mod_dead = defaultdict(int)
    named = {r[0] for r in hard} | {r[0] for r in soft} | {r[0] for r in attributed}
    for name, (mod, _kind) in info.items():
        if name in live:
            per_mod_live[mod] += 1
        elif name in named:
            per_mod_dead[mod] += 1
    empty_mods = sorted(m for m in per_mod_dead if per_mod_live[m] == 0)
    with open(os.path.join(out, "modules.txt"), "w") as fh:
        for m in empty_mods:
            fh.write(f"{m}\t{per_mod_dead[m]}\n")

    summary = (
        f"constants (ours):  {len(info)}\n"
        f"live:              {len(live)}\n"
        f"dead:              {len(info) - len(live)}\n"
        f"  generated:       {len(generated)}\n"
        f"  attributed:      {len(attributed)}\n"
        f"  hard candidates: {len(hard)}\n"
        f"  soft candidates: {len(soft)}\n"
        f"modules with no live declaration: {len(empty_mods)}\n"
    )
    with open(os.path.join(out, "summary.txt"), "w") as fh:
        fh.write(summary)
    sys.stdout.write(summary)


if __name__ == "__main__":
    main()
