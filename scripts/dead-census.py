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

    scripts/dead-census.py [--out DIR] [--skip-lean] [--candidates FILE]

## LIVE = the union of

* the **capstone roots** (CAPSTONES below), the theorems
  `comparator.json` names, and every `theorem`/`def` the README links
  by name (``[`theorem X`](…)``) — the statements the project exists to
  make — and every declaration an OVERVIEW link names (its first
  backticked identifier, resolved in the linked module: the tour cites
  results no capstone is a corollary of, e.g. `parseChunks_ok_parseBytes`);
* the **executable closure**: `main`, in each of the two environments;
* everything the **test suite** (`ConLecheTests*`), the **Challenge**
  module, the **parked completeness work** (`ConLeche/Complete/*`: results,
  not corollaries — kept, and what they use with them) and the **pin
  certificates** (`ConLeche.PinGen.Certs`, read by
  name out of the built olean at pin-generation time — no static walk
  can see that) declare;
* every raw pin an **`#annotate_basis`/`#annotate_pins`** command names
  (read by name at elaboration time, like the pin certificates);
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

## THE CHALLENGE IS ITS OWN ENVIRONMENT (lane GATEFIX)

`ConLeche/Challenge.lean` restates `model_exists` and
`no_False_declaration` under the SAME names as `ConLeche/MainTheorem.lean`
(it is the challenge half of the Comparator pair), so the two cannot share
an environment: `importModules` either rejects the pair (when the two
statements differ — a stale Challenge olean, since `lake build` does not
build it) or silently keeps the first-imported copy (identical theorem
statements are tolerated), which made the census walk the Challenge's
`sorry` in place of the main theorem's proof.  The Challenge therefore gets
a third pass of its own; the driver builds it (and the test library) first.

## DEAD = DELETABLE TOGETHER (lane GATEFIX, after DNEW-B's fixpoint)

Name-level DEAD is closed under users by construction (a user of a dead
constant is dead), but it is not a deletion set: equation lemmas, match
auxiliaries, projections and constructors are not written in the source,
and a dead FIELD of a live structure cannot be cut on its own.  The
driver therefore folds every constant into its OWNER — the longest prefix
of its (de-privatised) name that is a source declaration of its own
module — and works at owner level: an owner is dead when none of its
constants is live.  The DELETION SET is then the fixpoint of the dead
owners (or of `--candidates FILE`, one name per line, intersected with
them) under two rules (DNEW-B's): an owner used by an owner outside the
set is held back, and a `@[simp]` owner is held back unless its whole
module goes (a `simp` use leaves no trace in the proof term).  Over the
full dead set the first rule never fires; with `--candidates` it is what
makes a partial deletion safe.

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
    deletable.txt  the deletion set: owner / module / constants folded in
    held.txt       dead owners (or candidates) held back, with the reason
    deletable-modules.txt  modules every owner of which is in the set
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

MODIFIERS = (r"(?:public\s+|private\s+|protected\s+|partial\s+|noncomputable\s+|meta\s+"
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
    "ConLeche.no_False_declaration",
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
                        "ConLeche.PinGen.Certs", "ConLeche.Complete")
CHALLENGE = "ConLeche.Challenge"
README_LINK_RE = re.compile(r"\[`(?:theorem|def)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)`\]"
                            r"\(https://[^)]*?/blob/[^/]+/([^#)]+)\.lean")
# OVERVIEW's links name their target more freely ("theorem `X` in `path`",
# "the list `X` in …", "`X`'s account in …"): the first backticked
# identifier of a link text into a `.lean` file, when the linked module
# declares it (a text naming a file or a prose topic resolves to nothing
# and seeds nothing).
OVERVIEW_LINK_RE = re.compile(r"\[[^\]`]*`([A-Za-z_][A-Za-z0-9_'!?.]*)`[^\]]*\]"
                              r"\(https://[^)]*?/blob/[^/]+/([^#)]+)\.lean")


def doc_seeds():
    """the theorems `comparator.json` names (full names), and the README's
    by-name links as (short name, module) pairs, resolved against the graph"""
    names, links = set(), set()
    try:
        import json
        cj = json.load(open(os.path.join(ROOT, "comparator.json")))
        names |= set(cj.get("theorem_names", [])) | set(cj.get("definition_names", []))
    except OSError:
        pass
    try:
        links |= {(n, path.replace("/", "."))
                  for n, path in README_LINK_RE.findall(open(os.path.join(ROOT, "README.md")).read())}
    except OSError:
        pass
    soft = set()
    try:
        soft |= {(n, path.replace("/", "."))
                 for n, path in OVERVIEW_LINK_RE.findall(open(os.path.join(ROOT, "OVERVIEW.md")).read())}
    except OSError:
        pass
    return names, links, soft


def lean_modules():
    """every module under `ConLeche/` but the Challenge (its own pass)"""
    mods = ["ConLeche"]
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "ConLeche")):
        dirnames.sort()
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, fn), ROOT)
                m = rel[:-5].replace("/", ".")
                if m != CHALLENGE:
                    mods.append(m)
    return mods


def build():
    """the passes read built oleans: the default targets, and the two
    libraries `lake build` leaves out (the tests, the Challenge)"""
    for cmd in (["lake", "build"], ["lake", "build", "ConLecheTests", CHALLENGE]):
        r = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if r.returncode != 0:
            sys.stderr.write(r.stdout.decode()[-4000:])
            sys.exit(1)


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
            if len(parts) < 4:
                continue
            name, mod, kind, deps = parts[:4]
            graph[name] = deps.split() if deps else []
            info[name] = (mod, kind)
    return graph, info, csimp


def module_file(mod):
    return mod.replace(".", "/") + ".lean"


def suffixes(name):
    parts = name.split(".")
    return [".".join(parts[i:]) for i in range(len(parts))]


# `#annotate_basis`/`#annotate_pins` (`Kernel/BasisGen.lean`) read their
# raw pins BY NAME at elaboration time (`| xA := xRaw`), like the pin
# certificates: the olean records no edge, so every identifier the command
# names (the raw pins, the `over` environment) is a seed, resolved in the
# invoking module.
ANNOTATE_RE = re.compile(r"^#annotate_\w+[^\n]*(?:\n[ \t]+[^\n]*)*", re.M)
ANNOTATE_RHS_RE = TOKEN_RE


def annotate_seeds():
    """(short name, module) for every raw pin an `#annotate_*` command names"""
    out = set()
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "ConLeche")):
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            path = os.path.relpath(os.path.join(dirpath, fn), ROOT)
            text = open(os.path.join(ROOT, path), errors="replace").read()
            mod = path[:-len(".lean")].replace("/", ".")
            for block in ANNOTATE_RE.findall(text):
                out |= {(n, mod) for n in ANNOTATE_RHS_RE.findall(block)}
    return out


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
                    help="reuse the three raw passes already in --out")
    ap.add_argument("--candidates", metavar="FILE",
                    help="restrict the deletion set to these names (one per line)")
    args = ap.parse_args()
    out = os.path.join(ROOT, args.out)
    os.makedirs(out, exist_ok=True)

    p1 = os.path.join(out, "pass-main.tsv")
    p2 = os.path.join(out, "pass-pindump.tsv")
    p3 = os.path.join(out, "pass-challenge.tsv")
    if not args.skip_lean:
        build()
        run_lean(lean_modules() + ["Main", "ConLecheTests"], p1)
        run_lean(lean_modules() + ["PinDump"], p2)
        run_lean([CHALLENGE], p3)

    graph, info, csimp = read_pass(p1)
    for extra in (p2, p3):
        g2, i2, c2 = read_pass(extra)
        for n, ds in g2.items():
            if n in graph:
                graph[n] = sorted(set(graph[n]) | set(ds))
            else:
                graph[n], info[n] = ds, i2[n]
        csimp |= c2
    challenge_decls = {n for n, (mod, _k) in read_pass(p3)[1].items() if mod == CHALLENGE}
    clash = sorted(n for n in challenge_decls if info[n][0] != CHALLENGE)
    if clash:
        sys.stdout.write(f"challenge/main clash (kept apart, main's module recorded): "
                         f"{' '.join(clash)}\n")

    decls, attrs, registered, elab_files, tokens = source_index()

    # ---- seeds -------------------------------------------------------
    comparator, links, overview = doc_seeds()
    named_seeds = set(CAPSTONES) | comparator
    missing = sorted(n for n in named_seeds if n not in graph)
    for short, mod in sorted(links):
        hits = {n for n, (m, _k) in info.items()
                if m == mod and (n == short or n.endswith("." + short))}
        if hits:
            named_seeds |= hits
        else:
            missing.append(f"{short} (README link into {mod})")
    for short, mod in sorted(overview | annotate_seeds()):
        named_seeds |= {n for n, (m, _k) in info.items()
                        if m == mod and (n == short or n.endswith("." + short))}
    if missing:
        sys.stderr.write("dead-census: seed names that no longer exist: "
                         + " ".join(missing) + "\n")
        sys.exit(1)
    seeds = named_seeds | csimp | challenge_decls
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

    # a `partial def f` is an opaque constant whose code is `f._unsafe_rec`;
    # the dump has no edge between them, so a live `f` would leave its
    # body's callees dead
    for n in list(graph):
        if n.endswith("._unsafe_rec"):
            parent = n[: -len("._unsafe_rec")]
            if parent in graph:
                graph[parent] = sorted(set(graph[parent]) | {n})

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

    # ---- owners, and the deletion set -------------------------------
    def has_source(name):
        mod = info[name][0]
        u = name
        pp = "_private." + mod + ".0."
        if u.startswith(pp):
            u = u[len(pp):]
        own = module_file(mod)
        return any(own in decls.get(x, ()) for x in suffixes(u))

    def owner(name, depth=0):
        """a source declaration owns itself; a generated constant (an
        equation lemma, a matcher, a projection, a constructor — realised
        in whatever module first needed it) is owned by the owner of its
        longest proper prefix that is a constant of ours"""
        if has_source(name):
            return name
        pp = "_private." + info[name][0] + ".0."
        u = name[len(pp):] if name.startswith(pp) else name
        parts = u.split(".")
        for k in range(len(parts) - 1, 0, -1):
            pre = ".".join(parts[:k])
            # a lemma realised in the private scope names a public
            # constant's `_private` twin, and vice versa
            for c in (pp + pre, pre):
                if c in info and depth < 8:
                    return owner(c, depth + 1)
        return None

    own_of = {n: owner(n) for n in info}
    members = defaultdict(set)
    for n, o in own_of.items():
        members[o or n].add(n)
    owner_mod = {o: info[next(iter(ns))][0] for o, ns in members.items()}
    # Lean SHARES a matcher (`f.match_3`, its `_sparseCasesOn`, `splitter`
    # and equations) with every later definition that matches on the same
    # patterns, so a matcher's liveness or users say nothing about `f`: a
    # deleted `f`'s matcher is simply re-created by the next user.
    def is_matcher(n):
        return any(c.startswith(("match_", "_sparseCasesOn"))
                   for c in n.split(".")[1:])

    live_owner = {o for o, ns in members.items()
                  if ((o in live) if (o in info and has_source(o)) else (ns & live))}
    users = defaultdict(set)
    for n, ds in graph.items():
        on = own_of.get(n) or n
        for d in ds:
            od = own_of.get(d) or d
            if od != on and not is_matcher(d):
                users[od].add(on)

    def is_simp(o):
        own = module_file(owner_mod[o])
        return any("simp" in attrs.get((x, own), ()) for x in suffixes(o))

    held = {}
    sourced = {o for o in members if o in info and has_source(o)}
    cand = {o for o in sourced if o not in live_owner}
    if args.candidates:
        want = {l.strip() for l in open(args.candidates) if l.strip()}
        want_own = {own_of.get(w) or w for w in want}
        for w in sorted(want_own):
            if w not in members:
                held[w] = "unknown name"
            elif w in live_owner:
                held[w] = "live"
        cand &= want_own
    S = set(cand)
    mod_owners = defaultdict(set)
    for o in members:
        mod_owners[owner_mod[o]].add(o)
    while True:
        changed = False
        for o in sorted(S):
            out_users = sorted(u for u in users[o] if u not in S)
            if out_users:
                S.discard(o); held[o] = "used by " + " ".join(out_users[:3]); changed = True
            elif is_simp(o) and not mod_owners[owner_mod[o]] <= S:
                S.discard(o); held[o] = "@[simp], module survives"; changed = True
        if not changed:
            break
    with open(os.path.join(out, "deletable.txt"), "w") as fh:
        for o in sorted(S):
            fh.write(f"{o}\t{owner_mod[o]}\t{len(members[o])}\n")
    with open(os.path.join(out, "held.txt"), "w") as fh:
        for o in sorted(held):
            fh.write(f"{o}\t{owner_mod.get(o, '?')}\t{held[o]}\n")
    whole = sorted(m for m, os_ in mod_owners.items() if os_ <= S)
    with open(os.path.join(out, "deletable-modules.txt"), "w") as fh:
        for m in whole:
            fh.write(m + "\n")

    summary = (
        f"constants (ours):  {len(info)}\n"
        f"live:              {len(live)}\n"
        f"dead:              {len(info) - len(live)}\n"
        f"  generated:       {len(generated)}\n"
        f"  attributed:      {len(attributed)}\n"
        f"  hard candidates: {len(hard)}\n"
        f"  soft candidates: {len(soft)}\n"
        f"modules with no live declaration: {len(empty_mods)}\n"
        f"owners:            {len(members)} ({len(live_owner)} live)\n"
        f"deletion set:      {len(S)} owners, {sum(len(members[o]) for o in S)} constants"
        f" ({len(held)} held back); {len(whole)} modules whole\n"
    )
    with open(os.path.join(out, "summary.txt"), "w") as fh:
        fh.write(summary)
    sys.stdout.write(summary)


if __name__ == "__main__":
    main()
