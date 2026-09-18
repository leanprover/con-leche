#!/usr/bin/env python3
"""Phase 3's plan: which import edges may stop being `public`.

TWO constraints, both of them about the PUBLIC closure — a private import
gives the importer the imported module's public interface and nothing more:

  coverage   for every constant a module mentions ANYWHERE (proof terms
             included), some DIRECT import of it must carry that constant
             publicly.  This is what the first attempt missed: demoting an
             edge three tiers down breaks a module that never mentions it.
  publicness a module's import must be PUBLIC when the module's own public
             interface (scripts/pub-iface.lean) needs something that import
             carries.

Everything starts public; an edge is demoted only when neither constraint
breaks anywhere.  The build is the confirmation, not the search.

TWO MODES.

    scripts/pub-import-plan.py            the PLAN: run the fixpoint from the
                                          all-public tree and write
                                          $PUBPLAN_DIR/plan.json for
                                          scripts/pub-import-apply.py.
    scripts/pub-import-plan.py --check    the GATE (task #235): start from the
                                          tree's ACTUAL `public import` set
                                          and report every edge that is
                                          individually demotable.  Exit 1 if
                                          any is — the tree is then not at a
                                          local minimum.

The gate deliberately does NOT compare against a freshly computed plan: the
fixpoint is greedy, so its result depends on the order it tries edges in, and
a plan edge that is plain here and public there is not a finding.  "No public
import can be demoted on its own" is order-independent.

Inputs (regenerate with `tests/shake.sh`, which is this script's caller in the
standard battery):

    $PUBPLAN_DIR/census.tsv   lake env lean --run scripts/dead-census.lean <mods>
    $PUBPLAN_DIR/pub.tsv      lake env lean --run scripts/pub-iface.lean   <mods>

`$PUBPLAN_DIR` defaults to `_tmp/m3`.
"""
import re, subprocess, json, collections, os, sys

CHECK = '--check' in sys.argv[1:]
DIR   = os.environ.get('PUBPLAN_DIR', '_tmp/m3')

# THE PER-FILE FALLBACK (task #231 phase 3, kept by task #235).  The model is
# a filter on candidate demotions, never a claim, and two files' re-exports
# are reached by DOT-NOTATION, which no census row and no source-identifier
# scan can attribute to a module: `RecCtorsStored.cons` in Model/Install and
# a lemma of the Denote tier in Semantics/IndRecsCore.  Demoting these builds
# a tree whose `rfl`s stop closing, so they stay public and the gate must not
# ask for them again.
FALLBACK = {
    # task #315 M5: `DeclNestedRun` is an exposed `def … : Prop` whose
    # STATEMENT names the nested route's own vocabulary (`NestedParts`,
    # `ElimState`, `AuxStored`, the stage functions) and whose companion
    # `declNestedRun_of` is `checkNested_inv`; the census attributes
    # those to the proof, so the checker asks for the demotion and the
    # compiler refuses it.
    ('ConLeche.Semantics.Inductives.DeclNested', 'ConLeche.Kernel.Inductives.NestedInstall'),
    ('ConLeche.Semantics.Inductives.DeclNested', 'ConLeche.Verify.Inductives.NestedInv'),
    ('ConLeche.Model.Install',        'ConLeche.Model.Annot.BitExtend'),
    ('ConLeche.Model.Install',        'ConLeche.Semantics.ConstsBound'),
    ('ConLeche.Model.Install',        'ConLeche.Verify.Extend.Sibs'),
    ('ConLeche.Semantics.IndRecsCore','ConLeche.Verify.Denote.EnvExt'),
    ('ConLeche.Semantics.IndRecsCore','ConLeche.Verify.Denote.Levels'),
    # task #253: `PushChain` is an exposed `def … : Prop` whose BODY names
    # `NodupNames` (EnvBound); the model reads statements, not exposed
    # bodies, and the compiler wants the re-export.
    ('ConLeche.Verify.Cached.PushChain','ConLeche.Verify.EnvBound'),
    # task #285: `BasisGen` declares the `#annotate_basis` COMMAND, and
    # `TrustAxioms` invokes it through `BasisA`'s re-export.  A command
    # elaborator is registered, not named, so no census row attributes it —
    # demoting the line makes `TrustAxioms` fail to parse (`unexpected
    # token '#'`), which is task #235's third blind class seen from the
    # other side.  (The fixpoint is order-dependent: this edge became a
    # demotion candidate only when #285 changed the graph around it.)
    ('ConLeche.Kernel.BasisA','ConLeche.Kernel.BasisGen'),
    # task #315 U-10: the one-import-view class of U-5/U-7 again — the plan
    # proposed demoting EVERY public import of these files, which leaves
    # their statements without `SetTheory`/`Name`/`Env`/`NoProjEnv`/
    # `consMutualFormers` in the public view ("Unknown identifier … imported
    # privately"); one re-export each stays.
    # task #315 U-12: `NestedSlotRead`'s three re-exports became demotion
    # candidates when the M5 merge changed the graph around them (the
    # fixpoint is order-dependent).  Demoting all three empties the file's
    # public view (`Name`/`Level`/`Expr` unknown); demoting `Verify.Subst`
    # alone leaves the EXPOSED `def`s `Expr.absConstAt`/`absMembersGo`
    # naming `fvarsBelow`/`substFvarAt` privately ("unknown identifier",
    # task #253's class), and without `Annot.Bit` the proofs' `rfl`s stop
    # closing.  U-11 applied the plan's own `--only` result; it stays.
    ('ConLeche.Model.Inductives.NestedSlotRead','ConLeche.Model.Annot.EnvModel'),
    ('ConLeche.Model.Inductives.NestedSlotRead','ConLeche.Model.Annot.Bit'),
    ('ConLeche.Model.Inductives.NestedSlotRead','ConLeche.Verify.Subst'),
    # task #315 U-17: `auxStored_ctor_eq`'s PUBLIC statement projects
    # `b.ownOffset` (dot-notation on `MutualBlock.ownOffset`, MutualGrouped);
    # the census cannot attribute a field projection, the checker asks for
    # the demotion and the compiler refuses it ("environment does not
    # contain `MutualBlock.ownOffset`").
    ('ConLeche.Verify.Inductives.NestedAuxInv','ConLeche.Verify.Inductives.MutualGrouped'),
    ('ConLeche.Model.Inductives.BlockRecBridge','ConLeche.Model.Inductives.BlockRecWD'),
    ('ConLeche.Model.Inductives.MutualNoProj','ConLeche.Model.Inductives.TowerCons'),
    ('ConLeche.Model.Inductives.MutualNoProj','ConLeche.Verify.Inductives.MutualInv'),
    # task #290: every statement of `Verify/Frontend/Local.lean` is over
    # Naive's `NRes`, `isDigit`, `isWs`; the model calls the edge demotable
    # (the private `import Scan.Equiv` covers the constants), but a private
    # import is invisible to a public statement — the build says
    # `unknown identifier NRes`.
    ('ConLeche.Verify.Frontend.Local','ConLeche.Frontend.Scan.Naive'),
    # task #315 L-B (§U.23): `NestedPins`' one public import is the file's
    # whole public view — `NestedLoop` is where `SetTheory` reaches it, and
    # the edge became a demotion candidate when `NestedCopyIdx` (a public
    # importer of `NestedPins`) changed the graph around it (the fixpoint is
    # order-dependent); demoting it: `unknown identifier SetTheory`.
    ('ConLeche.Model.Inductives.NestedPins','ConLeche.Model.Inductives.NestedLoop'),
    # task #315 L-B (§U.23 (e)/(g)): the `inst` kit's one-import views —
    # `mkPisB` (NestedRestoreOpen), the elimination's records
    # (NestedElimInv) and the telescope kit (NestedCopyTele) reach the
    # files' PUBLIC statements through these re-exports; the checker calls
    # the edges demotable after integration 2 changed the graph, the
    # compiler refuses ("unknown identifier" / "invalid field notation").
    # task #315 M7-2 (item 5 step 2c): the rule's reading law added PLAIN
    # imports to both of its files (`BlockRepCross`/`MutualRecsSwap`/
    # `MutualRecsStore` for the provision crossings, `Verify.Denote.Install`
    # for the `findProj?` API), and the coverage model then attributes the
    # vocabulary to those private edges and calls the one re-export each
    # file lives on demotable — the one-import-view class again, seen from
    # the graph change.  Probed one at a time: the kit loses
    # `Env`/`Name`/`Expr`/`Level`, `NestedRecRule` loses
    # `NestedScratchOut`/`NestedCtorPinNames`/`NestedRecTysAuxOk` without
    # `NestedRecEqs` and `nestedRecLeaf`/`nestedProvList`/`NestedTailIn`'s
    # projections without `NestedRecsStore`.
    ('ConLeche.Verify.Inductives.NestedRecRuleKit','ConLeche.Verify.Inductives.NestedInv'),
    ('ConLeche.Model.Inductives.NestedRecRule','ConLeche.Model.Inductives.NestedRecEqs'),
    # task #315 M7-2 (item 5 step 2d): the auxiliary rule's reading is
    # stated at `BlockModel.ruleRhsAV` (MutualRecsLaw), which the PUBLIC
    # statement of `NestedTailIn.auxRuleRead` projects by dot-notation off
    # the scratch block model — the `MutualBlock.ownOffset` class above: no
    # census row attributes a field projection, so the checker asks for the
    # demotion and the compiler refuses it ("environment does not contain
    # `BlockModel.ruleRhsAV`").
    ('ConLeche.Model.Inductives.NestedRecRule','ConLeche.Model.Inductives.MutualRecsLaw'),
    ('ConLeche.Model.Inductives.NestedRecRule','ConLeche.Model.Inductives.NestedRecsStore'),
    ('ConLeche.Verify.Inductives.NestedCopyInstU','ConLeche.Verify.Inductives.NestedRestoreOpen'),
    ('ConLeche.Verify.Inductives.NestedCopyKinds','ConLeche.Verify.Inductives.NestedRestoreOpen'),
    ('ConLeche.Verify.Inductives.NestedCopyProv','ConLeche.Verify.Inductives.NestedElimInv'),
    ('ConLeche.Verify.Inductives.NestedCopyRewrite','ConLeche.Verify.Inductives.NestedCopyTele'),
    # task #315 L-B (§U.44): the same class at the normalisation's frame —
    # `NestedCopyNorm`'s public statements name `Env`, `Name`, `EnvWF`,
    # `openPisAtFvars`, `closeTelescope`, `Expr.ErasedEq` and the three
    # `norm*` functions, all of which reach it only through these two
    # re-exports; the checker calls both demotable, the compiler refuses
    # (`unknown identifier Env`).
    ('ConLeche.Verify.Inductives.NestedCopyNorm','ConLeche.Verify.Inductives.NestedCopyTele'),
    ('ConLeche.Verify.Inductives.NestedCopyNorm','ConLeche.Verify.Inductives.MutualNormPres'),
    # task #315 L-B (§U.34): the assembly's one public import is its whole
    # public view — `SetTheory`, `EnvModelM`, `NestedPinsRun`,
    # `NestedPinGroupSyn`, `PinData` and the block lists reach its
    # statements only through this re-export; the edge became a demotion
    # candidate when session 5's own theorems changed the graph around it
    # (the fixpoint is order-dependent), and the compiler refuses it
    # (`unknown identifier SetTheory`).
    ('ConLeche.Model.Inductives.NestedCopyInst','ConLeche.Model.Inductives.NestedCopyRead'),
    # task #315 U-7: `MutualIdxUniv`'s one public import is likewise the
    # file's whole public view — demoting it kills its own
    # `variable [SetTheory V]` (`unknown identifier SetTheory`).
    ('ConLeche.Model.Inductives.MutualIdxUniv','ConLeche.Model.Inductives.StructData'),
    # task #315 U-7: `MutualIdxUniv`'s public STATEMENTS name `restrictΨ`
    # (`formerLevels_of`) and `IdxOk` (`formerIdxOk`), which reach the file
    # only through `FixStageRec`'s closure — task #290's class: a private
    # import is invisible to a public statement (`unknown identifier`).
    ('ConLeche.Model.Inductives.MutualIdxUniv','ConLeche.Model.Inductives.FixStageRec'),
    # task #315 U-16: `InstAll`'s one public import is the file's whole
    # public view — demoting it kills its own `variable [SetTheory V]`
    # (`unknown identifier SetTheory`), the `MutualIdxUniv` class.
    ('ConLeche.Semantics.Tower.InstAll','ConLeche.Semantics.Tower.SumRecCase'),
    # task #315 U-16: the two nested Verify modules' one public import is
    # their whole public view (their statements name `Env`, `Expr`, the
    # kernel's nested functions) — the same class.
    ('ConLeche.Verify.Inductives.NestedAuxInv','ConLeche.Kernel.Inductives.NestedInstall'),
    ('ConLeche.Verify.Inductives.NestedElimInv','ConLeche.Kernel.Inductives.NestedInstall'),
    # task #315 U-18: `NestedRecNames`'s statements name `AuxStored`/`Env`
    # — the same class (the demotion the gate proposed is refused by the
    # compiler).
    ('ConLeche.Verify.Inductives.NestedRecNames','ConLeche.Kernel.Inductives.NestedInstall'),
    # task #315 U-19: the check called these five demotable and the
    # compiler refused each — `NestedStageCtor`'s statements reach
    # `SetTheory` only through `SumData`/`MutualTagI`'s public closure and
    # the kernel's nested functions through `NestedInstall`;
    # `NestedRestoreTbl`'s name `NestedParts`/`ElimState`/`restoreTbl`
    # (`NestedInstall`) and the `restoreWalk` kit (`NestedInv`) — the
    # same class.
    ('ConLeche.Model.Inductives.NestedStageCtor','ConLeche.Kernel.Inductives.NestedInstall'),
    ('ConLeche.Model.Inductives.NestedStageCtor','ConLeche.Model.Inductives.SumData'),
    ('ConLeche.Model.Inductives.NestedStageCtor','ConLeche.Semantics.Tower.MutualTagI'),
    ('ConLeche.Verify.Inductives.NestedRestoreTbl','ConLeche.Kernel.Inductives.NestedInstall'),
    ('ConLeche.Verify.Inductives.NestedRestoreTbl','ConLeche.Verify.Inductives.NestedInv'),
    # task #315 U-20: two of the eleven demotions the gate proposed when U-19
    # and U-19b were merged, refused by the compiler — `NestedPins`'s
    # `variable` binders reach `SetTheory` only through `NestedLoop`'s
    # public closure (the same class), and `NestedTransfer`'s public
    # statements name `Expr.eraseAnnots` (a public statement is elaborated
    # in the public view, where a plain import is invisible).  Lane L-A
    # met the first on its own base too (the edge became a candidate
    # there when `NestedPinsU`'s exposed `def` left the file — the same
    # order-dependence); one entry.
    ('ConLeche.Model.Inductives.NestedPins','ConLeche.Model.Inductives.NestedLoop'),
    ('ConLeche.Model.Inductives.NestedTransfer','ConLeche.Verify.EraseAnnots'),
    # task #315: `BlockRecWD`'s one public import is the file's whole
    # public view (`SetTheory`, `BlockReadings`, `BlockReps`, the datum);
    # the model calls it demotable (nothing downstream re-exports through
    # it that a STATEMENT names — `DeclBlock`'s needs are in exposed
    # `def … : Prop` BODIES, task #253's class), and demoting it makes the
    # file's own `variable [SetTheory V]` fail to resolve.
    ('ConLeche.Model.Inductives.BlockRecWD','ConLeche.Model.Inductives.BlockRecTyped'),
    # task #315 M7-2: `NestedRecFrames`'s three re-exports became demotion
    # candidates when §1e's own theorems changed the graph around them (the
    # fixpoint is order-dependent).  Each is refused by the compiler, the
    # `MutualIdxUniv`/`NestedPins` class: without `NestedRecCtor` the file's
    # `variable [SetTheory V]` and `OpenersFrom` are unknown in the public
    # view, without `NestedRecTypes` its statements lose `nestedRecCvAt`,
    # and without `NestedRestoreTbl` they lose `PinsAligned` — probed one at
    # a time, each demotion alone fails to build.
    ('ConLeche.Model.Inductives.NestedRecFrames','ConLeche.Model.Inductives.NestedRecCtor'),
    ('ConLeche.Model.Inductives.NestedRecFrames','ConLeche.Model.Inductives.NestedRecTypes'),
    ('ConLeche.Model.Inductives.NestedRecFrames','ConLeche.Verify.Inductives.NestedRestoreTbl'),
    # task #315 M7-2 (§U.29 (yyy)): the store swap's two files hold ONLY
    # theorems — bar the one `def nestedProvOf`, whose re-export the model
    # DOES see and does not ask for.  A theorem's STATEMENT is public but
    # its constants are attributed to the proof, so the model computes an
    # empty public need for both files and proposes demoting every other
    # re-export.  Each demotion is refused by the compiler, probed one at a
    # time: without `Verify.EnvWF` the WF file's `EnvWF env` is an unknown
    # identifier; in the swap file `Annot.EnvModelM` is where `SetTheory`
    # reaches the public view, `IndBlockFacts` where `SwapNResS` does,
    # `Extend.Recs` where `SwapShList` does and `NestedRecsWF` where
    # `storeNestedRecs` does.
    ('ConLeche.Verify.Inductives.NestedRecsWF','ConLeche.Verify.EnvWF'),
    ('ConLeche.Model.Inductives.NestedRecsSwap','ConLeche.Verify.Inductives.NestedRecsWF'),
    ('ConLeche.Model.Inductives.NestedRecsSwap','ConLeche.Semantics.IndBlockFacts'),
    ('ConLeche.Model.Inductives.NestedRecsSwap','ConLeche.Model.Annot.EnvModelM'),
    ('ConLeche.Model.Inductives.NestedRecsSwap','ConLeche.Verify.Extend.Recs'),
    # task #315 M7-2 (§U.29): the STORE'S RUN file is the same class one file
    # further on — its public statements are theorems bar three `def … : Prop`
    # (`nestedStoreList`, the two faces), so the census attributes almost
    # everything to the proofs and proposes demoting all three re-exports.
    # Each is refused by the compiler, probed one at a time: without
    # `NestedRecRule` the statements lose `nestedProvList`, `nestedRecCvAt`
    # and `nestedRulesAt`, without `NestedRecsWF` they lose
    # `ConLeche.nestedProvOf`, and without `NestedTables` the recorded
    # tables' face loses `NestedMemberTableOk`.
    ('ConLeche.Model.Inductives.NestedStoreRun','ConLeche.Model.Inductives.NestedRecRule'),
    ('ConLeche.Model.Inductives.NestedStoreRun','ConLeche.Verify.Inductives.NestedRecsWF'),
    ('ConLeche.Model.Inductives.NestedStoreRun','ConLeche.Model.Inductives.NestedTables'),
}

files=[f for f in subprocess.check_output(['git','ls-files','*.lean']).decode().split()
       if not f.startswith(('tests/e2e/src/','tests/trust-surface/','_probe/','bridge/','scripts/'))]
mod=lambda f: f[:-5].replace('/','.')
fileof={mod(f):f for f in files}
UMBRELLA={'ConLeche.lean','ConLeche/Term.lean','ConLeche/SetModel.lean','ConLeche/Semantics.lean',
          'ConLeche/Model.lean','ConLeche/Verify/Cached.lean','ConLeche/Verify/Denote.lean',
          'ConLeche/Kernel/Basis.lean'}
# frozen: the umbrellas exist to re-export, the classic roots have no `public`
# keyword, `tests/*` and the PinGen generator are outside the census roots.
CLASSIC={'tests/ProofDeps.lean','PinDump.lean'}
FROZEN_PREFIX=('tests/','ConLeche/PinGen/','ConLeche/Challenge.lean','ConLeche/PinGen.lean')
EXT=('Std','Lean','Init')

def imports(f):
    out=[]
    for i,l in enumerate(open(f).read().split('\n')):
        m=re.match(r'^(public\s+)?(meta\s+)?import\s+(all\s+)?([A-Za-z0-9_.]+)\s*$', l)
        if m and not m.group(3):
            out.append((i, bool(m.group(1)), bool(m.group(2)), m.group(4)))
    return out

mods=sorted(fileof)
idx={m:i for i,m in enumerate(mods)}
bit={m:1<<i for m,i in idx.items()}

# --- the graph: every non-meta, non-external import edge
D={m:[] for m in mods}
for m in mods:
    for _,_,ismeta,t in imports(fileof[m]):
        if ismeta or t.startswith(EXT): continue
        if t in idx: D[m].append(t)

# --- reach: every module whose constants this module mentions at all
declmod={}
deps=collections.defaultdict(set)
for line in open(DIR+'/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<3: continue
    declmod[p[0]]=p[1]
for line in open(DIR+'/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<4: continue
    for c in p[3].split():
        dm=declmod.get(c)
        if dm and dm in idx and dm!=p[1]: deps[p[1]].add(dm)
reach={m: 0 for m in mods}
for m,s in deps.items():
    if m in idx: reach[m]=sum(bit[x] for x in s if x in idx)

# --- opens: a bare `open N` needs N to EXIST in this module's view, which
# means some module in its cover must declare a constant under that prefix.
# (DESIGN #223 records this as the criterion `shake` misses.)
nsmods=collections.defaultdict(set)
for n,dm in declmod.items():
    parts=n.split('.')
    for k in range(1,len(parts)):
        nsmods['.'.join(parts[:k])].add(dm)
opens={}
for m in mods:
    src=open(fileof[m]).read()
    ns=set()
    for mm in re.finditer(r'^\s*open\s+([^\n]*)', src, re.M):
        seg=mm.group(1).split('--')[0]
        seg=re.sub(r'\(.*?\)','',seg)
        for tok in seg.replace(' in','').split():
            if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', tok) and tok not in ('in','scoped'):
                ns.add(tok)
    opens[m]=[sum(bit[x] for x in nsmods.get(n,()) if x in idx) for n in sorted(ns)]
    opens[m]=[b for b in opens[m] if b]

# --- source identifiers: a lemma named in a TACTIC argument (`simp [f]`,
# `exact h`, …) need not appear in the resulting proof term, so the census
# does not see it.  Add every identifier the source mentions whose name has a
# unique declaring module.  This can only keep MORE imports public, never
# fewer — soundness over aggressiveness.
sufmods=collections.defaultdict(set)
for n,dm in declmod.items():
    if dm not in idx: continue
    parts=n.split('.')
    for k in range(len(parts)):
        sufmods['.'.join(parts[k:])].add(dm)
srcneed={}
for m in mods:
    src=open(fileof[m]).read()
    acc=0
    for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.'!?]*", src)):
        ms=sufmods.get(tok)
        if ms and len(ms)==1:
            d=next(iter(ms))
            if d!=m: acc |= bit[d]
    srcneed[m]=acc

need={m:0 for m in mods}
for line in open(DIR+'/pub.tsv'):
    if '\t' not in line: continue
    m,rest=line.rstrip('\n').split('\t',1)
    if m in idx: need[m]=sum(bit[x] for x in rest.split() if x in idx)

# --- topological order
order=[]; seen=set()
def visit(m, st=()):
    if m in seen or m in st: return
    for t in D[m]: visit(t, st+(m,))
    seen.add(m); order.append(m)
for m in mods: visit(m)

# A module can only depend on what it imports.  The census walks the FINAL
# environment and adds `@[csimp]`/`@[implemented_by]` edges, which an attribute
# in a LATER module can create — those are not import edges and show up as
# impossible backwards dependencies (`Kernel/ExprOps` "needing" `Verify/Level`).
# Restrict both sets to each module's real transitive import closure.
allcl={}
for m in order:
    acc=bit[m]
    for t in D[m]: acc |= allcl.get(t, bit.get(t,0))
    allcl[m]=acc
for m in mods:
    reach[m] = (reach[m] | srcneed[m]) & allcl[m]
    need[m]  &= allcl[m]

P={m:set(D[m]) for m in mods}                    # public imports; start: all

def closures():
    cl={}
    for m in order:
        acc=bit[m]
        for t in P[m]:
            acc |= cl.get(t, bit.get(t,0))
        cl[m]=acc
    return cl

_OKBASE=set()

def violations(cl):
    """Every constraint the configuration `P` breaks, as a set of tokens."""
    out=set()
    for m in mods:
        cov=bit[m]
        pubcov=0
        for t in D[m]:
            cov |= cl[t]
            if t in P[m]: pubcov |= cl[t]
        if reach[m] & ~cov: out.add(('cover', m))
        if need[m] & ~pubcov: out.add(('pub', m))
        for j,b in enumerate(opens[m]):
            if not (b & cov): out.add(('open', m, j))
    return out

def ok(cl):
    return violations(cl) <= _OKBASE

# The STARTING tree is correct by construction — it is the tree that builds —
# so anything the model reports there is the MODEL's imprecision (an `open`
# picked out of a docstring line; a match auxiliary the census attributes to
# the module that first generated it).  Record those and require only that
# nothing gets worse — the model is a filter on candidate demotions, never a
# claim.
def _rebase(label):
    global _OKBASE
    _OKBASE=set()
    b=violations(closures())
    if b: print(f'model imprecision at {label} (ignored):', sorted(b))
    _OKBASE=b

_rebase('baseline')

frozen={m for m in mods
        if fileof[m] in UMBRELLA or fileof[m] in CLASSIC
        or fileof[m].startswith(FROZEN_PREFIX)}
# every module we are allowed to narrow MUST be covered by the census, or its
# dependency set is silently empty and the fixpoint will happily strip it bare
# (that is what an incomplete root list did on the first run: the whole
# `Frontend/*` cone had no rows and lost every re-export).
seen_mods={l.split('\t')[1] for l in open(DIR+'/census.tsv') if '\t' in l}
missing=[m for m in mods if m not in frozen and m not in seen_mods]
assert not missing, f'census does not cover: {missing[:6]} ({len(missing)} modules)'
tot=sum(len(D[m]) for m in mods)

if CHECK:
    # The tree as it stands: an edge is public iff its line says `public`.
    for m in mods:
        pubs=set()
        for _,ispub,ismeta,t in imports(fileof[m]):
            if ismeta or t.startswith(EXT) or t not in idx: continue
            if ispub: pubs.add(t)
        P[m]=pubs & set(D[m])
    _rebase('the tree as it stands')
    bad=[]
    for m in mods:
        if m in frozen: continue
        for t in sorted(P[m]):
            if (m,t) in FALLBACK: continue
            P[m].discard(t)
            if ok(closures()): bad.append((m,t))
            P[m].add(t)
    pub=sum(len(P[m]) for m in mods)
    if bad:
        print(f'DEMOTABLE `public import` ({len(bad)}) — `public import X` is for a '
              're-export something else\'s PUBLIC statement needs:')
        for m,t in bad: print(f'  {fileof[m]}: public import {t}')
        raise SystemExit(1)
    print(f'pub-imports: {pub} of {tot} in-tree edges public, none demotable '
          f'({len(FALLBACK)} dot-notation fallbacks)')
    raise SystemExit(0)

changed=True
while changed:
    changed=False
    for m in reversed(order):                    # importers first
        if m in frozen: continue
        for t in sorted(P[m]):
            P[m].discard(t)
            if ok(closures()):
                changed=True
            else:
                P[m].add(t)
pub=sum(len(P[m]) for m in mods)
print(f'{pub} of {tot} in-tree import edges must stay public  ->  {tot-pub} narrow')
json.dump({m:sorted(P[m]) for m in mods}, open(DIR+'/plan.json','w'))
