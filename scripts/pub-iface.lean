import Lean
open Lean

/-!
# `scripts/pub-iface.lean` — what each module's PUBLIC interface depends on
(task #231 phase 3)

`public import X` is needed exactly when this module's own **public
interface** mentions something that only `X`'s public interface carries.
Phase 2's finding is why this cannot be decided from the compiler's error
messages: a missing re-export does not produce an "unknown identifier" — the
name still resolves through the private import — it produces a `rfl` that
stops closing, a `simp only` that makes no progress, or an instance that goes
stuck, none of which name the module at fault.

So the oracle reads the environment in the **exporting view**
(`Environment.setExporting`), which is precisely what an importer sees
through a `public import`:

* a declaration absent from that view is `private`: it contributes nothing;
* a declaration present contributes the constants of its **type** — its
  statement is interface — and, when its body survived into the public view
  (i.e. it is `@[expose]`d), the constants of its **value** too.

**NOT SUFFICIENT ON ITS OWN** (task #231 phase 3, first attempt).  This says
which modules a module's public interface needs; narrowing on that alone
breaks the tree, because a *private* import also gives the importer only the
imported module's PUBLIC closure.  So there are two constraints, not one:

* *publicness* — `M`'s import of `I` must be public when `M`'s own public
  interface needs something in `I`'s public closure (this file);
* *coverage* — for every constant `M` mentions ANYWHERE (proof terms
  included), some direct import of `M` must carry it publicly.  Demoting an
  import three tiers down can therefore break a module that never mentions
  that import at all.

The second needs the reference set from `scripts/dead-census.lean` and a
fixpoint over the import DAG: start with every edge public, and demote an
edge only when no module's coverage breaks.  Recorded here so the next
attempt does not repeat the first one's mistake.

Output, one line per module of ours:

    <module> \t <needed-module> <needed-module> …

where the right-hand side is the set of modules declaring those constants,
restricted to ours (a prelude constant is reachable from every module).

    lake env lean --run scripts/pub-iface.lean ConLeche ConLeche.Model …
-/

def ours (m : Name) : Bool :=
  m == `ConLeche || Name.isPrefixOf `ConLeche m || m == `Main || m == `PinDump
    || m == `ConLecheTests || Name.isPrefixOf `ConLecheTests m

partial def constsOf (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => constsOf a (constsOf f acc)
  | .lam _ t b _ | .forallE _ t b _ => constsOf b (constsOf t acc)
  | .letE _ t v b _ => constsOf b (constsOf v (constsOf t acc))
  | .mdata _ b => constsOf b acc
  | .proj n _ b => constsOf b (acc.insert n)
  | _ => acc

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mods := args.map (·.toName)
  let env ← importModules ((mods.map fun m => ({ module := m } : Import)).toArray) {}
  let pub := env.setExporting true
  -- module index -> name
  let names := env.header.moduleNames
  let mut need : Std.HashMap Name NameSet := Std.HashMap.emptyWithCapacity
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := names[idx.toNat]!
    unless ours m do continue
    -- the PUBLIC presentation: absent = private, `axiomInfo` = body hidden
    let some ci := pub.find? n | continue
    let mut cs := constsOf ci.type (NameSet.empty)
    if let some v := ci.value? then
      cs := constsOf v cs
    let mut s := need.getD m NameSet.empty
    for c in cs do
      if let some j := env.getModuleIdxFor? c then
        let dm := names[j.toNat]!
        if ours dm && dm != m then s := s.insert dm
    need := need.insert m s
  for (m, s) in need.toList do
    IO.println s!"{m}\t{" ".intercalate (s.toList.map toString)}"
