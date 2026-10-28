module

public import ConLeche.Verify.Modular.View

public section

/-!
# The development a modular run checks (task #370)

A modular run ends with the store (`Mod.Store`) and, per module, what it
keeps (`Mod.ModData`).  This file names the development they stand for —
`devOf`, a `ConLeche.Modular.Module` per module: its context is what its
view reads off the store (`ctxOf`), its own environment the context with
its install's constants (`envAt`), every context name read from its home
module, its proofs the run's, its resolution the home's qualified name, and its
interface the presentations of its unit (`ifaceOf`) — and the facts the run establishes (`RunOk`).  `RunOk.localOk`
(`ConLeche/Verify/Modular/Local.lean`) is the theorem that they are the
local checks.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-- The trivial module (beyond the run's modules). -/
@[expose] def emptyModule : ConLeche.Modular.Module :=
  { imports := [], decls := [], context := ⟨[], []⟩, own := ⟨[], []⟩, src := fun _ => 0,
    proofs := fun _ => false, res := fun n => .qual 0 n }

/-- The qualified name module `i` resolves `n` to: through its context
the home's, else its own. -/
@[expose] def resOf (S : Store) (i : Nat) (d : ModData) (n : Name) : ConLeche.Modular.Key :=
  match (S.mb i).pick? n with
  | some (h, j, _) => S.keyAt h j n
  | none =>
    match (envAt d.fe (ctxOf (S.mb i))).find? n with
    | some ci =>
      if d.flags.contains n then .proof n ci.toConstantVal.levelParams ci.toConstantVal.type
      else .qual i n
    | none => .qual i n

/-- The gated read sets of module `h`'s constant `j` the unit check
accepts (`unitOk`): `a` its exported presentation, `g`/`v` its gates,
`t` its exported table. -/
@[expose] def gatedOk (S : Store) (h : Nat) (d : ModData) (j : Nat) (a : ConstantInfo)
    (g v : Array (Nat × UInt8)) (t : Option ProjTable) (x : Nat × ReadSet × ReadSet) : Bool :=
  x.1 == j && lawsOk x.2.1 (lawsOf t (if v.isEmpty then a else asAxiom a)) &&
    readsOk S h d.fe d.unit false g x.2.1 &&
    (v.isEmpty || (lawsOk x.2.2 (lawsOf t a) && readsOk S h d.fe d.unit false (g ++ v) x.2.2))

/-- **The presentations of module `h`'s constant `j`**: at the private
level the installed constant with its reads; at the exported level its
presentation — ungated with the ungated reads, gated with the reads of
its presentation when the value gate is closed (the assumption of its
statement, if it has a value gate) and, with a value gate, when it is
open. -/
@[expose] def presOf (S : Store) (h : Nat) (d : ModData) (j : Nat) : List ConLeche.Modular.Presented :=
  match (S.slot h).prv.priv[j]? with
  | none => []
  | some c =>
    ⟨c, ((S.slot h).prv.tbls[j]?).join, d.reads.all2.d.keys⟩ ::
    match (S.slot h).exp.at1[j]?, (S.slot h).exp.g1[j]?, (S.slot h).exp.v1[j]?,
      (S.slot h).exp.tbls[j]? with
    | some (some a), some g, some v, some t =>
      if g.isEmpty && v.isEmpty then [⟨a, t, d.reads.all1.d.keys⟩]
      else match d.reads.gated.find? (gatedOk S h d j a g v t) with
        | some (_, rt, rf) =>
          ⟨if v.isEmpty then a else asAxiom a, if v.isEmpty then t else none, rt.d.keys⟩ ::
            (if v.isEmpty then [] else [⟨a, t, rf.d.keys⟩])
        | none => []
    | _, _, _, _ => []

/-- **Module `h`'s interface**: the presentations of its constants, by
name. -/
@[expose] def ifaceOf (S : Store) (h : Nat) (d : ModData) (n : Name) : List ConLeche.Modular.Presented :=
  (List.range (S.slot h).prv.priv.size).flatMap fun j =>
    if ((S.slot h).prv.priv[j]?).map (·.name) == some n then presOf S h d j else []

/-- **Module `i` of the run.** -/
@[expose] def moduleOf (S : Store) (i : Nat) (d : ModData) : ConLeche.Modular.Module :=
  { imports := d.imports
    decls := d.ds.toList
    context := ctxOf (S.mb i)
    own := envAt d.fe (ctxOf (S.mb i))
    src := fun n => match (S.mb i).pick? n with
      | some (h, _, _) => h
      | none => 0
    proofs := d.flags.contains
    res := resOf S i d
    iface := ifaceOf S i d }

/-- **The development a run stands for.** -/
@[expose] def devOf (S : Store) (M : Array ModData) (i : Nat) : ConLeche.Modular.Module :=
  if h : i < M.size then moduleOf S i M[i] else emptyModule

/-- **What a modular run establishes**: the store's units are the run's;
every module's levels are over the run's modules; every module's
records were installed at its view, its records checked, its proofs
attested, its unit checked; every module passes its local checks; the
store's list of names with several alternates is complete. -/
structure RunOk (mode : CheckMode) (S : Store) (M : Array ModData) : Prop where
  slots : S.slots.size = M.size
  lvls : ∀ i, i < M.size → (S.lvl i).size = M.size
  below : ∀ i (h : i < M.size), ∀ b ∈ M[i].imports, b < i
  run : ∀ i (h : i < M.size), ∃ n,
    InstallRun mode natOpPinSets M[i].ds.toList (0, S.view i, #[]) (n, M[i].fe, M[i].pend)
  chk : ∀ i (h : i < M.size), ∀ pc ∈ M[i].pend.toList,
    ∃ s, checkPending mode M[i].fe pc {} = .ok ((), s)
  prf : ∀ i (h : i < M.size), ProofsAttested mode M[i].flags.contains M[i].fe M[i].pend
  slot : ∀ i (h : i < M.size), S.slot i = M[i].unit.slot
  priv : ∀ i (h : i < M.size), M[i].unit.slot.prv.priv = M[i].fe.env.consts.reverse.toArray
  unit : ∀ i (h : i < M.size), unitOk S i M[i].fe M[i].flags.contains M[i].unit M[i].reads = true
  locals : ∀ i, i < M.size → localOk S (M.map (·.unit)) i = true
  dups : dupsOk S = true

end ConLeche.Cached.Mod
