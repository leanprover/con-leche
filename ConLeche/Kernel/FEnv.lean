module

public import ConLeche.Kernel.Core
import Std.Data.HashMap.Lemmas

@[expose] public section

/-!
# `FEnv`: the environment with a name index

The spec environment together with a name index whose lookup function
agrees with `Env.find?`, built once per top-level entry call, with the
two literal flags of its lookups (`FEnv.natLit`, `FEnv.strLit`: kept by
every push, so the core reads them in `O(1)`), plus the `Env`-guard
twins that read through it (`natLitSupportedF`, `natOpGuardF`).

**Representation-free.**  Nothing here mentions an expression
representation: `FEnv` indexes `ConstantInfo`s by `Name`, and its flags and
guards ask only about the constants an environment holds.  Both
executable cores read the environment through it, and the F-mirror
agreement (`ConLeche/Verify/EnvBound.lean`) is stated about it.  The
`F` suffix on the guards reads "through the index".
-/

namespace ConLeche
/-! ## The frozen base layer -/

/-- **A frozen lookup layer**: the index of a whole stream, built once
before any record is checked and never written again
(`ConLeche/Cached/StreamIndex.lean`).  An entry `n ↦ (c, ci)` says that
the first constant named `n` in the stream is `ci`, at counter `c`; an
entry `T ↦ (r, t)` says that the first table of `T` is `t`, of record `r`.
A view of the stream below a record reads the entries below that record's
first counter `below` and that record's position `belowRec` only.  The
empty layer answers `none` everywhere (`FBase.find?_empty`). -/
structure FBase where
  idx : Std.HashMap Name (Nat × ConstantInfo) := {}
  tbls : Std.HashMap Name (Nat × ProjTable) := {}
  below : Nat := 0
  belowRec : Nat := 0

/-- The base layer's lookup: a visible entry's constant. -/
def FBase.find? (b : @& FBase) (n : Name) : Option ConstantInfo :=
  match b.idx[n]? with
  | some (c, ci) => if c < b.below then some ci else none
  | none => none

/-- The base layer's table lookup: a visible entry's table. -/
def FBase.findTable? (b : @& FBase) (T : Name) : Option ProjTable :=
  match b.tbls[T]? with
  | some (r, t) => if r < b.belowRec then some t else none
  | none => none

/-- The names a `Nat` literal's expansion needs. -/
def natLitNames : List Name := [natName, natZeroName, natSuccName]

/-- The names a string literal's expansion needs: the `Nat` ones and the string-support ones. -/
def strLitNames : List Name :=
  natLitNames ++ [stringName, stringOfListName, listName, listNilName, listConsName, charName,
    charOfNatName]

/-- **From which counter a view of a frozen layer holds all of `ns`**: one past the largest counter
of their entries, `none` if one has no entry (`FBase.fromLe_litFrom`).  A stream's index computes it
once for each literal flag (`ConLeche.Cached.StreamIndex.freeze`), so a record's view sets its flags
by a comparison. -/
def litFrom (idx : Std.HashMap Name (Nat × ConstantInfo)) : List Name → Option Nat
  | [] => some 0
  | n :: ns =>
    match idx[n]?, litFrom idx ns with
    | some (c, _), some k => some (max (c + 1) k)
    | _, _ => none

/-- Is a counter threshold (`litFrom`) reached at `c`. -/
def fromLe : Option Nat → Nat → Bool
  | some k, c => decide (k ≤ c)
  | none, _ => false

/-- A view holds all of `ns` exactly from `litFrom` on. -/
theorem FBase.fromLe_litFrom (b : FBase) :
    ∀ ns : List Name, fromLe (litFrom b.idx ns) b.below = ns.all (fun n => (b.find? n).isSome)
  | [] => by simp [litFrom, fromLe]
  | n :: ns => by
    have ih := FBase.fromLe_litFrom b ns
    rw [List.all_cons, ← ih]
    have hn : (b.find? n).isSome = (match b.idx[n]? with
        | some (c, _) => decide (c < b.below)
        | none => false) := by
      unfold FBase.find?
      split
      · split <;> simp_all
      · rfl
    rw [hn]
    rcases h1 : b.idx[n]? with _ | ⟨c, ci⟩
    · simp [litFrom, h1, fromLe]
    · rcases h2 : litFrom b.idx ns with _ | k
      · simp [litFrom, h1, h2, fromLe]
      · simp only [litFrom, h1, h2, fromLe]
        by_cases hc : c < b.below <;> simp [hc] <;> omega

/-! ## The indexed environment -/

/-- The index's lookup over its components: the index, then the frozen layer.  A job's own index is
empty until its record pushes, and the lookups are hot, so an empty index is not hashed into. -/
@[inline] def lookupIn (idx : @& Std.HashMap Name ConstantInfo) (base : @& FBase) (n : Name) :
    Option ConstantInfo :=
  if idx.isEmpty then base.find? n
  else
    match idx[n]? with
    | some ci => some ci
    | none => base.find? n

/-- The lookup over an index's components: the overlay first (`FEnv.ovl`), then `lookupIn`.
Inlined into `FEnv.find?`, which is the compiled lookup. -/
@[inline] def findIn (idx : @& Std.HashMap Name ConstantInfo) (base : @& FBase)
    (ovl : @& List ConstantInfo) (n : Name) : Option ConstantInfo :=
  match ovl with
  | [] => lookupIn idx base n
  | ovl@(_ :: _) =>
    match ovl.find? (·.name == n) with
    | some ci => some ci
    | none => lookupIn idx base n

/-- **Are `Nat` literals expandable**, by a lookup: `Nat`, `Nat.zero` and `Nat.succ` are stored
(`natLitStored`, read through `find`). -/
@[inline] def natLitStoredBy (find : Name → Option ConstantInfo) : Bool :=
  (find natName).isSome && (find natZeroName).isSome && (find natSuccName).isSome

/-- **Are string literals expandable**, by a lookup: the `Nat` constants and the string-support
constants are stored (`strLitStored`, read through `find`). -/
@[inline] def strLitStoredBy (find : Name → Option ConstantInfo) : Bool :=
  natLitStoredBy find && (find stringName).isSome && (find stringOfListName).isSome &&
    (find listName).isSome && (find listNilName).isSome &&
    (find listConsName).isSome && (find charName).isSome &&
    (find charOfNatName).isSome

theorem natLitStoredBy_all (f : Name → Option ConstantInfo) :
    natLitStoredBy f = natLitNames.all (fun n => (f n).isSome) := by
  simp [natLitStoredBy, natLitNames, Bool.and_assoc]

theorem strLitStoredBy_all (f : Name → Option ConstantInfo) :
    strLitStoredBy f = strLitNames.all (fun n => (f n).isSome) := by
  simp [strLitStoredBy, natLitStoredBy, strLitNames, natLitNames, Bool.and_assoc]

/-- The ten names the two literal flags read: a push of any other name leaves them as they are. -/
def litName (n : Name) : Bool :=
  n == natName || n == natZeroName || n == natSuccName || n == stringName ||
    n == stringOfListName || n == listName || n == listNilName || n == listConsName ||
    n == charName || n == charOfNatName

/-- The flags read only the ten names. -/
theorem natLitStoredBy_congr {f g : Name → Option ConstantInfo}
    (h : ∀ n, litName n = true → f n = g n) : natLitStoredBy f = natLitStoredBy g := by
  unfold natLitStoredBy
  rw [h natName (by simp [litName]), h natZeroName (by simp [litName]),
    h natSuccName (by simp [litName])]

theorem strLitStoredBy_congr {f g : Name → Option ConstantInfo}
    (h : ∀ n, litName n = true → f n = g n) : strLitStoredBy f = strLitStoredBy g := by
  unfold strLitStoredBy
  rw [natLitStoredBy_congr h, h stringName (by simp [litName]),
    h stringOfListName (by simp [litName]), h listName (by simp [litName]),
    h listNilName (by simp [litName]), h listConsName (by simp [litName]),
    h charName (by simp [litName]), h charOfNatName (by simp [litName])]

/-- The emptiness test changes no answer. -/
theorem lookupIn_eq (idx : Std.HashMap Name ConstantInfo) (base : FBase) (n : Name) :
    lookupIn idx base n = match idx[n]? with
      | some ci => some ci
      | none => base.find? n := by
  unfold lookupIn
  split
  · rename_i h
    rw [Std.HashMap.getElem?_of_isEmpty h]
  · rfl

/-- An insert answers every other name as before. -/
theorem findIn_insert_ne {idx : Std.HashMap Name ConstantInfo} {base : FBase}
    {ovl : List ConstantInfo} {ci : ConstantInfo} {n : Name} (h : ci.name ≠ n) :
    findIn (idx.insert ci.name ci) base ovl n = findIn idx base ovl n := by
  have hi : lookupIn (idx.insert ci.name ci) base n = lookupIn idx base n := by
    rw [lookupIn_eq, lookupIn_eq, Std.HashMap.getElem?_insert, ite_eq_right (by simpa using h)]
  cases ovl <;> simp only [findIn, hi]

/-- With no index and no overlay, the frozen layer answers. -/
theorem findIn_empty (b : FBase) : findIn ∅ b [] = b.find? := by
  funext n
  simp [findIn, lookupIn]

/-- The spec environment together with a name index whose lookup function
agrees with `Env.find?` (built once per top-level entry call), over the
frozen layer of a stream's index (`base`), and the two literal flags of
that lookup (task #579). -/
structure FEnv where
  env : Env
  idx : Std.HashMap Name ConstantInfo
  /-- The frozen lookup layer under the index (`FBase`): consulted on an
  index miss.  Empty everywhere except in a view of a stream's index;
  `mkFEnv` and `push` leave it as it is. -/
  base : FBase
  /-- The **overlay**: constants consed onto `env` WITHOUT
  entering the index, newest first (`overlay`).  Empty on every
  environment a step threads (`mkFEnv`, `push`); non-empty only on
  the inductive block's rule-less-recursor environment, a read-only view
  that shares the constructors' index instead of copying it.  `find?`
  reads it before the index, as if its constants had been pushed
  (`find?_overlay_pushAll`, `ConLeche/Verify/Cached/BlockOverlay.lean`). -/
  ovl : List ConstantInfo
  /-- **The projection tables** (task #362), keyed on the structure's
  name: `env.tables` as a map (the newest table of a name wins, as
  `List.find?` takes the first). -/
  tbls : Std.HashMap Name ProjTable
  /-- **Are `Nat` literals expandable** here: the core reads it at every literal it meets, so it is
  computed where the index is built and kept by every push (task #579). -/
  natLit : Bool
  /-- **Are string literals expandable** here (as `natLit`). -/
  strLit : Bool
  natLit_eq : natLit = natLitStoredBy (findIn idx base ovl)
  strLit_eq : strLit = strLitStoredBy (findIn idx base ovl)

/-- **An index from its components**, its literal flags computed by lookups (`strLitStoredBy`
spelled out, so the `Nat` lookups run once). -/
def FEnv.ofParts (env : Env) (idx : Std.HashMap Name ConstantInfo) (base : FBase)
    (ovl : List ConstantInfo) (tbls : Std.HashMap Name ProjTable) : FEnv :=
  let nat := natLitStoredBy (findIn idx base ovl)
  ⟨env, idx, base, ovl, tbls, nat,
    nat && (findIn idx base ovl stringName).isSome &&
      (findIn idx base ovl stringOfListName).isSome && (findIn idx base ovl listName).isSome &&
      (findIn idx base ovl listNilName).isSome && (findIn idx base ovl listConsName).isSome &&
      (findIn idx base ovl charName).isSome && (findIn idx base ovl charOfNatName).isSome,
    rfl, rfl⟩

theorem FEnv.ofParts_idx (e i b o t) : (FEnv.ofParts e i b o t).idx = i := rfl
theorem FEnv.ofParts_base (e i b o t) : (FEnv.ofParts e i b o t).base = b := rfl
theorem FEnv.ofParts_ovl (e i b o t) : (FEnv.ofParts e i b o t).ovl = o := rfl
theorem FEnv.ofParts_tbls (e i b o t) : (FEnv.ofParts e i b o t).tbls = t := rfl

/-- The index build, from the back: the newest (front) constant is
inserted last and wins, exactly as `List.find?` takes the first match —
so the agreement with `Env.find?` is unconditional (no freshness
assumption). -/
def mkIdxGo : List ConstantInfo → Std.HashMap Name ConstantInfo
  | [] => ∅
  | ci :: cs => (mkIdxGo cs).insert ci.name ci

/-- The table map's build, from the back: the newest (front) table is
inserted last and wins, exactly as `List.find?` takes the first. -/
def mkTblsGo : List ProjTable → Std.HashMap Name ProjTable
  | [] => ∅
  | t :: ts => (mkTblsGo ts).insert t.structName t

/-- Build the index of `env`. -/
def mkFEnv (env : Env) : FEnv :=
  FEnv.ofParts env (mkIdxGo env.consts) {} [] (mkTblsGo env.tables)

namespace FEnv

/-- Two indices with the same components are the same: the flags are their lookups'. -/
theorem ext_parts {fe₁ fe₂ : FEnv} (he : fe₁.env = fe₂.env) (hi : fe₁.idx = fe₂.idx)
    (hb : fe₁.base = fe₂.base) (ho : fe₁.ovl = fe₂.ovl) (ht : fe₁.tbls = fe₂.tbls) :
    fe₁ = fe₂ := by
  obtain ⟨e, i, b, o, t, n, s, hn, hs⟩ := fe₁
  obtain ⟨e', i', b', o', t', n', s', hn', hs'⟩ := fe₂
  cases he; cases hi; cases hb; cases ho; cases ht
  subst hn hs hn' hs'
  rfl

/-- The index, then the frozen layer (`lookupIn`). -/
@[inline] def lookup (fe : @& FEnv) (n : Name) : Option ConstantInfo :=
  lookupIn fe.idx fe.base n

/-- The emptiness test changes no answer. -/
theorem lookup_eq (fe : FEnv) (n : Name) :
    fe.lookup n = match fe.idx[n]? with
      | some ci => some ci
      | none => fe.base.find? n :=
  lookupIn_eq fe.idx fe.base n

/-- Indexed lookup (`= Env.find?` for `mkFEnv`); an index miss falls through to the base layer (empty
but in a view of a stream's index).  With an overlay, the overlay first -- exactly what pushing the
overlay's constants would answer (`findIn`).  `fe` is borrowed: the overlay branch otherwise makes
the compiler take it owned, reference-count traffic on every lookup. -/
def find? (fe : @& FEnv) (n : Name) : Option ConstantInfo :=
  findIn fe.idx fe.base fe.ovl n

/-- The `Nat`-literal flag is a function of the lookups. -/
theorem natLit_congr {fe₁ fe₂ : FEnv} (h : fe₁.find? = fe₂.find?) : fe₁.natLit = fe₂.natLit := by
  rw [fe₁.natLit_eq, fe₂.natLit_eq]
  exact congrArg natLitStoredBy h

/-- The string-literal flag is a function of the lookups. -/
theorem strLit_congr {fe₁ fe₂ : FEnv} (h : fe₁.find? = fe₂.find?) : fe₁.strLit = fe₂.strLit := by
  rw [fe₁.strLit_eq, fe₂.strLit_eq]
  exact congrArg strLitStoredBy h

/-- A push keeps every lookup that answers. -/
theorem findIn_insert_isSome {idx : Std.HashMap Name ConstantInfo} {base : FBase}
    {ovl : List ConstantInfo} {ci : ConstantInfo} {n : Name}
    (h : (findIn idx base ovl n).isSome) : (findIn (idx.insert ci.name ci) base ovl n).isSome := by
  have hl : (lookupIn idx base n).isSome → (lookupIn (idx.insert ci.name ci) base n).isSome := by
    rw [lookupIn_eq, lookupIn_eq, Std.HashMap.getElem?_insert]
    by_cases hk : (ci.name == n) = true
    · simp [hk]
    · rw [ite_eq_right hk]
      exact id
  cases ovl with
  | nil => exact hl h
  | cons c cs =>
    simp only [findIn] at h ⊢
    split
    · simp
    · rename_i hn
      rw [hn] at h
      exact hl h

/-- **Once string literals are expandable, a push changes neither flag**: both are true, and a
push only adds answers. -/
theorem push_flags_of_strLit (fe : FEnv) (ci : ConstantInfo) (h : fe.strLit = true) :
    fe.natLit = natLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) ∧
    fe.strLit = strLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) := by
  have hs := h
  rw [fe.strLit_eq] at hs
  have hs' : strLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) = true := by
    rw [strLitStoredBy_all, List.all_eq_true] at hs ⊢
    exact fun n hn => findIn_insert_isSome (hs n hn)
  have hnat : ∀ f, strLitStoredBy f = true → natLitStoredBy f = true := by
    intro f hf
    unfold strLitStoredBy at hf
    revert hf
    cases natLitStoredBy f <;> simp
  rw [hs', h, fe.natLit_eq, hnat _ (fe.strLit_eq ▸ h), hnat _ hs']
  exact ⟨rfl, rfl⟩

/-- **A push of a name the flags do not read changes neither flag.** -/
theorem push_flags_of_name (fe : FEnv) (ci : ConstantInfo) (h : litName ci.name = false) :
    fe.natLit = natLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) ∧
    fe.strLit = strLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) :=
  ⟨fe.natLit_eq.trans (natLitStoredBy_congr fun _ hn =>
      (findIn_insert_ne fun he => by simp_all).symm),
    fe.strLit_eq.trans (strLitStoredBy_congr fun _ hn =>
      (findIn_insert_ne fun he => by simp_all).symm)⟩

/-- The flags after a push, when they can change: before string literals are expandable, and
only at one of their ten names. -/
theorem push_flags (fe : FEnv) (ci : ConstantInfo) (h : (!fe.strLit && litName ci.name) = false) :
    fe.natLit = natLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) ∧
    fe.strLit = strLitStoredBy (findIn (fe.idx.insert ci.name ci) fe.base fe.ovl) := by
  cases hs : fe.strLit
  · rw [hs] at h
    exact hs ▸ push_flags_of_name fe ci (by simpa using h)
  · exact hs ▸ push_flags_of_strLit fe ci hs

/-- The index of the cons-extended environment (`push_mkFEnv`:
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts, env.tables⟩`).
The literal flags are recomputed only at one of their ten names (`litName`) and only while string
literals are not yet expandable: every other push leaves them as they are (`push_flags`), so once
the string-support constants are in, a push tests one `Bool`. -/
def push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  let idx := fe.idx.insert ci.name ci
  ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, idx, fe.base, fe.ovl, fe.tbls,
    if !fe.strLit && litName ci.name then natLitStoredBy (findIn idx fe.base fe.ovl) else fe.natLit,
    if !fe.strLit && litName ci.name then strLitStoredBy (findIn idx fe.base fe.ovl) else fe.strLit,
    by
      split
      · rfl
      · rename_i hc
        exact (push_flags fe ci (Bool.eq_false_iff.mpr hc)).1,
    by
      split
      · rfl
      · rename_i hc
        exact (push_flags fe ci (Bool.eq_false_iff.mpr hc)).2⟩

/-- **Push a projection table** (task #362): the table component
extended, the constant index untouched (`pushTable_mkFEnv`:
`FEnv.pushTable (mkFEnv env) t = mkFEnv ⟨env.consts, t :: env.tables⟩`,
definitionally). -/
def pushTable (fe : FEnv) (t : ProjTable) : FEnv :=
  ⟨⟨fe.env.consts, t :: fe.env.tables⟩, fe.idx, fe.base, fe.ovl, fe.tbls.insert t.structName t,
    fe.natLit, fe.strLit, fe.natLit_eq, fe.strLit_eq⟩

/-- Install a list of tables, head first (as `FEnv.pushAll` pushes
constants): `(pushTables Q fe).env.tables = Q.reverse ++ fe.env.tables`.
Tail-recursive, so the index is threaded owned. -/
def pushTables : List ProjTable → FEnv → FEnv
  | [], fe => fe
  | t :: Q, fe => pushTables Q (fe.pushTable t)

/-- Push a list of records, head first. -/
def pushAll : List ConstantInfo → FEnv → FEnv
  | [], fe => fe
  | ci :: rest, fe => pushAll rest (fe.push ci)

/-- **What an install step leaves behind**: the constants `L` pushed,
then the tables `Q` installed, each in install order — a constant push
and a table install touch different components, so every interleaving
of the two is this one. -/
def pushDelta (L : List ConstantInfo) (Q : List ProjTable) (fe : FEnv) : FEnv :=
  pushTables Q (pushAll L fe)

/-- **Cons `new` (newest first) as an overlay**: the environment `new` pushed onto `fe` would be
(`find?_overlay`, for an `fe` without an overlay), with the index SHARED, not mutated -- two live
environments, one bucket array.  Read-only: nothing pushes onto it. -/
def overlay (fe : FEnv) (new : List ConstantInfo) : FEnv :=
  ofParts ⟨new ++ fe.env.consts, fe.env.tables⟩ fe.idx fe.base (new ++ fe.ovl) fe.tbls

/-- The table map's lookup, ungated: a miss in the map falls through to
the base layer (empty but in a view of a stream's index). -/
def rawTable? (fe : FEnv) (T : Name) : Option ProjTable :=
  match fe.tbls[T]? with
  | some t => some t
  | none => fe.base.findTable? T

/-- **The table lookup** (task #362): `T`'s table, visible exactly
where the constant `T` is (`= Env.findTable?` for `mkFEnv`,
`mkFEnv_findTable?`). -/
def findTable? (fe : FEnv) (T : Name) : Option ProjTable :=
  if (fe.find? T).isSome then fe.rawTable? T else none

/-- Indexed projection-table lookup (`= Env.findProj?` for `mkFEnv`). -/
def findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry :=
  match fe.findTable? T with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

/-- `andRescueSlots` through the index. -/
def andRescueSlotsF (fe : FEnv) (ctor : Name) (nP : Nat) : Bool :=
  andRescueSlotsOf fe.findProj? ctor nP

end FEnv

/-! ### Indexed guard twins (same result as the `Env` versions) -/

/-- `natLitSupported` through the index. -/
def natLitSupportedF (fe : FEnv) : Bool :=
  natIndOk (fe.find? natName) && natZeroOk (fe.find? natZeroName) &&
    natSuccOk (fe.find? natSuccName)

/-- `natOpGuard` through the index. -/
def natOpGuardF (fe : FEnv) (c : Name) : Bool :=
  natLitSupportedF fe &&
  (natOpDeps c).all (fun n => (fe.find? n).isSome) &&
  (if c = natBeqName || c = natBleName || natDivModNames.contains c then
    (match fe.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .const boolName []
      | none => false) &&
    (match fe.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty &&
          ci.toConstantVal.type == .const boolName []
      | none => false)
   else true)

end ConLeche
