import Setlec.Cached.ExprC
import Setlec.Kernel.ArenaWF
import Setlec.Verify.IExpr

/-!
# The cached-representation seam floor (task #163)

The erasure `eraseC : ExprC → Expr`, the field invariant `WFc`, and
the facts that replace the arena's `EStore.WF` + `denote_inj` for the
cached checker variant (see DESIGN.md, "Task #163 CACHED-LIVE P1"):

* `WFc e := ofExpr (eraseC e) = e` — every field of every node equals
  the smart constructor's recurrence on the erased term;
* `eraseC` is **injective on `WFc`** (`eraseC_inj`): the fields are
  functions of the structure, so a well-formed `ExprC` is uniquely
  determined by its erasure — `denote_inj` without a table;
* field exactness: on `WFc` nodes the `O(1)` readers `bvarB`/`fvarB`/
  `hasLP`/`hash` read exactly the spec functions `Expr.bvarBound`/
  `Expr.fvarRange`/`Expr.hasLevelParam`/`hashSpec` of the erasure, so
  every cutoff the cached operations take is the cutoff the spec takes;
* equality: `beqSpec` (the hash-checking descent) decides equality of
  the *equality normal form* `zeroC` exactly (`beqSpec_iff_zeroC`),
  whence soundness on all terms, the `EquivBEq`/`LawfulHashable`
  instances the `Std.HashMap` lemmas need, and completeness on the
  invariant (`beq_iff`);
* `toExpr_eq`: the memoized readback *is* the erasure — proved, so
  `toExpr` is not a trust point.

Everything here consumes only the *pure* definitions (`ofExpr` =
`ofExprSpec`, `beq` = `beqSpec`); the two `unsafe` accelerations in
`Setlec/Cached/ExprC.lean` are named trust points the proofs never
touch.
-/

namespace Setlec.Cached

open Setlec

namespace ExprC

/-! ## The erasure and the field invariant

The erasure `eraseC`, the invariant `WFc`, `eraseC_ofExpr`,
`eraseC_inj` and the smart-constructor closure moved INTO the
implementation (`Setlec/Cached/ExprC.lean`, task #171) under the
self-contained-verification exception: the direct-parse frontend
carries `WFc` in its table types (the `WFStore` pattern), so the
invariant must be visible implementation-side.  Same namespace —
every downstream reference is unchanged. -/

/-! ### Inversion: a well-formed node has well-formed children and
recurrence fields

Each inversion re-reads `WFc`'s equation at one constructor: the left
side is the smart constructor on converted children, so constructor
injectivity pins the children converted (their own `WFc`) and every
field to its recurrence. -/

theorem WFc.fvar_inv {idx : Nat} {n : Name} {ty : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.fvar idx n ty h bb fb lp)) :
    WFc ty ∧ ExprC.fvar idx n ty h bb fb lp = mkFVar idx n ty := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.fvar idx n ty h bb fb lp) = .fvar idx n (eraseC ty)
      from rfl] at this
  rw [show ofExpr (.fvar idx n (eraseC ty)) =
      mkFVar idx n (ofExpr (eraseC ty)) from rfl] at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.fvar _ _ t _ _ _ _ => t | _ => ty) this
    simpa [mkFVar] using this
  refine ⟨hty, ?_⟩
  rw [← this, hty]

theorem WFc.app_inv {f a : ExprC} {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.app f a h bb fb lp)) :
    WFc f ∧ WFc a ∧ ExprC.app f a h bb fb lp = mkApp f a := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.app f a h bb fb lp) = .app (eraseC f) (eraseC a)
      from rfl] at this
  rw [show ofExpr (.app (eraseC f) (eraseC a)) =
      mkApp (ofExpr (eraseC f)) (ofExpr (eraseC a)) from rfl] at this
  have hf : WFc f := by
    show ofExpr (eraseC f) = f
    have := congrArg (fun e => match e with
      | ExprC.app g _ _ _ _ _ => g | _ => f) this
    simpa [mkApp] using this
  have ha : WFc a := by
    show ofExpr (eraseC a) = a
    have := congrArg (fun e => match e with
      | ExprC.app _ b _ _ _ _ => b | _ => a) this
    simpa [mkApp] using this
  refine ⟨hf, ha, ?_⟩
  rw [← this, hf, ha]

theorem WFc.lam_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.lam n ty b m h bb fb lp)) :
    WFc ty ∧ WFc b ∧ ExprC.lam n ty b m h bb fb lp = mkLam n ty b m := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.lam n ty b m h bb fb lp) =
      .lam n (eraseC ty) (eraseC b) m from rfl] at this
  rw [show ofExpr (.lam n (eraseC ty) (eraseC b) m) =
      mkLam n (ofExpr (eraseC ty)) (ofExpr (eraseC b)) m from rfl] at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.lam _ t _ _ _ _ _ _ => t | _ => ty) this
    simpa [mkLam] using this
  have hb : WFc b := by
    show ofExpr (eraseC b) = b
    have := congrArg (fun e => match e with
      | ExprC.lam _ _ bd _ _ _ _ _ => bd | _ => b) this
    simpa [mkLam] using this
  refine ⟨hty, hb, ?_⟩
  rw [← this, hty, hb]

theorem WFc.forallE_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.forallE n ty b m h bb fb lp)) :
    WFc ty ∧ WFc b ∧
      ExprC.forallE n ty b m h bb fb lp = mkForallE n ty b m := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.forallE n ty b m h bb fb lp) =
      .forallE n (eraseC ty) (eraseC b) m from rfl] at this
  rw [show ofExpr (.forallE n (eraseC ty) (eraseC b) m) =
      mkForallE n (ofExpr (eraseC ty)) (ofExpr (eraseC b)) m from rfl]
    at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.forallE _ t _ _ _ _ _ _ => t | _ => ty) this
    simpa [mkForallE] using this
  have hb : WFc b := by
    show ofExpr (eraseC b) = b
    have := congrArg (fun e => match e with
      | ExprC.forallE _ _ bd _ _ _ _ _ => bd | _ => b) this
    simpa [mkForallE] using this
  refine ⟨hty, hb, ?_⟩
  rw [← this, hty, hb]

theorem WFc.letE_inv {n : Name} {ty v b : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.letE n ty v b h bb fb lp)) :
    WFc ty ∧ WFc v ∧ WFc b ∧
      ExprC.letE n ty v b h bb fb lp = mkLetE n ty v b := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.letE n ty v b h bb fb lp) =
      .letE n (eraseC ty) (eraseC v) (eraseC b) from rfl] at this
  rw [show ofExpr (.letE n (eraseC ty) (eraseC v) (eraseC b)) =
      mkLetE n (ofExpr (eraseC ty)) (ofExpr (eraseC v))
        (ofExpr (eraseC b)) from rfl] at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.letE _ t _ _ _ _ _ _ => t | _ => ty) this
    simpa [mkLetE] using this
  have hv : WFc v := by
    show ofExpr (eraseC v) = v
    have := congrArg (fun e => match e with
      | ExprC.letE _ _ vv _ _ _ _ _ => vv | _ => v) this
    simpa [mkLetE] using this
  have hb : WFc b := by
    show ofExpr (eraseC b) = b
    have := congrArg (fun e => match e with
      | ExprC.letE _ _ _ bd _ _ _ _ => bd | _ => b) this
    simpa [mkLetE] using this
  refine ⟨hty, hv, hb, ?_⟩
  rw [← this, hty, hv, hb]

theorem WFc.proj_inv {s : Name} {i : Nat} {e : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.proj s i e h bb fb lp)) :
    WFc e ∧ ExprC.proj s i e h bb fb lp = mkProj s i e := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.proj s i e h bb fb lp) = .proj s i (eraseC e)
      from rfl] at this
  rw [show ofExpr (.proj s i (eraseC e)) =
      mkProj s i (ofExpr (eraseC e)) from rfl] at this
  have he : WFc e := by
    show ofExpr (eraseC e) = e
    have := congrArg (fun x => match x with
      | ExprC.proj _ _ sub _ _ _ _ => sub | _ => e) this
    simpa [mkProj] using this
  refine ⟨he, ?_⟩
  rw [← this, he]

/-! ## Field exactness (the reader form)

On `WFc` nodes the `O(1)` readers are exactly the spec functions of
the erasure — the same exactness the arena's `TWF.bvarBoundD_exact2` /
`fvarRangeD_exact2` / `ehasParamD_exact2` provide for the parallel
arrays, so the cutoff-consequence lemmas transpose verbatim. -/

/-- `bvarB` reads `Expr.bvarBound` of the erasure. -/
theorem bvarB_exact : ∀ {e : ExprC}, WFc e →
    e.bvarB = (eraseC e).bvarBound := by
  intro e
  induction e with
  | bvar i h bb fb lp =>
    intro hw
    have : mkBVar i = ExprC.bvar i h bb fb lp := hw
    rw [← this]
    rfl
  | fvar idx n ty h bb fb lp iht =>
    intro hw
    obtain ⟨-, heq⟩ := hw.fvar_inv
    rw [heq]
    rfl
  | sort u h bb fb lp =>
    intro hw
    have : mkSort u = ExprC.sort u h bb fb lp := hw
    rw [← this]
    rfl
  | const n us h bb fb lp =>
    intro hw
    have : mkConst n us = ExprC.const n us h bb fb lp := hw
    rw [← this]
    rfl
  | app f a h bb fb lp ihf iha =>
    intro hw
    obtain ⟨hf, ha, heq⟩ := hw.app_inv
    rw [heq]
    show max f.bvarB a.bvarB = _
    rw [ihf hf, iha ha]
    rfl
  | lam n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.lam_inv
    rw [heq]
    show max ty.bvarB (b.bvarB - 1) = _
    rw [iht hty, ihb hb]
    rfl
  | forallE n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.forallE_inv
    rw [heq]
    show max ty.bvarB (b.bvarB - 1) = _
    rw [iht hty, ihb hb]
    rfl
  | letE n ty v b h bb fb lp iht ihv ihb =>
    intro hw
    obtain ⟨hty, hv, hb, heq⟩ := hw.letE_inv
    rw [heq]
    show max (max ty.bvarB v.bvarB) (b.bvarB - 1) = _
    rw [iht hty, ihv hv, ihb hb]
    rfl
  | lit l h bb fb lp =>
    intro hw
    have : mkLit l = ExprC.lit l h bb fb lp := hw
    rw [← this]
    rfl
  | proj s i e h bb fb lp ihe =>
    intro hw
    obtain ⟨he, heq⟩ := hw.proj_inv
    rw [heq]
    show e.bvarB = _
    rw [ihe he]
    rfl

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded` of the erasure (the transposition of
`TWF.bvarBoundD_le2`). -/
theorem bvarB_le {e : ExprC} {d : Nat} (hw : WFc e) (hle : e.bvarB ≤ d) :
    (eraseC e).looseBVarsBounded d = true :=
  EStore.looseBVarsBounded_iff.mpr (bvarB_exact hw ▸ hle)

/-- `fvarB` reads `Expr.fvarRange` of the erasure. -/
theorem fvarB_exact : ∀ {e : ExprC}, WFc e →
    e.fvarB = (eraseC e).fvarRange := by
  intro e
  induction e with
  | bvar i h bb fb lp =>
    intro hw
    have : mkBVar i = ExprC.bvar i h bb fb lp := hw
    rw [← this]
    rfl
  | fvar idx n ty h bb fb lp iht =>
    intro hw
    obtain ⟨-, heq⟩ := hw.fvar_inv
    rw [heq]
    rfl
  | sort u h bb fb lp =>
    intro hw
    have : mkSort u = ExprC.sort u h bb fb lp := hw
    rw [← this]
    rfl
  | const n us h bb fb lp =>
    intro hw
    have : mkConst n us = ExprC.const n us h bb fb lp := hw
    rw [← this]
    rfl
  | app f a h bb fb lp ihf iha =>
    intro hw
    obtain ⟨hf, ha, heq⟩ := hw.app_inv
    rw [heq]
    show max f.fvarB a.fvarB = _
    rw [ihf hf, iha ha]
    rfl
  | lam n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.lam_inv
    rw [heq]
    show max ty.fvarB b.fvarB = _
    rw [iht hty, ihb hb]
    rfl
  | forallE n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.forallE_inv
    rw [heq]
    show max ty.fvarB b.fvarB = _
    rw [iht hty, ihb hb]
    rfl
  | letE n ty v b h bb fb lp iht ihv ihb =>
    intro hw
    obtain ⟨hty, hv, hb, heq⟩ := hw.letE_inv
    rw [heq]
    show max (max ty.fvarB v.fvarB) b.fvarB = _
    rw [iht hty, ihv hv, ihb hb]
    rfl
  | lit l h bb fb lp =>
    intro hw
    have : mkLit l = ExprC.lit l h bb fb lp := hw
    rw [← this]
    rfl
  | proj s i e h bb fb lp ihe =>
    intro hw
    obtain ⟨he, heq⟩ := hw.proj_inv
    rw [heq]
    show e.fvarB = _
    rw [ihe he]
    rfl

/-- Cutoff consequence: a range at or below the base certifies
`Expr.fvarsBelow` of the erasure — the predicate the abstraction
traversals consume (`abstractRange_eq_self`); the transposition of
`TWF.fvarRangeD_le`. -/
theorem fvarB_le {e : ExprC} {d : Nat} (hw : WFc e) (hle : e.fvarB ≤ d) :
    (eraseC e).fvarsBelow d :=
  EStore.fvarsBelow_iff.mpr (fvarB_exact hw ▸ hle)

/-! ### Has-level-param -/

/-- The clone's level walk is the kernel's `Level.hasParam`. -/
theorem levelHasParam_eq : ∀ u : Level, levelHasParam u = u.hasParam := by
  intro u
  induction u <;> simp_all [levelHasParam, Level.hasParam]

/-- …and its list fold is `List.any`. -/
theorem levelsHaveParam_eq : ∀ us : List Level,
    levelsHaveParam us = us.any Level.hasParam := by
  intro us
  induction us with
  | nil => rfl
  | cons u us ih => simp [levelsHaveParam, List.any_cons, levelHasParam_eq, ih]

/-- `hasLP` reads `Expr.hasLevelParam` of the erasure. -/
theorem hasLP_exact : ∀ {e : ExprC}, WFc e →
    e.hasLP = (eraseC e).hasLevelParam := by
  intro e
  induction e with
  | bvar i h bb fb lp =>
    intro hw
    have : mkBVar i = ExprC.bvar i h bb fb lp := hw
    rw [← this]
    rfl
  | fvar idx n ty h bb fb lp iht =>
    intro hw
    obtain ⟨hty, heq⟩ := hw.fvar_inv
    rw [heq]
    show ty.hasLP = _
    rw [iht hty]
    rfl
  | sort u h bb fb lp =>
    intro hw
    have : mkSort u = ExprC.sort u h bb fb lp := hw
    rw [← this]
    show levelHasParam u = _
    rw [levelHasParam_eq]
    rfl
  | const n us h bb fb lp =>
    intro hw
    have : mkConst n us = ExprC.const n us h bb fb lp := hw
    rw [← this]
    show levelsHaveParam us = _
    rw [levelsHaveParam_eq]
    rfl
  | app f a h bb fb lp ihf iha =>
    intro hw
    obtain ⟨hf, ha, heq⟩ := hw.app_inv
    rw [heq]
    show (f.hasLP || a.hasLP) = _
    rw [ihf hf, iha ha]
    rfl
  | lam n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.lam_inv
    rw [heq]
    show (ty.hasLP || b.hasLP || m.pw.hasParams) = _
    rw [iht hty, ihb hb]
    rfl
  | forallE n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.forallE_inv
    rw [heq]
    show (ty.hasLP || b.hasLP || m.pw.hasParams) = _
    rw [iht hty, ihb hb]
    rfl
  | letE n ty v b h bb fb lp iht ihv ihb =>
    intro hw
    obtain ⟨hty, hv, hb, heq⟩ := hw.letE_inv
    rw [heq]
    show (ty.hasLP || v.hasLP || b.hasLP) = _
    rw [iht hty, ihv hv, ihb hb]
    rfl
  | lit l h bb fb lp =>
    intro hw
    have : mkLit l = ExprC.lit l h bb fb lp := hw
    rw [← this]
    rfl
  | proj s i e h bb fb lp ihe =>
    intro hw
    obtain ⟨he, heq⟩ := hw.proj_inv
    rw [heq]
    show e.hasLP = _
    rw [ihe he]
    rfl

/-- Invisibility consequence: level instantiation is the identity on a
well-formed node whose cached flag is off (the `O(1)` shortcut every
`instLevelParams` traversal takes). -/
theorem hasLP_false {e : ExprC} {ks : List Name} {us : List Level}
    (hw : WFc e) (h : e.hasLP = false) :
    (eraseC e).instantiateLevelParams ks us = eraseC e :=
  Expr.instantiateLevelParams_eq_self (by rw [← hasLP_exact hw, h])

/-! ## Hash exactness

The cached hash is a function of the erasure: `hashSpec` is the
smart constructors' recurrence read on `Expr`.  (It is *not*
`Setlec.Expr.hashB`, the arena's budgeted hash — the clone's hash is
unbudgeted on the expression structure and budgeted only inside
levels, `levelHash = Level.hashB 4`.) -/

/-- The `Expr`-side hash specification: the smart constructors'
recurrences, node for node. -/
def hashSpec : Expr → UInt64
  | .bvar i => mixHash 3 (Hashable.hash i)
  | .fvar idx n ty =>
    mixHash 5 (mixHash (Hashable.hash idx)
      (mixHash (Hashable.hash n) (hashSpec ty)))
  | .sort u => mixHash 7 (levelHash u)
  | .const n us => mixHash 11 (mixHash (Hashable.hash n) (levelsHash us))
  | .app f a => mixHash 17 (mixHash (hashSpec f) (hashSpec a))
  | .lam n ty b m =>
    mixHash 19 (mixHash (Hashable.hash n)
      (mixHash (hashSpec ty) (mixHash (hashSpec b) (Hashable.hash m))))
  | .forallE n ty b m =>
    mixHash 23 (mixHash (Hashable.hash n)
      (mixHash (hashSpec ty) (mixHash (hashSpec b) (Hashable.hash m))))
  | .letE n ty v b =>
    mixHash 29 (mixHash (Hashable.hash n)
      (mixHash (hashSpec ty) (mixHash (hashSpec v) (hashSpec b))))
  | .lit l => mixHash 31 (Hashable.hash l)
  | .proj s i e =>
    mixHash 37 (mixHash (Hashable.hash s)
      (mixHash (Hashable.hash i) (hashSpec e)))

/-- The cached hash reads `hashSpec` of the erasure — the fact behind
both `LawfulHashable ExprC` and the completeness leg of `beq_iff`
(equal erasures on `WFc` force equal hash fields, node by node). -/
theorem hash_exact : ∀ {e : ExprC}, WFc e → e.hash = hashSpec (eraseC e) := by
  intro e
  induction e with
  | bvar i h bb fb lp =>
    intro hw
    have : mkBVar i = ExprC.bvar i h bb fb lp := hw
    rw [← this]
    rfl
  | fvar idx n ty h bb fb lp iht =>
    intro hw
    obtain ⟨hty, heq⟩ := hw.fvar_inv
    rw [heq]
    show mixHash 5 (mixHash (Hashable.hash idx)
      (mixHash (Hashable.hash n) ty.hash)) = _
    rw [iht hty]
    rfl
  | sort u h bb fb lp =>
    intro hw
    have : mkSort u = ExprC.sort u h bb fb lp := hw
    rw [← this]
    rfl
  | const n us h bb fb lp =>
    intro hw
    have : mkConst n us = ExprC.const n us h bb fb lp := hw
    rw [← this]
    rfl
  | app f a h bb fb lp ihf iha =>
    intro hw
    obtain ⟨hf, ha, heq⟩ := hw.app_inv
    rw [heq]
    show mixHash 17 (mixHash f.hash a.hash) = _
    rw [ihf hf, iha ha]
    rfl
  | lam n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.lam_inv
    rw [heq]
    show mixHash 19 (mixHash (Hashable.hash n)
      (mixHash ty.hash (mixHash b.hash (Hashable.hash m)))) = _
    rw [iht hty, ihb hb]
    rfl
  | forallE n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.forallE_inv
    rw [heq]
    show mixHash 23 (mixHash (Hashable.hash n)
      (mixHash ty.hash (mixHash b.hash (Hashable.hash m)))) = _
    rw [iht hty, ihb hb]
    rfl
  | letE n ty v b h bb fb lp iht ihv ihb =>
    intro hw
    obtain ⟨hty, hv, hb, heq⟩ := hw.letE_inv
    rw [heq]
    show mixHash 29 (mixHash (Hashable.hash n)
      (mixHash ty.hash (mixHash v.hash b.hash))) = _
    rw [iht hty, ihv hv, ihb hb]
    rfl
  | lit l h bb fb lp =>
    intro hw
    have : mkLit l = ExprC.lit l h bb fb lp := hw
    rw [← this]
    rfl
  | proj s i e h bb fb lp ihe =>
    intro hw
    obtain ⟨he, heq⟩ := hw.proj_inv
    rw [heq]
    show mixHash 37 (mixHash (Hashable.hash s)
      (mixHash (Hashable.hash i) e.hash)) = _
    rw [ihe he]
    rfl

/-! ## Equality

`beqSpec` (the pure spec `ExprC.beq` is defined as, and `beqFast` is
`implemented_by`) is the **hash-checking** structural descent: it
compares the cached hash field at every node as well as the payload.
Its exact characterization is therefore equality of the *equality
normal form* `zeroC` — the term with the three non-hash cached fields
collapsed — from which soundness, reflexivity, symmetry, transitivity
and `LawfulHashable` all read off as equational facts. -/

/-- The equality normal form: keep the structure, the payload and the
hash; collapse the three remaining cached fields.  `beqSpec` decides
exactly equality of this form (`beqSpec_iff_zeroC`). -/
def zeroC : ExprC → ExprC
  | .bvar i h .. => .bvar i h 0 0 false
  | .fvar idx n ty h .. => .fvar idx n (zeroC ty) h 0 0 false
  | .sort u h .. => .sort u h 0 0 false
  | .const n us h .. => .const n us h 0 0 false
  | .app f a h .. => .app (zeroC f) (zeroC a) h 0 0 false
  | .lam n ty b m h .. => .lam n (zeroC ty) (zeroC b) m h 0 0 false
  | .forallE n ty b m h .. => .forallE n (zeroC ty) (zeroC b) m h 0 0 false
  | .letE n ty v b h .. => .letE n (zeroC ty) (zeroC v) (zeroC b) h 0 0 false
  | .lit l h .. => .lit l h 0 0 false
  | .proj s i e h .. => .proj s i (zeroC e) h 0 0 false

/-- The normal form keeps the hash field. -/
theorem hash_zeroC (e : ExprC) : (zeroC e).hash = e.hash := by
  cases e <;> rfl

/-- …and the erasure. -/
theorem eraseC_zeroC : ∀ e : ExprC, eraseC (zeroC e) = eraseC e := by
  intro e
  induction e <;> simp_all [zeroC, eraseC]

/-- **The equality spec, characterized**: the hash-checking descent
succeeds exactly on terms with the same normal form.  (Note this is
*not* "equal erasures": `beqSpec` also compares every node's hash, and
on non-`WFc` terms two equal erasures may carry different hashes.) -/
theorem beqSpec_iff_zeroC : ∀ a b : ExprC,
    beqSpec a b = true ↔ zeroC a = zeroC b := by
  intro a
  induction a with
  | bvar i h bb fb lp =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash] <;>
      constructor <;> intro hx <;> simp_all
  | fvar idx n ty h bb fb lp iht =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash, iht] <;>
      constructor <;> intro hx <;> simp_all
  | sort u h bb fb lp =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash] <;>
      constructor <;> intro hx <;> simp_all
  | const n us h bb fb lp =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash] <;>
      constructor <;> intro hx <;> simp_all
  | app f a h bb fb lp ihf iha =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash, ihf, iha] <;>
      constructor <;> intro hx <;> simp_all
  | lam n ty bd m h bb fb lp iht ihb =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash, iht, ihb] <;>
      constructor <;> intro hx <;> simp_all
  | forallE n ty bd m h bb fb lp iht ihb =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash, iht, ihb] <;>
      constructor <;> intro hx <;> simp_all
  | letE n ty v bd h bb fb lp iht ihv ihb =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash, iht, ihv, ihb] <;>
      constructor <;> intro hx <;> simp_all
  | lit l h bb fb lp =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash] <;>
      constructor <;> intro hx <;> simp_all
  | proj s i e h bb fb lp ihe =>
    intro b
    cases b <;> simp [beqSpec, zeroC, hash, ihe] <;>
      constructor <;> intro hx <;> simp_all

/-- The `BEq` instance is the spec (`beq` is *defined* as `beqSpec`;
the `implemented_by` acceleration is a trust point the proofs never
see). -/
theorem beq_eq_beqSpec (a b : ExprC) : (a == b) = beqSpec a b := rfl

/-- **Soundness, no invariant needed**: the descent only succeeds on
terms with the same erasure.  This is what makes every memo hit exact
(`toExpr_eq`, and the cached checker's caches downstream). -/
theorem beqSpec_sound {a b : ExprC} (h : beqSpec a b = true) :
    eraseC a = eraseC b := by
  rw [← eraseC_zeroC a, ← eraseC_zeroC b, (beqSpec_iff_zeroC a b).mp h]

/-- …and only on terms with the same hash field (`LawfulHashable`). -/
theorem beqSpec_hash {a b : ExprC} (h : beqSpec a b = true) :
    a.hash = b.hash := by
  rw [← hash_zeroC a, ← hash_zeroC b, (beqSpec_iff_zeroC a b).mp h]

@[simp] theorem beqSpec_refl (a : ExprC) : beqSpec a a = true :=
  (beqSpec_iff_zeroC a a).mpr rfl

theorem beqSpec_symm {a b : ExprC} (h : beqSpec a b = true) :
    beqSpec b a = true :=
  (beqSpec_iff_zeroC b a).mpr ((beqSpec_iff_zeroC a b).mp h).symm

theorem beqSpec_trans {a b c : ExprC} (hab : beqSpec a b = true)
    (hbc : beqSpec b c = true) : beqSpec a c = true :=
  (beqSpec_iff_zeroC a c).mpr
    (((beqSpec_iff_zeroC a b).mp hab).trans ((beqSpec_iff_zeroC b c).mp hbc))

/-- Equality is an equivalence — the `Std.HashMap` lemmas' first
premise (an instance, so every memo-preservation proof gets it for
free). -/
instance : EquivBEq ExprC where
  symm h := beqSpec_symm h
  trans hab hbc := beqSpec_trans hab hbc
  rfl := beqSpec_refl _

/-- The `O(1)` `Hashable` instance (the cached field) is lawful for it
— the `Std.HashMap` lemmas' second premise. -/
instance : LawfulHashable ExprC where
  hash_eq _ _ h := beqSpec_hash h

/-- **Completeness on the invariant**: on `WFc` terms the decided
equality is exactly equality of the erasures (`←` by `eraseC_inj`: the
fields, hash included, are functions of the structure, so equal
erasures leave nothing for the hash test to reject). -/
theorem beq_iff {a b : ExprC} (ha : WFc a) (hb : WFc b) :
    (a == b) = true ↔ eraseC a = eraseC b := by
  rw [beq_eq_beqSpec]
  refine ⟨beqSpec_sound, fun h => ?_⟩
  rw [eraseC_inj ha hb h]
  exact beqSpec_refl b

/-! ## The readback is the erasure

`toExprGo` is memoized on `ExprC` keys, so it is *not* a trust point:
the memo invariant "every value the map yields is the erasure of the
key it was looked up at" survives insertion because a hit's key is
`beq`-equal to the query and `beq`-equal terms have equal erasures
(`beqSpec_sound`) — no `WFc` anywhere. -/

/-- The `toExpr` memo invariant. -/
def MemoErase (memo : Std.HashMap ExprC Expr) : Prop :=
  ∀ (k : ExprC) (v : Expr), memo[k]? = some v → v = eraseC k

theorem MemoErase.empty : MemoErase {} := by
  intro k v h
  simp at h

theorem MemoErase.insert {memo : Std.HashMap ExprC Expr} (hm : MemoErase memo)
    (e : ExprC) : MemoErase (memo.insert e (eraseC e)) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    exact beqSpec_sound hbeq
  · exact hm k v hk

/-- The memoized readback returns the erasure and preserves the memo
invariant. -/
theorem toExprGo_spec : ∀ (e : ExprC) {memo : Std.HashMap ExprC Expr},
    MemoErase memo →
    (toExprGo memo e).1 = eraseC e ∧ MemoErase (toExprGo memo e).2 := by
  intro e
  induction e with
  | bvar i hh bb fb lp =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | sort u hh bb fb lp =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | const n us hh bb fb lp =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | lit l hh bb fb lp =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · exact ⟨rfl, hm.insert _⟩
  | fvar idx n ty hh bb fb lp iht =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      subst h1
      exact ⟨rfl, h2.insert _⟩
  | proj s i sub hh bb fb lp ihe =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := ihe hm
      rcases hp : toExprGo memo sub with ⟨t, mt⟩
      rw [hp] at h1 h2
      simp only [hp]
      subst h1
      exact ⟨rfl, h2.insert _⟩
  | app f a hh bb fb lp ihf iha =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨hf1, hf2⟩ := ihf hm
      rcases hpf : toExprGo memo f with ⟨f', mf⟩
      rw [hpf] at hf1 hf2
      obtain ⟨ha1, ha2⟩ := iha hf2
      rcases hpa : toExprGo mf a with ⟨a', ma⟩
      rw [hpa] at ha1 ha2
      simp only [hpf, hpa]
      subst hf1
      subst ha1
      exact ⟨rfl, ha2.insert _⟩
  | lam n ty bd m hh bb fb lp iht ihb =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      obtain ⟨h3, h4⟩ := ihb h2
      rcases hq : toExprGo mt bd with ⟨b', mb⟩
      rw [hq] at h3 h4
      simp only [hp, hq]
      subst h1
      subst h3
      exact ⟨rfl, h4.insert _⟩
  | forallE n ty bd m hh bb fb lp iht ihb =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      obtain ⟨h3, h4⟩ := ihb h2
      rcases hq : toExprGo mt bd with ⟨b', mb⟩
      rw [hq] at h3 h4
      simp only [hp, hq]
      subst h1
      subst h3
      exact ⟨rfl, h4.insert _⟩
  | letE n ty v bd hh bb fb lp iht ihv ihb =>
    intro memo hm
    rw [toExprGo.eq_def]
    split
    · rename_i x hx
      exact ⟨hm _ _ hx, hm⟩
    · obtain ⟨h1, h2⟩ := iht hm
      rcases hp : toExprGo memo ty with ⟨t, mt⟩
      rw [hp] at h1 h2
      obtain ⟨h3, h4⟩ := ihv h2
      rcases hq : toExprGo mt v with ⟨v', mv⟩
      rw [hq] at h3 h4
      obtain ⟨h5, h6⟩ := ihb h4
      rcases hr : toExprGo mv bd with ⟨b', mb⟩
      rw [hr] at h5 h6
      simp only [hp, hq, hr]
      subst h1
      subst h3
      subst h5
      exact ⟨rfl, h6.insert _⟩

/-- **The readback is the erasure** — proved outright, so `toExpr` is
not a trust point. -/
theorem toExpr_eq (e : ExprC) : ExprC.toExpr e = eraseC e :=
  (toExprGo_spec e MemoErase.empty).1

end ExprC

end Setlec.Cached
