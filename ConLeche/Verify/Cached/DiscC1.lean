module

import ConLeche.Cached.CoreC
public import ConLeche.Verify.Cached.GuardsC
public import ConLeche.Verify.Cached.SimCEff
public import ConLeche.Verify.Cached.Grind
import ConLeche.Verify.InstSpine

public section

/-!
# Cached body walks, part 1: list helpers and small twins (task #163)

Per-helper simulation walks: each cached twin
(`ConLeche/Cached/CoreC.lean`) simulates its `Expr` original at the
fueled record on well-scoped inputs, stated as a `Std.WP` triple whose
post names the cached value as the fueled answer (`Runs`) and proved by
`vcgen` and `grind` (`ConLeche/Verify/Cached/Grind.lean`).  The list
loops (`defEqListC_spec`, `iotaCertsFullCAux_spec`) recurse one
`sym … => vcgen … <;> finish` per list arm, the induction hypothesis a
term in `vcgen`'s list.

The module also declares the knot's hypothesis `SSimC` and, after it,
the triple forms of its fields, with the `grind` vocabulary the walks of
this module and `DiscC2.lean` add (the η projections `projsOf`, the
native `Nat` operations' answers, the peel steps' scope).
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

/-- The cached conditional simulation at fuel `f`: every cached entry point simulates the corresponding fueled family on
well-scoped inputs.  Declared here so the per-body walks can
take it as their induction hypothesis; the knot batch proves it at
every fuel. -/
structure SSimC (mode : CheckMode) (eager : Bool) (env : Env) (f : Nat) : Prop where
  whnfCore : ∀ {c : Bool} {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode eager env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode eager env s₀ (RelEC d)
      ((coreKnotI mode eager (mkFEnv env) f).whnfCore c d i)
      ((fueledFns mode eager env).whnfCore c d e)
  whnf : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode eager env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode eager env s₀ (RelEC d)
      ((coreKnotI mode eager (mkFEnv env) f).whnf d i)
      ((fueledFns mode eager env).whnf d e)
  infer : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode eager env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode eager env s₀ (RelEC d)
      ((coreKnotI mode eager (mkFEnv env) f).infer d i)
      ((fueledFns mode eager env).infer d e)
  defeq : ∀ {s₀ : CState} {d : Nat} {i j : Expr} {a b : Expr},
    CSOK mode eager env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode eager env s₀ RelVC
      ((coreKnotI mode eager (mkFEnv env) f).defeq d i j)
      ((fueledFns mode eager env).defeq d a b)
  /-- the eager slot (task #353): the eager tower's comparison, under
  its own memos, simulates the fueled eager slot -/
  defeqE : ∀ {s₀ : CState} {d : Nat} {i j : Expr} {a b : Expr},
    CSOK mode eager env s₀ → RelC i a → RelC j b →
    Expr.WScoped d a → Expr.WScoped d b →
    SimC mode eager env s₀ RelVC
      ((coreKnotI mode eager (mkFEnv env) f).defeqE d i j)
      ((fueledFns mode eager env).defeqE d a b)
  /-- the io slot (task #172 B4): the memoized knot's `inferIO` entry
  simulates the fueled io-slot family -/
  inferIO : ∀ {s₀ : CState} {d : Nat} {i : Expr} {e : Expr},
    CSOK mode eager env s₀ → RelC i e → Expr.WScoped d e →
    SimC mode eager env s₀ (RelEC d)
      ((coreKnotI mode eager (mkFEnv env) f).inferIO d i)
      ((fueledFns mode eager env).inferIO d e)

/-- The base case: fuel `0` throws everywhere. -/
theorem ssimC_zero (env : Env) : SSimC mode eager env 0 := by
  cases eager <;> exact
    { whnfCore := fun _ _ _ => SimC.throw
      whnf := fun _ _ _ => SimC.throw
      infer := fun _ _ _ => SimC.throw
      defeq := fun _ _ _ _ _ => SimC.throw
      defeqE := fun _ _ _ _ _ => SimC.throw
      inferIO := fun _ _ _ => SimC.throw }

/-! ## The knot hypothesis's fields as triples

For `vcgen`'s list (`ih.infer_spec hs`, …).  They stay beside `SSimC`
rather than in `Grind.lean` because they name the cached knot
`coreKnotI`, which `Grind.lean` does not import. -/

section SSimCSpecs

variable {env : Env} {f : Nat}

theorem SSimC.whnfCore_spec (ih : SSimC mode eager env f) {c : Bool} {s₀ : CState} {d : Nat}
    {i : Expr} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode eager (mkFEnv env) f).whnfCore c d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).whnfCore c d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.whnfCore hs rfl hw).triple relEC_inv

theorem SSimC.whnf_spec (ih : SSimC mode eager env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode eager (mkFEnv env) f).whnf d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).whnf d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.whnf hs rfl hw).triple relEC_inv

theorem SSimC.infer_spec (ih : SSimC mode eager env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode eager (mkFEnv env) f).infer d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).infer d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.infer hs rfl hw).triple relEC_inv

theorem SSimC.inferIO_spec (ih : SSimC mode eager env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode eager (mkFEnv env) f).inferIO d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).inferIO d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  (ih.inferIO hs rfl hw).triple relEC_inv

theorem SSimC.defeq_spec (ih : SSimC mode eager env f) {s₀ : CState} {d : Nat} {i j : Expr}
    (hs : CSOK mode eager env s₀) (hwi : Expr.WScoped d i) (hwj : Expr.WScoped d j) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode eager (mkFEnv env) f).defeq d i j
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).defeq d i j) r; ⊤⦄ :=
  (ih.defeq hs rfl rfl hwi hwj).tripleVC

theorem SSimC.defeqE_spec (ih : SSimC mode eager env f) {s₀ : CState} {d : Nat} {i j : Expr}
    (hs : CSOK mode eager env s₀) (hwi : Expr.WScoped d i) (hwj : Expr.WScoped d j) :
    ⦃fun s => s = s₀⦄ (coreKnotI mode eager (mkFEnv env) f).defeqE d i j
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs ((fueledFns mode eager env).defeqE d i j) r; ⊤⦄ :=
  (ih.defeqE hs rfl rfl hwi hwj).tripleVC

end SSimCSpecs

/-- The `.proj T i b` nodes over the indices `l` (a named function, so
that its scope fact has a pattern: a `List.map` pattern loses its
lambda). -/
@[expose] def projsOf (T : Name) (b : Expr) (l : List Nat) : List Expr :=
  l.map fun i => Expr.proj T i b

@[conleche_grind =] theorem projsOf_nil (T : Name) (b : Expr) : projsOf T b [] = [] := rfl

@[conleche_grind =] theorem projsOf_cons (T : Name) (b : Expr) (i : Nat) (l : List Nat) :
    projsOf T b (i :: l) = Expr.proj T i b :: projsOf T b l := rfl

@[conleche_grind =] theorem etaProjs_eq (T : Name) (b : Expr) (n : Nat) :
    etaProjs T b n = projsOf T b (List.range n) := rfl

/-- The projections of a well-scoped term are well scoped. -/
theorem allWS_projsOf {d : Nat} {b : Expr} (T : Name) (l : List Nat) (h : Expr.WScoped d b) :
    AllWS d (projsOf T b l) := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  rw [Expr.WScoped]; exact h
grind_pattern [conleche_grind] allWS_projsOf => Expr.WScoped d b, projsOf T b l

/-- The constructor-shape gate reads the same store on both sides. -/
@[conleche_grind =] theorem etaCtorShapeC_eq (env : Env) (e : Expr) :
    etaCtorShapeC (mkFEnv env) e = etaCtorShape env e :=
  etaCtorShapeC_spec' rfl

/-- A native `Nat` operation's answer is closed. -/
@[conleche_grind .] theorem optWS_natOpResult (d : Nat) (c : Name) (a b : Nat) :
    OptWS d (natOpResult c a b) := by
  cases h : natOpResult c a b with
  | none => trivial
  | some e =>
    rcases natOpResult_shape h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> simp [OptWS, Expr.WScoped]

/-- The domain of a well-scoped instantiated `∀` is well scoped. -/
theorem wscoped_piDom {d : Nat} {dom body : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.forallE dom body).instantiateList acc)) :
    Expr.WScoped d (dom.instantiateList acc) := by
  rw [Expr.instantiateList, Expr.WScoped] at hw
  exact hw.1
grind_pattern [conleche_grind] wscoped_piDom =>
  Expr.WScoped d ((Expr.forallE dom body).instantiateList acc), dom.instantiateList acc

/-- The peel step's scope under a `∀` (`wscoped_peel`'s twin). -/
theorem wscoped_piPeel {d : Nat} {dom body a : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.forallE dom body).instantiateList acc))
    (ha : Expr.WScoped d a) :
    Expr.WScoped d (body.instantiateList (a :: acc)) := by
  rw [Expr.instantiateList, Expr.WScoped] at hw
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1_gen ha 0 hw.2
grind_pattern [conleche_grind] wscoped_piPeel =>
  Expr.WScoped d ((Expr.forallE dom body).instantiateList acc),
  body.instantiateList (a :: acc)

section Walks

variable {env : Env} {f : Nat}

/-- The full-grade argument check simulates its fueled original: the
same argument, so the same tower (task #353). -/
theorem defeqArgC_spec (ih : SSimC mode eager env f) {s₀ : CState} {d : Nat} {a ta ty : Expr}
    (hs : CSOK mode eager env s₀) (hwta : Expr.WScoped d ta) (hwty : Expr.WScoped d ty) :
    ⦃fun s => s = s₀⦄ defeqArgI (coreKnotI mode eager (mkFEnv env) f) d a ta ty
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (defeqArg (fueledFns mode eager env) d a ta ty) v;
        ⊤⦄ := by
  sym only [conleche_grind, defeqArg] =>
    vcgen [defeqArgI, ih.defeq_spec hs, ih.defeqE_spec hs] <;> finish

/-- The pairwise definitional-equality helper simulates its fueled
original on well-scoped lists. -/
theorem defEqListC_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ {args brgs : List Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      AllWS d args → AllWS d brgs →
      ⦃fun s => s = s₀⦄ defEqListI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d args brgs
      ⦃fun v s' => CSOK mode eager env s' ∧
          Runs (defEqList (fueledFns mode eager env) env d args brgs) v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro brgs
    cases brgs with
    | nil =>
      intro _ _ _ _
      sym only [conleche_grind, defEqList.eq_1] =>
        vcgen [defEqListI] <;> finish
    | cons _ _ =>
      intro _ _ _ _
      sym only [conleche_grind, defEqList] =>
        vcgen [defEqListI.eq_def] <;> finish
  | cons a as ihA =>
    intro brgs
    cases brgs with
    | nil =>
      intro _ _ _ _
      sym only [conleche_grind, defEqList] =>
        vcgen [defEqListI.eq_def] <;> finish
    | cons b bs =>
      intro _ _ _ _
      sym only [conleche_grind, defEqList.eq_2] =>
        vcgen [defEqListI, ih.defeq_spec, ihA] <;> finish

/-- The pure certificate loop at a bulk-instantiated telescope, stepped
in the cached loop's shape. -/
theorem iotaCertsFull_instList_cons {m : Type → Type} [Monad m] (r : CoreFns m) (env : Env)
    (d : Nat) (ty : Expr) (acc : List Expr) (a : Expr) (rest : List Expr) :
    iotaCertsFull r env d (ty.instantiateList acc) (a :: rest) =
      match ty, acc with
      | .forallE dom body, acc =>
          r.infer d a >>= fun ta => r.defeq d ta (dom.instantiateList acc) >>= fun c =>
          if c then iotaCertsFull r env d (body.instantiateList (a :: acc)) rest
          else pure false
      | .bvar _, [] => pure false
      | .bvar k, acc@(_ :: _) =>
          iotaCertsFull r env d ((Expr.bvar k).instantiateList acc) (a :: rest)
      | _, _ => pure false := by
  cases ty with
  | forallE dom body =>
    rw [Expr.instantiateList, iotaCertsFull.eq_2]; dsimp only; rw [Expr.instantiateList_cons]
  | bvar k => cases acc with
    | nil => rw [Expr.instantiateList_nil]; rfl
    | cons => rfl
  | _ => rw [Expr.instantiateList]; cases acc <;> rfl

/-- The bulk-accumulating full-grade certificate loop (task #342 L10)
simulates its fueled original. -/
theorem iotaCertsFullCAux_spec (ih : SSimC mode eager env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : List Expr} {s₀ : CState},
      CSOK mode eager env s₀ → Expr.WScoped d (ty.instantiateList acc) → AllWS d args →
      ⦃fun s => s = s₀⦄
        iotaCertsFullIAux (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d ty acc args
      ⦃fun v s' => CSOK mode eager env s' ∧
          Runs (iotaCertsFull (fueledFns mode eager env) env d (ty.instantiateList acc) args) v; ⊤⦄
  | [], _, _, _, _, _, _ => by
    sym only [conleche_grind, iotaCertsFull.eq_1] =>
      vcgen [iotaCertsFullIAux.eq_1] <;> finish
  | _ :: as, _, [], _, hs, _, _ => by
    sym only [conleche_grind, iotaCertsFull_instList_cons] =>
      vcgen [iotaCertsFullIAux.eq_def, instListM_spec hs, ih.infer_spec, ih.defeq_spec,
        iotaCertsFullCAux_spec ih (args := as)] <;> finish
  | a :: as, _, _ :: _, _, hs, _, _ => by
    sym only [conleche_grind, iotaCertsFull_instList_cons, Expr.instantiateList_nil] =>
      vcgen [iotaCertsFullIAux.eq_def, instListM_spec hs, ih.infer_spec, ih.defeq_spec,
        iotaCertsFullCAux_spec ih (args := as),
        iotaCertsFullCAux_spec ih (args := a :: as) (acc := [])] <;> finish
termination_by args _ acc => (args.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- `iotaCertsFullI` simulates its fueled original. -/
theorem iotaCertsFullC_spec (ih : SSimC mode eager env f) {d : Nat} {args : List Expr} {ty : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d ty) (hargs : AllWS d args) :
    ⦃fun s => s = s₀⦄ iotaCertsFullI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d ty args
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (iotaCertsFull (fueledFns mode eager env) env d ty args) v; ⊤⦄ := by
  sym only [conleche_grind, Expr.instantiateList_nil] =>
    vcgen [iotaCertsFullI, iotaCertsFullCAux_spec ih] <;> finish

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- `ensureSortI` simulates its fueled original. -/
theorem ensureSortC_spec (ih : SSimC mode eager env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ ensureSortI (coreKnotI mode eager (mkFEnv env) f) d i
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (ensureSort (fueledFns mode eager env) env d i) v;
        ⊤⦄ := by
  sym only [conleche_grind, ensureSort] =>
    vcgen [ensureSortI, ih.whnf_spec] <;> finish

/-- The cached twin computes the spec's `litToCtorIfNat`. -/
theorem litToCtorIfNatC_spec {s₀ : CState} (hs : CSOK mode eager env s₀) (i : Expr) :
    ⦃fun s => s = s₀⦄ litToCtorIfNatI (mkFEnv env) i
    ⦃fun r s' => CSOK mode eager env s' ∧ r = litToCtorIfNat env i; ⊤⦄ := by
  sym only [conleche_grind, litToCtorIfNat, natLitStoredF_eq] =>
    vcgen [litToCtorIfNatI] <;> finish

/-- The cached twin computes the spec's pure `unfoldDefinition`. -/
theorem unfoldDefinitionC_spec {s₀ : CState} (hs : CSOK mode eager env s₀) (i : Expr) :
    ⦃fun s => s = s₀⦄ unfoldDefinitionI (mkFEnv env) i
    ⦃fun o s' => CSOK mode eager env s' ∧ o = unfoldDefinition env i; ⊤⦄ := by
  sym only [conleche_grind, unfoldDefinition, constValAt?] =>
    vcgen [unfoldDefinitionI, mkAppNM, constValAtM_spec hs] <;> finish

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-- `litMajorToCtorI` simulates its fueled original. -/
theorem litMajorToCtorC_spec (ih : SSimC mode eager env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ litMajorToCtorI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs (litMajorToCtor (fueledFns mode eager env) env d i)
        r ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, litMajorToCtor, strLitStoredF_eq, strLitToConstructor_WScoped,
      litToCtorIfNat_WScoped] =>
    vcgen [litMajorToCtorI, litToCtorIfNatC_spec hs, ih.whnf_spec] <;> finish

/-- `projLitToCtorI` simulates its fueled original. -/
theorem projLitToCtorC_spec (ih : SSimC mode eager env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ projLitToCtorI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun r s' => CSOK mode eager env s' ∧ Runs (projLitToCtor (fueledFns mode eager env) env d i) r
        ∧
      Expr.WScoped d r; ⊤⦄ := by
  sym only [conleche_grind, projLitToCtor, strLitStoredF_eq, strLitToConstructor_WScoped] =>
    vcgen [projLitToCtorI, ih.whnf_spec] <;> finish

/-- `defeqSpineI` simulates its fueled original. -/
theorem defeqSpineC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqSpineI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (defeqSpine (fueledFns mode eager env) env d a b) v;
        ⊤⦄ := by
  sym only [conleche_grind, defeqSpine] =>
    vcgen [defeqSpineI, isEquivListLM_spec hs, defEqListC_spec ih] <;> finish

end Walks3

section Walks4

variable {env : Env} {f : Nat}

/-- `reduceNat`'s dispatch in the cached twin's nested shape, one
constructor per level (the definition's overlapping wildcard gives a
conditional equation whose premise `grind` cannot discharge from the
nested arms' hypotheses). -/
theorem reduceNat_nested {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (d : Nat) (e : Expr) :
    reduceNat r env d e =
      match e with
      | .app f₁ b =>
        match f₁ with
        | .const c us =>
          match us with
          | [] => reduceNat r env d (.app (.const c []) b)
          | _ :: _ => pure none
        | .app f₂ a =>
          match f₂ with
          | .const c us =>
            match us with
            | [] => reduceNat r env d (.app (.app (.const c []) a) b)
            | _ :: _ => pure none
          | _ => pure none
        | _ => pure none
      | _ => pure none := by
  cases e with
  | app f₁ b =>
    cases f₁ with
    | const c us => cases us <;> rfl
    | app f₂ a => cases f₂ with
      | const c us => cases us <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

/-- `reduceNatI` simulates its fueled original. -/
theorem reduceNatC_spec (ih : SSimC mode eager env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ reduceNatI (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun o s' => CSOK mode eager env s' ∧ Runs (reduceNat (fueledFns mode eager env) env d i) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, reduceNat_nested, reduceNat.eq_1, reduceNat.eq_2,
      natLitStoredF_eq, rawNatLitC?_spec] =>
    vcgen [reduceNatI, maxNatSizeM, ih.whnf_spec] <;> finish

end Walks4

end ConLeche.Cached
