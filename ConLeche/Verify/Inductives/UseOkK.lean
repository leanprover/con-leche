module

public import ConLeche.Verify.Inductives.PosDerivK
public import ConLeche.Verify.Shift
public import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Inductives.PosDerivKInv
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# What a key-named use must satisfy for the model (PRIMREC / NESTKN-M3)

`UseOkK` is the hook the monotonicity proof (`posDK_mono`,
`Model/Inductives/PosMonoK.lean`) needs on every `use` of the key-named
positivity derivation (`PosDKH`), beyond the premises the kernel checks today.
Each clause is marked:

* **(K)** — a check a kernel round must add (cheap; a failure is `.internal`
  or a reject, see DESIGN "PRIMREC / NESTKN-M2");
* **(P)** — a syntactic fact about the kernel's own constructions
  (`nestLayoutK`, `rbK`, `absKeysK`, `matchK`/`bindInnerK`), to be proved
  from their code.

The clauses, at a use of the key `kc` spelled `ps` at the user's layout `L`,
of the node `kn` with layout `lo` and met set `metc`, the match's bindings
`bs` (`θ = thetaK … bs`):

* (U0, P/K) the node's key's container is no member of the block and not
  `Quot` (the use's own container is — `contK`, `synKeysK`; a pending use
  from `metK` is not checked);
* (U1, P/K) the used container takes the spelling's parameter count;
* (U2, P) the node has one type per flexible family;
* (U3) each family type is scoped below its family, bvar-closed, readable
  (`ReadsS`), its leaves the key's (below the members) or earlier families'
  (P); and it is a TYPE: inferred into a sort at its family's depth (K);
* (U4, P) the node's parameters `DsF` are scoped at its base, bvar-closed,
  readable, their leaves the key's or the families';
* (U5, P) the node's family keys are concrete (scoped at the members,
  bvar-closed, readable), their leaves the key's;
* (U6, P) the node's key's leaves are the user's spelling's or the user's
  family keys';
* (U7) every family bound (the kernel's check since K2) to a term scoped at
  the user, bvar-closed, readable, its leaves the user's spelling's, the
  user's `DsF`'s or the user's family keys' (P); the binding HAS its family's
  type at the bindings — both inferred at the user, defeq (K); and a MET
  family's binding is read at the family's index count (`BindArityK`, K);
* (U8, K — PRIMREC / NESTKN-M4) a MET family bound to a key occurrence
  `C' ps'` has `ps' ≠ []` (inside `BindArityK`): the closure witness's
  richness at that family is `LfpClause.injNePt` (PROOFPLAN R4), which needs
  a parameter.  `metK` checks it cheaply (`.internal` on failure).
-/

namespace ConLeche

/-- **Structural readability**: the shape `denoteMeta` reads — no `let`, no
loose bound variable beyond the `k` enclosing binders, constants stored at
their level count, projections the reading supports, literals the
environment supports. -/
@[expose] def Expr.ReadsS (env : Env) : Nat → Expr → Prop
  | k, .bvar i => i < k
  | _, .fvar .. => True
  | _, .sort _ => True
  | _, .const n us => ∃ ci, env.find? n = some ci ∧ us.length = ci.toConstantVal.levelParams.length
  | k, .forallE t b _ => Expr.ReadsS env k t ∧ Expr.ReadsS env (k + 1) b
  | k, .lam t b _ => Expr.ReadsS env k t ∧ Expr.ReadsS env (k + 1) b
  | k, .app f a => Expr.ReadsS env k f ∧ Expr.ReadsS env k a
  | _, .letE .. => False
  | k, .proj sn i e => Expr.ReadsS env k e ∧ (env.findProj? sn i ≠ none ∨ i < 2)
  | _, .lit (.natVal _) => natLitSupported env = true
  | _, .lit (.strVal _) => strLitSupported env = true

/-- Leaf `l` is a leaf of one of `xs`. -/
@[expose] def LeafIn (xs : List Expr) (l : Nat × Expr) : Prop := ∃ x ∈ xs, l ∈ x.fvarLeaves

/-- The leaves of a layout's material: its `DsF` and its families' keys. -/
@[expose] def LayLeaf (L : LayoutK) (l : Nat × Expr) : Prop :=
  LeafIn L.dsF l ∨ ∃ p ∈ L.fams, LeafIn p.1.ds l

/-- **The arity a met family's binding is read at** (`nI`, the family's index
count): a family of the user of that index count; the user's own hole applied
to exactly `DsF`, its remaining arity `nI`; a key whose N2 check at the user
counted `nI` indices — and which has at least one PARAMETER (PRIMREC /
NESTKN-M4, clause U8: accessibility needs the binding's carrier never to hold
`pt`, `LfpClause.injNePt`, which reads a parameter; a key occurrence always has
one, `keyOcc?`, so the check never fires on a valid run). -/
@[expose] def BindArityK (ctx : NestCtx) (L : LayoutK) (b : Expr) (nI : Nat) : Prop :=
  (∀ i ty, b = .fvar i ty → ctx.hiAt 0 ≤ i → i < ctx.hiAt 0 + L.nF →
    ∃ key, L.fams[i - ctx.hiAt 0]? = some (key, nI)) ∧
  (∀ i ty, b.getAppFn = .fvar i ty → ctx.hiAt 0 + L.nF ≤ i → i < L.hi →
    b.getAppArgs = L.dsF ∧ ∃ g, L.grp[i - ctx.hiAt 0 - L.nF]? = some g ∧
      nI + L.dsF.length = nestArity ctx g) ∧
  (∀ n us, b.getAppFn = .const n us → b.getAppArgs ≠ [] ∧
    ∃ cty, nestInstType (m := CheckM) ctx L.hi ⟨n, us, b.getAppArgs⟩ = .ok (nI, cty))

/-- **The use hook the model needs** (see the module docstring). -/
@[expose] def UseOkK (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx) : UseHookK :=
  fun L kc kn ps lo metc bs =>
    -- (U0) the node's key's container
    (ctx.names.contains kn.cname = false ∧ kn.cname ≠ quotName) ∧
    -- (U1) the used container's parameter count
    (∃ Lc, nestContainer ctx kc.cname = some (ps.length, Lc)) ∧
    -- (U2) one type per family
    lo.L.famTys.length = lo.L.nF ∧ lo.L.fams.length = lo.L.nF ∧
    -- (U3) the families' types
    (∀ j (hj : j < lo.L.famTys.length),
      Expr.WScoped (ctx.hiAt 0 + j) lo.L.famTys[j] ∧ lo.L.famTys[j].looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded lo.L.famTys[j] ∧ Expr.ReadsS env 0 lo.L.famTys[j] ∧
      (∀ l ∈ lo.L.famTys[j].fvarLeaves, (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
        ∃ i, ∃ hi : i < j, l = (ctx.hiAt 0 + i, lo.L.famTys[i]'(by omega))) ∧
      ∃ T sv, ops.inferType env (ctx.hiAt 0 + j) lo.L.famTys[j] = .ok T ∧
        ops.ensureSort env (ctx.hiAt 0 + j) T = .ok sv) ∧
    -- (U4) the node's parameters
    (∀ x ∈ lo.L.dsF, Expr.WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ Expr.ReadsS env 0 x ∧
      ∀ l ∈ x.fvarLeaves, (l.1 < ctx.hiAt 0 ∧ LeafIn kn.ds l) ∨
        ∃ i, ∃ hi : i < lo.L.famTys.length, l = (ctx.hiAt 0 + i, lo.L.famTys[i])) ∧
    -- (U5) the node's family keys
    (∀ p ∈ lo.L.fams, ∀ x ∈ p.1.ds, Expr.WScoped (ctx.hiAt 0) x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧ Expr.ReadsS env 0 x ∧
      ∀ l ∈ x.fvarLeaves, LeafIn kn.ds l) ∧
    -- (U6) the node's key at the user
    (∀ l, LeafIn kn.ds l → LeafIn ps l ∨ ∃ p ∈ L.fams, LeafIn p.1.ds l) ∧
    -- (U7) the bindings
    (∀ j (hj : j < lo.L.nF), ∃ b, thetaK ctx lo.L.nF bs (ctx.hiAt 0 + j) = some b ∧
      Expr.WScoped L.hi b ∧ b.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded b ∧
      Expr.ReadsS env 0 b ∧ (∀ l ∈ b.fvarLeaves, LeafIn ps l ∨ LayLeaf L l) ∧
      (∃ T, ops.inferType env L.hi b = .ok T ∧
        (∃ T', ops.inferType env L.hi ((lo.L.famTys.getD j default).replaceFVars
          (thetaK ctx lo.L.nF bs)) = .ok T') ∧
        ops.isDefEq env L.hi T ((lo.L.famTys.getD j default).replaceFVars
          (thetaK ctx lo.L.nF bs)) = .ok true) ∧
      (j ∈ metc → ∀ key nI, lo.L.fams[j]? = some (key, nI) → BindArityK ctx L b nI))

/-! ## The kernel's hook checks (NESTKN-K3) -/

/-- **The met family's arity check** (`bindArityK`) establishes `BindArityK`. -/
theorem bindArityK_ok {ctx : NestCtx} {L : LayoutK} {b : Expr} {nI : Nat}
    (h : bindArityK (m := CheckM) ctx L b nI = .ok ()) : BindArityK ctx L b nI := by
  unfold bindArityK at h
  cases hf : b.getAppFn
  case fvar i ty =>
    rw [hf] at h
    simp only at h
    refine ⟨fun i' ty' hb hlo hhi => ?_, fun i' ty' hf' hlo hhi => ?_,
      fun n us hf' => (by rw [hf] at hf'; cases hf')⟩
    · subst hb
      simp only [Expr.getAppFn, Expr.fvar.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      rw [if_pos (by simp [Expr.getAppArgs, hlo, hhi])] at h
      split at h
      · rename_i key n hfam
        split at h
        · rename_i hn
          exact ⟨key, by rw [hfam, show n = nI by simpa using hn]⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rw [hf] at hf'
      simp only [Expr.fvar.injEq] at hf'
      obtain ⟨rfl, rfl⟩ := hf'
      rw [if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega),
        if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)] at h
      simp only [bind, Except.bind] at h
      split at h
      · rename_i hds
        split at h
        · rename_i g hg
          split at h
          · rename_i har
            exact ⟨by simpa using hds, g, hg, by simpa using har⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
  case const n us =>
    rw [hf] at h
    simp only [bind, Except.bind] at h
    refine ⟨fun i ty hb _ _ => (by subst hb; simp [Expr.getAppFn] at hf),
      fun i ty hf' _ _ => (by rw [hf] at hf'; cases hf'), fun n' us' hf' => ?_⟩
    rw [hf] at hf'
    simp only [Expr.const.injEq] at hf'
    obtain ⟨rfl, rfl⟩ := hf'
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hne
    split at h
    · simp at h
    rename_i r hr
    split at h
    · rename_i hn
      obtain ⟨r1, r2⟩ := r
      simp only [beq_iff_eq] at hn
      subst hn
      exact ⟨by simpa using hne, r2, asInternalK_ok hr⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  all_goals
    refine ⟨fun i ty hb _ _ => (by subst hb; simp [Expr.getAppFn] at hf),
      fun i ty hf' _ _ => (by rw [hf] at hf'; cases hf'),
      fun n us hf' => (by rw [hf] at hf'; cases hf')⟩

/-- **The bindings' check** (`bindsOkK`, U7's kernel part): at every family of `js`, the
binding bound, bvar-closed, of its family's type at the bindings (both inferred at the
user, defeq), and at a MET family read at its index count. -/
theorem bindsOkK_ok {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {L : LayoutK}
    {nd : NodeK} {θ : Nat → Option Expr} : ∀ {js : List Nat},
    bindsOkK (m := CheckM) ops env ctx L nd θ js = .ok () → ∀ j ∈ js, ∃ b,
      θ (ctx.hiAt 0 + j) = some b ∧ b.looseBVarsBounded 0 = true ∧
      (∃ T, ops.inferType env L.hi b = .ok T ∧
        (∃ T', ops.inferType env L.hi ((nd.famTys.getD j default).replaceFVars θ) = .ok T') ∧
        ops.isDefEq env L.hi T ((nd.famTys.getD j default).replaceFVars θ) = .ok true) ∧
      (j ∈ nd.met → BindArityK ctx L b (nd.famNIs.getD j 0))
  | [], _, j, hj => absurd hj (by simp)
  | j₀ :: js, h, j, hj => by
    simp only [bindsOkK, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i b hb
    split at h
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    rename_i hcl
    split at h
    · simp at h
    rename_i u hty
    have hty := asInternalK_ok hty
    try simp only [bind, Except.bind] at hty
    split at hty
    · simp at hty
    rename_i T hT
    split at hty
    · simp at hty
    rename_i T' hT'
    split at hty
    · simp at hty
    rename_i dq hdq
    split at hty
    rotate_left
    · simp [throw, throwThe, MonadExceptOf.throw] at hty
    rename_i hdq'
    have hrest : bindsOkK (m := CheckM) ops env ctx L nd θ js = .ok () ∧
        (j₀ ∈ nd.met → BindArityK ctx L b (nd.famNIs.getD j₀ 0)) := by
      split at h
      · split at h
        · simp at h
        rename_i v hv
        exact ⟨h, fun _ => bindArityK_ok (by simpa using hv)⟩
      · rename_i hm
        exact ⟨h, fun h' => absurd h' (by simpa using hm)⟩
    rcases List.mem_cons.mp hj with rfl | hj
    · refine ⟨b, unwrapOr_ok hb, by simpa using hcl, ⟨T, hT, ⟨T', hT'⟩, ?_⟩,
        hrest.2⟩
      rw [hdq, hdq']
    · exact bindsOkK_ok hrest.1 j hj

/-! ## Structural readability, its laws -/

theorem Expr.ReadsS.mono {env : Env} : ∀ {e : Expr} {k k' : Nat}, k ≤ k' →
    Expr.ReadsS env k e → Expr.ReadsS env k' e
  | .bvar i, k, k', hk, h => by simp only [Expr.ReadsS] at h ⊢; omega
  | .fvar .., _, _, _, h => h
  | .sort _, _, _, _, h => h
  | .const .., _, _, _, h => h
  | .forallE t b _, k, k', hk, h => ⟨ReadsS.mono hk h.1, ReadsS.mono (by omega) h.2⟩
  | .lam t b _, k, k', hk, h => ⟨ReadsS.mono hk h.1, ReadsS.mono (by omega) h.2⟩
  | .app f a, k, k', hk, h => ⟨ReadsS.mono hk h.1, ReadsS.mono hk h.2⟩
  | .letE .., _, _, _, h => h.elim
  | .proj _ _ e, k, k', hk, h => ⟨ReadsS.mono hk h.1, h.2⟩
  | .lit (.natVal _), _, _, _, h => h
  | .lit (.strVal _), _, _, _, h => h

/-- Opening a binder at a free variable keeps readability. -/
theorem Expr.ReadsS.instantiate1_fvar {env : Env} {i : Nat} {ty : Expr} :
    ∀ {e : Expr} {k : Nat}, Expr.ReadsS env (k + 1) e →
      Expr.ReadsS env k (e.instantiate1 (.fvar i ty) k)
  | .bvar j, k, h => by
    simp only [Expr.ReadsS] at h
    simp only [Expr.instantiate1]
    split
    · trivial
    · split
      · simp only [Expr.ReadsS]; omega
      · simp only [Expr.ReadsS]; omega
  | .fvar .., _, h => h
  | .sort _, _, h => h
  | .const .., _, h => h
  | .forallE t b _, k, h => ⟨instantiate1_fvar h.1, instantiate1_fvar (k := k + 1) h.2⟩
  | .lam t b _, k, h => ⟨instantiate1_fvar h.1, instantiate1_fvar (k := k + 1) h.2⟩
  | .app f a, k, h => ⟨instantiate1_fvar h.1, instantiate1_fvar h.2⟩
  | .letE .., _, h => h.elim
  | .proj _ _ e, k, h => ⟨instantiate1_fvar h.1, h.2⟩
  | .lit (.natVal _), _, h => h
  | .lit (.strVal _), _, h => h

/-- Replacing free variables by readable terms keeps readability. -/
theorem Expr.ReadsS.replaceFVars {env : Env} {f : Nat → Option Expr}
    (hf : ∀ i b, f i = some b → Expr.ReadsS env 0 b) :
    ∀ {e : Expr} {k : Nat}, Expr.ReadsS env k e → Expr.ReadsS env k (e.replaceFVars f)
  | .bvar _, _, h => h
  | .fvar i ty, k, _ => by
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => trivial
    | some b => exact ReadsS.mono (Nat.zero_le k) (hf i b hi)
  | .sort _, _, h => h
  | .const .., _, h => h
  | .forallE t b _, _, h => ⟨ReadsS.replaceFVars hf h.1, ReadsS.replaceFVars hf h.2⟩
  | .lam t b _, _, h => ⟨ReadsS.replaceFVars hf h.1, ReadsS.replaceFVars hf h.2⟩
  | .app f a, _, h => ⟨ReadsS.replaceFVars hf h.1, ReadsS.replaceFVars hf h.2⟩
  | .letE .., _, h => h.elim
  | .proj _ _ e, _, h => ⟨ReadsS.replaceFVars hf h.1, h.2⟩
  | .lit (.natVal _), _, h => h
  | .lit (.strVal _), _, h => h

/-! ## `replaceFVars`, syntactically -/

/-- The leaves of a replaced term: the term's own or a replacement's. -/
theorem Expr.fvarLeaves_replaceFVars {f : Nat → Option Expr} :
    ∀ (e : Expr) (l : Nat × Expr), l ∈ (e.replaceFVars f).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ i b, f i = some b ∧ l ∈ b.fvarLeaves
  | .bvar _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .fvar i ty, l, h => by
    simp only [Expr.replaceFVars] at h
    cases hi : f i with
    | none => rw [hi] at h; exact Or.inl h
    | some b => rw [hi] at h; exact Or.inr ⟨i, b, hi, h⟩
  | .sort _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .const .., l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .lit _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .app g a, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars g l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars a l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .lam t b _, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars t l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars b l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .forallE t b _, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars t l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars b l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .letE t v b, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with (h | h) | h
    · rcases fvarLeaves_replaceFVars t l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars v l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
    · rcases fvarLeaves_replaceFVars b l h with h | h
      · exact Or.inl (by simp [Expr.fvarLeaves, h])
      · exact Or.inr h
  | .proj _ _ x, l, h => by
    simp only [Expr.replaceFVars, Expr.fvarLeaves] at h
    rcases fvarLeaves_replaceFVars x l h with h | h
    · exact Or.inl (by simp [Expr.fvarLeaves, h])
    · exact Or.inr h

/-- A replaced term is as bvar-closed as the term, at bvar-closed replacements. -/
theorem Expr.looseBVarsBounded_replaceFVars {f : Nat → Option Expr}
    (hf : ∀ i b, f i = some b → b.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.replaceFVars f).looseBVarsBounded k = true
  | .bvar _, _, h => h
  | .fvar i ty, k, _ => by
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => rfl
    | some b => exact ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) (hf i b hi)
  | .sort _, _, h => h
  | .const .., _, h => h
  | .lit _, _, h => h
  | .app g a, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨looseBVarsBounded_replaceFVars hf g k h.1, looseBVarsBounded_replaceFVars hf a k h.2⟩
  | .lam t b _, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨looseBVarsBounded_replaceFVars hf t k h.1,
      looseBVarsBounded_replaceFVars hf b (k + 1) h.2⟩
  | .forallE t b _, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨looseBVarsBounded_replaceFVars hf t k h.1,
      looseBVarsBounded_replaceFVars hf b (k + 1) h.2⟩
  | .letE t v b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨looseBVarsBounded_replaceFVars hf t k h.1.1, looseBVarsBounded_replaceFVars hf v k h.1.2⟩,
      looseBVarsBounded_replaceFVars hf b (k + 1) h.2⟩
  | .proj _ _ x, k, h => by
    simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.replaceFVars, Expr.looseBVarsBounded]
    exact looseBVarsBounded_replaceFVars hf x k h

/-- A replaced term is scoped where its kept variables and the replacements are. -/
theorem Expr.WScoped_replaceFVars {f : Nat → Option Expr} {d : Nat}
    (hf : ∀ i b, f i = some b → Expr.WScoped d b) :
    ∀ (e : Expr) {D : Nat}, Expr.WScoped D e → (∀ l ∈ e.fvarLeaves, f l.1 = none → l.1 < d) →
      Expr.WScoped d (e.replaceFVars f)
  | .bvar _, _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .fvar i ty, D, h, hk => by
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none =>
      simp only [Option.getD_none, Expr.WScoped]
      simp only [Expr.WScoped] at h
      exact ⟨hk (i, ty) (by simp [Expr.fvarLeaves]) hi, h.2⟩
    | some b => exact hf i b hi
  | .sort _, _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .const .., _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .lit _, _, _, _ => by simp [Expr.replaceFVars, Expr.WScoped]
  | .app g a, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf g h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf a h.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .lam t b _, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf t h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf b h.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .forallE t b _, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf t h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf b h.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .letE t v b, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact ⟨WScoped_replaceFVars hf t h.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf v h.2.1 fun l hl => hk l (by simp [Expr.fvarLeaves, hl]),
      WScoped_replaceFVars hf b h.2.2 fun l hl => hk l (by simp [Expr.fvarLeaves, hl])⟩
  | .proj _ _ x, D, h, hk => by
    simp only [Expr.WScoped] at h
    simp only [Expr.replaceFVars, Expr.WScoped]
    exact WScoped_replaceFVars hf x h fun l hl => hk l (by simp [Expr.fvarLeaves, hl])

/-- **The leaves of a replaced term, sharply**: a replacement's, or a leaf of
the term at or below a KEPT variable of the term (a kept variable's
annotation reads only variables below it). -/
theorem Expr.fvarLeaves_replaceFVars_kept {f : Nat → Option Expr} :
    ∀ (e : Expr) {D : Nat}, Expr.WScoped D e → ∀ l ∈ (e.replaceFVars f).fvarLeaves,
      (∃ i b, f i = some b ∧ l ∈ b.fvarLeaves) ∨
      (l ∈ e.fvarLeaves ∧ ∃ i ty, f i = none ∧ (i, ty) ∈ e.fvarLeaves ∧ l.1 ≤ i)
  | .bvar _, _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .fvar i ty, D, hw, l, h => by
    simp only [Expr.replaceFVars] at h
    cases hi : f i with
    | none =>
      rw [hi] at h
      simp only [Option.getD_none] at h
      refine Or.inr ⟨h, i, ty, hi, by simp [Expr.fvarLeaves], ?_⟩
      simp only [Expr.fvarLeaves, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · simp only [Expr.WScoped] at hw
        exact Nat.le_of_lt (ConLeche.Expr.fvarLeaves_lt_of_wscoped hw.2 l h)
    | some b => rw [hi] at h; exact Or.inl ⟨i, b, hi, h⟩
  | .sort _, _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .const .., _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .lit _, _, _, l, h => by simp [Expr.replaceFVars, Expr.fvarLeaves] at h
  | .app g a, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars_kept g hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept a hw.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .lam t b _, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars_kept t hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept b hw.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .forallE t b _, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with h | h
    · rcases fvarLeaves_replaceFVars_kept t hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept b hw.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .letE t v b, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves, List.mem_append] at h
    rcases h with (h | h) | h
    · rcases fvarLeaves_replaceFVars_kept t hw.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept v hw.2.1 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
    · rcases fvarLeaves_replaceFVars_kept b hw.2.2 l h with h | ⟨h1, i, ty, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩
  | .proj _ _ x, D, hw, l, h => by
    simp only [Expr.WScoped] at hw
    simp only [Expr.replaceFVars, Expr.fvarLeaves] at h
    rcases fvarLeaves_replaceFVars_kept x hw l h with h | ⟨h1, i, ty, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨by simp [Expr.fvarLeaves, h1], i, ty, h2, by simp [Expr.fvarLeaves, h3], h4⟩

end ConLeche
