module

public import ConLeche.Verify.Inductives.PosDerivK
public import ConLeche.Verify.Inductives.UseSynK
public import ConLeche.Verify.Shift
public import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Inductives.PosDerivKInv
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# What a key-named use must satisfy for the model (PRIMREC / NESTKN-M3, M3B)

`UseOkK` is the hook the monotonicity and accessibility proofs (`posDK_mono`,
`posDK_acc`, through `useCoreK`, `Model/Inductives/UseBridgeK.lean`) need on
every `use` of the key-named positivity derivation (`PosDKH`), beyond the
premises the use rule carries.  Since NESTKN-M3B the run DISCHARGES it
(`Verify/Inductives/UseOkKRun.lean`): its clauses are either kernel checks
(K) or syntactic facts about the kernel's own constructions (P), proved in
`Verify/Inductives/UseSynK.lean`.

The clauses, at a use of the key `kc` spelled `ps` at the user's layout `L`,
of the node `kn` with layout `lo` and met set `metc`, the match's bindings
`bs` (`θ = thetaK … bs`):

* (U0, K) the node's key's container is no member of the block and not
  `Quot` (checked at every use, carried to the node through the cache);
* (U1, K) the used container takes the spelling's parameter count;
* (R) the used key's parameters are the spelling read back (`rbK`) — every
  caller builds the key that way;
* (U3-K) each family type is a TYPE: inferred into a sort at its family's
  depth (`nestLayoutK`);
* (U4-K) the node's head key at `DsF` inferred at the node's base
  (`nestLayoutK`'s joint typing) — `DsF` reads;
* (U5-K) each family's key inferred at the members' depth (`nestLayoutK`) —
  the keys read;
* (U7-K) every family bound to a bvar-closed term that HAS its family's type
  at the bindings — both inferred at the user, defeq; a MET family's binding
  read at the family's index count (`BindArityK`, with U8 — PRIMREC /
  NESTKN-M4: a key occurrence binding has a parameter);
* (P) at a use site whose spelling and layout are syntactically good
  (`SiteSynK`, what the model knows at every use), the use's syntax
  (`UseSynK`): the node's material scoped, bvar-closed, its leaves the
  key's or its families' (U2–U5); the key's leaves the spelling's or the
  user's families' keys' (U6); every binding scoped at the user, its leaves
  the spelling's or the user's layout material's (U7).

Readability is not a clause: every term the model reads here is inferred by
a (K) clause, and an inferred, scoped term reads (`acceptedReads_of`).
-/

namespace ConLeche

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
    -- (R) the used key is the spelling read back
    kc.ds = ps.map (rbK ctx L) ∧
    -- (U3-K) the families' types are types
    (∀ j (hj : j < lo.L.famTys.length), ∃ T sv,
      ops.inferType env (ctx.hiAt 0 + j) lo.L.famTys[j] = .ok T ∧
        ops.ensureSort env (ctx.hiAt 0 + j) T = .ok sv) ∧
    -- (U4-K) the node's head key at `DsF`
    (∃ n T, ops.inferType env (ctx.hiAt 0 + lo.L.nF)
      (Expr.mkAppN (.const n lo.L.lvls) lo.L.dsF) = .ok T) ∧
    -- (U5-K) the families' keys
    (∀ p ∈ lo.L.fams, ∃ T, ops.inferType env (ctx.hiAt 0) p.1.expr = .ok T) ∧
    -- (U7-K) the bindings
    (∀ j (hj : j < lo.L.nF), ∃ b, thetaK ctx lo.L.nF bs (ctx.hiAt 0 + j) = some b ∧
      b.looseBVarsBounded 0 = true ∧
      (∃ T, ops.inferType env L.hi b = .ok T ∧
        (∃ T', ops.inferType env L.hi ((lo.L.famTys.getD j default).replaceFVars
          (thetaK ctx lo.L.nF bs)) = .ok T') ∧
        ops.isDefEq env L.hi T ((lo.L.famTys.getD j default).replaceFVars
          (thetaK ctx lo.L.nF bs)) = .ok true) ∧
      (j ∈ metc → ∀ key nI, lo.L.fams[j]? = some (key, nI) → BindArityK ctx L b nI)) ∧
    -- (P) the use's syntax, at a syntactically good site
    (SiteSynK ctx L ps → UseSynK ctx L kn ps lo bs)

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

end ConLeche
