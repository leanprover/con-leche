import Setlec.Verify.Denote
import Setlec.Verify.Denote.OpenVars
import Setlec.Verify.Denote.VClosed

/-!
# The mode-indexed algorithmic relation family (task #148, T2)

*(Re-based to `Setlec/SetBase/*` at THE SEPARATION's S2, task #161.  The
ruled criterion for the base is "no `EnvS`": these relations are
parametric in `cval : TConstVal` and import nothing but
`Setlec/Verify/*`, and BOTH consistency proofs are stated over them —
the collapsed lane's `no_proof_of_Empty_R` and the graded lane's
`no_proof_of_Empty_P` alike.  The gate's own rule says a module both
lanes need "stays R until it is re-based to `Setlec/SetBase/*` by
name"; this is that re-basing.  Path and module name changed;
namespaces, statements and proofs verbatim.)*


The five mutually inductive relations of the campaign design's §1
(`Setlec/SetR/DESIGN.md` records the deviations): reduction, inference,
definitional equality, the telescope walk and the spine walk, on
env-free TT syntax (`Setlec.TT.VExpr`), over `List VExpr` contexts,
parametrized by

* `μ : CheckMode` — the mode index (task #147's kernel mode; the
  design's `CMode`).  Only `.setModel` gets a soundness reading in this
  campaign; **no rule below reads `μ`** — the family as written is the
  set-mode certificate inventory, and the seven tt-only checks
  (#126/#129/#130/#135/#136/#137/#146) are deliberately absent (the
  premise-exactness discipline, design §0);
* `env : Env` — the environment whose stored data the side conditions
  read (lookups, capability flags, level guards);
* `cval : TConstVal` — the constant valuation (`Setlec/Verify/Denote.lean`);
  stream constants appear in subjects as `cval n ψ`;
* `φ : Name → Nat` — the ground level assignment.

**Two-pack discipline** (design §0): each rule's *premises* are one
sub-derivation per certificate the set-mode checker runs at that site,
in the checker's own order; its *side conditions* are the checker's
Boolean guards and `denote` facts — all V-free, and all `Δ`/depth-free
(closed denotations are spelled `denoteClosed`; the two depth-`rP`
`denote` facts of the nested iota premise are depth-fixed by stored
data, never by the ambient context).  That discipline is what makes the
mutual weakening lemma (`Setlec/SetBase/Weaken.lean`, M1) go through.

Every rule cites its checker site (`Setlec/Kernel/Core.lean` unless
noted); the checker is the source of truth, and a premise that reads
wrong against the cited body is a finding, not a silent fix.

**Type-normalization premises are `DefEq`, not `Red`** (the 2026-08-27
amendment, T3's finding + T4's decision — the full record is in
`Setlec/SetR/DESIGN.md`).  Wherever the checker runs
`t ← infer x; w ← whnf t; match w`, the rule's premise pair is
`Infer x tx` + `DefEq tx Shape`: the bridge's infer-claim is stated up
to the relation's own equality (design §0 decision 1), so it cannot
name the checker's actual `t` — the slack sits *between* the two
premises, and `Red` (directed reduction, deliberately without a
conversion prefix) cannot absorb it, while `DefEq` contains the actual
chain via `DefEq.trans (DefEq.symm …) (DefEq.ofRed …)`.  Subject-side
reductions (the iota major, `reduceNat` arguments, `Red p P` in the
`.proj` clause) remain `Red` — there the checker reduces the term
itself and the bridge derives the reduction directly.

Four checker features contribute **zero rules** (design §7.2): delta
(`denote` reads definitions through `cval`; a delta step is an identity
of denotations), `Nat`-literal packing/unpacking (`⟦.lit (n+1)⟧` *is*
`.app ⟦succ⟧ (natLitT n)` syntactically), `litToCtorIfNat`, and the
whnf/defeq loop structure (`Red.trans` chains in the bridge).
-/

namespace Setlec.SetR

open Setlec.TT
open Setlec.TTVerify

/-- Is the term a λ?  The task-#152 chain guard (`!body.isLam`),
`VExpr`-level: the check fires once per λ-chain, at the innermost
binder, and I7's codomain premise is guarded the same way. -/
def _root_.Setlec.TT.VExpr.isLam : VExpr → Bool
  | .lam .. => true
  | _ => false

@[simp] theorem _root_.Setlec.TT.VExpr.isLam_liftN (e : VExpr)
    (n k : Nat) : (e.liftN n k).isLam = e.isLam := by
  cases e <;> rfl

/-! ## Term-level helpers

Transposes of the checker's spine builders.  Searched against the T1
inventory first (`Setlec/Verify/Denote/*`): `natLitT`/`strLitT` exist
and are reused; the three below did not exist on the `VExpr` side. -/

/-- The term of a `Nat` literal at the stored `Nat.zero`/`Nat.succ`
valuations — `denote`'s own `.lit (.natVal n)` clause, named. -/
def natLitV (cval : TConstVal) (φ : Name → Nat) (n : Nat) : VExpr :=
  natLitT (cval natZeroName (Level.substFn φ [] []))
    (cval natSuccName (Level.substFn φ [] [])) n

/-- The stored `Nat.succ` valuation (the ops are level-monomorphic:
`natLitSupported` pins empty level parameters). -/
def succV (cval : TConstVal) (φ : Name → Nat) : VExpr :=
  cval natSuccName (Level.substFn φ [] [])

/-- The projection spines of a structural-eta comparison: field `j` is
the installed projection function applied to the type's arguments and
the stuck side.  Transpose of the map in `structEtaCertWith`
(`Core.lean:966-968`); `ψt` is the *type's* level assignment
(`structEtaProjCerts` pins `cvp.levelParams = cvT.levelParams`). -/
def projSpinesV (cval : TConstVal) (T : Name) (ψt : Name → Nat)
    (ts : List VExpr) (b : VExpr) (nF : Nat) : List VExpr :=
  (List.range nF).map fun j =>
    VExpr.mkAppN (cval (projFnName T j) ψt) (ts ++ [b])

/-- The eta-rescue fabrication's argument spine: the reduced type's
arguments followed by the projections of the stuck major.  Transpose of
`etaFabArgs` (`Core.lean:1058-1061`). -/
def etaFabArgsV (cval : TConstVal) (T : Name) (ψt : Name → Nat)
    (ts : List VExpr) (major : VExpr) (nF : Nat) : List VExpr :=
  ts ++ projSpinesV cval T ψt ts major nF

/-- The eta-rescue fabrication's spine at the entry kind (task #175
W4c): the tower spelling's readings (`projNV`) at an all-tower slot
family, the projection functions' applications otherwise — the
transpose of `etaFabArgsE` (`Core.lean`), `env`-dependent exactly as
that is. -/
def etaFabArgsVE (cval : TConstVal) (env : Env) (T : Name) (ψt : Name → Nat)
    (ts : List VExpr) (major : VExpr) (nF : Nat) : List VExpr :=
  ts ++ (if towerSlotsAll env T nF then
    (List.range nF).map fun j => projNV j major
  else projSpinesV cval T ψt ts major nF)

/-- `VExpr`-level residual of a `pi`-telescope along an argument list —
the transpose of `piResidual` (`Core.lean:747-750`), used by the
`.proj` inference rule to spell its conclusion type without mentioning
the checker's `Expr`s. -/
def piResidualV : VExpr → List VExpr → Option VExpr
  | T, [] => some T
  | .pi _ B, a :: as => piResidualV (B.inst a) as
  | _, _ :: _ => none

/-! ## The relation family (design §1)

`Red` is one relation for both `whnfCore` and the `whnf` loop: delta
steps and `reduceNat`'s succ-packing are invisible at the denotation,
so the core/loop distinction has no relational content. -/

mutual

/-- **Reduction** (design §1.1, R1–R14): the reflexive-transitive
closure of the head steps `whnfCore`/`whnf` take, each step packing
exactly the certificates the set-mode checker runs at that site. -/
inductive Red (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → VExpr → VExpr → Prop where
  /-- R1: value clauses, stuck fallbacks, `iotaRec = none`, uncertified
  redexes — every `pure e` branch of the reduction bodies. -/
  | refl {Δ : List VExpr} {v : VExpr} : Red μ env cval φ Δ v v
  /-- R2: the recursive `whnfCore` continuations and the `whnf` loop
  (`whnfStep`/`whnfLoop`, `Core.lean:1511-1530`). -/
  | trans {Δ : List VExpr} {v w x : VExpr} :
      Red μ env cval φ Δ v w → Red μ env cval φ Δ w x →
      Red μ env cval φ Δ v x
  /-- R3: head normalization inside an application
  (`whnfCoreBody`'s `.app` clause, `Core.lean:1412-1413`). -/
  | appFn {Δ : List VExpr} {f f' a : VExpr} :
      Red μ env cval φ Δ f f' →
      Red μ env cval φ Δ (.app f a) (.app f' a)
  /-- R4: beta, with the per-redex argument certificate
  (`Core.lean:1423-1425`; unconditional since the task-#100
  de-gating). -/
  | beta {Δ : List VExpr} {A b a ta : VExpr} :
      Infer μ env cval φ Δ a ta →
      DefEq μ env cval φ Δ ta A →
      Red μ env cval φ Δ (.app (.lam A b) a) (b.inst a)
  /-- R5: zeta, premise-free (`whnfCoreBody`'s `.letE` clause,
  `Core.lean:1476-1481`). -/
  | zeta {Δ : List VExpr} {T v b : VExpr} :
      Red μ env cval φ Δ (.letE T v b) (b.inst v)
  /-- R6: the native structural projection
  `proj_i (ctor p⃗ x⃗) ↦ x_i`, driven by the projection table
  (`whnfCoreBody`'s `.proj` clause, `Core.lean:1431-1475`), with the
  `projCert` pack — and **no constructor-telescope certification**
  (#126's `projTeleCert` was TT-lane-only; deleted at task #161's
  de-gating round, item A).  `sn` is the node's struct-name slot, which the
  denotation does not carry; it is quantified, and soundness pins what
  a native entry can be through `ProjOk`.

  **The constructor spine's telescope certificate is a premise**
  (the 2026-08-27 T4 amendment, second increment — record in
  `Setlec/SetR/DESIGN.md`): the checker's `projCert` infers the
  constructor form `P` as a whole, and that run's own per-argument
  re-checks are what the model's soundness consumes
  (`Model/Core/Whnf.lean:639-741`, via `inferTypeCore_app_inv'`).
  The relational `Infer P te` premise alone under-determines them
  (`Infer.const` overlaps app-shaped subjects), so the rule exposes
  them as a `Tele` walk over the constructor's denoted stored type —
  the same premise-exactness argument as repair A. -/
  | projRed {Δ : List VExpr} {p P fv ta ta' te te' TC restC : VExpr}
      {i : Nat} {sn : Name} {entry : ProjEntry} {ci : ConstantInfo}
      {us : List Level} {vs : List VExpr} :
      -- side conditions (V-free), read off the clause's guards
      env.findProj? sn i = some entry →
      entry.native = true →
      i < entry.numFields →
      vs.length = entry.numParams + entry.numFields →
      us.length = entry.levelParams.length →
      -- the constructor head's denotation data (`denote_const` shape)
      env.find? entry.ctor = some ci →
      us.length = ci.toConstantVal.levelParams.length →
      P = VExpr.mkAppN
        (cval entry.ctor
          (Level.substFn φ ci.toConstantVal.levelParams us)) vs →
      vs[entry.numParams + i]? = some fv →
      -- the constructor's stored type, denoted (D1 closedness)
      denoteClosed cval env φ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some TC →
      VExpr.Closed TC →
      -- the subject reduces to constructor form
      Red μ env cval φ Δ p P →
      -- the constructor spine's telescope certificate (the infer run's
      -- own argument re-checks, exposed — see the docstring)
      Tele μ env cval φ Δ TC vs restC →
      -- `projCert`, task #161 item B1 (harvest site 18 / P9): the
      -- clause runs two `inferTypeCore`s and nothing else.  The four
      -- sort legs it used to run — infer *that* type, whnf it to a
      -- sort, `Level.isEquiv` against the entry's instantiated
      -- `fieldSort`/`structSort`, for the field and for the subject —
      -- are deleted, so this rule states only the two runs.  The Prop
      -- collapse that used the field's sort leg is re-derived from the
      -- constructor telescope certificate (`Tele` above, the R6
      -- amendment): `mem_univ_zero` on the pinned pair's own component
      -- memberships.  (`DefEq`, not `Red`: the bridge's infer-claim is
      -- up to `DefEq`, the 2026-08-27 amendment.)
      Infer μ env cval φ Δ fv ta →
      DefEq μ env cval φ Δ ta ta' →
      Infer μ env cval φ Δ P te →
      DefEq μ env cval φ Δ te te' →
      Red μ env cval φ Δ (.proj i p) fv
  /-- R6′ (task #175 wiring W5): the structural projection at a
  **tower-backed** entry — R6's premises verbatim plus the entry
  kind, concluding at the uniform iterated reading (`projNV i`),
  which is what `denote`'s tower branch reads a `.proj` node to. -/
  | projRedTower {Δ : List VExpr} {p P fv ta ta' te te' TC restC : VExpr}
      {i : Nat} {sn : Name} {entry : ProjEntry} {ci : ConstantInfo}
      {us : List Level} {vs : List VExpr} :
      env.findProj? sn i = some entry →
      entry.native = true → entry.tower = true →
      i < entry.numFields →
      vs.length = entry.numParams + entry.numFields →
      us.length = entry.levelParams.length →
      -- the tower-fire guard (task #175 W4c/O4): the clause fires only
      -- under the `Prop` guard at the constructor's instantiation
      entry.fireOk us = true →
      env.find? entry.ctor = some ci →
      us.length = ci.toConstantVal.levelParams.length →
      P = VExpr.mkAppN
        (cval entry.ctor
          (Level.substFn φ ci.toConstantVal.levelParams us)) vs →
      vs[entry.numParams + i]? = some fv →
      denoteClosed cval env φ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some TC →
      VExpr.Closed TC →
      Red μ env cval φ Δ p P →
      Tele μ env cval φ Δ TC vs restC →
      Infer μ env cval φ Δ fv ta →
      DefEq μ env cval φ Δ ta ta' →
      Infer μ env cval φ Δ P te →
      DefEq μ env cval φ Δ te te' →
      Red μ env cval φ Δ (projNV i p) fv
  /-- R7/R16: a `String` literal steps to (the reduction of) its
  denoted constructor form — `projLitToCtor` (`Core.lean:1224-1229`)
  and `litMajorToCtor`'s string case (`Core.lean:1208-1213`), one
  rule for both sites.  The side `denoteClosed` fact is the honest
  transpose (`⟦strLitToConstructor s⟧` is `strLitT` up to the
  near-`rfl` clause equations; the bridge discharges it there). -/
  | strLitCtor {Δ : List VExpr} {s : String} {SC P : VExpr} :
      strLitSupported env = true →
      denoteClosed cval env φ (strLitToConstructor s) = some SC →
      VExpr.Closed SC →
      Red μ env cval φ Δ SC P →
      Red μ env cval φ Δ (strLitT cval env φ s) P
  /-- R8: `Nat.succ` literal packing (`reduceNat`,
  `Core.lean:686-693`).  The conclusion's right side is syntactically
  `.app ⟦succ⟧ (natLitT n)`, so this is R3+R1 content — kept as a named
  rule for bridge legibility (design R8). -/
  | natSucc {Δ : List VExpr} {va : VExpr} {n : Nat} :
      natLitSupported env = true →
      Red μ env cval φ Δ va (natLitV cval φ n) →
      Red μ env cval φ Δ (.app (succV cval φ) va) (natLitV cval φ (n + 1))
  /-- R9: unary certified `Nat` ops (`pred`/`log2`; `reduceNat`,
  `Core.lean:695-702`). -/
  | natOp1 {Δ : List VExpr} {va V : VExpr} {c : Name} {n : Nat} {r : Expr} :
      (c = natPredName ∨ c = natLog2Name) →
      natOpGuard env c = true →
      natOpResult c n 0 = some r →
      denoteClosed cval env φ r = some V →
      VExpr.Closed V →
      Red μ env cval φ Δ va (natLitV cval φ n) →
      Red μ env cval φ Δ
        (.app (cval c (Level.substFn φ [] [])) va) V
  /-- R10: binary certified `Nat` ops (the 14-name list; `reduceNat`,
  `Core.lean:711-721`). -/
  | natOp2 {Δ : List VExpr} {va vb V : VExpr} {c : Name} {n₁ n₂ : Nat}
      {r : Expr} :
      (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
        c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
        c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
        c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
        c = natShiftLeftName ∨ c = natShiftRightName) →
      natOpGuard env c = true →
      natOpResult c n₁ n₂ = some r →
      denoteClosed cval env φ r = some V →
      VExpr.Closed V →
      Red μ env cval φ Δ va (natLitV cval φ n₁) →
      Red μ env cval φ Δ vb (natLitV cval φ n₂) →
      Red μ env cval φ Δ
        (.app (.app (cval c (Level.substFn φ [] [])) va) vb) V
  /-- R11: **iota** (`iotaRec`, `Core.lean:1266-1354`), the wide rule.
  The subject is the *original* spine (`xs`, major unreduced at slot
  `mI`); premises 1–2 normalize and possibly rescue the major, exactly
  as `iotaRec` does internally (over-application is handled by R3 in
  the bridge, as by the outer app recursion in the checker).  The
  nested parameter premise reuses `RecRulesTT`'s
  `openRev`/`instRevChain` spelling verbatim
  (`Setlec/TTVerify/EnvTT.lean:230-237`); `rP ≤ mI` is a side
  condition **guarded on `.nested` fires** (the 2026-08-28 D3
  amendment: `EnvWF` concludes it only in the `.nested` branch, and
  the weakening lemma needs it only there — the pin chain's arity;
  soundness reads the unconditional fact off the install layer,
  `RecRulesV`'s first conclusion, as `RecRulesTT` concludes it). -/
  | iota {Δ : List VExpr} {n : Name} {cv : ConstantVal} {mI rP : Nat}
      {rules : List RecRule} {rl : RecRule} {cvj : ConstantVal}
      {cnP cnF : Nat} {us usj : List Level}
      {xs ys : List VExpr} {m₀ m TV TVj R restR restC H : VExpr}
      {cargs : List VExpr} :
      -- side conditions: the stored recursor, rule and constructor
      env.find? n = some (.recInfo cv mI rP rules) →
      rules.find? (fun r' => r'.ctor == rl.ctor) = some rl →
      rl.fire ≠ .inert →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (∀ lvls pins, rl.fire = .nested lvls pins → rP ≤ mI) →
      xs.length = mI + 1 →
      ys.length = rl.ctorParams + rl.nfields →
      us.length = cv.levelParams.length →
      usj.length = cvj.levelParams.length →
      (cv.type.stripPis (mI + 1)).isSome = true →
      (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome = true →
      -- the fire site's level guard (`Core.lean:1310-1312`; the level
      -- comparand ignores the argument spine)
      Level.isEquivList usj
        (recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1
        = some true →
      -- the stored types and the rule's right-hand side, denoted.  The
      -- explicit closedness conjuncts are deviation D1
      -- (`Setlec/SetR/DESIGN.md`): `denoteClosed` alone does not entail
      -- them, and the weakening lemma transports them
      denoteClosed cval env φ
        (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
      VExpr.Closed TV →
      denoteClosed cval env φ
        (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVj →
      VExpr.Closed TVj →
      denoteClosed cval env φ
        (rl.rhs.instantiateLevelParams cv.levelParams us) = some R →
      VExpr.Closed R →
      -- the rescued major's constructor shape
      m = VExpr.mkAppN
        (cval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys →
      -- premise 1: the major normalizes (string-literal conversion via
      -- R7 inside this chain)
      Red μ env cval φ Δ (xs.getD mI default) m₀ →
      -- premise 2: the rescue (R12–R14) or `refl`
      Red μ env cval φ Δ m₀ m →
      -- premise 3: the parameter comparands (`Core.lean:1313-1315`) —
      -- plain: the recursor's own leading arguments
      (rl.fire = .plain →
        DefEqL μ env cval φ Δ (ys.take rl.ctorParams)
          (xs.take rl.ctorParams)) →
      -- premise 3': nested — the stored pins, read through the reverse
      -- opening at the recursor's first `rP` denoted arguments
      -- (the `bvarsBelow` hypothesis is deviation D1's premise-side
      -- form: the consumer supplies the pin value's scoping, which the
      -- depth-`rP` `denote` fact alone does not carry)
      (∀ lvls pins, rl.fire = .nested lvls pins →
        ∀ i, i < rl.ctorParams →
        ∀ vp : VExpr,
          denote cval env φ rP
            (openRev 0 rP ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) = some vp →
          VExpr.bvarsBelow rP vp →
          DefEq μ env cval φ Δ (ys.getD i default)
            (VExpr.instRevChain (xs.take rP) vp)) →
      -- premise 4: the recursor telescope certificate
      -- (`Core.lean:1316-1318`), at the rescued major
      Tele μ env cval φ Δ TV (xs.take mI ++ [m]) restR →
      -- premise 5: the constructor telescope certificate
      -- (`Core.lean:1319-1321`)
      Tele μ env cval φ Δ TVj ys restC →
      -- premise 6: the index check (`Core.lean:1327-1336`), through the
      -- `IotaIndexPin` decomposition of the constructor residual
      restC = VExpr.mkAppN H cargs →
      (mI = rP ∨ cargs.length = rl.ctorParams + (mI - rP)) →
      DefEqL μ env cval φ Δ (cargs.drop rl.ctorParams)
        ((xs.take mI).drop rP) →
      Red μ env cval φ Δ
        (VExpr.mkAppN (cval n (Level.substFn φ cv.levelParams us)) xs)
        (VExpr.mkAppN R (xs.take rP ++ ys.drop rl.ctorParams))
  /-- R12: the K-flagged stuck-major rescue (`majorToCtor`'s K branch,
  `Core.lean:1087-1133`).  The `¬ isCtorApp` dispatch gate and the
  fab-scoping guards are Expr-side, bridge-only (no `VExpr` shadow; the
  relation subject is already the denoted fabrication).  The
  proof-irrelevance certificate enters as a `DefEq` premise — the
  bridge builds it through D8/D9 from `proofIrrel`'s inversion. -/
  | rescueK {Δ : List VExpr} {m₀ tm TM tf TVj rest : VExpr}
      {recName T : Name} {cv cvj : ConstantVal} {mI rP : Nat}
      {rl : RecRule} {cnP cnF : Nat} {cvT : ConstantVal} {caps : IndCaps}
      {tus ust : List Level} {ts : List VExpr} :
      -- side conditions: the single-rule recursor and its K-capable family
      env.find? recName = some (.recInfo cv mI rP [rl]) →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn = .const T tus →
      env.find? T = some (.indInfo cvT caps) →
      caps.ruleK = true →
      cnF = 0 →
      cvj.levelParams.length = ust.length →
      ust.length = cvT.levelParams.length →
      cnP ≤ ts.length →
      (cvj.type.stripPis cnP).isSome = true →
      TM = VExpr.mkAppN
        (cval T (Level.substFn φ cvT.levelParams ust)) ts →
      denoteClosed cval env φ
        (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj →
      VExpr.Closed TVj →
      -- the major's type, normalized to the family's application
      -- (`DefEq`: type-normalization premise, see the amendment note)
      Infer μ env cval φ Δ m₀ tm →
      DefEq μ env cval φ Δ tm TM →
      -- the synthetic-spine certificate (task #71, `Core.lean:1108-1111`)
      Tele μ env cval φ Δ TVj (ts.take cnP) rest →
      -- the official `to_cnstr_when_K` type check on the fabrication
      -- (`Core.lean:1125`)
      Infer μ env cval φ Δ
        (VExpr.mkAppN
          (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
          (ts.take cnP)) tf →
      DefEq μ env cval φ Δ TM tf →
      -- the proof-irrelevance certificate (D8/D9 via `proofIrrel`)
      DefEq μ env cval φ Δ
        (VExpr.mkAppN
          (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
          (ts.take cnP)) m₀ →
      Red μ env cval φ Δ m₀
        (VExpr.mkAppN
          (cval rl.ctor (Level.substFn φ cvj.levelParams ust))
          (ts.take cnP))
  /-- R13: the structural-eta stuck-major rescue (`majorToCtor`'s eta
  branch, `Core.lean:1135-1173`).  The `structEtaCertWith` pack enters
  as a `DefEq` premise — D10 concludes exactly `fab ≡ m₀`, and the
  bridge reaches it through `structEtaCertWith`'s inversion with
  `wtb := TM` (at `--set-model` that pack excludes the #137
  constructor-telescope cert). -/
  | rescueEta {Δ : List VExpr} {m₀ tm TM TVj rest : VExpr}
      {recName T : Name} {cv cvj : ConstantVal} {mI rP : Nat}
      {rl : RecRule} {cnP cnF : Nat} {cvT : ConstantVal} {caps : IndCaps}
      {tus ust : List Level} {ts : List VExpr} :
      env.find? recName = some (.recInfo cv mI rP [rl]) →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn = .const T tus →
      env.find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      rl.ctor = caps.etaCtor →
      Name.isProjFnShape recName = false →
      ts.length = caps.etaParams →
      ust.length = cvT.levelParams.length →
      piResultNeverZero cvT.levelParams ust cvT.type = true →
      cvj.levelParams.length = ust.length →
      (cvj.type.stripPis (caps.etaParams + caps.etaFields)).isSome = true →
      TM = VExpr.mkAppN
        (cval T (Level.substFn φ cvT.levelParams ust)) ts →
      denoteClosed cval env φ
        (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj →
      VExpr.Closed TVj →
      Infer μ env cval φ Δ m₀ tm →
      DefEq μ env cval φ Δ tm TM →
      -- the synthetic-spine certificate at the fabricated spine
      -- (task #71, `Core.lean:1166-1170` — always on)
      Tele μ env cval φ Δ TVj
        (etaFabArgsVE cval env T (Level.substFn φ cvT.levelParams ust) ts m₀
          caps.etaFields) rest →
      -- the `structEtaCertWith` pack (D10, with `wtb := TM`)
      DefEq μ env cval φ Δ
        (VExpr.mkAppN
          (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
          (etaFabArgsVE cval env T (Level.substFn φ cvT.levelParams ust) ts m₀
            caps.etaFields)) m₀ →
      Red μ env cval φ Δ m₀
        (VExpr.mkAppN
          (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust))
          (etaFabArgsVE cval env T (Level.substFn φ cvT.levelParams ust) ts m₀
            caps.etaFields))
  /-- R14: the 0-field fallthrough of the eta rescue
  (`Core.lean:1184-1188`): the fabrication is the bare constructor at
  the type's arguments, certified by proof irrelevance (D8/D9 via
  `proofIrrel`, as in R12). -/
  | rescueUnit0 {Δ : List VExpr} {m₀ tm TM TVj rest : VExpr}
      {recName T : Name} {cv cvj : ConstantVal} {mI rP : Nat}
      {rl : RecRule} {cnP cnF : Nat} {cvT : ConstantVal} {caps : IndCaps}
      {tus ust : List Level} {ts : List VExpr} :
      env.find? recName = some (.recInfo cv mI rP [rl]) →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn = .const T tus →
      env.find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      rl.ctor = caps.etaCtor →
      Name.isProjFnShape recName = false →
      caps.etaFields = 0 →
      ts.length = caps.etaParams →
      ust.length = cvT.levelParams.length →
      piResultNeverZero cvT.levelParams ust cvT.type = true →
      cvj.levelParams.length = ust.length →
      (cvj.type.stripPis (caps.etaParams + caps.etaFields)).isSome = true →
      TM = VExpr.mkAppN
        (cval T (Level.substFn φ cvT.levelParams ust)) ts →
      denoteClosed cval env φ
        (cvj.type.instantiateLevelParams cvj.levelParams ust) = some TVj →
      VExpr.Closed TVj →
      Infer μ env cval φ Δ m₀ tm →
      DefEq μ env cval φ Δ tm TM →
      -- the synthetic-spine certificate (0 fields: the spine is `ts`)
      Tele μ env cval φ Δ TVj ts rest →
      -- the proof-irrelevance certificate
      DefEq μ env cval φ Δ
        (VExpr.mkAppN
          (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts)
        m₀ →
      Red μ env cval φ Δ m₀
        (VExpr.mkAppN
          (cval caps.etaCtor (Level.substFn φ cvj.levelParams ust)) ts)
  /-- R15 (T3's finding 2, 2026-08-27): projection congruence — the
  `.proj` clause of `whnfCoreBody` (`Core.lean:1431-1475`) reduces the
  scrutinee and returns the stuck `.proj` on every non-firing branch.
  Premise-free beyond the scrutinee reduction (the clause runs no
  certificate on that path); appended at the end of `Red`'s own
  constructor list so the T2 rules keep their relative order. -/
  | projArg {Δ : List VExpr} {e e' : VExpr} {i : Nat} :
      Red μ env cval φ Δ e e' →
      Red μ env cval φ Δ (.proj i e) (.proj i e')

/-- **Inference** (design §1.3, I1–I10): successful `inferTypeCore`
runs (`inferBody`), premise-exact at `--set-model` — the proj rule
carries **no parameter-telescope certification** (#129's
`projParamCert` was TT-lane-only; deleted at task #161's de-gating
round, item A). -/
inductive Infer (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → VExpr → VExpr → Prop where
  /-- I1: sorts (`Core.lean:1549`). -/
  | sort {Δ : List VExpr} {u : Nat} :
      Infer μ env cval φ Δ (.sort u) (.sort (u + 1))
  /-- I2: variables (`Core.lean:1550-1559`; the fvar scope check is the
  bridge's `CtxOkR` side).  The slack of design §0 decision 1 lives in
  the *bridge* statement, not here: this is the plain lookup rule. -/
  | bvar {Δ : List VExpr} {i : Nat} {A : VExpr} :
      Δ[i]? = some A →
      Infer μ env cval φ Δ (.bvar i) (A.liftN (i + 1))
  /-- I3: constants (`Core.lean:1560-1567`).  Stored types are closed
  (`constsResolve` + `looseBVarsBounded` at install), so the conclusion
  type needs no lift; the `denoteClosed` spelling is what the weakening
  lemma consumes. -/
  | const {Δ : List VExpr} {n : Name} {ci : ConstantInfo}
      {us : List Level} {T : VExpr} :
      env.find? n = some ci →
      us.length = ci.toConstantVal.levelParams.length →
      denoteClosed cval env φ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some T →
      VExpr.Closed T →
      Infer μ env cval φ Δ
        (cval n (Level.substFn φ ci.toConstantVal.levelParams us)) T
  /-- I4: `Nat` literals (`Core.lean:1568-1570`). -/
  | litNat {Δ : List VExpr} {n : Nat} :
      natLitSupported env = true →
      Infer μ env cval φ Δ (natLitV cval φ n)
        (cval natName (Level.substFn φ [] []))
  /-- I5: `String` literals (`Core.lean:1571-1577`). -/
  | litStr {Δ : List VExpr} {s : String} :
      strLitSupported env = true →
      Infer μ env cval φ Δ (strLitT cval env φ s)
        (cval stringName (Level.substFn φ [] []))
  /-- I6: ∀-formation (`Core.lean:1578-1587`): the domain's sort and
  the opened body's sort (`ensureSort` = an I-premise + D-premise
  pair; the normalization premise is `DefEq`, amendment note). -/
  | pi {Δ : List VExpr} {A B tA tB : VExpr} {u v : Nat} :
      Infer μ env cval φ Δ A tA →
      DefEq μ env cval φ Δ tA (.sort u) →
      Infer μ env cval φ (A :: Δ) B tB →
      DefEq μ env cval φ (A :: Δ) tB (.sort v) →
      Infer μ env cval φ Δ (.pi A B) (.sort (imax u v))
  /-- I7: λ: the domain must be a type; the body's type is read back
  under the binder.  **Task-#152 amendment (#151 tier C)**: at the
  verified mode the checker also sort-checks the λ-chain's body type,
  once per chain at the innermost binder (`!body.isLam`); the premise
  is guarded exactly the same way, with the sort data (`B'`, `tB`,
  `v`) unconstrained when the guard does not fire.  The sort fact is
  stated at the checker's *own* computed body type `B'`, `DefEq`-linked
  to the third premise's `B` — `Infer`'s type slot is determined only
  up to `DefEq` (finding A5), so demanding the derivation at `B`
  itself would not be premise-exact.  Inner binders recover
  their codomain sorts by `hasSort_pi_of` induction along the chain
  (`Setlec/SetR/Annot/Validity.lean`). -/
  | lam {Δ : List VExpr} {A b tA B B' tB : VExpr} {u v : Nat} :
      Infer μ env cval φ Δ A tA →
      DefEq μ env cval φ Δ tA (.sort u) →
      Infer μ env cval φ (A :: Δ) b B →
      (μ.verified = true → b.isLam = false →
        DefEq μ env cval φ (A :: Δ) B B') →
      (μ.verified = true → b.isLam = false →
        Infer μ env cval φ (A :: Δ) B' tB) →
      (μ.verified = true → b.isLam = false →
        DefEq μ env cval φ (A :: Δ) tB (.sort v)) →
      Infer μ env cval φ Δ (.lam A b) (.pi A B)
  /-- I8: application (`Core.lean:1601-1613`), with the per-argument
  re-check — always on at `--set-model`. -/
  | app {Δ : List VExpr} {f a tf A B ta : VExpr} :
      Infer μ env cval φ Δ f tf →
      DefEq μ env cval φ Δ tf (.pi A B) →
      Infer μ env cval φ Δ a ta →
      DefEq μ env cval φ Δ ta A →
      Infer μ env cval φ Δ (.app f a) (B.inst a)
  /-- I9: projections (`Core.lean:1614-1644`): the subject's type
  whnfs to a native entry's family application; the conclusion type is
  the entry's stored type peeled along the arguments and the subject
  (`piResidualV`, the `VExpr`-level `piResidual`).  Head-match only —
  **no parameter-telescope certification** (#129's `projParamCert` was
  TT-lane-only; deleted at task #161's de-gating round, item A). -/
  | proj {Δ : List VExpr} {p tp TP resV : VExpr} {i : Nat} {T : Name}
      {entry : ProjEntry} {ciT : ConstantInfo} {us : List Level}
      {ps : List VExpr} :
      env.findProj? T i = some entry →
      entry.native = true →
      ps.length = entry.numParams →
      us.length = entry.levelParams.length →
      env.find? T = some ciT →
      us.length = ciT.toConstantVal.levelParams.length →
      denoteClosed cval env φ
        (entry.ty.instantiateLevelParams entry.levelParams us) = some TP →
      VExpr.Closed TP →
      piResidualV TP (ps ++ [p]) = some resV →
      Infer μ env cval φ Δ p tp →
      DefEq μ env cval φ Δ tp
        (VExpr.mkAppN
          (cval T (Level.substFn φ ciT.toConstantVal.levelParams us)) ps) →
      Infer μ env cval φ Δ (.proj i p) resV
  /-- I9′ (task #175 wiring W5): projections at a **tower-backed**
  entry — I9's premises verbatim plus the entry kind, concluding at the
  uniform iterated reading. -/
  | projTower {Δ : List VExpr} {p tp TP resV : VExpr} {i : Nat} {T : Name}
      {entry : ProjEntry} {ciT : ConstantInfo} {us : List Level}
      {ps : List VExpr} :
      env.findProj? T i = some entry →
      entry.native = true → entry.tower = true →
      ps.length = entry.numParams →
      us.length = entry.levelParams.length →
      env.find? T = some ciT →
      us.length = ciT.toConstantVal.levelParams.length →
      denoteClosed cval env φ
        (entry.ty.instantiateLevelParams entry.levelParams us) = some TP →
      VExpr.Closed TP →
      piResidualV TP (ps ++ [p]) = some resV →
      Infer μ env cval φ Δ p tp →
      DefEq μ env cval φ Δ tp
        (VExpr.mkAppN
          (cval T (Level.substFn φ ciT.toConstantVal.levelParams us)) ps) →
      Infer μ env cval φ Δ (projNV i p) resV
  /-- I10: `let` (`Core.lean:1645-1656`): annotation is a type, value
  matches it, body inferred with the value transparent. -/
  | letE {Δ : List VExpr} {T v b tT tv B : VExpr} {u : Nat} :
      Infer μ env cval φ Δ T tT →
      DefEq μ env cval φ Δ tT (.sort u) →
      Infer μ env cval φ Δ v tv →
      DefEq μ env cval φ Δ tv T →
      Infer μ env cval φ Δ (b.inst v) B →
      Infer μ env cval φ Δ (.letE T v b) B

/-- **Definitional equality** (design §1.2, D1–D14): positive
`isDefEqCore` verdicts (`defeqStep`, `Core.lean:1701-1899`).  `refl`
covers every branch that collapses at the denotation: the syntactic
fast path, `sort/sort` under `Level.isEquiv`, `lit/lit`,
`fvar i ≡ fvar i`, same-constant heads under `isEquivList`, and
`lit 0 ≡ Nat.zero`. -/
inductive DefEq (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → VExpr → VExpr → Prop where
  /-- D1. -/
  | refl {Δ : List VExpr} {v : VExpr} : DefEq μ env cval φ Δ v v
  /-- D2: used by the bridge for the mirrored certificate directions
  (`pairEtaCert`/`structEtaCert` run both ways; eta fires on either
  side's λ). -/
  | symm {Δ : List VExpr} {a b : VExpr} :
      DefEq μ env cval φ Δ a b → DefEq μ env cval φ Δ b a
  /-- D3: composes reduction with comparison in the bridge. -/
  | trans {Δ : List VExpr} {a b c : VExpr} :
      DefEq μ env cval φ Δ a b → DefEq μ env cval φ Δ b c →
      DefEq μ env cval φ Δ a c
  /-- D4: reduction is included — `whnfCore` normalization, `reduceNat`
  acceleration, delta (denotation-invisible), string-literal
  expansion. -/
  | ofRed {Δ : List VExpr} {a a' : VExpr} :
      Red μ env cval φ Δ a a' → DefEq μ env cval φ Δ a a'
  /-- D5: ∀-congruence (`Core.lean:1842-1850`).  The body comparison
  is stated in the left domain's context; the checker opens each body
  with its own annotation, and the bridge absorbs the difference
  through the relation's own equality (design §0 decision 1). -/
  | piCong {Δ : List VExpr} {A₁ A₂ B₁ B₂ : VExpr} :
      DefEq μ env cval φ Δ A₁ A₂ →
      DefEq μ env cval φ (A₁ :: Δ) B₁ B₂ →
      DefEq μ env cval φ Δ (.pi A₁ B₁) (.pi A₂ B₂)
  /-- D6: λ-congruence (`Core.lean:1851-1854`). -/
  | lamCong {Δ : List VExpr} {A₁ A₂ b₁ b₂ : VExpr} :
      DefEq μ env cval φ Δ A₁ A₂ →
      DefEq μ env cval φ (A₁ :: Δ) b₁ b₂ →
      DefEq μ env cval φ Δ (.lam A₁ b₁) (.lam A₂ b₂)
  /-- D7: spine-wise application congruence — both the stuck
  congruence (`Core.lean:1855-1881`) and `defeqSpine`'s same-head
  short-circuit (`Core.lean:1667-1679`), one rule with two bridge
  entry points.  The length side condition is the checker's own guard
  (redundant given `DefEqL`, and carried anyway — transpose the
  statement, not a reading of it). -/
  | appCong {Δ : List VExpr} {h₁ h₂ : VExpr} {as₁ as₂ : List VExpr} :
      as₁.length = as₂.length →
      DefEq μ env cval φ Δ h₁ h₂ →
      DefEqL μ env cval φ Δ as₁ as₂ →
      DefEq μ env cval φ Δ (VExpr.mkAppN h₁ as₁) (VExpr.mkAppN h₂ as₂)
  /-- D8: proof irrelevance, the `Prop` branch (`proofIrrel`,
  `Core.lean:782-792`): both sides' types' sorts are `Prop` (ground
  `0` — `Level.isEquiv uT .zero` is absorbed by the denotation).

  The chained `Infer`s carry a linking `DefEq` (the 2026-08-28
  amendment, T3's finding 3): the checker's second `infer` runs at the
  first's *produced* type, and the bridge's infer-claim is up to
  `DefEq`, so the slack sits between the two premises exactly as in
  repair A. -/
  | irrelProp {Δ : List VExpr} {a b ta ta' sta tb tb' stb : VExpr} :
      Infer μ env cval φ Δ a ta →
      DefEq μ env cval φ Δ ta ta' →
      Infer μ env cval φ Δ ta' sta →
      DefEq μ env cval φ Δ sta (.sort 0) →
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb tb' →
      Infer μ env cval φ Δ tb' stb →
      DefEq μ env cval φ Δ stb (.sort 0) →
      DefEq μ env cval φ Δ a b
  /-- D9: proof irrelevance, the unit branch (`proofIrrel`,
  `Core.lean:775-781`): each side's type whnfs to a pinned unit-like
  family head (`isUnitLikeTy` matches a bare constant, so the reduct
  is a valuation leaf) — no common-type check, exactly as the
  checker. -/
  | irrelUnit {Δ : List VExpr} {a b ta tb : VExpr}
      {c₁ c₂ : Name} {us₁ us₂ : List Level} :
      isUnitLikeTy env (.const c₁ us₁) = true →
      us₁.length = (levelParamsAt env c₁).length →
      isUnitLikeTy env (.const c₂ us₂) = true →
      us₂.length = (levelParamsAt env c₂).length →
      Infer μ env cval φ Δ a ta →
      DefEq μ env cval φ Δ ta
        (cval c₁ (Level.substFn φ (levelParamsAt env c₁) us₁)) →
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb
        (cval c₂ (Level.substFn φ (levelParamsAt env c₂) us₂)) →
      DefEq μ env cval φ Δ a b
  /-- D10: structural eta for a stored eta-capable structure
  (`structEtaCert`/`structEtaCertWith`, `Core.lean:919-992`), premise-
  exact at `--set-model`: **no #137 constructor-telescope premise**.
  The per-field data (projection lookups, denoted telescope types,
  residuals) is quantified function-valued over the field index, one
  fact per `structEtaProjCerts` step (`Core.lean:898-913`).  The
  mirrored direction is D2. -/
  | structEta {Δ : List VExpr} {b tb TFv restT : VExpr}
      {c T : Name} {cvc cvT : ConstantVal} {caps : IndCaps}
      {cnP cnF : Nat} {us us' : List Level} {as ts : List VExpr}
      {cvp : Nat → ConstantVal} {mIp rPp : Nat → Nat}
      {rulesP : Nat → List RecRule} {TPv restP : Nat → VExpr} :
      -- side conditions (`Core.lean:922-947`)
      env.find? c = some (.ctorInfo cvc cnP cnF) →
      as.length = cnP + cnF →
      env.find? T = some (.indInfo cvT caps) →
      caps.eta = true → caps.etaCtor = c →
      caps.etaParams = cnP → caps.etaFields = cnF →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains c = false →
      ts.length = cnP →
      us'.length = cvT.levelParams.length →
      cvc.levelParams = cvT.levelParams →
      (cvT.type.stripPis cnP).isSome = true →
      Level.isEquivList us us' = some true →
      denoteClosed cval env φ
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv →
      VExpr.Closed TFv →
      -- per-field side conditions (`structEtaProjCerts`)
      (∀ j, j < cnF →
        env.find? (projFnName T j)
          = some (.recInfo (cvp j) (mIp j) (rPp j) (rulesP j))) →
      (∀ j, j < cnF → (cvp j).levelParams = cvT.levelParams) →
      (∀ j, j < cnF → ((cvp j).type.stripPis (cnP + 1)).isSome = true) →
      (∀ j, j < cnF →
        denoteClosed cval env φ
          ((cvp j).type.instantiateLevelParams (cvp j).levelParams us')
          = some (TPv j)) →
      (∀ j, j < cnF → VExpr.Closed (TPv j)) →
      -- the stuck side's type, normalized to the family's application
      -- (`DefEq`: type-normalization premise, amendment note)
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb
        (VExpr.mkAppN
          (cval T (Level.substFn φ cvT.levelParams us')) ts) →
      -- the type-former telescope certificate
      Tele μ env cval φ Δ TFv ts restT →
      -- the per-field projection-telescope certificates
      (∀ j, j < cnF →
        Tele μ env cval φ Δ (TPv j) (ts ++ [b]) (restP j)) →
      -- parameters against the type's arguments; fields against the
      -- projections
      DefEqL μ env cval φ Δ (as.take cnP) ts →
      DefEqL μ env cval φ Δ (as.drop cnP)
        (projSpinesV cval T (Level.substFn φ cvT.levelParams us') ts b
          cnF) →
      DefEq μ env cval φ Δ
        (VExpr.mkAppN (cval c (Level.substFn φ cvc.levelParams us)) as) b
  /-- D10 at **tower-backed** slots (task #175 W4c): `structEta`'s
  twin for a family whose projection slots are the direct install's
  native tower entries — the per-field certificates are the entries'
  stored types, and the fabricated projections are `.proj T j b`
  nodes, whose tower reading is `projNV j`. -/
  | structEtaTower {Δ : List VExpr} {b tb TFv restT : VExpr}
      {c T : Name} {cvc cvT : ConstantVal} {caps : IndCaps}
      {cnP cnF : Nat} {us us' : List Level} {as ts : List VExpr}
      {ent : Nat → ProjEntry} {TPv restP : Nat → VExpr} :
      env.find? c = some (.ctorInfo cvc cnP cnF) →
      as.length = cnP + cnF →
      env.find? T = some (.indInfo cvT caps) →
      caps.eta = true → caps.etaCtor = c →
      caps.etaParams = cnP → caps.etaFields = cnF →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains c = false →
      ts.length = cnP →
      us'.length = cvT.levelParams.length →
      cvc.levelParams = cvT.levelParams →
      (cvT.type.stripPis cnP).isSome = true →
      Level.isEquivList us us' = some true →
      denoteClosed cval env φ
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv →
      VExpr.Closed TFv →
      (∀ j, j < cnF →
        env.find? (projFnName T j) = some (.projInfo (ent j))) →
      (∀ j, j < cnF → (ent j).tower = true) →
      (∀ j, j < cnF → (ent j).levelParams = cvT.levelParams) →
      (∀ j, j < cnF → ((ent j).ty.stripPis (cnP + 1)).isSome = true) →
      (∀ j, j < cnF →
        denoteClosed cval env φ
          ((ent j).ty.instantiateLevelParams (ent j).levelParams us')
          = some (TPv j)) →
      (∀ j, j < cnF → VExpr.Closed (TPv j)) →
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb
        (VExpr.mkAppN
          (cval T (Level.substFn φ cvT.levelParams us')) ts) →
      Tele μ env cval φ Δ TFv ts restT →
      (∀ j, j < cnF →
        Tele μ env cval φ Δ (TPv j) (ts ++ [b]) (restP j)) →
      DefEqL μ env cval φ Δ (as.take cnP) ts →
      DefEqL μ env cval φ Δ (as.drop cnP)
        ((List.range cnF).map fun j => projNV j b) →
      DefEq μ env cval φ Δ
        (VExpr.mkAppN (cval c (Level.substFn φ cvc.levelParams us)) as) b
  /-- D11: unit-likeness for a stored unit-like family
  (`structUnitCert`, `Core.lean:998-1020`). -/
  | structUnit {Δ : List VExpr} {a b ta tb TB TFv rest : VExpr}
      {T : Name} {cvT : ConstantVal} {caps : IndCaps}
      {us' : List Level} {ts : List VExpr} :
      env.find? T = some (.indInfo cvT caps) →
      caps.unitlike = true →
      reservedBasisNames.contains T = false →
      ts.length = caps.unitParams →
      us'.length = cvT.levelParams.length →
      (cvT.type.stripPis caps.unitParams).isSome = true →
      denoteClosed cval env φ
        (cvT.type.instantiateLevelParams cvT.levelParams us') = some TFv →
      VExpr.Closed TFv →
      Infer μ env cval φ Δ a ta →
      DefEq μ env cval φ Δ ta
        (VExpr.mkAppN
          (cval T (Level.substFn φ cvT.levelParams us')) ts) →
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb TB →
      DefEq μ env cval φ Δ
        (VExpr.mkAppN
          (cval T (Level.substFn φ cvT.levelParams us')) ts) TB →
      Tele μ env cval φ Δ TFv ts rest →
      DefEq μ env cval φ Δ a b
  /-- D12: pair eta for the pinned basis pair (`pairEtaCert`),
  premise-exact at `--set-model`: **no parameter-telescope premise**
  (#130's `projParamCert` was TT-lane-only; deleted at task #161's
  de-gating round, item A).  The mirrored direction is D2. -/
  | pairEta {Δ : List VExpr} {pα pβ s₁ s₂ b tb A B : VExpr}
      {c c' : Name} {cvm : ConstantVal} {cvi : ConstantVal}
      {caps' : IndCaps} {cvr : ConstantVal} {mI rP : Nat} {rr : RecRule}
      {us us' : List Level} :
      env.find? c = some (.ctorInfo cvm 2 2) →
      env.find? c' = some (.indInfo cvi caps') →
      env.find? (c'.str "rec") = some (.recInfo cvr mI rP [rr]) →
      rr.ctor = c → rr.nfields = 2 → mI = rP →
      reservedBasisNames.contains (c'.str "rec") = true →
      Level.isEquivList us us' = some true →
      us.length = cvm.levelParams.length →
      us'.length = cvi.levelParams.length →
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb
        (.app (.app (cval c' (Level.substFn φ cvi.levelParams us')) A) B) →
      DefEq μ env cval φ Δ pα A →
      DefEq μ env cval φ Δ pβ B →
      DefEq μ env cval φ Δ s₁ (.proj 0 b) →
      DefEq μ env cval φ Δ s₂ (.proj 1 b) →
      DefEq μ env cval φ Δ
        (.app (.app (.app (.app
          (cval c (Level.substFn φ cvm.levelParams us)) pα) pβ) s₁) s₂) b
  /-- D13: one-sided λ eta (`etaCert`, `Core.lean:1026-1039`): the
  stuck side's type whnfs to a ∀ at a matching domain and the λ's body
  is pointwise the application.  The mirrored direction is D2. -/
  | eta {Δ : List VExpr} {A₁ b₁ b tb A₂ B : VExpr} :
      Infer μ env cval φ Δ b tb →
      DefEq μ env cval φ Δ tb (.pi A₂ B) →
      DefEq μ env cval φ Δ A₂ A₁ →
      DefEq μ env cval φ (A₁ :: Δ) b₁ (.app b.lift (.bvar 0)) →
      DefEq μ env cval φ Δ (.lam A₁ b₁) b
  /-- D14: a packed literal against a `succ` application
  (`Core.lean:1807-1818`).  `natLitV (k+1)` *is*
  `.app succV (natLitV k)`, so this is D7 content — named for bridge
  legibility; the other orientation is D2. -/
  | litSuccApp {Δ : List VExpr} {x : VExpr} {k : Nat} :
      natLitSupported env = true →
      DefEq μ env cval φ Δ (natLitV cval φ k) x →
      DefEq μ env cval φ Δ (natLitV cval φ (k + 1))
        (.app (succV cval φ) x)
  /-- D15 (T3's finding 2, 2026-08-27): projection congruence — the
  stuck-comparison block (`Core.lean:1884-1889`) accepts two `.proj`
  nodes on index equality plus scrutinee defeq.  Appended at the end
  of `DefEq`'s own constructor list so the T2 rules keep their
  relative order. -/
  | projCong {Δ : List VExpr} {e₁ e₂ : VExpr} {i : Nat} :
      DefEq μ env cval φ Δ e₁ e₂ →
      DefEq μ env cval φ Δ (.proj i e₁) (.proj i e₂)

/-- **Telescope certification** (design §1.4): `iotaCerts`
(`Core.lean:735-743`) — each spine argument's inferred type is defeq
to the corresponding instantiated domain. -/
inductive Tele (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → VExpr → List VExpr → VExpr → Prop where
  | nil {Δ : List VExpr} {T : VExpr} : Tele μ env cval φ Δ T [] T
  | cons {Δ : List VExpr} {A B a ta rest : VExpr} {as : List VExpr} :
      Infer μ env cval φ Δ a ta →
      DefEq μ env cval φ Δ ta A →
      Tele μ env cval φ Δ (B.inst a) as rest →
      Tele μ env cval φ Δ (.pi A B) (a :: as) rest

/-- **Spine equality** (design §1.4): `defEqList`
(`Core.lean:754-761`) — pairwise definitional equality of two
spines. -/
inductive DefEqL (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) : List VExpr → List VExpr → List VExpr → Prop where
  | nil {Δ : List VExpr} : DefEqL μ env cval φ Δ [] []
  | cons {Δ : List VExpr} {a b : VExpr} {as bs : List VExpr} :
      DefEq μ env cval φ Δ a b →
      DefEqL μ env cval φ Δ as bs →
      DefEqL μ env cval φ Δ (a :: as) (b :: bs)

end

/-- A `DefEqL` derivation relates spines of equal length (the D7 side
condition's supplier at rule-application sites). -/
theorem DefEqL.length_eq {μ : CheckMode} {env : Env} {cval : TConstVal}
    {φ : Name → Nat} {Δ as bs : List VExpr}
    (h : DefEqL μ env cval φ Δ as bs) : as.length = bs.length := by
  -- mutual inductives do not support `induction`; recurse on the list
  induction as generalizing bs with
  | nil => cases h; rfl
  | cons a as ih => cases h with
    | cons _ htail => simpa using ih htail

/-! ## The iterated-projection congruences (task #175 wiring W5)

The tower reading of a `.proj` node is `projNV i`, a chain of pair
projections; `Red.projArg` and `DefEq.projCong` iterate along it. -/

theorem Red.projNV_arg {μ : CheckMode} {env : Env} {cval : TConstVal}
    {φ : Name → Nat} {Δ : List VExpr} :
    ∀ {i : Nat} {e e' : VExpr}, Red μ env cval φ Δ e e' →
      Red μ env cval φ Δ (projNV i e) (projNV i e')
  | 0, _, _, h => Red.projArg h
  | i + 1, e, e', h =>
    Red.projNV_arg (i := i) (e := .proj 1 e) (e' := .proj 1 e')
      (Red.projArg h)

theorem DefEq.projNV_cong {μ : CheckMode} {env : Env} {cval : TConstVal}
    {φ : Name → Nat} {Δ : List VExpr} :
    ∀ {i : Nat} {e₁ e₂ : VExpr}, DefEq μ env cval φ Δ e₁ e₂ →
      DefEq μ env cval φ Δ (projNV i e₁) (projNV i e₂)
  | 0, _, _, h => DefEq.projCong h
  | i + 1, e₁, e₂, h =>
    DefEq.projNV_cong (i := i) (e₁ := .proj 1 e₁) (e₂ := .proj 1 e₂)
      (DefEq.projCong h)

end Setlec.SetR
