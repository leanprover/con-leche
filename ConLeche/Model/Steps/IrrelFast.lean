module

public import ConLeche.Model.Steps.Irrel
import ConLeche.Model.Steps.IotaRows
import ConLeche.Model.Steps.IotaKit
import ConLeche.Model.IOLicense
import ConLeche.Model.Steps.IotaGate
import ConLeche.Verify.PropRead
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The fast `isProof` "yes" arm: the squash-regime licence (task #168, stage 3)

`propIrrel` (the hoisted `Prop`-branch test) answers `true` without an
inference when **both sides' head-symbol readers say "a proposition at
every valuation"** (`isProofFast`, `ConLeche/Kernel/PropRead.lean`).
This file is the model theorem that licenses it — the io licence's
dual:

* **The squash-regime licence.**  A datum that is always-zero
  (`pw.isProp`, i.e. `pw ≡ .ifAllZero []`) reads at bit `0` at every
  valuation (`pwBit_eq_zero_of_isProp`), so the head's product reading
  is `piR 0 A B` — a truth value — whose inhabitant is `pt`
  (`eq_pt_of_mem_piR_zero`), and every application of `pt` is `pt`
  (`app_pt`, `interp_mkAppN_pt`).  No `WellDenotedV` slot of the subject,
  no domain membership, no graph rigidity: `irrel_fast_lam`,
  `irrel_fast_const_pi`, `irrel_fast_fvar_pi`.
* **The one graph-regime step.**  For a head whose type is a
  type-former application `I b⃗` (`h : a = b`, `trivial : True`), the
  proof's type must land in `univ 0`: `I`'s stored type is a telescope
  `∀ p⃗, Sort u` every binder of which the reader checked to be
  `.never` (`peelNeverPis`), so its reading is a `.pi` chain at nonzero
  bits (`neverChain_of_peel`) and every slot is licensed —
  `io_domain_transfer` recovers each argument's membership from the
  type reading's own hereditary app slot (`spine_mem_univ_of_neverChain`,
  the ι licence's mixed walk with every slot on the licensed side).
  Then `mem_univ_zero` finishes.
* **The fence** is the io licence's (`io_squash_no_transfer`) mirrored:
  at a nonzero bit the product has two distinct members
  (`irrel_fast_fence`), so the licensed fragment is exactly the
  always-zero datum — `alwaysZero_iff_forall_pwBit_eq_zero`.

`prf_of_isProofFast` is the kernel-shaped theorem: a subject the reader
calls a proof interprets to `pt`.  `propIrrelPQ_of_claims` wires it
into the hoist's row beside the slow branch's `prop_side_pt`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Name Level Expr BinderMeta PropWhen ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## 1. The squash-regime facts, V level -/

/-- Every application of `pt` is `pt` (`app_pt`, folded along a spine). -/
theorem foldl_app_pt' {ρ : Nat → V} : ∀ (as : List AnnotTerm),
    as.foldl (fun r a => app r (interp V ρ a)) (pt : V) = pt
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' as

/-- A spine on a `pt`-valued head interprets to `pt`. -/
theorem interp_mkAppN_pt {ρ : Nat → V} {f : AnnotTerm}
    (hf : interp V ρ f = pt) (as : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as) = pt := by
  rw [interp_mkAppN, hf]
  exact foldl_app_pt' as

/-- The kernel's "definitely `Prop`" test on a datum is the ∀-φ uniform
version of the claims' zero side: the bit is `0` at every valuation
(the dual of `pwBit_ne_zero_of_isNever`). -/
theorem pwBit_eq_zero_of_isProp {pw : PropWhen}
    (h : pw.isProp = true) (φ : Name → Nat) : pwBit φ pw = 0 := by
  rw [eq_of_beq h]
  simp [pwBit]

/-- **Exactness**: `pw.isProp` is *the* datum that is zero at every
valuation — `isNever_iff_forall_pwBit_ne_zero`'s mirror. -/
theorem alwaysZero_iff_forall_pwBit_eq_zero {pw : PropWhen} :
    pw.isProp = true ↔ ∀ φ : Name → Nat, pwBit φ pw = 0 := by
  constructor
  · exact pwBit_eq_zero_of_isProp
  · intro h
    cases pw with
    | never => exact absurd (h (fun _ => 0)) (by simp [pwBit])
    | ifAllZero ps =>
      cases ps with
      | nil => rfl
      | cons n ps =>
        have := h (fun _ => 1)
        simp [pwBit] at this

/-- A level whose zero-ness datum is always-zero evaluates to `0`. -/
theorem eval_eq_zero_of_isProp {u : Level}
    (h : (Level.zeronessOf u).isProp = true) (φ : Name → Nat) :
    Level.eval φ u = 0 := by
  have := pwBit_eq_zero_of_isProp h φ
  rw [pwBit_eq_zero_iff, ConLeche.PropWhen.zeronessOf_sound] at this
  exact beq_iff_eq.mp this

/-- **THE FENCE.**  At a nonzero bit the product reading is a graph set
with two distinct members: a `prf` verdict read off a datum that is
not always-zero would equate them.  So the fast "yes" is exactly the
always-zero datum, model-class-wide. -/
theorem irrel_fast_fence :
    ∃ (A : V) (B : V → V) (f g : V),
      f ∈ˢ piR 1 A B ∧ g ∈ˢ piR 1 A B ∧ f ≠ g := by
  refine ⟨truthVal True, fun _ => univZero,
    lamR 1 (truthVal True) (fun _ => truthVal False),
    lamR 1 (truthVal True) (fun _ => truthVal True), ?_, ?_, ?_⟩
  · exact lamR_mem fun _ _ => truthVal_mem_univZero False
  · exact lamR_mem fun _ _ => truthVal_mem_univZero True
  · intro h
    have h1 : app (lamR 1 (truthVal True) (fun _ => (truthVal False : V))) (pt : V)
        = app (lamR 1 (truthVal True) (fun _ => (truthVal True : V))) (pt : V) :=
      congrArg (fun z => app z (pt : V)) h
    rw [app_lamR_pos (by decide) (pt_mem_truthVal trivial),
      app_lamR_pos (by decide) (pt_mem_truthVal trivial)] at h1
    have : (pt : V) ∈ˢ (truthVal False : V) := h1 ▸ pt_mem_truthVal trivial
    exact (mem_truthVal.mp this).1

/-! ## 2. The type former's telescope: a `.pi` chain at nonzero bits -/

/-- The reading's first `n` heads are `.pi` nodes at nonzero regime
bits, and the residual is `.sort u` — the reading of a type former's
stored type `∀ p⃗, Sort u` whose binders the reader checked to be
`.never`. -/
@[expose] def NeverChain : Nat → Nat → AnnotTerm → Prop
  | 0, u, e => e = .sort u
  | n + 1, u, e =>
    match e with
    | .pi _ v _ B => v ≠ 0 ∧ NeverChain n u B
    | _ => False

theorem neverChain_succ_inv {n u : Nat} {e : AnnotTerm}
    (h : NeverChain (n + 1) u e) :
    ∃ w v A B, e = .pi w v A B ∧ v ≠ 0 ∧ NeverChain n u B := by
  match e with
  | .pi w v A B => exact ⟨w, v, A, B, rfl, h.1, h.2⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

/-- Substitution preserves the chain (`inst` maps `.pi` to `.pi` and
`.sort` to itself). -/
theorem NeverChain.inst : ∀ {n u : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    NeverChain n u e → NeverChain n u (e.inst a k) := by
  intro n
  induction n with
  | zero => intro u e a k h; subst h; rfl
  | succ n ih =>
    intro u e a k h
    obtain ⟨w, v, A, B, rfl, hv, hB⟩ := neverChain_succ_inv h
    exact ⟨hv, ih a (k + 1) hB⟩

/-- **A `.never`-peeled telescope reads to a chain**: each binder's bit
is nonzero (`pwBit_ne_zero_of_isNever`), the residual sort evaluates. -/
theorem neverChain_of_peel {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {T : Expr} {u : Level} {ta : AnnotTerm},
      T.peelNeverPis n = some (.sort u) →
      denoteMeta acval env φ d T = some ta →
      NeverChain n (Level.eval φ u) ta := by
  intro n
  induction n with
  | zero =>
    intro d T u ta hp hd
    obtain rfl := Expr.peelNeverPis_zero_inv hp
    rw [denoteMeta] at hd
    exact (Option.some.inj hd).symm
  | succ n ih =>
    intro d T u ta hp hd
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv hp
    obtain ⟨tA, tB, -, htB, rfl⟩ := denoteMeta_forallE_inv hd
    exact ⟨pwBit_ne_zero_of_isNever hnev φ,
      ih (Expr.peelNeverPis_instantiate1 n _ 0 hb) htB⟩

/-- **A type former's application lands in its result universe.**  The
walk along the chain: at every slot the bit is nonzero, so the
argument's membership in the domain is `io_domain_transfer` from the
applied spine's own hereditary app slot — no certificate anywhere. -/
theorem spine_mem_univ_of_neverChain {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {u : Nat},
      NeverChain vs.length u Ta →
      WellDenotedV V ρ Ta → WellDenotedV V ρ (AnnotTerm.mkAppN f vs) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ (univ u : V) := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f u hch _ _ hf
    obtain rfl : Ta = .sort u := hch
    exact hf
  | cons a vs ih =>
    intro Ta f u hch hokT hokS hf
    obtain ⟨w, v, A, B, rfl, hv, hB⟩ := neverChain_succ_inv hch
    have hokApp : WellDenotedV V ρ (.app f a) := wellDenotedV_mkAppN_head vs hokS
    have hoka : WellDenotedV V ρ a :=
      ⟨((WellDenoted_app V ρ f a) ▸ hokApp.1).2.1,
        ((AnnotValid_app V ρ f a) ▸ hokApp.2).2⟩
    have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
      fun y hy =>
        ⟨((WellDenoted_pi V ρ w v A B) ▸ hokT.1).2 y hy,
          ((AnnotValid_pi V ρ w v A B) ▸ hokT.2).2.1 y hy⟩
    have hf' : interp V ρ f
        ∈ˢ piR v (interp V ρ A) (fun x => interp V (cons x ρ) B) := hf
    have hmem : interp V ρ a ∈ˢ interp V ρ A := by
      obtain ⟨v', A', B', hslot, ha, -⟩ :=
        ((WellDenoted_app V ρ f a) ▸ hokApp.1).2.2
      exact io_domain_transfer hv hslot ha hf'
    have hokB' : WellDenotedV V ρ (B.inst a) :=
      (WellDenotedV_inst0 hoka).mpr (hokB _ hmem)
    have hfa : interp V ρ (.app f a) ∈ˢ interp V ρ (B.inst a) := by
      rw [interp_app, interp_inst0]
      exact app_mem_piR_pos hv hf' hmem
    exact ih (NeverChain.inst a 0 hB) hokB' hokS hfa

/-- The reading of a type-former application `T = hd b⃗` lands in
`univ 0` once the head's type reads to a chain of `b⃗`'s length ending
in `Sort 0`, the head inhabits it, and both readings are graded. -/
theorem mem_univ_zero_of_spine {acval : Name → (Name → Nat) → AnnotTerm}
    {ρ : Nat → V} {d : Nat} {T hd : Expr} {Ta fa taH : AnnotTerm}
    (hfn : T.getAppFn = hd)
    (hTa : denoteMeta acval env φ d T = some Ta)
    (hfa : denoteMeta acval env φ d hd = some fa)
    (hchain : NeverChain T.getAppArgs.length 0 taH)
    (hokH : WellDenotedV V ρ taH) (hokT : WellDenotedV V ρ Ta)
    (hmem : interp V ρ fa ∈ˢ interp V ρ taH) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  rw [← ConLeche.Expr.mkAppN_getApp T, hfn] at hTa
  obtain ⟨fa', vs, hfa', hsp, rfl⟩ := denoteMeta_mkAppN_inv hTa
  rw [hfa] at hfa'
  obtain rfl := Option.some.inj hfa'
  rw [hsp.length] at hchain
  exact spine_mem_univ_of_neverChain vs hchain hokH hokT hmem

/-- **A constant-headed type former's application** (`I b⃗`, `I` stored
with type `∀ p⃗, Sort u`, every binder `.never`, `u` zero at the use's
levels) lands in `univ 0`: `ConstType` supplies `I`'s membership in
its instantiated stored type and that type's grading; the chain is
read off the stored syntax at the composed valuation. -/
theorem typeFormer_mem_univ_zero {m : EnvModel V env}
    (hct : ConstType m φ) {ρ : Nat → V} {d : Nat} {T : Expr}
    {I : Name} {us : List Level} {ci : ConstantInfo} {u : Level} {Ta : AnnotTerm}
    (hfn : T.getAppFn = .const I us) (hfI : env.find? I = some ci)
    (hnt : ci.isTowerEntry = false)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hpeel : ci.toConstantVal.type.peelNeverPis T.getAppArgs.length =
      some (.sort u))
    (hz : Level.eval (Level.substFn φ ci.toConstantVal.levelParams us) u = 0)
    (hTa : denoteMeta m.acval env φ d T = some Ta) (hokT : WellDenotedV V ρ Ta) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  obtain ⟨taI, htaI, hokI, hmemI, -, -⟩ := constType_pkg hct hfI hnt hlen
  have htaI' := htaI d
  rw [denotePInstLevels] at htaI'
  have hchain := neverChain_of_peel (env := env) T.getAppArgs.length hpeel htaI'
  rw [hz] at hchain
  exact mem_univ_zero_of_spine hfn hTa (denoteMeta_const hfI hlen) hchain
    (hokI ρ) hokT (hmemI ρ)

/-! ## 3. The kernel-shaped licence -/

/-- A leaf of a spine's head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN : ∀ (as : List Expr) (f : Expr)
    (l : Nat × Expr), l ∈ f.fvarLeaves →
    l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, h => h
  | a :: as, f, l, h =>
    mem_fvarLeaves_mkAppN as (.app f a) l (by simp [Expr.fvarLeaves, h])

/-- A leaf of a term's head is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn' {a hd : Expr} {l : Nat × Expr}
    (h : a.getAppFn = hd) (hl : l ∈ hd.fvarLeaves) : l ∈ a.fvarLeaves := by
  rw [← ConLeche.Expr.mkAppN_getApp a, h]
  exact mem_fvarLeaves_mkAppN _ _ _ hl

/-- The leaf of a term's head fvar is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn {a ty : Expr} {idx : Nat}
    (h : a.getAppFn = .fvar idx ty) : (idx, ty) ∈ a.fvarLeaves :=
  mem_fvarLeaves_of_getAppFn' h (by simp [Expr.fvarLeaves])

/-- The leaves of an fvar's type are leaves of the fvar. -/
theorem mem_fvarLeaves_of_ty {ty : Expr} {idx : Nat}
    {l : Nat × Expr} (h : l ∈ ty.fvarLeaves) :
    l ∈ (Expr.fvar idx ty).fvarLeaves := by
  simp [Expr.fvarLeaves, h]

/-- **A term whose validated data say "proof" is `pt`.**  The
head-symbol case split of `isProofFast`, each case closed by the
squash-regime licence (a ∀-typed head, a λ) or the one graph-regime
step (a type-former-typed head). -/
theorem prf_of_isProofFast {m : EnvModel V env} (hct : ConstType m φ)
    {d : Nat} {a : Expr} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (h : isProofFast env.find? a = true)
    (hCa : CtxOk m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) : interp V ρ aa = (pt : V) := by
  obtain ⟨pw, hpw, hprop⟩ := isProofFast_inv env.find? h
  rcases proofPW_some_inv env.find? hpw with
    ⟨ty, bd, mb, rfl, rfl⟩ | ⟨-, hhead⟩
  · -- a λ: its datum is the body's type's sort, at bit `0`
    obtain ⟨ta, ba, -, -, rfl⟩ := denoteMeta_lam_inv hda
    rw [interp_lam, pwBit_eq_zero_of_isProp hprop, lamR_zero]
  -- an application spine: the head decides
  have hspine := hda
  rw [← ConLeche.Expr.mkAppN_getApp a] at hspine
  obtain ⟨fa, vs, hfa, -, rfl⟩ := denoteMeta_mkAppN_inv hspine
  refine interp_mkAppN_pt ?_ vs
  rcases headProofPW_some_inv env.find? hhead with
    ⟨c, us, ci, hfn, hf, hnt, hlen, pw0, hty, rfl⟩ |
    ⟨idx, ty, hfn, hty⟩ | rfl
  · -- a constant head: the stored type decides
    rw [hfn, denoteMeta_const hf hlen] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨ta, hta, hokT, hmem, hnf, -⟩ := constType_pkg hct hf hnt hlen
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, hT, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idx, ty', u, hfnT, -, -⟩
    · -- ∀-typed: the squash product
      have hta' := hta d
      rw [hT, ConLeche.Expr.instantiateLevelParams] at hta'
      obtain ⟨tA, tB, -, -, rfl⟩ := denoteMeta_forallE_inv hta'
      have hbit : pwBit φ (Level.substPW ci.toConstantVal.levelParams us mb.pw)
          = 0 := pwBit_eq_zero_of_isProp hprop φ
      have hm := hmem ρ
      rw [interp_pi, hbit] at hm
      exact eq_pt_of_mem_piR_zero hm
    · -- `Sort`-typed: never a proof
      exact absurd hprop (by simp)
    · -- a type-former application: the graph-regime step
      have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hfI)
      have hdefU : (Level.zeronessOf u).paramsDefined
          ciI.toConstantVal.levelParams = true := by
        obtain ⟨bs, hbs⟩ := Expr.stripPis_of_peelNeverPis _ hpeel
        have := ConLeche.Expr.allLevelParamsDefined_stripPis_body _ hbs hwf.2.1
        exact ConLeche.Level.zeronessOf_paramsDefined
          (by simpa [ConLeche.Expr.allLevelParamsDefined] using this)
      have hcomp := ConLeche.Level.substPW_comp
        (ks := ci.toConstantVal.levelParams) (us := us) hlenI hdefU
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams
          (us'.map (Level.subst ci.toConstantVal.levelParams us))) u = 0 := by
        have hb := pwBit_eq_zero_of_isProp hprop φ
        rw [hcomp, pwBit_substPW, pwBit_eq_zero_iff,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have hT : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).getAppFn =
          .const I (us'.map (Level.subst ci.toConstantVal.levelParams us)) := by
        rw [ConLeche.Expr.getAppFn_instantiateLevelParams, hfnT]
        rfl
      have hpeel' : ciI.toConstantVal.type.peelNeverPis
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us).getAppArgs.length =
          some (.sort u) := by
        rw [ConLeche.Expr.getAppArgs_instantiateLevelParams, List.length_map]
        exact hpeel
      have huniv := typeFormer_mem_univ_zero hct hT hfI hntI
        (by rw [List.length_map]; exact hlenI) hpeel' hz (hta d) (hokT ρ)
      exact mem_univ_zero huniv (hmem ρ)
    · -- an fvar-headed stored type: stored types are closed
      exact absurd (ConLeche.Expr.hasFvar_of_getAppFn_fvar hfnT)
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams] at hnf; simp [hnf])
  · -- an fvar head: the context supplies the membership
    rw [hfn, denoteMeta_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨-, -, tya, Aa, htya, hAa, heq, hokT⟩ :=
      hCa.2 _ (mem_fvarLeaves_of_getAppFn hfn)
    have hx : interp V ρ (.bvar (d - 1 - idx)) ∈ˢ interp V ρ tya := by
      rw [interp_bvar, heq ρ hρ]
      exact hρ _ _ hAa
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, rfl, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idy, tyy, u, hfnT, hpeel, rfl⟩
    · -- ∀-typed: the squash product
      obtain ⟨tA, tB, -, -, rfl⟩ := denoteMeta_forallE_inv htya
      rw [interp_pi, pwBit_eq_zero_of_isProp hprop] at hx
      exact eq_pt_of_mem_piR_zero hx
    · exact absurd hprop (by simp)
    · -- a constant-headed type former: the graph-regime step
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams us') u
          = 0 := by
        have hb := pwBit_eq_zero_of_isProp hprop φ
        rw [pwBit_substPW, pwBit_eq_zero_iff,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have huniv := typeFormer_mem_univ_zero hct hfnT hfI hntI hlenI hpeel hz
        htya (hokT ρ hρ)
      exact mem_univ_zero huniv hx
    · -- an fvar-headed type former (`h : motive n`): the head's type
      -- is in the context too
      obtain ⟨-, -, tyyA, Ay, htyy, hAy, heqy, hokY⟩ :=
        hCa.2 _ (mem_fvarLeaves_of_getAppFn' hfn
          (mem_fvarLeaves_of_ty (idx := idx)
            (mem_fvarLeaves_of_getAppFn hfnT)))
      have hy : interp V ρ (.bvar (d - 1 - idy)) ∈ˢ interp V ρ tyyA := by
        rw [interp_bvar, heqy ρ hρ]
        exact hρ _ _ hAy
      have hchain := neverChain_of_peel (env := env) (acval := m.acval)
        ty.getAppArgs.length hpeel htyy
      rw [eval_eq_zero_of_isProp hprop φ] at hchain
      have huniv := mem_univ_zero_of_spine hfnT htya (denoteMeta_fvar _ _ _ _)
        hchain (hokY ρ hρ) (hokT ρ hρ) hy
      exact mem_univ_zero huniv hx
  · -- a sort, a ∀, a literal: never a proof
    exact absurd hprop (by simp)

/-! ## 4. The hoist's row, both arms -/

/-- **The hoisted `Prop`-branch row** (task #168, Option U + stage 3):
the hoist runs `propIrrel`, whose `true` verdicts are the fast "yes"
arm (both sides `isProofFast`, licensed by `prf_of_isProofFast`) and
the slow `Prop` branch (`prop_side_pt` twice).  The fast "not a proof"
arm never answers `true`, so it owes nothing here. -/
theorem propIrrelPQ_of_claims {m : EnvModel V env}
    (hct : ConstType m φ)
    (ihis : InferClaimIOS μ m φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (hreads : InferReadsIOS m μ φ fuel) :
    PropIrrelPQ μ m φ fuel := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
    hokA hokB ρ hρ
  rcases ConLeche.propIrrel_inv h with
    ⟨hfa, hfb⟩ |
    ⟨ta, sta, uT, tb, stb, vT, hta, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · rw [prf_of_isProofFast hct hfa hCa hda ρ hρ,
      prf_of_isProofFast hct hfb hCb hdb ρ hρ]
  · rw [prop_side_pt ihis hsss hreads hta hsta hwsta huT hwa hba hLa
        hCa hda hokA ρ hρ,
      prop_side_pt ihis hsss hreads htb hstb hwstb hvT hwb hbb hLb
        hCb hdb hokB ρ hρ]

end ConLeche.Model
