module

public import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Rules.Recompose
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Rules.Sound
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Modes
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Semantics.Frame

public section

/-!
# The tiers surface (task #305 closing)

The tiers surface: what the declaration fold and the install rows read
about the checker beyond the four claims — the run-stated readability
facts.  Everything semantic is `Model/Rules/Recompose.lean`'s
`checkSoundAtP5` (re-exported here); what remains is stated over runs
of `inferTypeCore` and cannot be in the rules tier: `InferReads` (the
inferred type reads — derived from the rules tier's existence-form
motive), `SortSemAt`, and `acceptedReads_of` (whatever `inferTypeCore`
accepts, `denote` reads — a fuel induction over the checker's own
clause structure, the subject side, which no derivation supplies
because the motives take the subject's reading as a premise).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level whnf inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

-- The recomposition, re-exported under the names the fold has always
-- used (`Model/Rules/Recompose.lean`): `checkSoundAtP5` is the five
-- claims at every fuel, `checkSoundAt` its four-way projection.
export ConLeche.Model.Rules (checkSoundAtP5 checkSoundAt)

/-! ## The inferred type reads -/

/-- **The infer quarter's totality residue**: an accepted subject's
inferred type reads.  Conditioned exactly as the claims are: the run,
the subject's scoping package, the subject's CONTEXT, and the
subject's own reading.

The context premise is needed: the `.fvar` clause returns the leaf's
stored annotation, which the subject's reading never mentions.  In the
rules tier readability is the motive's existence form, whose premise
IS the context. -/
@[expose] def InferReads {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List Term} {ea : Term},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m φ d Δa e →
    denote m.acval env φ d e = some ea →
    ∃ ta, denote m.acval env φ d t = some ta

/-- **`InferReads`, discharged from the rules tier** (task #305):
the bridge turns the run into a derivation and the infer
motive CONCLUDES the type's reading — the shape `Recompose.lean`'s
fourth case destructures. -/
theorem inferReads_of (hμ : μ.isVerified = true)
    {m : EnvModel V env} (hin : Rules.RulesInputs V m φ) :
    InferReads m μ φ fuel := by
  intro d e t Δa ea hrun hws hb hLb hC hea
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  obtain ⟨-, -, ta, hta, -⟩ :=
    Rules.infer_sound hin (Rules.inferTypeCore_bridge hrun)
      ⟨hws, hb, hLb⟩ hC.toS hea
  exact ⟨ta, hta⟩

/-! ## The derived sort fact -/

/-- **The sort fact, at the induction's own fuel.**  Every use is at
the induction-bounded checker fuel, and `sortSemAt_of_claims`
*derives* the fact from the claims one level down.  The subject's
scoping package is carried so the claims can be applied. -/
@[expose] def SortSemAt {env : Env} (m : EnvModel V env) (μ : CheckMode)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {u : Level} {Δa : List Term}
    {ea : Term},
    CtxOk m φ d Δa e →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    inferTypeCore μ env fuel d e = .ok t →
    whnf μ env fuel d t = .ok (.sort u) →
    denote m.acval env φ d e = some ea →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenoted V ρ ea ∧ interp V ρ ea ∈ˢ (univ (u.eval φ) : V)

/-- **`SortSemAt`'s discharge**: the
sort fact at `fuel` from the claims at `fuel` plus the one totality
factor — infer the type (`hreads` says it reads), grade both readings
(`ihi`), then walk the type to its sort (`ihw`) and the membership
lands in the universe. -/
theorem sortSemAt_of_claims {env : Env} {m : EnvModel V env}
    {fuel : Nat}
    (ihw : WhnfClaim μ m φ fuel) (ihi : InferClaim μ m φ fuel)
    (hreads : InferReads m μ φ fuel) :
    SortSemAt m μ φ fuel := by
  intro d e t u Δa ea hC hws hb hLb hi hw hea
  obtain ⟨ta, hta⟩ :=
    hreads hi hws hb hLb hC hea
  obtain ⟨hokE, hokT, hmem⟩ := ihi hi hws hb hLb hC hea hta
  have hwt : Expr.WScoped d t :=
    inferTypeCore_WScoped m.wf fuel hi hws
  have hbt : t.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hi hws hb hLb
  have hLt : Expr.LeavesBounded t := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel hi hws l hl)
  have hCt : CtxOk m φ d Δa t :=
    hC.of_subset (inferTypeCore_fvarLeaves m.wf fuel hi hws)
  obtain ⟨-, heq⟩ := ihw hw hwt hbt hLt hCt hta (denote_sort _ _ _)
    (fun ρ hρ => (hokT ρ hρ).1)
  intro ρ hρ
  refine ⟨hokE ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  -- "not pt" source (1): the inferred type is a type
  rw [heq ρ hρ (hokT ρ hρ).2.ne_pt, interp_sort] at hm
  exact hm

/-! ## The subject-side totality walk

**Whatever `inferTypeCore` accepts, `denote` reads.**  A plain fuel
induction over the checker's own clause structure, every clause a
*coincidence of guards*: `denote` fails on exactly four things, and
at each of them the front door has already checked the same condition.

| `denote` failure | the front door's guard |
| --- | --- |
| a loose `.bvar` | outside the fragment (`.notImplemented`); also excluded by the subject's own `looseBVarsBounded 0` |
| `.const` unfindable / mis-arity | `env.find?` + `us.length = cv.levelParams.length`, the two `throw`s of the `.const` clause |
| a literal without its basis | `natLitSupported` / `strLitSupported`, the literal clauses' guards |
| `.proj T i` without a table entry | the `.proj` clause throws without an `env.findProj?` entry, and at an entry the reading is the tower (`denote_proj_tower`) |

The `.fvar` clause reads **unconditionally** — `denote` never looks
at the leaf's stored annotation; that asymmetry is what made
`InferReads` refutable without its context premise and what makes
*this* statement free of a leaf premise.

`inferBody`'s `letE` arm is the official `infer_let` (task #342): it
infers the type, the value and the body at the value.  The reading opens
the body at a fresh variable instead; the substitution lemma
(`denote_substFvarAt`) recovers that reading from the body read at
the value.

No environment field is consulted: the walk is a statement about the
*checker*, not about the model, which is why it is a theorem at
`EnvModel` rather than a bundle entry. -/

/-! ### The three run inversions the walk adds

`Verify/InferLemmas.lean` has the binder, application, `letE` and
projection inversions already; the `.const` one
there drops the arity equation (it is consumed inside its own
`split`) and the two literal clauses have none.  All three are one
`simp only [inferBody, …]` deep. -/

/-- **The `.const` clause's arity guard, recorded.**
`inferTypeCore_const_inv` returns the stored type; this returns the
equation the clause's second `throw` tests — which is precisely
`denote`'s `.const` guard. -/
theorem inferTypeCore_const_inv_len {fuel d : Nat}
    {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCore μ env fuel d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      us.length = ci.toConstantVal.levelParams.length := by
  match fuel, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure,
      Bind.bind, Except.bind] at h
    revert h
    cases hf : env.find? n with
    | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | some ci =>
      intro h
      dsimp only at h
      by_cases hlen : us.length = ci.toConstantVal.levelParams.length
      · exact ⟨ci, rfl, hlen⟩
      · rw [ite_eq_right hlen] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The `Nat`-literal clause's guard, recorded** — `denote`'s own
literal guard, verbatim. -/
theorem inferTypeCore_natLit_inv {fuel d k : Nat} {t : Expr}
    (h : inferTypeCore μ env fuel d (.lit (.natVal k)) = .ok t) :
    ConLeche.natLitSupported env = true := by
  match fuel, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure] at h
    by_cases hg : ConLeche.natLitSupported env = true
    · exact hg
    · rw [ite_eq_right hg] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The string-literal clause's guard, recorded.** -/
theorem inferTypeCore_strLit_inv {fuel d : Nat} {s : String} {t : Expr}
    (h : inferTypeCore μ env fuel d (.lit (.strVal s)) = .ok t) :
    ConLeche.strLitSupported env = true := by
  match fuel, h with
  | 0, h => rw [ConLeche.inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [ConLeche.inferTypeCore_succ] at h
    simp only [ConLeche.inferBody, pure, Except.pure] at h
    by_cases hg : ConLeche.strLitSupported env = true
    · exact hg
    · rw [ite_eq_right hg] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The walk -/

/-- The walk, with the fuel explicit (the induction's own shape). -/
private theorem acceptedReads_aux (m : EnvModel V env) (φ : Name → Nat) :
    ∀ (F : Nat) {d : Nat} {e t : Expr},
      inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denote m.acval env φ d e = some ea := by
  intro F
  induction F with
  | zero =>
    intro d e t h _ _ _
    rw [ConLeche.inferTypeCore_zero] at h
    exact nomatch h
  | succ F ih =>
    intro d e t h hws hb hL
    match e with
    | .bvar i =>
      simp only [Expr.looseBVarsBounded] at hb
      exact absurd (of_decide_eq_true hb) (Nat.not_lt_zero i)
    | .sort u => exact ⟨_, denote_sort _ _ _⟩
    | .fvar idx ty => exact ⟨_, denote_fvar _ _ _ _⟩
    | .const n us =>
      obtain ⟨ci, hf, hlen⟩ := inferTypeCore_const_inv_len h
      exact ⟨_, denote_const hf hlen⟩
    | .lit (.natVal k) =>
      exact ⟨_, denote_natLit (inferTypeCore_natLit_inv h)⟩
    | .lit (.strVal s) =>
      -- the reading is the (long) pinned character spine; name it by
      -- case analysis rather than transcribing it
      rcases hd : denote m.acval env φ d (.lit (.strVal s)) with _ | ea
      · rw [denote, ite_eq_left (inferTypeCore_strLit_inv h)] at hd
        exact nomatch hd
      · exact ⟨ea, rfl⟩
    | .app f a =>
      obtain ⟨tf, _, _, htf, -, -, hrest⟩ :=
        ConLeche.inferTypeCore_app_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨fa, hfa⟩ := ih htf hws.1 hb.1 (fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl]))
      obtain ⟨aa, haa⟩ : ∃ aa, denote m.acval env φ d a = some aa := by
        rcases hrest with hsk | ⟨ta, hta, -⟩
        · -- Task #368: the skipped argument is a
          -- stored constant without levels, so it reads
          have hhit := ConLeche.bvUnsatSkip_hit hsk
          unfold ConLeche.bvUnsatHit at hhit
          split at hhit
          · simp only [Bool.and_eq_true] at hhit
            obtain ⟨n, ci, rfl, hci, hlp⟩ := ConLeche.bvUnsatArgOk_const hhit.1.2
            exact ⟨_, denote_const hci (by simp [hlp])⟩
          · exact nomatch hhit
        · exact ih hta hws.2 hb.2 (fun l hl =>
            hL l (by simp [Expr.fvarLeaves, hl]))
      exact ⟨_, by rw [denote_app, hfa, haa]; rfl⟩
    | .forallE ty body =>
      obtain ⟨tty, u, bt, v, htty, -, hbt, -, -, -⟩ :=
        ConLeche.inferTypeCore_forall_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLty : Expr.LeavesBounded ty := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded body := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨hwo, hbo, hLo⟩ :=
        frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
      obtain ⟨ta, hta⟩ := ih htty hws.1 hb.1 hLty
      obtain ⟨ba, hba⟩ := ih hbt hwo hbo hLo
      exact ⟨_, by rw [denote_forallE, hta, hba]; rfl⟩
    | .lam ty body =>
      obtain ⟨tty, u, bt, htty, -, hbt, -, -, -⟩ :=
        ConLeche.inferTypeCore_lam_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLty : Expr.LeavesBounded ty := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded body := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨hwo, hbo, hLo⟩ :=
        frame_open2 hws.1 hb.1 hws.2 hb.2 hLty hLbd
      obtain ⟨ta, hta⟩ := ih htty hws.1 hb.1 hLty
      obtain ⟨ba, hba⟩ := ih hbt hwo hbo hLo
      exact ⟨_, by rw [denote_lam, hta, hba]; rfl⟩
    | .proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, htpe, -, -, hfe, -, -, -, -,
        hsn⟩ := ConLeche.inferTypeCore_proj_inv h
      subst hsn
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded] at hb
      obtain ⟨pa, hpa⟩ := ih htpe hws hb (fun l hl =>
        hL l (by simpa [Expr.fvarLeaves] using hl))
      exact ⟨_, denote_proj_tower hfe hpa⟩
    | .letE ty val body =>
      -- official's `infer_let`: the type, the value and the body at the
      -- value are inferred; the reading opens the body at a fresh
      -- variable, which the substitution lemma recovers from the body
      -- read at the value
      obtain ⟨tty, -, tv, htty, -, htv, -, hbt⟩ := ConLeche.inferTypeCore_letE_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLty : Expr.LeavesBounded ty := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLv : Expr.LeavesBounded val := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded body := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨ta, hta⟩ := ih htty hws.1 hb.1.1 hLty
      obtain ⟨va, hva⟩ := ih htv hws.2.1 hb.1.2 hLv
      have hwi : Expr.WScoped d (body.instantiate1 val) :=
        Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
      have hbi : (body.instantiate1 val).looseBVarsBounded 0 = true :=
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
      have hLi : Expr.LeavesBounded (body.instantiate1 val) := fun l hl => by
        rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
        · exact hLbd l h2
        · exact hLv l h2
      obtain ⟨ia, hia⟩ := ih hbt hwi hbi hLi
      obtain ⟨hwo, -, -⟩ := frame_open2 hws.1 hb.1.1 hws.2.2 hb.2 hLty hLbd
      have hsub := denote_substFvarAt (env := env) (φ := φ) (acval := m.acval)
        m.acval_closed (acval_inst_self m) hws.2.1 hb.1.2 hva
        (body.instantiate1 (.fvar d ty)) d (Nat.le_refl d) hwo.fvarsBelow
      rw [ConLeche.Expr.substFvarAt_instantiate1_self body 0 hws.2.2.fvarsBelow, hia] at hsub
      cases hba : denote m.acval env φ (d + 1) (body.instantiate1 (.fvar d ty)) with
      | none => rw [hba] at hsub; exact nomatch hsub
      | some ba =>
        exact ⟨_, by rw [denote_letE, hta, hva, hba]; rfl⟩

/-- **`accepted_reads`, discharged.**  Whatever the front door's
inference accepts, the stored-term reading `denote` reads.  See the
module docstring for the guard table and for the `letE` clause. -/
theorem acceptedReads_of (m : EnvModel V env) (φ : Name → Nat)
    {F d : Nat} {e t : Expr}
    (h : inferTypeCore μ env F d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) :
    ∃ ea, denote m.acval env φ d e = some ea :=
  acceptedReads_aux m φ F h hws hb hL

end ConLeche.Model
