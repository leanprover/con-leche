import ConLeche.SetP.Step2.ReadsP
import ConLeche.SetP.Step2.TowerKitP

/-!
# The subject-side totality walk (task #161, ENDGAME A)

`accepted_reads` — the last field of `SemTierInputsP` — discharged:
**whatever `inferTypeCore` accepts, `denoteP` reads.**

The walk is a plain fuel induction over the checker's own clause
structure, and every clause is a *coincidence of guards*: `denoteP`
fails on exactly four things, and at each of them the front door has
already checked the same condition.

| `denoteP` failure | the front door's guard |
| --- | --- |
| a loose `.bvar` | outside the fragment (`.notImplemented`); also excluded by the subject's own `looseBVarsBounded 0` |
| `.const` unfindable / mis-arity | `env.find?` + `us.length = cv.levelParams.length`, the two `throw`s of the `.const` clause |
| a literal without its basis | `natLitSupported` / `strLitSupported`, the literal clauses' guards |
| `.proj i` with `2 ≤ i` | the projection table: a `native` entry is one of the two pinned pair entries, so `i < 2` (`projPinsP`) |

The `.fvar` clause reads **unconditionally** — `denoteP` never looks
at the leaf's stored annotation (this is the asymmetry batch 6's
FINDING recorded from the other side: it is what made *`InferReadsP`*
refutable and what makes *this* statement free of a leaf premise).

## The one clause that is not a guard coincidence: `letE`

`inferBody`'s `letE` clause is ζ — it recurses on
`b.instantiate1 v` — while `denoteP`'s `letE` clause **opens** the
body, `b.instantiate1 (.fvar d ty)`.  The two are not the same
term, so the induction hypothesis lands on the wrong one.
`denoteP_beta` (`Annot/BitInst.lean`) is exactly the bridge, and in
the direction this walk needs: it states the ζ reading as the *opened*
reading mapped through `AVExpr.inst`, so `some` on the left forces
`some` inside the map.  The value's own reading — the `x` that lemma
instantiates at — is the induction hypothesis at `v`, which the same
clause infers.

No environment field is consulted beyond `EnvS`'s `proj_ok`
(syntactic, `V`-free): the walk is a statement about the *checker*,
not about the model, which is why it can be a theorem at
`EnvS2Core` rather than a bundle entry.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory
open ConLeche.Semantics (AVExpr)
open ConLeche (CheckMode Env Expr Name Level inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The three run inversions the walk adds

`Verify/InferLemmas.lean` has the binder, application, `letE` and
projection inversions already; the `.const` one there drops the arity
equation (it is consumed inside its own `split`) and the two literal
clauses have none, because no previous consumer needed the guard.  All
three are one `simp only [inferBody, …]` deep. -/

/-- **The `.const` clause's arity guard, recorded.**
`inferTypeCore_const_inv` returns the stored type; this returns the
equation the clause's second `throw` tests — which is precisely
`denoteP`'s `.const` guard. -/
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
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **The `Nat`-literal clause's guard, recorded** — `denoteP`'s own
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
    · rw [if_neg hg] at h
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
    · rw [if_neg hg] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The walk -/

/-- The walk, with the fuel explicit (the induction's own shape). -/
private theorem acceptedReadsP_aux (m : EnvS2Core V env) (φ : Name → Nat) :
    ∀ (F : Nat) {d : Nat} {e t : Expr},
      inferTypeCore μ env F d e = .ok t →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∃ ea, denoteP m.acval env φ d e = some ea := by
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
    | .sort u => exact ⟨_, denoteP_sort _ _ _⟩
    | .fvar idx ty => exact ⟨_, denoteP_fvar _ _ _ _⟩
    | .const n us =>
      obtain ⟨ci, hf, hlen⟩ := inferTypeCore_const_inv_len h
      exact ⟨_, denoteP_const hf hlen⟩
    | .lit (.natVal k) =>
      exact ⟨_, denoteP_natLit (inferTypeCore_natLit_inv h)⟩
    | .lit (.strVal s) =>
      -- the reading is the (long) pinned character spine; name it by
      -- case analysis rather than transcribing it
      rcases hd : denoteP m.acval env φ d (.lit (.strVal s)) with _ | ea
      · rw [denoteP, if_pos (inferTypeCore_strLit_inv h)] at hd
        exact nomatch hd
      · exact ⟨ea, rfl⟩
    | .app f a =>
      obtain ⟨tf, _, _, _, htf, -, -, ta, hta, -⟩ :=
        ConLeche.inferTypeCore_app_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨fa, hfa⟩ := ih htf hws.1 hb.1 (fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl]))
      obtain ⟨aa, haa⟩ := ih hta hws.2 hb.2 (fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl]))
      exact ⟨_, by rw [denoteP_app, hfa, haa]; rfl⟩
    | .forallE ty body mb =>
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
      exact ⟨_, by rw [denoteP_forallE, hta, hba]; rfl⟩
    | .lam ty body mb =>
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
      exact ⟨_, by rw [denoteP_lam, hta, hba]; rfl⟩
    | .proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, htpe, -, -, hfe, -, -, -, -,
        hsn⟩ := ConLeche.inferTypeCore_proj_inv h
      subst hsn
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded] at hb
      obtain ⟨pa, hpa⟩ := ih htpe hws hb (fun l hl =>
        hL l (by simpa [Expr.fvarLeaves] using hl))
      exact ⟨_, denoteP_proj_tower hfe hpa⟩
    | .letE ty val body =>
      obtain ⟨tty, s, tv, htty, -, htv, -, hbody⟩ :=
        ConLeche.inferTypeCore_letE_inv h
      simp only [Expr.WScoped] at hws
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have hLty : Expr.LeavesBounded ty := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLval : Expr.LeavesBounded val := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      have hLbd : Expr.LeavesBounded body := fun l hl =>
        hL l (by simp [Expr.fvarLeaves, hl])
      obtain ⟨ta, hta⟩ := ih htty hws.1 hb.1.1 hLty
      obtain ⟨va, hva⟩ := ih htv hws.2.1 hb.1.2 hLval
      -- the ζ reduct reads (the clause's own recursion) …
      have hsubred : ∀ l ∈ (body.instantiate1 val).fvarLeaves,
          l ∈ (Expr.letE ty val body).fvarLeaves := by
        intro l hl
        rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
        · simp [Expr.fvarLeaves, h2]
        · simp [Expr.fvarLeaves, h2]
      obtain ⟨za, hza⟩ := ih hbody
        (Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2)
        (Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2)
        (fun l hl => hL l (hsubred l hl))
      -- … and `denoteP_beta` reads it as the *opened* body's reading
      rw [denoteP_beta m.acval_closed (acval_inst_self m)
        (ty := ty) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hva 0] at hza
      rcases hba : denoteP m.acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty)) with _ | ba
      · rw [hba] at hza; exact nomatch hza
      exact ⟨_, by rw [denoteP, hta, hva, hba]; rfl⟩

/-- **`accepted_reads`, discharged** — the statement `SemTierInputsP`
carried as its last field, now a theorem.  Whatever the front door's
inference accepts, the validated-annotation reading reads.  See the
module docstring for the guard table and for the `letE` bridge. -/
theorem acceptedReadsP_of (m : EnvS2Core V env) (φ : Name → Nat)
    {F d : Nat} {e t : Expr}
    (h : inferTypeCore μ env F d e = .ok t)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e) :
    ∃ ea, denoteP m.acval env φ d e = some ea :=
  acceptedReadsP_aux m φ F h hws hb hL

end ConLeche.SetP
