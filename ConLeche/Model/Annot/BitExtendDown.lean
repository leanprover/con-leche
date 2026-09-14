module

public import ConLeche.Model.Annot.BitExtend
public import ConLeche.Verify.ProjSlots
public import ConLeche.Verify.Subst
import ConLeche.Verify.EnvGuards
import ConLeche.Verify.EnvWF

public section

/-!
# `denoteMeta` DOWN an environment extension (task #306)

Every crossing the tree has — `denoteMeta_envExtend_mono`
(`Annot/BitExtend.lean`), its tower-slot refinement
`denoteMeta_envExtend_mono_at` (`Annot/BitExtendTower.lean`),
`denoteMeta_cons_mono` (`Annot/ConsMono.lean`) — carries a reading
UP a fresh extension.  The nested route's D2 step needs the other
direction: a term read at the scratch environment `envAux` must be
shown to read *the same* at the smaller `env₁` that holds the block's
real formers alone (DESIGN §M.44, "the DOWNWARD reading transfer").

`denoteMeta` is total, so the downward direction is not free: three
clauses read `env` and each of them can differ.

* **`.const`** — a constant stored only at the larger environment
  reads `some` there and `none` at the smaller.  The subject condition
  `e.constsResolve env₀ = true` excludes it, and `FindPreserved env₀
  env` then makes the two lookups the same entry.
* **`.proj sn i`** — the clause's `none` branch is *not* a failure: a
  `.proj` at a slot the environment does not table reads by the pair
  fallback `AnnotTerm.projPair?`.  So a node at a slot `env` tables
  and `env₀` does not reads a DIFFERENT value, not `none`, and no
  environment hypothesis can repair it: the side condition
  `∀ sn i, env₀.findProj? sn i = none → Expr.NoProjAt sn i e` — the
  subject has no `.proj` node at any slot the smaller environment
  lacks — is what the arm needs, and it is exactly the hypothesis
  K.13's `projTablesOk` supplies for the annotated inputs.
  Where `env₀` *does* table the slot, `FindPreserved` transports the
  entry up (`findProj?_of_table`) and the two readings agree.
  The upward premise `hproj` (`env₀.findProj? sn i = none →
  env.findProj? sn i = none`) of `denoteMeta_envExtend_mono` is
  therefore **not** needed here and is not taken: the side condition
  already refutes the only node that could see the difference.
* **the two literal guards** — a support-completing extension flips
  `natLitSupported`/`strLitSupported` upward, and a literal supported
  at `env` but not at `env₀` reads `some` above and `none` below.
  This is **not** repaired by an environment-level premise (task #310):
  `LitGuardsMono env env₀` — the guards DOWNWARD — is refutable for
  the nested route's pair, where a block CONSTRUCTOR can complete the
  string support at the scratch environment and not at the formers'
  (DESIGN §M.49, finding 1).  It is a condition on the SUBJECT, and
  `e.constsResolve env₀ = true` already carries it: the literal
  clauses of `constsResolve` name exactly the support constants
  (`Nat`/`Nat.zero`/`Nat.succ`, plus the seven string names), the
  reading hypothesis at `env` forces `env`'s guard, `FindPreserved`
  identifies the named entries, and `natLitSupported_congr` /
  `strLitSupported_congr` (`Verify/EnvGuards.lean`) then transport the
  guard DOWN.  The string clause's value additionally mentions
  `levelParamsAt env listNilName`/`listConsName`; `levelParamsAt_congr`
  moves those, off the `env₀`-side support alone.

The induction runs `denoteMeta.induct (env := env₀)` — the SMALLER
environment's case split — because both side conditions
(`constsResolve` and the untabled-slot condition) are phrased there:
the `.const` arms then match the `constsResolve` clause node for node,
and the `.proj` arm's `none` case is the one the side condition
closes.  The larger
environment's reading is consumed through the inversion lemmas
(`denoteMeta_forallE_inv` and friends), which are environment-generic.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-- **The downward crossing**: a successful reading at the larger
environment is reproduced verbatim at the smaller one, for a subject
that RESOLVES below (`e.constsResolve env₀ = true` — its constants,
its `.proj` structures and its literals' support constants are all
stored at the smaller environment) and whose `.proj` nodes name only
slots the smaller environment tables.

The converse of `denoteMeta_envExtend_mono`.  Both side conditions are
conditions on the SUBJECT: no environment-level premise appears — not
`findProj?`-preservation (the untabled-slot condition already refutes
the only node that could see the difference) and, since task #310, not
a downward literal-guard monotonicity either (`LitGuardsMono env env₀`
is refutable for the nested route's pair; see the module docstring). -/
theorem denoteMeta_envExtend_down {env₀ env : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) :
    ∀ (d : Nat) (e : Expr), e.constsResolve env₀ = true →
      (∀ (sn : Name) (i : Nat), env₀.findProj? sn i = none →
        (env.findProj? sn i).isSome = true → Expr.NoProjAt sn i e) →
      ∀ {ea : AnnotTerm}, denoteMeta acval env φ d e = some ea →
        denoteMeta acval env₀ φ d e = some ea := by
  -- a name stored below is stored above with the same entry, so the
  -- two lookups at a name the subject resolves are one lookup
  have hfind : ∀ n : Name, (env₀.find? n).isSome = true →
      env₀.find? n = env.find? n := by
    intro n h
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
    rw [hci, hF hci]
  -- a slot tabled below is tabled above, with the same entry
  have hmono : ∀ (sn : Name) (i : Nat) (entry : ConLeche.ProjEntry),
      env₀.findProj? sn i = some entry →
      env.findProj? sn i = some entry := by
    intro sn i entry h
    obtain ⟨tbl, hf0, hi, rfl⟩ := ConLeche.Env.findProj?_some h
    exact ConLeche.Env.findProj?_of_table (hF hf0) hi
  intro d e
  induction d, e using denoteMeta.induct (env := env₀) with
  | case1 d u => intro _ _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case2 d idx ty => intro _ _ ea h; rw [denoteMeta] at h ⊢; exact h
  | case3 d n us ci hf hlen =>
    intro _ _ ea h
    rw [denoteMeta, hF hf] at h
    rw [denoteMeta, hf]
    exact h
  | case4 d n us ci hf hlen =>
    intro _ _ ea h
    rw [denoteMeta, hF hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro hc _ ea h
    simp only [Expr.constsResolve, hf, Option.isSome_none, Bool.false_eq_true] at hc
  | case6 d ty body m ihty ihbody =>
    intro hc hnp ea h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    have hnp' := fun (sn : Name) (i : Nat) (h0 : env₀.findProj? sn i = none)
        (hs : (env.findProj? sn i).isSome = true) =>
      Expr.noProjAt_forallE.mp (hnp sn i h0 hs)
    have hcb : (body.instantiate1 (.fvar d ty)).constsResolve env₀ = true :=
      ConLeche.Expr.constsResolve_instantiate1 hc.1 0 hc.2
    have hnpb : ∀ (sn : Name) (i : Nat), env₀.findProj? sn i = none →
        (env.findProj? sn i).isSome = true →
        Expr.NoProjAt sn i (body.instantiate1 (.fvar d ty)) :=
      fun sn i h0 hs => Expr.NoProjAt.instantiate1
        (Expr.noProjAt_fvar.mpr (hnp' sn i h0 hs).1) _ _ (hnp' sn i h0 hs).2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    rw [denoteMeta, ihty hc.1 (fun sn i h0 hs => (hnp' sn i h0 hs).1) hta,
      ihbody hcb hnpb hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro hc hnp ea h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    have hnp' := fun (sn : Name) (i : Nat) (h0 : env₀.findProj? sn i = none)
        (hs : (env.findProj? sn i).isSome = true) =>
      Expr.noProjAt_lam.mp (hnp sn i h0 hs)
    have hcb : (body.instantiate1 (.fvar d ty)).constsResolve env₀ = true :=
      ConLeche.Expr.constsResolve_instantiate1 hc.1 0 hc.2
    have hnpb : ∀ (sn : Name) (i : Nat), env₀.findProj? sn i = none →
        (env.findProj? sn i).isSome = true →
        Expr.NoProjAt sn i (body.instantiate1 (.fvar d ty)) :=
      fun sn i h0 hs => Expr.NoProjAt.instantiate1
        (Expr.noProjAt_fvar.mpr (hnp' sn i h0 hs).1) _ _ (hnp' sn i h0 hs).2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    rw [denoteMeta, ihty hc.1 (fun sn i h0 hs => (hnp' sn i h0 hs).1) hta,
      ihbody hcb hnpb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc hnp ea h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    have hnp' := fun (sn : Name) (i : Nat) (h0 : env₀.findProj? sn i = none)
        (hs : (env.findProj? sn i).isSome = true) =>
      Expr.noProjAt_app.mp (hnp sn i h0 hs)
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    rw [denoteMeta, ihf hc.1 (fun sn i h0 hs => (hnp' sn i h0 hs).1) hfa,
      iha hc.2 (fun sn i h0 hs => (hnp' sn i h0 hs).2) haa]
    rfl
  | case9 d ty val body =>
    intro _ _ ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hc hnp ea h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    have hnp' := fun (sn' : Name) (i' : Nat) (h0 : env₀.findProj? sn' i' = none)
        (hs : (env.findProj? sn' i').isSome = true) =>
      Expr.noProjAt_proj.mp (hnp sn' i' h0 hs)
    cases hfp0 : env₀.findProj? sn i with
    | none =>
      cases hfpE : env.findProj? sn i with
      | none =>
        -- untabled on both sides: both readings take the pair branch
        obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
        rcases hcase with ⟨entry', hfp, rfl⟩ | ⟨-, hdec⟩
        · rw [hfpE] at hfp; exact nomatch hfp
        · rw [denoteMeta, ihe hc.2 (fun sn' i' h0 hs => (hnp' sn' i' h0 hs).2) hea', hfp0]
          exact hdec
      | some entry =>
        -- the side condition forbids the node whose reading moves
        exact absurd ⟨rfl, rfl⟩ (hnp' sn i hfp0 (by rw [hfpE]; rfl)).1
    | some entry =>
      have hfpE : env.findProj? sn i = some entry := hmono sn i entry hfp0
      obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
      rcases hcase with ⟨entry', hfp, rfl⟩ | ⟨hnt, hdec⟩
      · rw [hfpE] at hfp
        obtain rfl : entry' = entry := (Option.some.inj hfp).symm
        rw [denoteMeta, ihe hc.2 (fun sn' i' h0 hs => (hnp' sn' i' h0 hs).2) hea', hfp0]
        rfl
      · rw [hfpE] at hnt
        exact nomatch hnt
  | case11 d n hsup =>
    intro _ _ ea h
    cases hs : natLitSupported env with
    | true =>
      rw [denoteMeta, if_pos hs] at h
      rw [denoteMeta, if_pos hsup]
      exact h
    | false =>
      rw [denoteMeta, if_neg (by simp [hs])] at h
      exact nomatch h
  | case12 d n hsup =>
    -- the subject's support names are stored below and identified
    -- above, so the guard the reading at `env` forces is `env₀`'s
    intro hc _ ea h
    refine absurd ?_ hsup
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    rw [natLitSupported_congr (hfind _ h1) (hfind _ h2) (hfind _ h3)]
    cases hs : natLitSupported env with
    | true => rfl
    | false =>
      rw [denoteMeta, if_neg (by simp [hs])] at h
      exact nomatch h
  | case13 d s hsup =>
    intro _ _ ea h
    obtain ⟨hnil, hcons⟩ := strLitSupported_listNames hsup
    cases hs : strLitSupported env with
    | true =>
      rw [denoteMeta, if_pos hs] at h
      rw [denoteMeta, if_pos hsup, levelParamsAt_congr hF hnil,
        levelParamsAt_congr hF hcons]
      exact h
    | false =>
      rw [denoteMeta, if_neg (by simp [hs])] at h
      exact nomatch h
  | case14 d s hsup =>
    intro hc _ ea h
    refine absurd ?_ hsup
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
    rw [strLitSupported_congr (hfind _ h1) (hfind _ h2) (hfind _ h3) (hfind _ h4)
      (hfind _ h5) (hfind _ h6) (hfind _ h7) (hfind _ h8) (hfind _ h9) (hfind _ h10)]
    cases hs : strLitSupported env with
    | true => rfl
    | false =>
      rw [denoteMeta, if_neg (by simp [hs])] at h
      exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _ _ ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The literal clauses alone (task #310)

The downward transfer asks the SUBJECT to resolve at the smaller
environment, and a caller that transfers a term *blind to annotations*
(`Expr.blank`, `Model/Inductives/WhnfContentRun.lean`) holds the
`.const` and `.proj` names in the currency of blind mentions
(`Expr.mentionsConstE`) already.  What that currency does NOT carry is
the literal clauses — `constsResolve` minus its `.const` and `.proj`
clauses, and blind to `fvar` annotations exactly as the blank is. -/

/-- The literal-support clauses of `Expr.constsResolve`, blind to
`fvar` annotations: every `Nat` literal outside an annotation has the
`Nat` trio stored, and every `String` literal the seven string names
on top of it. -/
@[expose] def litsResolve (env : Env) : Expr → Bool
  | .bvar _ | .sort _ | .fvar _ _ | .const _ _ => true
  | .lit (.natVal _) =>
    (env.find? ConLeche.natName).isSome && (env.find? ConLeche.natZeroName).isSome &&
      (env.find? ConLeche.natSuccName).isSome
  | .lit (.strVal _) =>
    (env.find? ConLeche.natName).isSome && (env.find? ConLeche.natZeroName).isSome &&
      (env.find? ConLeche.natSuccName).isSome && (env.find? ConLeche.stringName).isSome &&
      (env.find? ConLeche.stringOfListName).isSome && (env.find? ConLeche.listName).isSome &&
      (env.find? ConLeche.listNilName).isSome && (env.find? ConLeche.listConsName).isSome &&
      (env.find? ConLeche.charName).isSome && (env.find? ConLeche.charOfNatName).isSome
  | .app f a => litsResolve env f && litsResolve env a
  | .lam ty body _ | .forallE ty body _ => litsResolve env ty && litsResolve env body
  | .letE ty val body =>
    litsResolve env ty && litsResolve env val && litsResolve env body
  | .proj _ _ e => litsResolve env e

/-- A resolving term resolves its literals (`constsResolve`'s literal
clauses ARE these, and its other clauses only add). -/
theorem litsResolve_of_constsResolve {env : Env} :
    ∀ e : Expr, e.constsResolve env = true → litsResolve env e = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ => rfl
  | .fvar _ _, _ => rfl
  | .lit (.natVal _), h => by simpa [litsResolve, Expr.constsResolve] using h
  | .lit (.strVal _), h => by simpa [litsResolve, Expr.constsResolve] using h
  | .app f a, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_of_constsResolve f h.1, litsResolve_of_constsResolve a h.2⟩
  | .lam ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_of_constsResolve ty h.1, litsResolve_of_constsResolve b h.2⟩
  | .forallE ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_of_constsResolve ty h.1, litsResolve_of_constsResolve b h.2⟩
  | .letE ty v b, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨⟨litsResolve_of_constsResolve ty h.1.1, litsResolve_of_constsResolve v h.1.2⟩,
      litsResolve_of_constsResolve b h.2⟩
  | .proj _ _ e, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve]
    exact litsResolve_of_constsResolve e h.2

/-- The literal clauses survive an instantiation whose value carries
them (the sequenced subjects of the nested route are built this
way). -/
theorem litsResolve_instantiate1 {env : Env} {v : Expr}
    (hv : litsResolve env v = true) :
    ∀ (e : Expr) (k : Nat), litsResolve env e = true →
      litsResolve env (e.instantiate1 v k) = true
  | .bvar i, k, _ => by
    simp only [ConLeche.Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ => rfl
  | .lit _, _, h => h
  | .app f a, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_instantiate1 hv f k h.1, litsResolve_instantiate1 hv a k h.2⟩
  | .lam ty b _, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_instantiate1 hv ty k h.1, litsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .forallE ty b _, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_instantiate1 hv ty k h.1, litsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .letE ty v' b, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨⟨litsResolve_instantiate1 hv ty k h.1.1, litsResolve_instantiate1 hv v' k h.1.2⟩,
      litsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .proj _ _ e, k, h => by
    simp only [litsResolve] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve]
    exact litsResolve_instantiate1 hv e k h

end ConLeche.Model

/-! ## `NoProjAt` through the sequenced instantiations

The side condition is a statement about the SUBJECT, and the lane's
subjects are built by instantiating an opener at a spine.  The single
step (`Expr.NoProjAt.instantiate1`), the application spine
(`Expr.NoProjAt.mkAppN`) and the level pass
(`Expr.NoProjAt.instantiateLevelParams`) are in `Verify/ProjSlots.lean`
and `Verify/Inductives/StructRec.lean`; the sequenced form
(`Expr.instSeq`, `Verify/Subst.lean`) had none. -/

namespace ConLeche.Expr

variable {T : Name} {i : Nat}

/-- Instantiating a whole spine preserves the absence of a slot's
node: every node of the result is a node of the body or of one of the
arguments (`instantiate1`, iterated). -/
theorem NoProjAt.instSeq :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, NoProjAt T i a) → NoProjAt T i e →
        NoProjAt T i (Expr.instSeq args t e)
  | [], _, _, _, he => he
  | a :: as, t, e, has, he =>
    NoProjAt.instSeq as (t - 1)
      (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))
      (NoProjAt.instantiate1 (has a List.mem_cons_self) e t he)

end ConLeche.Expr
