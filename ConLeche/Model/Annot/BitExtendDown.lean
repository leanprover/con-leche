module

public import ConLeche.Model.Annot.BitExtend
public import ConLeche.Verify.ProjSlots
public import ConLeche.Verify.Subst

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
  reads `some` there and `none` at the smaller.  `ConstsBound env₀ e`
  excludes it (the same premise the upward crossing carries), and
  `FindPreserved env₀ env` then makes the two lookups the same entry.
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
  The premise is consequently `LitGuardsMono env env₀` — the SAME
  predicate with the roles exchanged, i.e. the guards DOWNWARD
  (`natLitSupported env = true → natLitSupported env₀ = true`, and
  likewise for strings).  Only that direction is used: at a literal
  supported by `env₀` the arm splits on `env`'s own guard and the
  unsupported branch refutes the hypothesis, so the upward direction
  is never asked for.  The string clause's value additionally mentions
  `levelParamsAt env listNilName`/`listConsName`; `levelParamsAt_congr`
  moves those, off the `env₀`-side support alone.

The induction runs `denoteMeta.induct (env := env₀)` — the SMALLER
environment's case split — because both side conditions (`ConstsBound`
and the untabled-slot condition) are phrased there: the `.const` arms
then match the `ConstsBound` clause node for node, and the `.proj`
arm's `none` case is the one the side condition closes.  The larger
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
whose constants are stored below (`ConstsBound env₀ e`) and whose
`.proj` nodes name only slots the smaller environment tables.

The converse of `denoteMeta_envExtend_mono`; see the module docstring
for why the literal guards are asked DOWNWARD (`LitGuardsMono env
env₀`) and why no `findProj?`-preservation premise appears. -/
theorem denoteMeta_envExtend_down {env₀ env : Env}
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (hF : FindPreserved env₀ env) (hG : LitGuardsMono env env₀) :
    ∀ (d : Nat) (e : Expr), ConstsBound env₀ e →
      (∀ (sn : Name) (i : Nat), env₀.findProj? sn i = none →
        Expr.NoProjAt sn i e) →
      ∀ {ea : AnnotTerm}, denoteMeta acval env φ d e = some ea →
        denoteMeta acval env₀ φ d e = some ea := by
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
    rw [constsBound_const, hf] at hc
    exact nomatch hc
  | case6 d ty body m ihty ihbody =>
    intro hc hnp ea h
    rw [constsBound_forallE] at hc
    have hnp' := fun (sn : Name) (i : Nat) (h0 : env₀.findProj? sn i = none) =>
      Expr.noProjAt_forallE.mp (hnp sn i h0)
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    have hnpb : ∀ (sn : Name) (i : Nat), env₀.findProj? sn i = none →
        Expr.NoProjAt sn i (body.instantiate1 (.fvar d ty)) :=
      fun sn i h0 => Expr.NoProjAt.instantiate1
        (Expr.noProjAt_fvar.mpr (hnp' sn i h0).1) _ _ (hnp' sn i h0).2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv h
    rw [denoteMeta, ihty hc.1 (fun sn i h0 => (hnp' sn i h0).1) hta,
      ihbody hcb hnpb hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro hc hnp ea h
    rw [constsBound_lam] at hc
    have hnp' := fun (sn : Name) (i : Nat) (h0 : env₀.findProj? sn i = none) =>
      Expr.noProjAt_lam.mp (hnp sn i h0)
    have hcb : ConstsBound env₀ (body.instantiate1 (.fvar d ty)) :=
      ConstsBound.instantiate1
        (by rw [constsBound_fvar]; exact hc.1) _ _ hc.2
    have hnpb : ∀ (sn : Name) (i : Nat), env₀.findProj? sn i = none →
        Expr.NoProjAt sn i (body.instantiate1 (.fvar d ty)) :=
      fun sn i h0 => Expr.NoProjAt.instantiate1
        (Expr.noProjAt_fvar.mpr (hnp' sn i h0).1) _ _ (hnp' sn i h0).2
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_lam_inv h
    rw [denoteMeta, ihty hc.1 (fun sn i h0 => (hnp' sn i h0).1) hta,
      ihbody hcb hnpb hba]
    rfl
  | case8 d f a ihf iha =>
    intro hc hnp ea h
    rw [constsBound_app] at hc
    have hnp' := fun (sn : Name) (i : Nat) (h0 : env₀.findProj? sn i = none) =>
      Expr.noProjAt_app.mp (hnp sn i h0)
    obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv h
    rw [denoteMeta, ihf hc.1 (fun sn i h0 => (hnp' sn i h0).1) hfa,
      iha hc.2 (fun sn i h0 => (hnp' sn i h0).2) haa]
    rfl
  | case9 d ty val body =>
    intro _ _ ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro hc hnp ea h
    rw [constsBound_proj] at hc
    have hnp' := fun (sn' : Name) (i' : Nat) (h0 : env₀.findProj? sn' i' = none) =>
      Expr.noProjAt_proj.mp (hnp sn' i' h0)
    cases hfp0 : env₀.findProj? sn i with
    | none =>
      -- the side condition forbids the node whose reading moves
      exact absurd ⟨rfl, rfl⟩ (hnp' sn i hfp0).1
    | some entry =>
      have hfpE : env.findProj? sn i = some entry := hmono sn i entry hfp0
      obtain ⟨ea', hea', hcase⟩ := denoteMeta_proj_inv h
      rcases hcase with ⟨entry', hfp, rfl⟩ | ⟨hnt, hdec⟩
      · rw [hfpE] at hfp
        obtain rfl : entry' = entry := (Option.some.inj hfp).symm
        rw [denoteMeta, ihe hc (fun sn' i' h0 => (hnp' sn' i' h0).2) hea', hfp0]
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
    intro _ _ ea h
    rw [denoteMeta, if_neg (fun hs => hsup (hG.1 hs))] at h
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
    intro _ _ ea h
    rw [denoteMeta, if_neg (fun hs => hsup (hG.2 hs))] at h
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
