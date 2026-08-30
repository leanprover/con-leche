import Setlec.SetR.Annot.SortCoh.Discharge

/-!
# Run-level sort coherence — the substitution-transport kit, seams and coreLock

Split from `SortCoh.lean` (pure motion; the umbrella
`Setlec.SetR.Annot.SortCoh` re-exports the whole family).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-! ### The substitution-transport kit (core lemmas) -/

/-- Loose-bvar bounds are monotone. -/
theorem looseBVarsBounded_mono : ∀ {e : Expr} {j k : Nat}, j ≤ k →
    e.looseBVarsBounded j = true → e.looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at h ⊢
    omega
  | fvar idx n ty ih => intro j k hjk h; rfl
  | sort u => intro j k hjk h; rfl
  | const n us => intro j k hjk h; rfl
  | app f a ihf iha =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    exact ⟨ihf hjk h.1, iha hjk h.2⟩
  | lam n ty body m iht ihb =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    exact ⟨iht hjk h.1, ihb (Nat.succ_le_succ hjk) h.2⟩
  | forallE n ty body m iht ihb =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    exact ⟨iht hjk h.1, ihb (Nat.succ_le_succ hjk) h.2⟩
  | letE n ty val body iht ihv ihb =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨⟨iht hjk h1, ihv hjk h2⟩, ihb (Nat.succ_le_succ hjk) h3⟩
  | lit l => intro j k hjk h; rfl
  | proj sn i e ih =>
    intro j k hjk h
    simp only [Setlec.Expr.looseBVarsBounded] at h ⊢
    exact ih hjk h

/-- Substitution transports well-scopedness (fvars and their
annotations pass through untouched; the plugged argument brings its
own). -/
theorem wScoped_instantiate1 {d : Nat} {a : Expr}
    (ha : Expr.WScoped d a) :
    ∀ {b : Expr} {k : Nat}, Expr.WScoped d b →
      Expr.WScoped d (b.instantiate1 a k) := by
  intro b
  induction b with
  | bvar i =>
    intro k hb
    simp only [Setlec.Expr.instantiate1]
    by_cases h : i = k
    · rw [if_pos h]; exact ha
    · rw [if_neg h]
      by_cases h2 : i > k <;> simp [h2, Setlec.Expr.WScoped]
  | fvar idx n ty ih => intro k hb; exact hb
  | sort u => intro k hb; exact hb
  | const n us => intro k hb; exact hb
  | app f a' ihf iha' =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨ihf hb.1, iha' hb.2⟩
  | lam n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨iht hb.1, ihb hb.2⟩
  | forallE n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨iht hb.1, ihb hb.2⟩
  | letE n ty val body iht ihv ihb =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ⟨iht hb.1, ihv hb.2.1, ihb hb.2.2⟩
  | lit l => intro k hb; exact hb
  | proj sn i e ih =>
    intro k hb
    simp only [Setlec.Expr.WScoped] at hb
    simp only [Setlec.Expr.instantiate1, Setlec.Expr.WScoped]
    exact ih hb

/-- Substitution of a closed argument transports the bvar bound down
one binder. -/
theorem looseBVarsBounded_instantiate1 {a : Expr}
    (ha : a.looseBVarsBounded 0 = true) :
    ∀ {b : Expr} {k : Nat}, b.looseBVarsBounded (k + 1) = true →
      (b.instantiate1 a k).looseBVarsBounded k = true := by
  intro b
  induction b with
  | bvar i =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at hb
    simp only [Setlec.Expr.instantiate1]
    by_cases h : i = k
    · rw [if_pos h]
      exact looseBVarsBounded_mono (Nat.zero_le k) ha
    · rw [if_neg h]
      have h2 : ¬ i > k := by omega
      rw [if_neg h2]
      simp only [Setlec.Expr.looseBVarsBounded, decide_eq_true_eq]
      omega
  | fvar idx n ty ih => intro k hb; rfl
  | sort u => intro k hb; rfl
  | const n us => intro k hb; rfl
  | app f a' ihf iha' =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, ihf hb.1, iha' hb.2,
      Bool.and_self]
  | lam n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, iht hb.1, ihb hb.2,
      Bool.and_self]
  | forallE n ty body m iht ihb =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, iht hb.1, ihb hb.2,
      Bool.and_self]
  | letE n ty val body iht ihv ihb =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, iht h1, ihv h2, ihb h3,
      Bool.and_self]
  | lit l => intro k hb; rfl
  | proj sn i e ih =>
    intro k hb
    simp only [Setlec.Expr.looseBVarsBounded] at hb
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.looseBVarsBounded, ih hb]

/-- Substitution introduces no fvar leaves beyond the body's and the
argument's. -/
theorem fvarLeaves_instantiate1_mem {a : Expr} :
    ∀ {b : Expr} {k : Nat},
      ∀ l ∈ (b.instantiate1 a k).fvarLeaves,
        l ∈ b.fvarLeaves ∨ l ∈ a.fvarLeaves := by
  intro b
  induction b with
  | bvar i =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1] at hl
    by_cases h : i = k
    · rw [if_pos h] at hl; exact .inr hl
    · rw [if_neg h] at hl
      by_cases h2 : i > k
      · rw [if_pos h2] at hl
        simp [Setlec.Expr.fvarLeaves] at hl
      · rw [if_neg h2] at hl
        simp [Setlec.Expr.fvarLeaves] at hl
  | fvar idx n ty ih => intro k l hl; exact .inl hl
  | sort u => intro k l hl; exact .inl hl
  | const n us => intro k l hl; exact .inl hl
  | app f a' ihf iha' =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases ihf _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inl h'))
      · exact .inr h'
    · rcases iha' _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | lam n ty body m iht ihb =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases iht _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inl h'))
      · exact .inr h'
    · rcases ihb _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | forallE n ty body m iht ihb =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases iht _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inl h'))
      · exact .inr h'
    · rcases ihb _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | letE n ty val body iht ihv ihb =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    rcases List.mem_append.1 hl with h | h
    · rcases List.mem_append.1 h with h2 | h2
      · rcases iht _ h2 with h' | h'
        · exact .inl (List.mem_append.2 (.inl
            (List.mem_append.2 (.inl h'))))
        · exact .inr h'
      · rcases ihv _ h2 with h' | h'
        · exact .inl (List.mem_append.2 (.inl
            (List.mem_append.2 (.inr h'))))
        · exact .inr h'
    · rcases ihb _ h with h' | h'
      · exact .inl (List.mem_append.2 (.inr h'))
      · exact .inr h'
  | lit l' => intro k l hl; exact .inl hl
  | proj sn i e ih =>
    intro k l hl
    simp only [Setlec.Expr.instantiate1,
      Setlec.Expr.fvarLeaves] at hl
    simp only [Setlec.Expr.fvarLeaves]
    exact ih _ hl

/-- `Q` survives a left-side certified β-contraction (the contractum
is not a whnfCore output, so the three step preservers cannot serve;
at `FrameQ` this discharges through the claims' β `Red` step — the
cert premise is exactly the rule's — plus the substitution kit for
the guards). -/
def QPreserveBetaF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {n : Name} {ty b a ta c : Expr}
    {m : Setlec.BinderMeta} {as : List Expr},
    inferTypeCore μ env g d a = .ok ta →
    isDefEqCore μ env g d ta ty = .ok true →
    Q d (Setlec.Expr.mkAppN (.app (.lam n ty b m) a) as) c →
    Q d (Setlec.Expr.mkAppN (b.instantiate1 a) as) c

/-- `Q` survives a left-side zeta-contraction (`ZetaEq.interp_eq` is
the named `FrameQ`-side supplier). -/
def QPreserveZetaF (_env : Env) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d : Nat} {n : Name} {ty v b c : Expr} {as : List Expr},
    Q d (Setlec.Expr.mkAppN (.letE n ty v b) as) c →
    Q d (Setlec.Expr.mkAppN (b.instantiate1 v) as) c

/-- `Q` survives completing the head's whnfCore under a spine (the
carrier's head re-basing steps; at `FrameQ` this discharges through
the claims' core preservation — whnfCore preserves denotation —
spine-composed). -/
def QPreserveHeadF (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {P F c : Expr} {as : List Expr},
    whnfCore μ env g d P = .ok F →
    Q d (Setlec.Expr.mkAppN P as) c →
    Q d (Setlec.Expr.mkAppN F as) c

/-- whnfCore introduces no fvar leaves (the supplier is a Verify-tier
mutual induction over the core family, `StoredWF`-backed: stored
rule/definition values are fvar-free, and every contraction
substitutes existing subterms). -/
def LeavesSubCoreF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {g d : Nat} {e e' : Expr},
    whnfCore μ env g d e = .ok e' →
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves

/-- `LeavesSubCoreF`'s supplier: the Verify-tier mutual fuel
induction (`whnfPres_leaves`), under environment well-formedness. -/
theorem leavesSubCore_of (henv : Setlec.EnvWF env) :
    LeavesSubCoreF μ env :=
  fun h => Setlec.whnfCore_leaves henv _ h

/-- `Q` descends through an app-node pair (the peel's head
recursion; at `FrameQ` the frame is per-side structural — a
defined application has defined parts). -/
def QDescendAppF (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {d : Nat} {P y R z : Expr},
    Q d (.app P y) (.app R z) → Q d P R

/- TOMBSTONE (do not restate): `CoreIdemF` — whnfCore idempotence on
outputs — briefly re-entered the ledger here as the head re-basing's
connecting-run supplier, and was caught at its supplier seal against
the STANDING refutation (`WhnfCoreIdem`, the strLit corner: an
accepted env's `String.ofList` body makes the proj-scrutinee literal
re-expansion a genuine second reduction step).  The consumers ride
the R-a family instead: iota fires and δ-steps force const heads
(`iotaRec_some_head` / `unfoldDefinition_some_head` →
`whnfCore_reidem_const`), β-side heads are λ-values
(`whnfCore_lam_run`), sort stops are values (`whnfCore_sort_run`),
and non-const stuck sides exit dead seams. -/

/-- An iota fire's subject is const-headed. -/
theorem iotaRec_some_head {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e x : Expr}
    (h : Setlec.iotaRec μ r env d e = .ok (some x)) :
    ∃ n us, e.getAppFn = Setlec.Expr.const n us := by
  by_cases hc : ∃ n us, e.getAppFn = Setlec.Expr.const n us
  · exact hc
  · rw [iotaRec_none_of_fn_not_const
        (fun n us hh => hc ⟨n, us, hh⟩)] at h
    exact nomatch h

/-! ### The seam datatype and its app-lift (the coreLock design) -/

/-- **The liftable seams**: the configurations the layer-peeling
lockstep cannot zip through, each convertible by the top-level
caller (which holds the loop runs) and each liftable through an
app-layer because view-heads propagate.  `deadL`/`deadR` carry a
self-sustaining stuck package (run + head-shape data) so the lift
is one derivation step. -/
inductive CoreSeam (μ : CheckMode) (env : Env) (fc d : Nat) :
    Expr → Expr → Prop
  | certHead (F₁ F₂ : Expr) (as bs : List Expr)
      (hba : F₁.looseBVarsBounded 0 = true)
      (hbb : F₂.looseBVarsBounded 0 = true)
      (hc : isDefEqCore μ env fc d F₁ F₂ = .ok true)
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) :
      CoreSeam μ env fc d (Setlec.Expr.mkAppN F₁ as)
        (Setlec.Expr.mkAppN F₂ bs)
  | recHead (n : Name) (cv : Setlec.ConstantVal) (mI rP : Nat)
      (rules : List Setlec.RecRule) (us us' : List Level)
      (as bs : List Expr)
      (hf : env.find? n = some (.recInfo cv mI rP rules))
      (hev : ∀ φ' : Name → Nat,
        us.map (Level.eval φ') = us'.map (Level.eval φ'))
      (hlen : as.length = bs.length)
      (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) :
      CoreSeam μ env fc d (Setlec.Expr.mkAppN (.const n us) as)
        (Setlec.Expr.mkAppN (.const n us') bs)
  | projHead (sn : Name) (i : Nat) (e₁ e₂ : Expr) (as bs : List Expr)
      (he : CertZip μ env fc d e₁ e₂)
      (hlen : as.length = bs.length)
      (hargs : ∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
        CertZip μ env fc d as[j] bs[j]) :
      CoreSeam μ env fc d (Setlec.Expr.mkAppN (.proj sn i e₁) as)
        (Setlec.Expr.mkAppN (.proj sn i e₂) bs)
  | deadL (u v u' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d u = .ok u')
      (hnc : ∀ p q, u'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, u' ≠ .lam n ty body m)
      (hns : ∀ ℓ, u' ≠ .sort ℓ) :
      CoreSeam μ env fc d u v
  | deadR (u v v' : Expr) (b : Nat)
      (hrun : ∀ g, b ≤ g → whnfCore μ env g d v = .ok v')
      (hnc : ∀ p q, v'.getAppFn ≠ .const p q)
      (hnl : ∀ n ty body m, v' ≠ .lam n ty body m)
      (hns : ∀ ℓ, v' ≠ .sort ℓ) :
      CoreSeam μ env fc d u v

/-- One stuck derivation step for the dead seams' lift: an app over
a dead-stuck head is itself dead-stuck. -/
theorem dead_step {μ : CheckMode} {env : Env} {d : Nat}
    {u u' y : Expr} {b : Nat}
    (hrun : ∀ g, b ≤ g → whnfCore μ env g d u = .ok u')
    (hnc : ∀ p q, u'.getAppFn ≠ .const p q)
    (hnl : ∀ n ty body m, u' ≠ .lam n ty body m) :
    ∀ g, b + 1 ≤ g → whnfCore μ env g d (.app u y)
      = .ok (.app u' y) := by
  intro g hg
  cases g with
  | zero => exact absurd hg (by omega)
  | succ g' =>
  rw [show whnfCore μ env (g' + 1) d (.app u y)
      = Setlec.whnfCoreBody μ (Setlec.pureFns μ env g') env d
        (.app u y) from Setlec.whnfCore_succ ..]
  have hiota : Setlec.iotaRec μ (Setlec.pureFns μ env g') env d
      (.app u' y) = .ok none :=
    iotaRec_none_of_fn_not_const
      (by intro p q hh
          exact hnc p q
            ((show (Expr.app u' y).getAppFn = u'.getAppFn
              from rfl) ▸ hh))
  have hu : (Setlec.pureFns μ env g').whnfCore d u = .ok u' :=
    hrun g' (by omega)
  cases u' with
  | lam n ty body m => exact absurd rfl (hnl n ty body m)
  | const p q =>
    exact absurd (show (Expr.const p q).getAppFn = Expr.const p q
      from rfl) (hnc p q)
  | bvar i =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | fvar i n ty =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | sort u₀ =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | forallE n ty body m =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | letE n ty v b' =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | lit l =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | proj sn i e =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl
  | app p q =>
    unfold Setlec.whnfCoreBody
    simp only [Bind.bind, Except.bind]
    rw [hu]
    simp only []
    rw [hiota]
    rfl

/-- **Seams lift through app-layers** (view-heads propagate; the
flatten seams append the argument zip, the dead seams take one
stuck derivation step). -/
theorem coreSeam_lift_app {μ : CheckMode} {env : Env} {fc d : Nat}
    {P₁ P₂ y₁ y₂ : Expr}
    (hz : CertZip μ env fc d y₁ y₂)
    (hs : CoreSeam μ env fc d P₁ P₂) :
    CoreSeam μ env fc d (.app P₁ y₁) (.app P₂ y₂) := by
  cases hs with
  | certHead F₁ F₂ as bs hba hbb hc hlen hargs =>
    rw [show Expr.app (Setlec.Expr.mkAppN F₁ as) y₁
        = Setlec.Expr.mkAppN F₁ (as ++ [y₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN F₂ bs) y₂
        = Setlec.Expr.mkAppN F₂ (bs ++ [y₂]) from
      mkAppN_append_one.symm]
    refine CoreSeam.certHead F₁ F₂ (as ++ [y₁]) (bs ++ [y₂])
      hba hbb hc (by simp [hlen]) ?_
    intro i hi₁ hi₂
    by_cases hlt : i < as.length
    · have hlt₂ : i < bs.length := hlen ▸ hlt
      rw [getElem_append_left' as [y₁] i hlt,
        getElem_append_left' bs [y₂] i hlt₂]
      exact hargs i hlt hlt₂
    · have hi : i = as.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hi₁
        omega
      subst hi
      rw [getElem_append_last as y₁]
      simp only [hlen]
      rw [getElem_append_last bs y₂]
      exact hz
  | recHead n cv mI rP rules us us' as bs hf hev hlen hargs =>
    rw [show Expr.app (Setlec.Expr.mkAppN (.const n us) as) y₁
        = Setlec.Expr.mkAppN (.const n us) (as ++ [y₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN (.const n us') bs) y₂
        = Setlec.Expr.mkAppN (.const n us') (bs ++ [y₂]) from
      mkAppN_append_one.symm]
    refine CoreSeam.recHead n cv mI rP rules us us'
      (as ++ [y₁]) (bs ++ [y₂]) hf hev (by simp [hlen]) ?_
    intro i hi₁ hi₂
    by_cases hlt : i < as.length
    · have hlt₂ : i < bs.length := hlen ▸ hlt
      rw [getElem_append_left' as [y₁] i hlt,
        getElem_append_left' bs [y₂] i hlt₂]
      exact hargs i hlt hlt₂
    · have hi : i = as.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hi₁
        omega
      subst hi
      rw [getElem_append_last as y₁]
      simp only [hlen]
      rw [getElem_append_last bs y₂]
      exact hz
  | projHead sn i e₁ e₂ as bs he hlen hargs =>
    rw [show Expr.app (Setlec.Expr.mkAppN (.proj sn i e₁) as) y₁
        = Setlec.Expr.mkAppN (.proj sn i e₁) (as ++ [y₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN (.proj sn i e₂) bs) y₂
        = Setlec.Expr.mkAppN (.proj sn i e₂) (bs ++ [y₂]) from
      mkAppN_append_one.symm]
    refine CoreSeam.projHead sn i e₁ e₂ (as ++ [y₁]) (bs ++ [y₂])
      he (by simp [hlen]) ?_
    intro j hj₁ hj₂
    by_cases hlt : j < as.length
    · have hlt₂ : j < bs.length := hlen ▸ hlt
      rw [getElem_append_left' as [y₁] j hlt,
        getElem_append_left' bs [y₂] j hlt₂]
      exact hargs j hlt hlt₂
    · have hj : j = as.length := by
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hj₁
        omega
      subst hj
      rw [getElem_append_last as y₁]
      simp only [hlen]
      rw [getElem_append_last bs y₂]
      exact hz
  | deadL u v u' b hrun hnc hnl hns =>
    refine CoreSeam.deadL _ _ (.app u' y₁) (b + 1)
      (dead_step hrun hnc hnl) ?_ ?_ ?_
    · intro p q h
      exact hnc p q
        ((show (Expr.app u' y₁).getAppFn = u'.getAppFn from rfl) ▸ h)
    · intro n ty body m h; exact nomatch h
    · intro ℓ h; exact nomatch h
  | deadR u v v' b hrun hnc hnl hns =>
    refine CoreSeam.deadR _ _ (.app v' y₂) (b + 1)
      (dead_step hrun hnc hnl) ?_ ?_ ?_
    · intro p q h
      exact hnc p q
        ((show (Expr.app v' y₂).getAppFn = v'.getAppFn from rfl) ▸ h)
    · intro n ty body m h; exact nomatch h
    · intro ℓ h; exact nomatch h

/-! ### Spine-fold invariant helpers (the trace-transport kit) -/

/-- Head leaves persist into the spine. -/
theorem mem_fvarLeaves_mkAppN_head {l : Nat × Name × Expr} :
    ∀ {as : List Expr} {F : Expr}, l ∈ F.fvarLeaves →
      l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves := by
  intro as
  induction as with
  | nil => intro F h; exact h
  | cons a as ih =>
    intro F h
    exact ih (F := .app F a)
      (by simp only [Setlec.Expr.fvarLeaves]
          exact List.mem_append.2 (.inl h))

/-- Argument leaves persist into the spine. -/
theorem mem_fvarLeaves_mkAppN_arg {l : Nat × Name × Expr} :
    ∀ {as : List Expr} {F a : Expr}, a ∈ as → l ∈ a.fvarLeaves →
      l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves := by
  intro as
  induction as with
  | nil => intro F a h; exact absurd h List.not_mem_nil
  | cons a' as ih =>
    intro F a h hl
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_fvarLeaves_mkAppN_head (F := .app F a)
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inr hl))
    · exact ih h hl

/-- Spine leaves come from the head or an argument. -/
theorem fvarLeaves_mkAppN_cases {l : Nat × Name × Expr} :
    ∀ {as : List Expr} {F : Expr},
      l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves →
      l ∈ F.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves := by
  intro as
  induction as with
  | nil => intro F h; exact .inl h
  | cons a as ih =>
    intro F h
    rcases ih (F := .app F a) h with h' | ⟨a', ha', hl'⟩
    · simp only [Setlec.Expr.fvarLeaves] at h'
      rcases List.mem_append.1 h' with h'' | h''
      · exact .inl h''
      · exact .inr ⟨a, List.mem_cons_self .., h''⟩
    · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hl'⟩

/-- Build well-scopedness of a spine from its parts. -/
theorem wScoped_mkAppN_build {d : Nat} :
    ∀ {as : List Expr} {F : Expr}, Expr.WScoped d F →
      (∀ a ∈ as, Expr.WScoped d a) →
      Expr.WScoped d (Setlec.Expr.mkAppN F as) := by
  intro as
  induction as with
  | nil => intro F hF _; exact hF
  | cons a as ih =>
    intro F hF hargs
    exact ih (F := .app F a)
      (by simp only [Setlec.Expr.WScoped]
          exact ⟨hF, hargs a (List.mem_cons_self ..)⟩)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-- Decompose well-scopedness of a spine into its parts. -/
theorem wScoped_mkAppN_parts {d : Nat} :
    ∀ {as : List Expr} {F : Expr},
      Expr.WScoped d (Setlec.Expr.mkAppN F as) →
      Expr.WScoped d F ∧ ∀ a ∈ as, Expr.WScoped d a := by
  intro as
  induction as with
  | nil => intro F h; exact ⟨h, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a as ih =>
    intro F h
    obtain ⟨happ, hargs⟩ := ih (F := .app F a) h
    simp only [Setlec.Expr.WScoped] at happ
    refine ⟨happ.1, ?_⟩
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact happ.2
    · exact hargs a' ha'

/-- Build the bvar bound of a spine from its parts. -/
theorem looseBVarsBounded_mkAppN_build {k : Nat} :
    ∀ {as : List Expr} {F : Expr}, F.looseBVarsBounded k = true →
      (∀ a ∈ as, a.looseBVarsBounded k = true) →
      (Setlec.Expr.mkAppN F as).looseBVarsBounded k = true := by
  intro as
  induction as with
  | nil => intro F hF _; exact hF
  | cons a as ih =>
    intro F hF hargs
    exact ih (F := .app F a)
      (by simp only [Setlec.Expr.looseBVarsBounded,
            Bool.and_eq_true]
          exact ⟨hF, hargs a (List.mem_cons_self ..)⟩)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

/-- Decompose the bvar bound of a spine into its parts. -/
theorem looseBVarsBounded_mkAppN_parts {k : Nat} :
    ∀ {as : List Expr} {F : Expr},
      (Setlec.Expr.mkAppN F as).looseBVarsBounded k = true →
      F.looseBVarsBounded k = true ∧
        ∀ a ∈ as, a.looseBVarsBounded k = true := by
  intro as
  induction as with
  | nil => intro F h; exact ⟨h, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a as ih =>
    intro F h
    obtain ⟨happ, hargs⟩ := ih (F := .app F a) h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at happ
    refine ⟨happ.1, ?_⟩
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact happ.2
    · exact hargs a' ha'

/-- A head's leaf subset spreads over the spine. -/
theorem head_leaves_sub {P F : Expr} {as : List Expr}
    (hsub : ∀ l ∈ F.fvarLeaves, l ∈ P.fvarLeaves) :
    ∀ l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN P as).fvarLeaves := by
  intro l hl
  rcases fvarLeaves_mkAppN_cases hl with h | ⟨a', ha', hl'⟩
  · exact mem_fvarLeaves_mkAppN_head (hsub l h)
  · exact mem_fvarLeaves_mkAppN_arg ha' hl'

/-- One β-step's leaf subset (spine form). -/
theorem beta_leaves_sub {n : Name} {ty b a : Expr}
    {m : Setlec.BinderMeta} {as : List Expr} :
    ∀ l ∈ (Setlec.Expr.mkAppN (b.instantiate1 a) as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN (.app (.lam n ty b m) a) as).fvarLeaves
    := by
  intro l hl
  rcases fvarLeaves_mkAppN_cases hl with h | ⟨a', ha', hl'⟩
  · rcases fvarLeaves_instantiate1_mem _ h with h' | h'
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inl (List.mem_append.2
              (.inr h'))))
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inr h'))
  · exact mem_fvarLeaves_mkAppN_arg ha' hl'

/-- One zeta-step's leaf subset (spine form). -/
theorem zeta_leaves_sub {n : Name} {ty v b : Expr} {as : List Expr} :
    ∀ l ∈ (Setlec.Expr.mkAppN (b.instantiate1 v) as).fvarLeaves,
      l ∈ (Setlec.Expr.mkAppN (.letE n ty v b) as).fvarLeaves := by
  intro l hl
  rcases fvarLeaves_mkAppN_cases hl with h | ⟨a', ha', hl'⟩
  · rcases fvarLeaves_instantiate1_mem _ h with h' | h'
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inr h'))
    · exact mem_fvarLeaves_mkAppN_head
        (by simp only [Setlec.Expr.fvarLeaves]
            exact List.mem_append.2 (.inl (List.mem_append.2
              (.inr h'))))
  · exact mem_fvarLeaves_mkAppN_arg ha' hl'

/-- **The reduction trace**: spine-positioned β/zeta chains plus
head-whnf re-basing steps (transitive by construction; the
contraction constructors match the two contraction species' shapes
exactly, the head constructor matches `QPreserveHeadF`'s).  The
head steps are what the peel's ZipPack outcome erases — a refl
bottom swallows arbitrary whnfCore history — so seam subjects
reached past such a bottom need them. -/
inductive Contracts (μ : CheckMode) (env : Env) (d : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : Contracts μ env d e e
  | beta (n : Name) (ty b a ta : Expr) (m : Setlec.BinderMeta)
      (as : List Expr) (g : Nat) {w : Expr}
      (hinf : inferTypeCore μ env g d a = .ok ta)
      (hdq : isDefEqCore μ env g d ta ty = .ok true)
      (hrest : Contracts μ env d
        (Setlec.Expr.mkAppN (b.instantiate1 a) as) w) :
      Contracts μ env d
        (Setlec.Expr.mkAppN (.app (.lam n ty b m) a) as) w
  | zeta (n : Name) (ty v b : Expr) (as : List Expr) {w : Expr}
      (hrest : Contracts μ env d
        (Setlec.Expr.mkAppN (b.instantiate1 v) as) w) :
      Contracts μ env d
        (Setlec.Expr.mkAppN (.letE n ty v b) as) w
  | head (P F : Expr) (as : List Expr) (g : Nat) {w : Expr}
      (hr : whnfCore μ env g d P = .ok F)
      (hrest : Contracts μ env d (Setlec.Expr.mkAppN F as) w) :
      Contracts μ env d (Setlec.Expr.mkAppN P as) w

/-- Q rides the trace. -/
theorem Contracts.q_transport {μ : CheckMode} {env : Env} {d : Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hQB : QPreserveBetaF μ env Q) (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    {u w c : Expr} (h : Contracts μ env d u w) :
    Q d u c → Q d w c := by
  induction h with
  | refl e => exact id
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    exact fun hq => ih (hQB hinf hdq hq)
  | zeta n ty v b as hrest ih =>
    exact fun hq => ih (hQZ hq)
  | head P F as g hr hrest ih =>
    exact fun hq => ih (hQH hr hq)

/-- The trace only shrinks the leaf set. -/
theorem Contracts.leaves_sub {μ : CheckMode} {env : Env} {d : Nat}
    (hLS : LeavesSubCoreF μ env)
    {u w : Expr} (h : Contracts μ env d u w) :
    ∀ l ∈ w.fvarLeaves, l ∈ u.fvarLeaves := by
  induction h with
  | refl e => exact fun l hl => hl
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    exact fun l hl => beta_leaves_sub l (ih l hl)
  | zeta n ty v b as hrest ih =>
    exact fun l hl => zeta_leaves_sub l (ih l hl)
  | head P F as g hr hrest ih =>
    exact fun l hl => head_leaves_sub (hLS hr) l (ih l hl)

/-- `SubjInv` rides the trace (the substitution kit at each step;
self-pairing restricts through the leaf subset). -/
theorem Contracts.subjInv {μ : CheckMode} {env : Env} {d : Nat}
    (hIC : InvPreserveCoreF μ env) (hLS : LeavesSubCoreF μ env)
    {u w : Expr} (h : Contracts μ env d u w)
    (hI : SubjInv d u) : SubjInv d w := by
  induction h with
  | refl e => exact hI
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    refine ih ?_
    obtain ⟨hw, hb, hL, hp⟩ := hI
    obtain ⟨hwapp, hwargs⟩ := wScoped_mkAppN_parts hw
    obtain ⟨hbapp, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
    simp only [Setlec.Expr.WScoped] at hwapp
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hbapp
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wScoped_mkAppN_build
        (wScoped_instantiate1 hwapp.2 hwapp.1.2) hwargs
    · exact looseBVarsBounded_mkAppN_build
        (looseBVarsBounded_instantiate1 hbapp.2 hbapp.1.2) hbargs
    · exact fun l hl => hL l (beta_leaves_sub l hl)
    · intro l hl l' hl' heq
      rw [List.mem_append] at hl hl'
      exact hp l
        (List.mem_append.2 (.inl (beta_leaves_sub l
          (hl.elim id id))))
        l' (List.mem_append.2 (.inl (beta_leaves_sub l'
          (hl'.elim id id)))) heq
  | zeta n ty v b as hrest ih =>
    refine ih ?_
    obtain ⟨hw, hb, hL, hp⟩ := hI
    obtain ⟨hwlet, hwargs⟩ := wScoped_mkAppN_parts hw
    obtain ⟨hblet, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
    simp only [Setlec.Expr.WScoped] at hwlet
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at hblet
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wScoped_mkAppN_build
        (wScoped_instantiate1 hwlet.2.1 hwlet.2.2) hwargs
    · exact looseBVarsBounded_mkAppN_build
        (looseBVarsBounded_instantiate1 hblet.1.2 hblet.2) hbargs
    · exact fun l hl => hL l (zeta_leaves_sub l hl)
    · intro l hl l' hl' heq
      rw [List.mem_append] at hl hl'
      exact hp l
        (List.mem_append.2 (.inl (zeta_leaves_sub l
          (hl.elim id id))))
        l' (List.mem_append.2 (.inl (zeta_leaves_sub l'
          (hl'.elim id id)))) heq
  | head P F as g hr hrest ih =>
    refine ih ?_
    obtain ⟨hw, hb, hL, hp⟩ := hI
    obtain ⟨hwP, hwargs⟩ := wScoped_mkAppN_parts hw
    obtain ⟨hbP, hbargs⟩ := looseBVarsBounded_mkAppN_parts hb
    have hIP : SubjInv d P :=
      ⟨hwP, hbP,
        fun l hl => hL l (mem_fvarLeaves_mkAppN_head hl),
        fun l hl l' hl' heq => hp l
          (List.mem_append.2 (.inl (mem_fvarLeaves_mkAppN_head
            ((List.mem_append.1 hl).elim id id))))
          l' (List.mem_append.2 (.inl (mem_fvarLeaves_mkAppN_head
            ((List.mem_append.1 hl').elim id id)))) heq⟩
    have hIF : SubjInv d F := hIC hr hIP
    have hsub : ∀ l ∈ (Setlec.Expr.mkAppN F as).fvarLeaves,
        l ∈ (Setlec.Expr.mkAppN P as).fvarLeaves :=
      head_leaves_sub (hLS hr)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact wScoped_mkAppN_build hIF.1 hwargs
    · exact looseBVarsBounded_mkAppN_build hIF.2.1 hbargs
    · exact fun l hl => hL l (hsub l hl)
    · intro l hl l' hl' heq
      rw [List.mem_append] at hl hl'
      exact hp l
        (List.mem_append.2 (.inl (hsub l (hl.elim id id))))
        l' (List.mem_append.2 (.inl (hsub l' (hl'.elim id id)))) heq

/-- Cross-pairing rides two traces (through the leaf subsets). -/
theorem Contracts.pairing {μ : CheckMode} {env : Env} {d : Nat}
    (hLS : LeavesSubCoreF μ env) {u v w₁ w₂ : Expr}
    (h₁ : Contracts μ env d u w₁) (h₂ : Contracts μ env d v w₂)
    (hp : PairedLeaves u v) : PairedLeaves w₁ w₂ := by
  intro l hl l' hl' heq
  rw [List.mem_append] at hl hl'
  refine hp l ?_ l' ?_ heq
  · exact List.mem_append.2
      (hl.elim (fun h => .inl (h₁.leaves_sub hLS l h))
        (fun h => .inr (h₂.leaves_sub hLS l h)))
  · exact List.mem_append.2
      (hl'.elim (fun h => .inl (h₁.leaves_sub hLS l' h))
        (fun h => .inr (h₂.leaves_sub hLS l' h)))

/-- Traces lift through app-layers (the contraction site keeps its
spine position under one more argument). -/
theorem Contracts.app_lift {μ : CheckMode} {env : Env} {d : Nat}
    {u w y : Expr} (h : Contracts μ env d u w) :
    Contracts μ env d (.app u y) (.app w y) := by
  induction h with
  | refl e => exact .refl _
  | beta n ty b a ta m as g hinf hdq hrest ih =>
    rw [show Expr.app (Setlec.Expr.mkAppN
        (.app (.lam n ty b m) a) as) y
      = Setlec.Expr.mkAppN (.app (.lam n ty b m) a) (as ++ [y])
      from mkAppN_append_one.symm]
    refine Contracts.beta n ty b a ta m (as ++ [y]) g hinf hdq ?_
    rw [show Setlec.Expr.mkAppN (b.instantiate1 a) (as ++ [y])
      = Expr.app (Setlec.Expr.mkAppN (b.instantiate1 a) as) y
      from mkAppN_append_one]
    exact ih
  | zeta n ty v b as hrest ih =>
    rw [show Expr.app (Setlec.Expr.mkAppN (.letE n ty v b) as) y
      = Setlec.Expr.mkAppN (.letE n ty v b) (as ++ [y])
      from mkAppN_append_one.symm]
    refine Contracts.zeta n ty v b (as ++ [y]) ?_
    rw [show Setlec.Expr.mkAppN (b.instantiate1 v) (as ++ [y])
      = Expr.app (Setlec.Expr.mkAppN (b.instantiate1 v) as) y
      from mkAppN_append_one]
    exact ih
  | head P F as g hr hrest ih =>
    rw [show Expr.app (Setlec.Expr.mkAppN P as) y
      = Setlec.Expr.mkAppN P (as ++ [y]) from mkAppN_append_one.symm]
    refine Contracts.head P F (as ++ [y]) g hr ?_
    rw [show Setlec.Expr.mkAppN F (as ++ [y])
      = Expr.app (Setlec.Expr.mkAppN F as) y from mkAppN_append_one]
    exact ih

/-! ### The coreLock helper tier -/

/-- whnfCore is the identity on non-redex shapes. -/
theorem whnfCore_inert {μ : CheckMode} {env : Env} {g d : Nat}
    {e e' : Expr}
    (hna : ∀ f a, e ≠ .app f a)
    (hnl : ∀ n ty v b, e ≠ .letE n ty v b)
    (hnp : ∀ sn i s, e ≠ .proj sn i s)
    (h : whnfCore μ env g d e = .ok e') : e' = e := by
  cases g with
  | zero => rw [Setlec.whnfCore_zero] at h; exact nomatch h
  | succ g' =>
    rw [Setlec.whnfCore_succ] at h
    unfold Setlec.whnfCoreBody at h
    cases e with
    | app f a => exact absurd rfl (hna f a)
    | letE n ty v b => exact absurd rfl (hnl n ty v b)
    | proj sn i s => exact absurd rfl (hnp sn i s)
    | bvar i => simp only [] at h; exact nomatch h
    | fvar i n ty => simp only [] at h; exact (Except.ok.inj h).symm
    | sort u0 => simp only [] at h; exact (Except.ok.inj h).symm
    | const n us => simp only [] at h; exact (Except.ok.inj h).symm
    | lam n ty b m => simp only [] at h; exact (Except.ok.inj h).symm
    | forallE n ty b m =>
      simp only [] at h; exact (Except.ok.inj h).symm
    | lit l => simp only [] at h; exact (Except.ok.inj h).symm

/-- Pairing restricts along leaf subsets on both slots. -/
theorem pairedLeaves_mono {a b a' b' : Expr}
    (hsa : ∀ l ∈ a'.fvarLeaves, l ∈ a.fvarLeaves)
    (hsb : ∀ l ∈ b'.fvarLeaves, l ∈ b.fvarLeaves)
    (hp : PairedLeaves a b) : PairedLeaves a' b' := by
  intro l hl l' hl' heq
  rw [List.mem_append] at hl hl'
  exact hp l (List.mem_append.2 (hl.imp (hsa l) (hsb l)))
    l' (List.mem_append.2 (hl'.imp (hsa l') (hsb l'))) heq

/-- A function-position leaf is an app leaf. -/
theorem mem_fvarLeaves_app_left {f a : Expr} :
    ∀ l ∈ f.fvarLeaves, l ∈ (Expr.app f a).fvarLeaves := by
  intro l hl
  simp only [Setlec.Expr.fvarLeaves]
  exact List.mem_append.2 (.inl hl)

/-- An argument-position leaf is an app leaf. -/
theorem mem_fvarLeaves_app_right {f a : Expr} :
    ∀ l ∈ a.fvarLeaves, l ∈ (Expr.app f a).fvarLeaves := by
  intro l hl
  simp only [Setlec.Expr.fvarLeaves]
  exact List.mem_append.2 (.inr hl)

/-- The subject package descends through an app node. -/
theorem subjInv_app {d : Nat} {f a : Expr}
    (h : SubjInv d (.app f a)) : SubjInv d f ∧ SubjInv d a := by
  obtain ⟨hw, hb, hL, hp⟩ := h
  simp only [Setlec.Expr.WScoped] at hw
  simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (mem_fvarLeaves_app_left l hl),
      pairedLeaves_mono mem_fvarLeaves_app_left
        mem_fvarLeaves_app_left hp⟩,
    ⟨hw.2, hb.2, fun l hl => hL l (mem_fvarLeaves_app_right l hl),
      pairedLeaves_mono mem_fvarLeaves_app_right
        mem_fvarLeaves_app_right hp⟩⟩

/-- Pairwise argument zips extend by one (the flatten seams' append
step, extracted). -/
theorem zip_args_append {μ : CheckMode} {env : Env} {fc d : Nat}
    {as bs : List Expr} {y₁ y₂ : Expr}
    (hlen : as.length = bs.length)
    (hargs : ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i])
    (hy : CertZip μ env fc d y₁ y₂) :
    ∀ i (h₁ : i < (as ++ [y₁]).length) (h₂ : i < (bs ++ [y₂]).length),
      CertZip μ env fc d (as ++ [y₁])[i] (bs ++ [y₂])[i] := by
  intro i hi₁ hi₂
  by_cases hlt : i < as.length
  · have hlt₂ : i < bs.length := hlen ▸ hlt
    rw [getElem_append_left' as [y₁] i hlt,
      getElem_append_left' bs [y₂] i hlt₂]
    exact hargs i hlt hlt₂
  · have hi : i = as.length := by
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hi₁
      omega
    subst hi
    rw [getElem_append_last as y₁]
    simp only [hlen]
    rw [getElem_append_last bs y₂]
    exact hy

/-- A non-app expression is its own spine head. -/
theorem getAppFn_of_not_app {e : Expr}
    (h : ∀ p q, e ≠ .app p q) : e.getAppFn = e := by
  cases e with
  | app p q => exact absurd rfl (h p q)
  | bvar i => rfl
  | fvar i n ty => rfl
  | sort u0 => rfl
  | const n us => rfl
  | lam n ty b m => rfl
  | forallE n ty b m => rfl
  | letE n ty v b => rfl
  | lit l => rfl
  | proj sn i s => rfl

/-- A recorded iota fire under a non-recursor const head is
absurd. -/
theorem absurd_rec_fire {μ : CheckMode} {env : Env}
    {d g₁' g₂' : Nat} {S₁ S₂ : Expr} {n : Name}
    {us us' : List Level} {C : Prop}
    (hfn₁ : S₁.getAppFn = .const n us)
    (hfn₂ : S₂.getAppFn = .const n us')
    (hsome :
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₁') env d S₁
        = .ok (some e'')) ∨
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₂') env d S₂
        = .ok (some e'')))
    (hnr : ∀ cv mI rP rules,
      env.find? n ≠ some (.recInfo cv mI rP rules)) : C := by
  exfalso
  rcases hsome with ⟨e'', hio⟩ | ⟨e'', hio⟩
  · rw [iotaRec_none_of_not_rec hfn₁ hnr] at hio
    exact nomatch hio
  · rw [iotaRec_none_of_not_rec hfn₂ hnr] at hio
    exact nomatch hio

/-- **The stuck-spine exit**: a zipped app-pair on which some side's
iota fires exits as a flatten seam — the spine view walks to the
first cert layer (`certHead`) or a shared-name const head
(`recHead` under `recInfo`), and every other head shape refutes
the fire.  Fire-agnostic on the other side (mixed fire is the
top's `ZipIotaCase` business). -/
theorem zip_stuck_spine_exit {μ : CheckMode} {env : Env}
    {fc d g₁' g₂' : Nat} {F₁ F₂ a₁ a₂ : Expr}
    (hzF : CertZip μ env fc d F₁ F₂)
    (hza : CertZip μ env fc d a₁ a₂)
    (hsome :
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₁') env d
        (.app F₁ a₁) = .ok (some e'')) ∨
      (∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g₂') env d
        (.app F₂ a₂) = .ok (some e''))) :
    CoreSeam μ env fc d (.app F₁ a₁) (.app F₂ a₂) := by
  obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlen, hargs, hhead⟩ :=
    certZip_app_view hzF
  rcases hhead with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
  · rw [show Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁
        = Setlec.Expr.mkAppN H₁ (cs ++ [a₁]) from
      mkAppN_append_one.symm,
      show Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂
        = Setlec.Expr.mkAppN H₂ (ds ++ [a₂]) from
      mkAppN_append_one.symm]
    exact CoreSeam.certHead H₁ H₂ (cs ++ [a₁]) (ds ++ [a₂])
      hba hbb hc (by simp [hlen]) (zip_args_append hlen hargs hza)
  · have hfn₁ : (Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁).getAppFn
        = H₁ := by
      rw [show (Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁).getAppFn
          = (Setlec.Expr.mkAppN H₁ cs).getAppFn from rfl,
        Setlec.Expr.getAppFn_mkAppN cs H₁,
        getAppFn_of_not_app hne₁]
    have hfn₂ : (Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂).getAppFn
        = H₂ := by
      rw [show (Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂).getAppFn
          = (Setlec.Expr.mkAppN H₂ ds).getAppFn from rfl,
        Setlec.Expr.getAppFn_mkAppN ds H₂,
        getAppFn_of_not_app hne₂]
    have hcontra : (∀ p q, H₁ ≠ Expr.const p q) →
        (∀ p q, H₂ ≠ Expr.const p q) → False := by
      intro hnc₁ hnc₂
      rcases hsome with ⟨e'', hio⟩ | ⟨e'', hio⟩
      · rw [iotaRec_none_of_fn_not_const
            (fun n us h => hnc₁ n us (hfn₁.symm.trans h))] at hio
        exact nomatch hio
      · rw [iotaRec_none_of_fn_not_const
            (fun n us h => hnc₂ n us (hfn₂.symm.trans h))] at hio
        exact nomatch hio
    have recExit : ∀ {n : Name} {us us' : List Level},
        H₁ = .const n us → H₂ = .const n us' →
        (∀ φ' : Name → Nat,
          us.map (Level.eval φ') = us'.map (Level.eval φ')) →
        CoreSeam μ env fc d
          (.app (Setlec.Expr.mkAppN H₁ cs) a₁)
          (.app (Setlec.Expr.mkAppN H₂ ds) a₂) := by
      intro n us us' he₁ he₂ hev
      subst he₁; subst he₂
      cases hf : env.find? n with
      | some ci =>
        cases ci with
        | recInfo cv mI rP rules =>
          rw [show Expr.app
                (Setlec.Expr.mkAppN (Expr.const n us) cs) a₁
              = Setlec.Expr.mkAppN (Expr.const n us) (cs ++ [a₁])
              from mkAppN_append_one.symm,
            show Expr.app
                (Setlec.Expr.mkAppN (Expr.const n us') ds) a₂
              = Setlec.Expr.mkAppN (Expr.const n us') (ds ++ [a₂])
              from mkAppN_append_one.symm]
          exact CoreSeam.recHead n cv mI rP rules us us'
            (cs ++ [a₁]) (ds ++ [a₂]) hf hev (by simp [hlen])
            (zip_args_append hlen hargs hza)
        | defnInfo cv val hints =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | thmInfo cv val =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | axiomInfo cv =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | indInfo cv caps =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | ctorInfo cv x y =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
        | projInfo entry =>
          exact absurd_rec_fire hfn₁ hfn₂ hsome
            (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
      | none =>
        exact absurd_rec_fire hfn₁ hfn₂ hsome
          (fun cv' mI rP rules h => by rw [hf] at h; exact nomatch h)
    cases hzH with
    | refl _ =>
      cases H₁ with
      | const n us => exact recExit rfl rfl (fun φ' => rfl)
      | app p q => exact absurd rfl (hne₁ p q)
      | bvar i =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | fvar i n ty =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | sort u0 =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | lam n ty b m =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | forallE n ty b m =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | letE n ty v b =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | lit l =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
      | proj sn i s =>
        exact (hcontra (fun p q hh => nomatch hh)
          (fun p q hh => nomatch hh)).elim
    | cert _ _ hba hbb hc =>
      rw [show Expr.app (Setlec.Expr.mkAppN H₁ cs) a₁
          = Setlec.Expr.mkAppN H₁ (cs ++ [a₁]) from
        mkAppN_append_one.symm,
        show Expr.app (Setlec.Expr.mkAppN H₂ ds) a₂
          = Setlec.Expr.mkAppN H₂ (ds ++ [a₂]) from
        mkAppN_append_one.symm]
      exact CoreSeam.certHead H₁ H₂ (cs ++ [a₁]) (ds ++ [a₂])
        hba hbb hc (by simp [hlen]) (zip_args_append hlen hargs hza)
    | constSlack n us us' hev => exact recExit rfl rfl hev
    | sortSlack u0 v0 hev =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | fvar i n ty₁ ty₂ hty =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | app p₁ q₁ p₂ q₂ hp hq => exact absurd rfl (hne₁ p₁ q₁)
    | lam n ty₁ ty₂ b₁ b₂ m hty hb =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | forallE n ty₁ ty₂ b₁ b₂ m hty hb =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hv hb =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim
    | proj s i e₁ e₂ he =>
      exact (hcontra (fun p q hh => nomatch hh)
        (fun p q hh => nomatch hh)).elim

/-- **The layer-peeling lockstep** (the ratified carrier): a zipped
pair's whnfCore runs either land zipped — the invariants free from
the landed preservers, since outputs are whnfCore outputs — or
exit at a liftable seam re-based by connecting runs and reduction
traces, so the top-level caller can loop-align.  Strong induction
on the pair's core-run fuel sum; subjects peeled one app-layer at
a time, never reassociated. -/
theorem coreLock {μ : CheckMode} {env : Env}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q) :
    ∀ (N : Nat) {g₁ g₂ fc d : Nat} {u v u' v' : Expr},
      g₁ + g₂ ≤ N →
      CertZip μ env fc d u v →
      SubjInv d u → SubjInv d v →
      PairedLeaves u v → Q d u v →
      whnfCore μ env g₁ d u = .ok u' →
      whnfCore μ env g₂ d v = .ok v' →
      (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧ SubjInv d v' ∧
        PairedLeaves u' v' ∧ Q d u' v') ∨
      (∃ w₁ w₂ c₁ c₂, c₁ ≤ g₁ ∧ c₂ ≤ g₂ ∧
        whnfCore μ env c₁ d w₁ = .ok u' ∧
        whnfCore μ env c₂ d w₂ = .ok v' ∧
        Contracts μ env d u w₁ ∧ Contracts μ env d v w₂ ∧
        CoreSeam μ env fc d w₁ w₂) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IH =>
  intro g₁ g₂ fc d u v u' v' hN hz hIu hIv hP hQ h₁ h₂
  have hIu' : SubjInv d u' := hIC h₁ hIu
  have hIv' : SubjInv d v' := hIC h₂ hIv
  have hP' : PairedLeaves u' v' := ((hLC h₂ (hLC h₁ hP).symm)).symm
  have hQ' : Q d u' v' := hQs (hQC h₂ (hQs (hQC h₁ hQ)))
  cases hz with
  | refl _ =>
    have hdet : u' = v' := by
      have ha := hm.2.2.1 (Nat.le_max_left g₁ g₂) h₁
      have hb := hm.2.2.1 (Nat.le_max_right g₁ g₂) h₂
      rw [ha] at hb
      exact Except.ok.inj hb
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hdet]
    exact .refl v'
  | cert _ _ hba hbb hc =>
    exact .inr ⟨u, v, g₁, g₂, Nat.le_refl _, Nat.le_refl _,
      h₁, h₂, .refl u, .refl v,
      CoreSeam.certHead u v [] [] hba hbb hc rfl
        (fun i hi _ => absurd hi (Nat.not_lt_zero i))⟩
  | sortSlack u₀ v₀ hev =>
    have hu : u' = .sort u₀ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .sort v₀ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .sortSlack u₀ v₀ hev
  | constSlack n us us' hev =>
    have hu : u' = .const n us := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .const n us' := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .constSlack n us us' hev
  | fvar i n ty₁ ty₂ hty =>
    have hu : u' = .fvar i n ty₁ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .fvar i n ty₂ := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .fvar i n ty₁ ty₂ hty
  | lam n ty₁ ty₂ b₁ b₂ m hty hbody =>
    have hu : u' = .lam n ty₁ b₁ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .lam n ty₂ b₂ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .lam n ty₁ ty₂ b₁ b₂ m hty hbody
  | forallE n ty₁ ty₂ b₁ b₂ m hty hbody =>
    have hu : u' = .forallE n ty₁ b₁ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₁
    have hv : v' = .forallE n ty₂ b₂ m := whnfCore_inert
      (fun _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) h₂
    refine .inl ⟨?_, hIu', hIv', hP', hQ'⟩
    rw [hu, hv]
    exact .forallE n ty₁ ty₂ b₁ b₂ m hty hbody
  | proj s i e₁ e₂ he =>
    exact .inr ⟨.proj s i e₁, .proj s i e₂, g₁, g₂,
      Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
      CoreSeam.projHead s i e₁ e₂ [] [] he rfl
        (fun j hj _ => absurd hj (Nat.not_lt_zero j))⟩
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody =>
    cases g₁ with
    | zero => rw [Setlec.whnfCore_zero] at h₁; exact nomatch h₁
    | succ gp =>
    cases g₂ with
    | zero => rw [Setlec.whnfCore_zero] at h₂; exact nomatch h₂
    | succ gr =>
    rw [whnfCore_letE_step] at h₁ h₂
    have tr₁ : Contracts μ env d (.letE n ty₁ v₁ b₁)
        (b₁.instantiate1 v₁) :=
      Contracts.zeta n ty₁ v₁ b₁ [] (.refl _)
    have tr₂ : Contracts μ env d (.letE n ty₂ v₂ b₂)
        (b₂.instantiate1 v₂) :=
      Contracts.zeta n ty₂ v₂ b₂ [] (.refl _)
    have hzc : CertZip μ env fc d (b₁.instantiate1 v₁)
        (b₂.instantiate1 v₂) := certZip_subst hval hbody 0
    have hIc₁ : SubjInv d (b₁.instantiate1 v₁) :=
      tr₁.subjInv hIC hLS hIu
    have hIc₂ : SubjInv d (b₂.instantiate1 v₂) :=
      tr₂.subjInv hIC hLS hIv
    have hPc : PairedLeaves (b₁.instantiate1 v₁)
        (b₂.instantiate1 v₂) := Contracts.pairing hLS tr₁ tr₂ hP
    have hQc : Q d (b₁.instantiate1 v₁) (b₂.instantiate1 v₂) :=
      hQs (tr₂.q_transport hQB hQZ hQH
        (hQs (tr₁.q_transport hQB hQZ hQH hQ)))
    rcases IH (gp + gr) (by omega) (Nat.le_refl _) hzc hIc₁ hIc₂
        hPc hQc h₁ h₂ with hpack |
      ⟨w₁, w₂, c₁, c₂, hb₁, hb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
    · exact .inl ⟨hpack.1, hIu', hIv', hP', hQ'⟩
    · exact .inr ⟨w₁, w₂, c₁, c₂, Nat.le_succ_of_le hb₁,
        Nat.le_succ_of_le hb₂, hr₁, hr₂,
        Contracts.zeta n ty₁ v₁ b₁ [] ht₁,
        Contracts.zeta n ty₂ v₂ b₂ [] ht₂, hsm⟩
  | app f₁ a₁ f₂ a₂ hzf hza =>
    cases g₁ with
    | zero => rw [Setlec.whnfCore_zero] at h₁; exact nomatch h₁
    | succ gp =>
    cases g₂ with
    | zero => rw [Setlec.whnfCore_zero] at h₂; exact nomatch h₂
    | succ gr =>
    obtain ⟨F₁, hh₁, legs₁⟩ := whnfCore_app_decompose h₁
    obtain ⟨F₂, hh₂, legs₂⟩ := whnfCore_app_decompose h₂
    obtain ⟨hIf₁, hIa₁⟩ := subjInv_app hIu
    obtain ⟨hIf₂, hIa₂⟩ := subjInv_app hIv
    have hPf : PairedLeaves f₁ f₂ := pairedLeaves_mono
      mem_fvarLeaves_app_left mem_fvarLeaves_app_left hP
    have hQf : Q d f₁ f₂ := hQA hQ
    rcases IH (gp + gr) (by omega) (Nat.le_refl _) hzf hIf₁ hIf₂
        hPf hQf hh₁ hh₂ with
      ⟨hzF, hIF₁, hIF₂, hPF, hQF⟩ |
      ⟨w₁h, w₂h, c₁, c₂, hb₁, hb₂, hw₁, hw₂, ht₁, ht₂, hsm⟩
    · -- pack: the legs matrix
      -- the uniform cert-head exit (any legs)
      have certExit : whnfCore μ env gp d F₁ = .ok F₁ →
          whnfCore μ env gr d F₂ = .ok F₂ →
          F₁.looseBVarsBounded 0 = true →
          F₂.looseBVarsBounded 0 = true →
          isDefEqCore μ env fc d F₁ F₂ = .ok true →
          (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧ SubjInv d v' ∧
            PairedLeaves u' v' ∧ Q d u' v') ∨
          (∃ w₁ w₂ c₁ c₂, c₁ ≤ gp + 1 ∧ c₂ ≤ gr + 1 ∧
            whnfCore μ env c₁ d w₁ = .ok u' ∧
            whnfCore μ env c₂ d w₂ = .ok v' ∧
            Contracts μ env d (.app f₁ a₁) w₁ ∧
            Contracts μ env d (.app f₂ a₂) w₂ ∧
            CoreSeam μ env fc d w₁ w₂) := by
        intro hS₁ hS₂ hba hbb hc
        exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
          max gp gp + 1, max gr gr + 1, (by omega), (by omega),
          whnfCore_app_assemble hm hS₁ legs₁,
          whnfCore_app_assemble hm hS₂ legs₂,
          Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
          Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
          CoreSeam.certHead F₁ F₂ [a₁] [a₂] hba hbb hc rfl
            (fun i hi₁ _ => by
              have h0 : i = 0 := by
                simp only [List.length_cons, List.length_nil] at hi₁
                omega
              subst h0
              exact hza)⟩
      rcases legs₁ with
        ⟨n₁, ty₁, b₁, m₁, ta₁, rfl, hinf₁, hdq₁, hrun₁⟩ |
        ⟨n₁, ty₁, b₁, m₁, ta₁, rfl, hinf₁, hdq₁, rfl⟩ |
        ⟨hnl₁, hio₁⟩
      · -- β fired on the left
        rcases legs₂ with
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, hrun₂⟩ |
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, rfl⟩ |
          ⟨hnl₂, hio₂⟩
        · -- both fired: recurse on the contracta
          have betaRec : CertZip μ env fc d b₁ b₂ →
              (CertZip μ env fc d u' v' ∧ SubjInv d u' ∧
                SubjInv d v' ∧ PairedLeaves u' v' ∧ Q d u' v') ∨
              (∃ w₁ w₂ c₁ c₂, c₁ ≤ gp + 1 ∧ c₂ ≤ gr + 1 ∧
                whnfCore μ env c₁ d w₁ = .ok u' ∧
                whnfCore μ env c₂ d w₂ = .ok v' ∧
                Contracts μ env d (.app f₁ a₁) w₁ ∧
                Contracts μ env d (.app f₂ a₂) w₂ ∧
                CoreSeam μ env fc d w₁ w₂) := by
            intro hbody
            have hzc : CertZip μ env fc d (b₁.instantiate1 a₁)
                (b₂.instantiate1 a₂) := certZip_subst hza hbody 0
            have tr₁ : Contracts μ env d (.app f₁ a₁)
                (b₁.instantiate1 a₁) :=
              Contracts.head f₁ (.lam n₁ ty₁ b₁ m₁) [a₁] gp hh₁
                (Contracts.beta n₁ ty₁ b₁ a₁ ta₁ m₁ [] gp hinf₁
                  hdq₁ (.refl _))
            have tr₂ : Contracts μ env d (.app f₂ a₂)
                (b₂.instantiate1 a₂) :=
              Contracts.head f₂ (.lam n₂ ty₂ b₂ m₂) [a₂] gr hh₂
                (Contracts.beta n₂ ty₂ b₂ a₂ ta₂ m₂ [] gr hinf₂
                  hdq₂ (.refl _))
            have hIc₁ : SubjInv d (b₁.instantiate1 a₁) :=
              tr₁.subjInv hIC hLS hIu
            have hIc₂ : SubjInv d (b₂.instantiate1 a₂) :=
              tr₂.subjInv hIC hLS hIv
            have hPc : PairedLeaves (b₁.instantiate1 a₁)
                (b₂.instantiate1 a₂) :=
              Contracts.pairing hLS tr₁ tr₂ hP
            have hQc : Q d (b₁.instantiate1 a₁)
                (b₂.instantiate1 a₂) :=
              hQs (tr₂.q_transport hQB hQZ hQH
                (hQs (tr₁.q_transport hQB hQZ hQH hQ)))
            rcases IH (gp + gr) (by omega) (Nat.le_refl _) hzc
                hIc₁ hIc₂ hPc hQc hrun₁ hrun₂ with hpack |
              ⟨w₁, w₂, c₁, c₂, hb₁, hb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
            · exact .inl ⟨hpack.1, hIu', hIv', hP', hQ'⟩
            · exact .inr ⟨w₁, w₂, c₁, c₂, Nat.le_succ_of_le hb₁,
                Nat.le_succ_of_le hb₂, hr₁, hr₂,
                Contracts.head f₁ (.lam n₁ ty₁ b₁ m₁) [a₁] gp hh₁
                  (Contracts.beta n₁ ty₁ b₁ a₁ ta₁ m₁ [] gp hinf₁
                    hdq₁ ht₁),
                Contracts.head f₂ (.lam n₂ ty₂ b₂ m₂) [a₂] gr hh₂
                  (Contracts.beta n₂ ty₂ b₂ a₂ ta₂ m₂ [] gr hinf₂
                    hdq₂ ht₂),
                hsm⟩
          cases hzF with
          | refl _ => exact betaRec (.refl b₁)
          | cert _ _ hba hbb hc =>
            exact certExit (whnfCore_lam_run (whnfCore_pos hh₁))
              (whnfCore_lam_run (whnfCore_pos hh₂)) hba hbb hc
          | lam _ _ _ _ _ _ hty hbody => exact betaRec hbody
        · -- right side stuck at a failed β-cert: dead on the right
          exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
            Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
            CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
              (.app (.lam n₂ ty₂ b₂ m₂) a₂) (gr + 1)
              (fun g hg => hm.2.2.1 hg h₂)
              (fun p q h => nomatch h)
              (fun _ _ _ _ h => nomatch h)
              (fun _ h => nomatch h)⟩
        · -- left λ against a right iota package: cert node forced
          cases hzF with
          | refl _ => exact absurd rfl (hnl₂ n₁ ty₁ b₁ m₁)
          | cert _ _ hba hbb hc =>
            rcases hio₂ with ⟨e₂'', hio₂s, hrun₂'⟩ | ⟨hio₂n, rfl⟩
            · obtain ⟨n2, us2, hhd₂⟩ := iotaRec_some_head hio₂s
              exact certExit (whnfCore_lam_run (whnfCore_pos hh₁))
                (whnfCore_reidem_const hm hh₂ hhd₂) hba hbb hc
            · by_cases hc2 : ∃ n' us',
                  F₂.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n2, us2, hhd₂⟩ := hc2
                exact certExit (whnfCore_lam_run (whnfCore_pos hh₁))
                  (whnfCore_reidem_const hm hh₂ hhd₂) hba hbb hc
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₂ a₂) (gr + 1)
                    (fun g hg => hm.2.2.1 hg h₂)
                    (fun p q hh => hc2 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
          | lam _ _ ty₂' _ b₂' _ hty hbody =>
            exact absurd rfl (hnl₂ n₁ ty₂' b₂' m₁)
      · -- left side stuck at a failed β-cert: dead on the left
        exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
          Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
          CoreSeam.deadL (.app f₁ a₁) (.app f₂ a₂)
            (.app (.lam n₁ ty₁ b₁ m₁) a₁) (gp + 1)
            (fun g hg => hm.2.2.1 hg h₁)
            (fun p q h => nomatch h)
            (fun _ _ _ _ h => nomatch h)
            (fun _ h => nomatch h)⟩
      · -- left iota package
        rcases legs₂ with
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, hrun₂⟩ |
          ⟨n₂, ty₂, b₂, m₂, ta₂, rfl, hinf₂, hdq₂, rfl⟩ |
          ⟨hnl₂, hio₂⟩
        · -- right λ against a left iota package: cert node forced
          cases hzF with
          | refl _ => exact absurd rfl (hnl₁ n₂ ty₂ b₂ m₂)
          | cert _ _ hba hbb hc =>
            rcases hio₁ with ⟨e₁'', hio₁s, hrun₁'⟩ | ⟨hio₁n, rfl⟩
            · obtain ⟨n1, us1, hhd₁⟩ := iotaRec_some_head hio₁s
              exact certExit (whnfCore_reidem_const hm hh₁ hhd₁)
                (whnfCore_lam_run (whnfCore_pos hh₂)) hba hbb hc
            · by_cases hc1 : ∃ n' us',
                  F₁.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n1, us1, hhd₁⟩ := hc1
                exact certExit (whnfCore_reidem_const hm hh₁ hhd₁)
                  (whnfCore_lam_run (whnfCore_pos hh₂)) hba hbb hc
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadL (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₁ a₁) (gp + 1)
                    (fun g hg => hm.2.2.1 hg h₁)
                    (fun p q hh => hc1 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
          | lam _ ty₁' _ b₁' _ _ hty hbody =>
            exact absurd rfl (hnl₁ n₂ ty₁' b₁' m₂)
        · -- right side stuck at a failed β-cert: dead on the right
          exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
            Nat.le_refl _, Nat.le_refl _, h₁, h₂, .refl _, .refl _,
            CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
              (.app (.lam n₂ ty₂ b₂ m₂) a₂) (gr + 1)
              (fun g hg => hm.2.2.1 hg h₂)
              (fun p q h => nomatch h)
              (fun _ _ _ _ h => nomatch h)
              (fun _ h => nomatch h)⟩
        · -- both iota packages
          rcases hio₁ with ⟨e₁'', hio₁s, hrun₁'⟩ | ⟨hio₁n, rfl⟩
          · obtain ⟨n1, us1, hhd₁⟩ := iotaRec_some_head hio₁s
            have hS₁ : whnfCore μ env gp d F₁ = .ok F₁ :=
              whnfCore_reidem_const hm hh₁ hhd₁
            rcases hio₂ with ⟨e₂'', hio₂s, hrun₂'⟩ | ⟨hio₂n, rfl⟩
            · obtain ⟨n2, us2, hhd₂⟩ := iotaRec_some_head hio₂s
              exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
                max gp gp + 1, max gr gr + 1,
                (by omega), (by omega),
                whnfCore_app_assemble hm hS₁
                  (.inr (.inr ⟨hnl₁, .inl ⟨e₁'', hio₁s, hrun₁'⟩⟩)),
                whnfCore_app_assemble hm
                  (whnfCore_reidem_const hm hh₂ hhd₂)
                  (.inr (.inr ⟨hnl₂, .inl ⟨e₂'', hio₂s, hrun₂'⟩⟩)),
                Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
                Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
                zip_stuck_spine_exit (g₁' := gp) (g₂' := gr)
                  hzF hza (.inl ⟨e₁'', hio₁s⟩)⟩
            · by_cases hc2 : ∃ n' us',
                  F₂.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n2, us2, hhd₂⟩ := hc2
                exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
                  max gp gp + 1, max gr gr + 1,
                  (by omega), (by omega),
                  whnfCore_app_assemble hm hS₁
                    (.inr (.inr ⟨hnl₁, .inl ⟨e₁'', hio₁s, hrun₁'⟩⟩)),
                  whnfCore_app_assemble hm
                    (whnfCore_reidem_const hm hh₂ hhd₂)
                    (.inr (.inr ⟨hnl₂, .inr ⟨hio₂n, rfl⟩⟩)),
                  Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
                  Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
                  zip_stuck_spine_exit (g₁' := gp) (g₂' := gr)
                    hzF hza (.inl ⟨e₁'', hio₁s⟩)⟩
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadR (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₂ a₂) (gr + 1)
                    (fun g hg => hm.2.2.1 hg h₂)
                    (fun p q hh => hc2 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
          · rcases hio₂ with ⟨e₂'', hio₂s, hrun₂'⟩ | ⟨hio₂n, rfl⟩
            · obtain ⟨n2, us2, hhd₂⟩ := iotaRec_some_head hio₂s
              by_cases hc1 : ∃ n' us',
                  F₁.getAppFn = Setlec.Expr.const n' us'
              · obtain ⟨n1, us1, hhd₁⟩ := hc1
                exact .inr ⟨.app F₁ a₁, .app F₂ a₂,
                  max gp gp + 1, max gr gr + 1,
                  (by omega), (by omega),
                  whnfCore_app_assemble hm
                    (whnfCore_reidem_const hm hh₁ hhd₁)
                    (.inr (.inr ⟨hnl₁, .inr ⟨hio₁n, rfl⟩⟩)),
                  whnfCore_app_assemble hm
                    (whnfCore_reidem_const hm hh₂ hhd₂)
                    (.inr (.inr ⟨hnl₂, .inl ⟨e₂'', hio₂s, hrun₂'⟩⟩)),
                  Contracts.head f₁ F₁ [a₁] gp hh₁ (.refl _),
                  Contracts.head f₂ F₂ [a₂] gr hh₂ (.refl _),
                  zip_stuck_spine_exit (g₁' := gp) (g₂' := gr)
                    hzF hza (.inr ⟨e₂'', hio₂s⟩)⟩
              · exact .inr ⟨.app f₁ a₁, .app f₂ a₂, gp + 1, gr + 1,
                  Nat.le_refl _, Nat.le_refl _, h₁, h₂,
                  .refl _, .refl _,
                  CoreSeam.deadL (.app f₁ a₁) (.app f₂ a₂)
                    (.app F₁ a₁) (gp + 1)
                    (fun g hg => hm.2.2.1 hg h₁)
                    (fun p q hh => hc1 ⟨p, q, hh⟩)
                    (fun _ _ _ _ hh => nomatch hh)
                    (fun _ hh => nomatch hh)⟩
            · -- both inert: the pair stays zipped
              exact .inl ⟨.app F₁ a₁ F₂ a₂ hzF hza,
                hIu', hIv', hP', hQ'⟩
    · -- seam from the heads: lift it through the layer
      exact .inr ⟨.app w₁h a₁, .app w₂h a₂,
        max c₁ gp + 1, max c₂ gr + 1, (by omega), (by omega),
        whnfCore_app_assemble hm hw₁ legs₁,
        whnfCore_app_assemble hm hw₂ legs₂,
        ht₁.app_lift, ht₂.app_lift,
        coreSeam_lift_app hza hsm⟩

/-! ### The loop-level dispatch riding coreLock -/

/-- A spine head's non-const fact spreads over the spine. -/
theorem mkAppN_fn_ne_const {H : Expr} {cs : List Expr}
    (h : ∀ p q, H.getAppFn ≠ .const p q) :
    ∀ p q, (Setlec.Expr.mkAppN H cs).getAppFn ≠ .const p q := by
  intro p q hh
  rw [Setlec.Expr.getAppFn_mkAppN] at hh
  exact h p q hh

/-- Shape disequalities give the head fact (non-app subjects are
their own spine heads). -/
theorem not_const_getAppFn_of_shape {e : Expr}
    (h : ∀ p q, e ≠ .app p q) (h2 : ∀ p q, e ≠ .const p q) :
    ∀ p q, e.getAppFn ≠ .const p q := by
  intro p q hh
  rw [getAppFn_of_not_app h] at hh
  exact h2 p q hh

/-- A non-empty spine is an application, never a sort. -/
theorem mkAppN_cons_ne_sort {H a : Expr} {as : List Expr} :
    ∀ ℓ, Setlec.Expr.mkAppN H (a :: as) ≠ .sort ℓ := by
  intro ℓ h
  obtain ⟨p, q, hpq⟩ := mkAppN_cons_app (F := H) (a := a) (as := as)
  rw [hpq] at h
  exact nomatch h

/-- A spine over a non-sort head is never a sort. -/
theorem mkAppN_ne_sort {H : Expr} (hH : ∀ ℓ, H ≠ .sort ℓ) :
    ∀ {cs : List Expr} (ℓ : Level),
      Setlec.Expr.mkAppN H cs ≠ .sort ℓ := by
  intro cs
  cases cs with
  | nil => exact hH
  | cons a as => exact fun ℓ => mkAppN_cons_ne_sort ℓ

/-- **The dead exit**: a non-const-headed, non-sort whnfCore output
refutes its own sort-loop — the nat leg by `NatStepNoSort`, the δ
leg by the head shape, the stop leg by the sort equation. -/
theorem loop_dead_exit {μ : CheckMode} {env : Env}
    (hN : NatStepNoSort μ env) {ga la d : Nat}
    {k : Expr → Setlec.CheckM Expr} {X e₁ : Expr} {ℓa : Level}
    {C : Prop}
    (hwca : whnfCore μ env ga d X = .ok e₁)
    (ha : Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la X
      = .ok (.sort ℓa))
    (tri :
      (∃ e₂, Setlec.reduceNat (Setlec.pureFns μ env ga) env d e₁
          = .ok (some e₂) ∧ k e₂ = .ok (.sort ℓa)) ∨
      (Setlec.reduceNat (Setlec.pureFns μ env ga) env d e₁
          = .ok none ∧
        ∃ e₂, Setlec.unfoldDefinition env e₁ = some e₂ ∧
          k e₂ = .ok (.sort ℓa)) ∨
      (Setlec.reduceNat (Setlec.pureFns μ env ga) env d e₁
          = .ok none ∧
        Setlec.unfoldDefinition env e₁ = none ∧
        Expr.sort ℓa = e₁))
    (hnc : ∀ p q, e₁.getAppFn ≠ .const p q)
    (hns : ∀ ℓ, e₁ ≠ .sort ℓ) : C := by
  exfalso
  rcases tri with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ | ⟨-, -, hstop⟩
  · exact hN hwca hrx ha
  · rw [unfoldDefinition_none_of_fn_not_const hnc] at hud
    exact nomatch hud
  · exact hns ℓa hstop.symm

/-- **The head dispatch**: a zipped pair with sort-loops agrees —
one loop step decomposed per side, `coreLock` on the core runs, the
pack classified by the spine view (Θ at the first cert layer, the
const-head case at const heads, dead exits elsewhere), the seams
converted by the routed loop-level cases with re-based loop runs
(assembled from the seam's connecting runs at the premise knot
fuels — the coreLock fuel bounds).  Both the λ- and letE-head
cases collapse onto this. -/
theorem zipHeadDispatch {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQB : QPreserveBetaF μ env Q)
    (hQZ : QPreserveZetaF env Q)
    (hQH : QPreserveHeadF μ env Q)
    (hLS : LeavesSubCoreF μ env)
    (hQs : ∀ {d' : Nat} {a b : Expr}, Q d' a b → Q d' b a)
    (hQA : QDescendAppF Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hIo : ZipIotaCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ∀ {fc d ga la gb lb : Nat} {X₁ X₂ : Expr} {ℓa ℓb : Level},
      ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
      CertZip μ env fc d X₁ X₂ →
      SubjInv d X₁ → SubjInv d X₂ →
      PairedLeaves X₁ X₂ → Q d X₁ X₂ →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la X₁
        = .ok (.sort ℓa) →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb X₂
        = .ok (.sort ℓb) →
      ℓa.eval φ = ℓb.eval φ := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb X₁ X₂ ℓa ℓb below hz hI₁ hI₂ hp hQ ha hb
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨e₁, hwca, triA⟩ := whnfStep_decompose haD
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨e₂, hwcb, triB⟩ := whnfStep_decompose hbD
  have hwca' : whnfCore μ env ga d X₁ = .ok e₁ := hwca
  have hwcb' : whnfCore μ env gb d X₂ = .ok e₂ := hwcb
  have stepA : ∀ {W : Expr},
      whnfCore μ env ga d W = .ok e₁ →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d (la' + 1) W
        = .ok (.sort ℓa) := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triA with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  have stepB : ∀ {W : Expr},
      whnfCore μ env gb d W = .ok e₂ →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d (lb' + 1) W
        = .ok (.sort ℓb) := by
    intro W hW
    rw [whnfLoop_succ]
    rcases triB with ⟨x, hrx, hkx⟩ | ⟨hrn, x, hud, hkx⟩ |
      ⟨hrn, hud, hstop⟩
    · exact whnfStep_assemble_nat hW hrx hkx
    · exact whnfStep_assemble_delta hW hrn hud hkx
    · rw [hstop]
      exact whnfStep_assemble_stuck hW hrn hud
  have belowFc : ZipBelowFc μ env φ Q fc :=
    fun hlt hz' hIs hIt hp' hq' hla hlb =>
      below (Or.inl hlt) hz' hIs hIt hp' hq' hla hlb
  rcases @coreLock μ env Q hm hIC hLC hQC hQB hQZ hQH hLS
      (fun {d'} {a b} h => hQs h) (fun {d'} {P} {y} {R} {z} h => hQA h)
      (ga + gb) ga gb fc d X₁ X₂ e₁ e₂
      (Nat.le_refl _) hz hI₁ hI₂ hp hQ hwca' hwcb' with
    ⟨hzE, hIe₁, hIe₂, hpE, hQE⟩ |
    ⟨w₁, w₂, c₁, c₂, hcb₁, hcb₂, hr₁, hr₂, ht₁, ht₂, hsm⟩
  · -- the pack: classify the zipped outputs by the spine view
    have hcoreA : whnfCore μ env ga d e₁ = .ok e₁ := by
      rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ | ⟨-, -, hstop⟩
      · exact (hN hwca' hrx ha).elim
      · obtain ⟨n0, us0, hhd⟩ := unfoldDefinition_some_head hud
        exact whnfCore_reidem_const hm hwca' hhd
      · rw [← hstop]
        exact whnfCore_sort_run (whnfCore_pos hwca')
    have hcoreB : whnfCore μ env gb d e₂ = .ok e₂ := by
      rcases triB with ⟨y, hry, -⟩ | ⟨-, y, hud, -⟩ | ⟨-, -, hstop⟩
      · exact (hN hwcb' hry hb).elim
      · obtain ⟨n0, us0, hhd⟩ := unfoldDefinition_some_head hud
        exact whnfCore_reidem_const hm hwcb' hhd
      · rw [← hstop]
        exact whnfCore_sort_run (whnfCore_pos hwcb')
    have ha' := stepA hcoreA
    have hb' := stepB hcoreB
    obtain ⟨H₁, H₂, cs, ds, rfl, rfl, hlenv, hargsv, hheadv⟩ :=
      certZip_app_view hzE
    rcases hheadv with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hzH⟩
    · exact hΘ belowFc hba hbb hc hlenv hargsv hIe₁ hIe₂ hpE hQE
        ha' hb'
    · cases hzH with
      | refl _ =>
        cases H₁ with
        | const n us =>
          exact hConst below (fun φ' => rfl) hlenv hargsv
            hIe₁ hIe₂ hpE hQE ha' hb'
        | sort u₀ =>
          cases cs with
          | cons ch ct =>
            exact loop_dead_exit hN hwca' ha triA
              (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
              (fun ℓ => mkAppN_cons_ne_sort ℓ)
          | nil =>
            cases ds with
            | cons dh dt => exact nomatch hlenv
            | nil =>
              rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ |
                ⟨-, -, hstopA⟩
              · exact (hN hwca' hrx ha).elim
              · have hnone : Setlec.unfoldDefinition env
                    (Setlec.Expr.mkAppN (Expr.sort u₀) []) = none :=
                  unfoldDefinition_none_of_fn_not_const
                    (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
                exact nomatch (hnone.symm.trans hud)
              · rcases triB with ⟨y, hry, -⟩ | ⟨-, y, hud', -⟩ |
                  ⟨-, -, hstopB⟩
                · exact (hN hwcb' hry hb).elim
                · have hnone : Setlec.unfoldDefinition env
                      (Setlec.Expr.mkAppN (Expr.sort u₀) []) = none :=
                    unfoldDefinition_none_of_fn_not_const
                      (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
                  exact nomatch (hnone.symm.trans hud')
                · have hA : ℓa = u₀ :=
                    Expr.sort.inj (show Expr.sort ℓa = Expr.sort u₀
                      from hstopA)
                  have hB : ℓb = u₀ :=
                    Expr.sort.inj (show Expr.sort ℓb = Expr.sort u₀
                      from hstopB)
                  rw [hA, hB]
        | app p q => exact absurd rfl (hne₁ p q)
        | bvar i =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.bvar i) (fun _ h2 => nomatch h2) ℓ0 hh)
        | fvar i n ty =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.fvar i n ty) (fun _ h2 => nomatch h2) ℓ0 hh)
        | lam n ty b m =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.lam n ty b m) (fun _ h2 => nomatch h2) ℓ0 hh)
        | forallE n ty b m =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.forallE n ty b m) (fun _ h2 => nomatch h2) ℓ0 hh)
        | letE n ty v b =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.letE n ty v b) (fun _ h2 => nomatch h2) ℓ0 hh)
        | lit l =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.lit l) (fun _ h2 => nomatch h2) ℓ0 hh)
        | proj sn i pe =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.proj sn i pe) (fun _ h2 => nomatch h2) ℓ0 hh)
      | cert _ _ hba hbb hc =>
        exact hΘ belowFc hba hbb hc hlenv hargsv hIe₁ hIe₂ hpE hQE
          ha' hb'
      | constSlack n us us' hev =>
        exact hConst below hev hlenv hargsv hIe₁ hIe₂ hpE hQE
          ha' hb'
      | sortSlack u₀ v₀ hev =>
        cases cs with
        | cons ch ct =>
          exact loop_dead_exit hN hwca' ha triA
            (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
            (fun ℓ => mkAppN_cons_ne_sort ℓ)
        | nil =>
          cases ds with
          | cons dh dt => exact nomatch hlenv
          | nil =>
            rcases triA with ⟨x, hrx, -⟩ | ⟨-, x, hud, -⟩ |
              ⟨-, -, hstopA⟩
            · exact (hN hwca' hrx ha).elim
            · have hnone : Setlec.unfoldDefinition env
                  (Setlec.Expr.mkAppN (Expr.sort u₀) []) = none :=
                unfoldDefinition_none_of_fn_not_const
                  (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
              exact nomatch (hnone.symm.trans hud)
            · rcases triB with ⟨y, hry, -⟩ | ⟨-, y, hud', -⟩ |
                ⟨-, -, hstopB⟩
              · exact (hN hwcb' hry hb).elim
              · have hnone : Setlec.unfoldDefinition env
                    (Setlec.Expr.mkAppN (Expr.sort v₀) []) = none :=
                  unfoldDefinition_none_of_fn_not_const
                    (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
                exact nomatch (hnone.symm.trans hud')
              · have hA : ℓa = u₀ :=
                  Expr.sort.inj (show Expr.sort ℓa = Expr.sort u₀
                    from hstopA)
                have hB : ℓb = v₀ :=
                  Expr.sort.inj (show Expr.sort ℓb = Expr.sort v₀
                    from hstopB)
                rw [hA, hB]
                exact hev φ
      | fvar i n ty₁' ty₂' hty =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.fvar i n ty₁') (fun _ h2 => nomatch h2) ℓ0 hh)
      | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
      | lam n ty₁' ty₂' b₁' b₂' m hty hbody =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.lam n ty₁' b₁' m) (fun _ h2 => nomatch h2) ℓ0 hh)
      | forallE n ty₁' ty₂' b₁' b₂' m hty hbody =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.forallE n ty₁' b₁' m) (fun _ h2 => nomatch h2) ℓ0 hh)
      | letE n ty₁' ty₂' v₁' v₂' b₁' b₂' hty hv hbody =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.letE n ty₁' v₁' b₁') (fun _ h2 => nomatch h2) ℓ0 hh)
      | proj sn i pe₁ pe₂ he =>
        exact loop_dead_exit hN hwca' ha triA
          (by intro p q hh; rw [Setlec.Expr.getAppFn_mkAppN] at hh; simp [Setlec.Expr.getAppFn] at hh)
          (by intro ℓ0 hh; exact mkAppN_ne_sort (H := Expr.proj sn i pe₁) (fun _ h2 => nomatch h2) ℓ0 hh)
  · -- the seam: transport, re-base the loops, convert
    have hIw₁ : SubjInv d w₁ := ht₁.subjInv hIC hLS hI₁
    have hIw₂ : SubjInv d w₂ := ht₂.subjInv hIC hLS hI₂
    have hpw : PairedLeaves w₁ w₂ :=
      Contracts.pairing hLS ht₁ ht₂ hp
    have hQw : Q d w₁ w₂ :=
      hQs (ht₂.q_transport hQB hQZ hQH
        (hQs (ht₁.q_transport hQB hQZ hQH hQ)))
    have hw₁ga : whnfCore μ env ga d w₁ = .ok e₁ :=
      hm.2.2.1 hcb₁ hr₁
    have hw₂gb : whnfCore μ env gb d w₂ = .ok e₂ :=
      hm.2.2.1 hcb₂ hr₂
    have haw := stepA hw₁ga
    have hbw := stepB hw₂gb
    cases hsm with
    | certHead F₁ F₂ as bs hba hbb hc hlen hargs =>
      exact hΘ belowFc hba hbb hc hlen hargs hIw₁ hIw₂ hpw hQw
        haw hbw
    | recHead n cv mI rP rules us us' as bs hf hev hlen hargs =>
      exact @hIo fc d ga (la' + 1) gb (lb' + 1) mI rP n us us'
        cv rules as bs ℓa ℓb hf
        (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
            hmes hz' hIs' hIt' hp' hq' hla hlb =>
          below hmes hz' hIs' hIt' hp' hq' hla hlb)
        hev hlen hargs hIw₁ hIw₂ hpw hQw haw hbw
    | projHead sn i pe₁ pe₂ as bs he hlen hargs =>
      exact @hProj fc d ga (la' + 1) gb (lb' + 1) i sn pe₁ pe₂
        as bs ℓa ℓb
        (fun {fc'} {d'} {ga'} {la₀} {gb'} {lb₀} {s'} {t'} {ℓa'} {ℓb'}
            hmes hz' hIs' hIt' hp' hq' hla hlb =>
          below hmes hz' hIs' hIt' hp' hq' hla hlb)
        he hlen hargs hIw₁ hIw₂ hpw hQw haw hbw
    | deadL _ _ u'd bnd hrun hnc hnl hns =>
      have h1 : whnfCore μ env (max bnd ga) d w₁ = .ok u'd :=
        hrun (max bnd ga) (Nat.le_max_left _ _)
      have h2 : whnfCore μ env (max bnd ga) d w₁ = .ok e₁ :=
        hm.2.2.1 (Nat.le_max_right _ _) hw₁ga
      rw [h1] at h2
      obtain rfl := Except.ok.inj h2
      exact loop_dead_exit hN hwca' ha triA hnc hns
    | deadR _ _ v'd bnd hrun hnc hnl hns =>
      have h1 : whnfCore μ env (max bnd gb) d w₂ = .ok v'd :=
        hrun (max bnd gb) (Nat.le_max_left _ _)
      have h2 : whnfCore μ env (max bnd gb) d w₂ = .ok e₂ :=
        hm.2.2.1 (Nat.le_max_right _ _) hw₂gb
      rw [h1] at h2
      obtain rfl := Except.ok.inj h2
      exact loop_dead_exit hN hwcb' hb triB hnc hns

end Discharge

end Setlec.SetR.Interp2
