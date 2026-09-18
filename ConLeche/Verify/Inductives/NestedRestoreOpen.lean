module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Denote.TeleOpen

public section

/-!
# The restored constructor, opened (task #315)

`restoreNested` (`ConLeche/Kernel/Inductives/NestedInstall.lean`)
rewrites an auxiliary constructor's type under its parameter prefix:
the walk replaces an auxiliary head by the pin it stands for and is the
identity everywhere else.  The reading side never sees that walk — it
sees the *opened* telescope, `openPisAtFvars` at the parameters and
then at the fields — and what it needs is the opened form of the
restored type in terms of the opened form of the auxiliary one.

That is what `restoreNested_opened` says: the restored type opens at
the SAME parameter variables, to the SAME residual, with one variable
per auxiliary field, and each restored field domain is

* the auxiliary one, when that mentions no auxiliary name, or
* `pin p⃗ is`, when the auxiliary one is `auxJ p⃗ is`.

The bookkeeping in between is the mismatch the openers create: a field
whose domain the walk *did* rewrite is opened at two variables that
carry different annotations (the auxiliary's domain on one side, the
restored one on the other).  The block's positivity facts (`hnodep`,
the `nativeOpenedOk`/`mutualOpenedOk` guard's own reading) say such a
variable occurs in no later domain and not in the residual, so the two
openings agree wherever it matters — `RestoreOpenAgree` carries that
through the induction.
-/

namespace ConLeche

open Expr

/-! ## `mentionsFvar` under substitution -/

theorem mentionsFvar_bvar {q i : Nat} : (Expr.bvar i).mentionsFvar q = false := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem mentionsFvar_sort {q : Nat} {u : Level} : (Expr.sort u).mentionsFvar q = false := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem mentionsFvar_const {q : Nat} {n : Name} {us : List Level} :
    (Expr.const n us).mentionsFvar q = false := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

theorem mentionsFvar_lit {q : Nat} {l : Literal} : (Expr.lit l).mentionsFvar q = false := by
  simp [Expr.mentionsFvar, Expr.fvarLeaves]

/-- A variable mentioned before a substitution is mentioned after it. -/
theorem mentionsFvar_instantiate1_mono {v : Expr} {q : Nat} :
    ∀ {e : Expr} {d : Nat}, e.mentionsFvar q = true →
      (e.instantiate1 v d).mentionsFvar q = true := by
  intro e
  induction e with
  | bvar i => intro d h; rw [mentionsFvar_bvar] at h; exact Bool.noConfusion h
  | sort u => intro d h; rw [mentionsFvar_sort] at h; exact Bool.noConfusion h
  | const n us => intro d h; rw [mentionsFvar_const] at h; exact Bool.noConfusion h
  | lit l => intro d h; rw [mentionsFvar_lit] at h; exact Bool.noConfusion h
  | fvar idx ty _ => intro d h; simpa only [Expr.instantiate1] using h
  | app f a ihf iha =>
    intro d h
    rw [Expr.mentionsFvar_app, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_app, Bool.or_eq_true]
    exact h.imp (fun h1 => ihf h1) (fun h2 => iha h2)
  | lam ty b m ihty ihb =>
    intro d h
    rw [Expr.mentionsFvar_lam, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_lam, Bool.or_eq_true]
    exact h.imp (fun h1 => ihty h1) (fun h2 => ihb h2)
  | forallE ty b m ihty ihb =>
    intro d h
    rw [Expr.mentionsFvar_forallE, Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_forallE, Bool.or_eq_true]
    exact h.imp (fun h1 => ihty h1) (fun h2 => ihb h2)
  | letE ty vl b ihty ihv ihb =>
    intro d h
    rw [Expr.mentionsFvar_letE] at h
    simp only [Bool.or_eq_true] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_letE, Bool.or_eq_true]
    exact h.imp (fun h1 => h1.imp (fun h2 => ihty h2) (fun h2 => ihv h2)) (fun h2 => ihb h2)
  | proj s i pe ih =>
    intro d h
    rw [Expr.mentionsFvar_proj] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_proj]
    exact ih h

/-- Contrapositive: a variable absent after a substitution was absent
before it. -/
theorem mentionsFvar_instantiate1_false {v : Expr} {q d : Nat} {e : Expr}
    (h : (e.instantiate1 v d).mentionsFvar q = false) : e.mentionsFvar q = false := by
  cases he : e.mentionsFvar q with
  | false => rfl
  | true => rw [mentionsFvar_instantiate1_mono he] at h; exact Bool.noConfusion h

/-- Substituting a variable-free term into a variable-free term keeps
the variable out. -/
theorem mentionsFvar_instantiate1_of_false {v : Expr} {q : Nat}
    (hv : v.mentionsFvar q = false) :
    ∀ {e : Expr} {d : Nat}, e.mentionsFvar q = false →
      (e.instantiate1 v d).mentionsFvar q = false := by
  intro e
  induction e with
  | bvar i =>
    intro d _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> exact mentionsFvar_bvar
  | fvar idx ty _ => intro d h; simpa only [Expr.instantiate1] using h
  | sort u => intro d _; exact mentionsFvar_sort
  | const n us => intro d _; exact mentionsFvar_const
  | lit l => intro d _; exact mentionsFvar_lit
  | app f a ihf iha =>
    intro d h
    rw [Expr.mentionsFvar_app, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_app, Bool.or_eq_false_iff]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro d h
    rw [Expr.mentionsFvar_lam, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_lam, Bool.or_eq_false_iff]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h
    rw [Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_forallE, Bool.or_eq_false_iff]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE ty vl b ihty ihv ihb =>
    intro d h
    rw [Expr.mentionsFvar_letE] at h
    simp only [Bool.or_eq_false_iff] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_letE, Bool.or_eq_false_iff]
    exact ⟨⟨ihty h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i pe ih =>
    intro d h
    rw [Expr.mentionsFvar_proj] at h
    simp only [Expr.instantiate1, Expr.mentionsFvar_proj]
    exact ih h

/-- The sequence form of `mentionsFvar_instantiate1_false`. -/
theorem mentionsFvar_instSeq_false {q : Nat} :
    ∀ (vs : List Expr) (t : Nat) {e : Expr},
      (Expr.instSeq vs t e).mentionsFvar q = false → e.mentionsFvar q = false := by
  intro vs
  induction vs with
  | nil => intro t e h; exact h
  | cons v vs ih =>
    intro t e h
    exact mentionsFvar_instantiate1_false (v := v) (d := t) (ih (t - 1) h)

/-- The sequence form of `mentionsFvar_instantiate1_of_false`. -/
theorem mentionsFvar_instSeq_of_false {q : Nat} :
    ∀ (vs : List Expr) (t : Nat) {e : Expr}, e.mentionsFvar q = false →
      (∀ v ∈ vs, v.mentionsFvar q = false) →
      (Expr.instSeq vs t e).mentionsFvar q = false := by
  intro vs
  induction vs with
  | nil => intro t e h _; exact h
  | cons v vs ih =>
    intro t e h hv
    exact ih (t - 1)
      (mentionsFvar_instantiate1_of_false (hv v List.mem_cons_self) h)
      (fun x hx => hv x (List.mem_cons_of_mem _ hx))

/-- A spine's arguments inherit the head term's absent variables. -/
theorem mentionsFvar_mkAppN_false {q : Nat} :
    ∀ (args : List Expr) (f : Expr), (Expr.mkAppN f args).mentionsFvar q = false →
      f.mentionsFvar q = false ∧ ∀ a ∈ args, a.mentionsFvar q = false := by
  intro args
  induction args with
  | nil => intro f h; exact ⟨h, fun a ha => nomatch ha⟩
  | cons a as ih =>
    intro f h
    obtain ⟨hfa, has⟩ := ih (.app f a) h
    rw [Expr.mentionsFvar_app, Bool.or_eq_false_iff] at hfa
    refine ⟨hfa.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hfa.2
    · exact has x hx'

/-- The sequence form of `Expr.mentionsConst_instantiate1`, read
backwards: a constant absent from a substituted term was absent from
the term. -/
theorem mentionsConst_instSeq_false {m : Name} :
    ∀ (vs : List Expr) (t : Nat) {e : Expr},
      (Expr.instSeq vs t e).mentionsConst m = false → e.mentionsConst m = false := by
  intro vs
  induction vs with
  | nil => intro t e h; exact h
  | cons v vs ih =>
    intro t e h
    have h1 := ih (t - 1) h
    cases he : e.mentionsConst m with
    | false => rfl
    | true =>
      rw [Expr.mentionsConst_instantiate1 (v := v) (j := t) he] at h1
      exact Bool.noConfusion h1

/-! ## Two openings that differ only where nothing looks -/


/-- **Member-freedom transfer at an instantiation** (task #315 L-B):
`mentionsConst_instSeq_false` at the LIST, which is the form every
consumer wants — the walks ask `mentionsMember` of a field's domain,
not `mentionsConst` of one name.  It is `os_field_domain_free`'s step
for a caller that already holds the instantiation equation
(`copyOrdFLeft`'s `hxdom2`) rather than the two openings. -/
theorem mentionsMember_instSeq_false {names : List Name} (vs : List Expr) (t : Nat) {e : Expr}
    (h : mentionsMember names (Expr.instSeq vs t e) = false) :
    mentionsMember names e = false := by
  rcases hM : mentionsMember names e with _ | _
  · rfl
  · exfalso
    obtain ⟨T, hT, hTm⟩ := List.any_eq_true.mp hM
    rw [mentionsConst_instSeq_false vs t
      (by simpa using List.any_eq_false.mp h T hT)] at hTm
    exact nomatch hTm

/-- Two opener lists that agree except at positions carrying a "bad"
variable — where they may differ in the ANNOTATION only. -/
def RestoreOpenAgree (bad : Nat → Prop) (vs ws : List Expr) : Prop :=
  vs.length = ws.length ∧
  ∀ (k : Nat) (v w : Expr), vs[k]? = some v → ws[k]? = some w →
    v = w ∨ ∃ (idx : Nat) (a b : Expr), v = .fvar idx a ∧ w = .fvar idx b ∧ bad idx

/-- Substituting two variables that differ only in their annotation is
the same substitution, when the variable does not occur in the
result. -/
theorem instantiate1_congr_fvar {idx : Nat} {a b : Expr} :
    ∀ {e : Expr} {d : Nat}, (e.instantiate1 (.fvar idx a) d).mentionsFvar idx = false →
      e.instantiate1 (.fvar idx a) d = e.instantiate1 (.fvar idx b) d := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.instantiate1] at h ⊢
    by_cases hid : i = d
    · rw [if_pos hid] at h ⊢
      rw [Expr.mentionsFvar_fvar] at h
      simp at h
    · rw [if_neg hid, if_neg hid]
  | fvar i ty _ => intro d _; rfl
  | sort u => intro d _; rfl
  | const n us => intro d _; rfl
  | lit l => intro d _; rfl
  | app f x ihf ihx =>
    intro d h
    simp only [Expr.instantiate1, Expr.mentionsFvar_app, Bool.or_eq_false_iff] at h ⊢
    rw [ihf h.1, ihx h.2]
  | lam ty bd m ihty ihb =>
    intro d h
    simp only [Expr.instantiate1, Expr.mentionsFvar_lam, Bool.or_eq_false_iff] at h ⊢
    rw [ihty h.1, ihb h.2]
  | forallE ty bd m ihty ihb =>
    intro d h
    simp only [Expr.instantiate1, Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at h ⊢
    rw [ihty h.1, ihb h.2]
  | letE ty vl bd ihty ihv ihb =>
    intro d h
    simp only [Expr.instantiate1, Expr.mentionsFvar_letE, Bool.or_eq_false_iff] at h ⊢
    rw [ihty h.1.1, ihv h.1.2, ihb h.2]
  | proj s i pe ih =>
    intro d h
    simp only [Expr.instantiate1, Expr.mentionsFvar_proj] at h ⊢
    rw [ih h]

/-- **The congruence**: two agreeing opener lists open a term alike, as
soon as the result mentions none of the bad variables. -/
theorem instSeq_congr_of_agree {bad : Nat → Prop} :
    ∀ (vs ws : List Expr) (t : Nat) (e : Expr),
      RestoreOpenAgree bad vs ws →
      (∀ idx, bad idx → (Expr.instSeq vs t e).mentionsFvar idx = false) →
      Expr.instSeq vs t e = Expr.instSeq ws t e := by
  intro vs
  induction vs with
  | nil =>
    intro ws t e hag _
    cases ws with
    | nil => rfl
    | cons w ws => exact absurd hag.1 (by simp)
  | cons v vs ih =>
    intro ws t e hag hfree
    cases ws with
    | nil => exact absurd hag.1 (by simp)
    | cons w ws =>
      have htail : RestoreOpenAgree bad vs ws :=
        ⟨by simpa using hag.1, fun k x y hx hy =>
          hag.2 (k + 1) x y (by simpa using hx) (by simpa using hy)⟩
      rcases hag.2 0 v w rfl rfl with rfl | ⟨idx, a, b, rfl, rfl, hbad⟩
      · exact ih ws (t - 1) (e.instantiate1 v t) htail hfree
      · have h1 : (e.instantiate1 (.fvar idx a) t).mentionsFvar idx = false :=
          mentionsFvar_instSeq_false vs (t - 1) (hfree idx hbad)
        have heq : e.instantiate1 (.fvar idx a) t = e.instantiate1 (.fvar idx b) t :=
          instantiate1_congr_fvar h1
        show Expr.instSeq vs (t - 1) (e.instantiate1 (.fvar idx a) t)
          = Expr.instSeq ws (t - 1) (e.instantiate1 (.fvar idx b) t)
        rw [← heq]
        exact ih ws (t - 1) _ htail hfree

/-- Agreement is inherited by a common prefix. -/
theorem RestoreOpenAgree.prefix {bad : Nat → Prop} {vs ws : List Expr}
    (h : RestoreOpenAgree bad vs ws) (pre : List Expr) :
    RestoreOpenAgree bad (pre ++ vs) (pre ++ ws) := by
  refine ⟨by simp [h.1], fun k x y hx hy => ?_⟩
  by_cases hk : k < pre.length
  · rw [List.getElem?_append_left hk] at hx hy
    exact Or.inl (Option.some.inj (hx.symm.trans hy))
  · rw [List.getElem?_append_right (by omega)] at hx hy
    exact h.2 (k - pre.length) x y hx hy

/-- Agreement extends by one position. -/
theorem RestoreOpenAgree.snoc {bad : Nat → Prop} {vs ws : List Expr} {v w : Expr}
    (h : RestoreOpenAgree bad vs ws)
    (hvw : v = w ∨ ∃ (idx : Nat) (a b : Expr), v = .fvar idx a ∧ w = .fvar idx b ∧ bad idx) :
    RestoreOpenAgree bad (vs ++ [v]) (ws ++ [w]) := by
  have hlen : vs.length = ws.length := h.1
  refine ⟨by simp [h.1], fun k x y hx hy => ?_⟩
  by_cases hk : k < vs.length
  · rw [List.getElem?_append_left hk] at hx
    rw [List.getElem?_append_left (by omega)] at hy
    exact h.2 k x y hx hy
  · rw [List.getElem?_append_right (by omega)] at hx
    rw [List.getElem?_append_right (by omega)] at hy
    rw [h.1] at hx
    cases hkk : k - ws.length with
    | zero =>
      rw [hkk] at hx hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      rw [← hx, ← hy]
      exact hvw
    | succ j =>
      rw [hkk] at hx
      simp at hx

/-- Agreement is monotone in the bad set. -/
theorem RestoreOpenAgree.mono {bad bad' : Nat → Prop} {vs ws : List Expr}
    (h : RestoreOpenAgree bad vs ws) (hb : ∀ idx, bad idx → bad' idx) :
    RestoreOpenAgree bad' vs ws :=
  ⟨h.1, fun k x y hx hy =>
    (h.2 k x y hx hy).imp id (fun ⟨idx, a, b, h1, h2, h3⟩ => ⟨idx, a, b, h1, h2, hb idx h3⟩)⟩

/-! ## Opening a `∀`-telescope -/

/-- Every entry of an opener list is a variable. -/
def AllFvarsL (l : List Expr) : Prop :=
  ∀ v ∈ l, ∃ (idx : Nat) (ty : Expr), v = .fvar idx ty

theorem AllFvarsL.bounded {l : List Expr} (h : AllFvarsL l) :
    ∀ v ∈ l, v.looseBVarsBounded 0 = true := by
  intro v hv
  obtain ⟨idx, ty, rfl⟩ := h v hv
  rfl

theorem AllFvarsL.singleton (idx : Nat) (ty : Expr) : AllFvarsL [Expr.fvar idx ty] :=
  fun _ hv => ⟨idx, ty, List.mem_singleton.mp hv⟩

theorem AllFvarsL.append {l₁ l₂ : List Expr} (h₁ : AllFvarsL l₁) (h₂ : AllFvarsL l₂) :
    AllFvarsL (l₁ ++ l₂) := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact h₁ v h
  · exact h₂ v h

/-- A variable absent from every opened domain and from the residual is
absent from the telescope. -/
theorem openPisAtFvars_mentionsFvar_false {q : Nat} :
    ∀ (m : Nat) {e : Expr} {s : Nat} {fvs : List Expr} {rest : Expr},
      openPisAtFvars m e s = some (fvs, rest) →
      (∀ y ∈ fvs, y.fvarTypeD.mentionsFvar q = false) →
      rest.mentionsFvar q = false → e.mentionsFvar q = false := by
  intro m
  induction m with
  | zero =>
    intro e s fvs rest h _ hr
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hr
  | succ m ih =>
    intro e s fvs rest h hfvs hr
    cases e with
    | forallE dom body bm =>
      simp only [openPisAtFvars] at h
      cases hop : openPisAtFvars m (body.instantiate1 (.fvar s dom)) (s + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hdom : dom.mentionsFvar q = false :=
          hfvs (.fvar s dom) List.mem_cons_self
        have hbody := ih hop
          (fun y hy => hfvs y (List.mem_cons_of_mem _ hy)) hr
        rw [Expr.mentionsFvar_forallE, hdom,
          mentionsFvar_instantiate1_false hbody]
        rfl
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ => exact nomatch h

/-- A `∀`-telescope over a body (exposed: the reading law unfolds it
binder by binder, task #315 U-19b). -/
@[expose] def mkPisB : List (Expr × BinderMeta) → Expr → Expr
  | [], e => e
  | b :: bs, e => .forallE b.1 (mkPisB bs e) b.2

theorem mkPisB_eq_foldr : ∀ (bs : List (Expr × BinderMeta)) (body : Expr),
    bs.foldr (fun (b : Expr × BinderMeta) acc => Expr.forallE b.1 acc b.2) body
      = mkPisB bs body
  | [], _ => rfl
  | b :: bs, body => by
    show Expr.forallE b.1 (bs.foldr _ body) b.2 = _
    rw [mkPisB_eq_foldr bs body]
    rfl

theorem stripPis_mkPisB : ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
    {body : Expr}, e.stripPis k = some (bs, body) → e = mkPisB bs body := by
  intro k
  induction k with
  | zero =>
    intro e bs body h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e bs body h
    cases e with
    | forallE ty b bm =>
      rw [Expr.stripPis] at h
      cases hb : b.stripPis k with
      | none => rw [hb] at h; exact nomatch h
      | some p =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        show Expr.forallE ty b bm = Expr.forallE ty (mkPisB p.1 p.2) bm
        rw [← ih hb]
    | _ => simp [Expr.stripPis] at h

/-- Instantiating a telescope's binder domains, each at its own
depth. -/
def instTeleB (v : Expr) : Nat → List (Expr × BinderMeta) → List (Expr × BinderMeta)
  | _, [] => []
  | j, b :: bs => (b.1.instantiate1 v j, b.2) :: instTeleB v (j + 1) bs

theorem instTeleB_length (v : Expr) : ∀ (j : Nat) (bs : List (Expr × BinderMeta)),
    (instTeleB v j bs).length = bs.length
  | _, [] => rfl
  | j, b :: bs => by
    show (instTeleB v (j + 1) bs).length + 1 = bs.length + 1
    rw [instTeleB_length v (j + 1) bs]

/-- `instTeleB` maps the domains and keeps the metas, positionally
(task #315 U-19b: the reading law compares the auxiliary and the
restored telescopes' binder bits). -/
theorem instTeleB_getElem? (v : Expr) :
    ∀ (bs : List (Expr × BinderMeta)) (j k : Nat),
      (instTeleB v j bs)[k]? = bs[k]?.map fun b => (b.1.instantiate1 v (j + k), b.2)
  | [], _, _ => by simp [instTeleB]
  | _ :: _, _, 0 => by simp [instTeleB]
  | _ :: bs, j, k + 1 => by
    show (instTeleB v (j + 1) bs)[k]? = _
    rw [instTeleB_getElem? v bs (j + 1) k]
    simp only [List.getElem?_cons_succ]
    rw [show j + 1 + k = j + (k + 1) from by omega]

theorem mkPisB_instantiate1 (v : Expr) : ∀ (bs : List (Expr × BinderMeta)) (e : Expr)
    (j : Nat), (mkPisB bs e).instantiate1 v j
      = mkPisB (instTeleB v j bs) (e.instantiate1 v (j + bs.length))
  | [], e, j => rfl
  | b :: bs, e, j => by
    show Expr.forallE (b.1.instantiate1 v j) ((mkPisB bs e).instantiate1 v (j + 1)) b.2 = _
    rw [mkPisB_instantiate1 v bs e (j + 1)]
    show _ = Expr.forallE (b.1.instantiate1 v j)
      (mkPisB (instTeleB v (j + 1) bs) (e.instantiate1 v (j + (bs.length + 1)))) b.2
    rw [show j + 1 + bs.length = j + (bs.length + 1) from by omega]

/-- **The opening of a telescope depends only on its binders**: the
same openers, and the body opened at them. -/
theorem openPisAtFvars_mkPisB : ∀ (n : Nat) (bs : List (Expr × BinderMeta)),
    bs.length = n → ∀ (i : Nat),
    ∃ fvs : List Expr, fvs.length = n ∧ AllFvarsL fvs ∧
      ∀ Y : Expr, openPisAtFvars n (mkPisB bs Y) i
        = some (fvs, Expr.instSeq fvs (n - 1) Y) := by
  intro n
  induction n with
  | zero =>
    intro bs hbs i
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hbs
    exact ⟨[], rfl, ⟨fun v hv => absurd hv (by simp), fun Y => rfl⟩⟩
  | succ n ih =>
    intro bs hbs i
    cases bs with
    | nil => exact nomatch hbs
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hbs
      obtain ⟨fvs', hlen', hall', hlaw'⟩ :=
        ih (instTeleB (Expr.fvar i b.1) 0 bs)
          (by rw [instTeleB_length, hbs]) (i + 1)
      refine ⟨Expr.fvar i b.1 :: fvs', by simp [hlen'], ?_, fun Y => ?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact ⟨i, b.1, rfl⟩
        · exact hall' v hv'
      · show openPisAtFvars (n + 1) (Expr.forallE b.1 (mkPisB bs Y) b.2) i = _
        rw [openPisAtFvars, mkPisB_instantiate1 (Expr.fvar i b.1) bs Y 0,
          hlaw' (Y.instantiate1 (Expr.fvar i b.1) (0 + bs.length))]
        show some (Expr.fvar i b.1 :: fvs',
            Expr.instSeq fvs' (n - 1)
              (Y.instantiate1 (Expr.fvar i b.1) (0 + bs.length)))
          = some (Expr.fvar i b.1 :: fvs',
            Expr.instSeq fvs' (n + 1 - 1 - 1)
              (Y.instantiate1 (Expr.fvar i b.1) (n + 1 - 1)))
        rw [show 0 + bs.length = n + 1 - 1 from by omega,
          show n + 1 - 1 - 1 = n - 1 from by omega]

/-! ## Reading a substituted term's shape -/

/-- Under variable openers a `∀` was a `∀`. -/
theorem instSeq_forallE_inv : ∀ (vs : List Expr), AllFvarsL vs →
    ∀ (t : Nat) (e : Expr) {d b : Expr} {m : BinderMeta},
      Expr.instSeq vs t e = .forallE d b m → ∃ d₀ b₀, e = .forallE d₀ b₀ m := by
  intro vs
  induction vs with
  | nil => intro _ t e d b m h; exact ⟨_, _, h⟩
  | cons v vs ih =>
    intro hall t e d b m h
    have hv := hall v List.mem_cons_self
    obtain ⟨idx, ty, rfl⟩ := hv
    obtain ⟨d₀, b₀, he⟩ :=
      ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) (e.instantiate1 _ t) h
    cases e with
    | bvar i =>
      simp only [Expr.instantiate1] at he
      split at he
      · exact nomatch he
      · split at he <;> exact nomatch he
    | forallE d' b' m' =>
      simp only [Expr.instantiate1, Expr.forallE.injEq] at he
      exact ⟨d', b', by rw [he.2.2]⟩
    | _ => simp only [Expr.instantiate1] at he; exact nomatch he

/-- Under variable openers a constant head was a constant head. -/
theorem instSeq_getAppFn_const_inv : ∀ (vs : List Expr), AllFvarsL vs →
    ∀ (t : Nat) (e : Expr) {n : Name} {us : List Level},
      (Expr.instSeq vs t e).getAppFn = .const n us → e.getAppFn = .const n us := by
  intro vs
  induction vs with
  | nil => intro _ t e n us h; exact h
  | cons v vs ih =>
    intro hall t e n us h
    obtain ⟨idx, ty, rfl⟩ := hall v List.mem_cons_self
    exact Expr.getAppFn_const_of_instantiate1
      (ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) _ h)

/-- Opening maps a spine's arguments. -/
theorem instSeq_getAppArgs : ∀ (vs : List Expr), AllFvarsL vs →
    ∀ (t : Nat) (e : Expr),
      (Expr.instSeq vs t e).getAppArgs = e.getAppArgs.map (Expr.instSeq vs t ·) := by
  intro vs
  induction vs with
  | nil => intro _ t e; simp [Expr.instSeq]
  | cons v vs ih =>
    intro hall t e
    obtain ⟨idx, ty, rfl⟩ := hall v List.mem_cons_self
    show (Expr.instSeq vs (t - 1) (e.instantiate1 _ t)).getAppArgs = _
    rw [ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) (t - 1) _,
      Expr.getAppArgs_instantiate1_var, List.map_map]
    rfl

/-! ## Two bridge lemmas for the opening depth -/

/-- `instSeq` peels a `∀` at the telescope's own depth. -/
theorem instSeq_forallE_at {V : List Expr} {n : Nat} (hV : V.length = n) (d b : Expr)
    (m : BinderMeta) :
    Expr.instSeq V (n - 1) (.forallE d b m)
      = .forallE (Expr.instSeq V (n - 1) d) (Expr.instSeq V n b) m := by
  cases n with
  | zero =>
    obtain rfl : V = [] := List.eq_nil_of_length_eq_zero hV
    rfl
  | succ n =>
    rw [Expr.instSeq_forallE V (n + 1 - 1) d b m (by omega)]
    rfl

/-- One more opener lands at cut `0`. -/
theorem instSeq_snoc_at {V : List Expr} {n : Nat} (hV : V.length = n) (v X : Expr) :
    Expr.instSeq (V ++ [v]) n X = (Expr.instSeq V n X).instantiate1 v 0 := by
  rw [Expr.instSeq_append V [v] n X, hV, Nat.sub_self]
  rfl

/-- `instSeq_liftLooseBVars_prefix` with an OFFSET: the spine sits `off`
binders deeper (a reflexive constructor field's own `∀`-prefix), so the
lift is that much wider and the cut that much lower, and the prefix'
instantiations still land on the prefix. -/
theorem instSeq_liftLooseBVars_prefix_off :
    ∀ (pre rest : List Expr) (off : Nat) {q : Expr},
      (∀ a ∈ pre, a.looseBVarsBounded 0 = true) →
      q.looseBVarsBounded pre.length = true →
      Expr.instSeq (pre ++ rest) (pre.length + rest.length + off - 1)
          (q.liftLooseBVars (rest.length + off) 0)
        = Expr.instSeq pre (pre.length - 1) q := by
  intro pre
  induction pre with
  | nil =>
    intro rest off q _ hq
    have hq0 : q.looseBVarsBounded 0 = true := by simpa using hq
    show Expr.instSeq rest (0 + rest.length + off - 1)
        (q.liftLooseBVars (rest.length + off) 0) = q
    rw [Expr.liftLooseBVars_eq_self hq0, Expr.instSeq_eq_self _ _ hq0]
  | cons a pre' ih =>
    intro rest off q hpre hq
    have ha : a.looseBVarsBounded 0 = true := hpre a List.mem_cons_self
    have hq' : (q.instantiate1 a pre'.length).looseBVarsBounded pre'.length = true :=
      Expr.looseBVarsBounded_instantiate1_gen ha (by simpa using hq)
    show Expr.instSeq (pre' ++ rest) ((a :: pre').length + rest.length + off - 1 - 1)
        ((q.liftLooseBVars (rest.length + off) 0).instantiate1 a
          ((a :: pre').length + rest.length + off - 1))
      = Expr.instSeq pre' ((a :: pre').length - 1 - 1)
        (q.instantiate1 a ((a :: pre').length - 1))
    rw [show (a :: pre').length + rest.length + off - 1
        = pre'.length + (rest.length + off) from by simp; omega,
      show (a :: pre').length - 1 = pre'.length from by simp,
      Expr.liftLooseBVars_instantiate1 ha (Nat.zero_le _),
      show pre'.length + (rest.length + off) - 1
        = pre'.length + rest.length + off - 1 from by omega]
    exact ih rest off (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hq'

/-! ## A pin's fire, opened -/

/-- **The pin case.**  When the opened auxiliary domain is `auxJ p⃗ is`
with `auxJ` a pin key, the restored domain is the pin — instantiated at
the parameter openers, EXACTLY (the pin is closed over the block's
parameters, `hpinB`) — applied to the same index arguments. -/
theorem restoreOpen_pin_domain {R : RestoreTbl} (hk : R.KeysInAux) {nP j : Nat}
    (off : Nat) (hnP : R.nP = nP) {bad : Nat → Prop} {fvsP osA osR is : List Expr}
    {pin dA dR : Expr} {n : Name} {us : List Level}
    (hlenP : fvsP.length = nP) (hallP : AllFvarsL fvsP) (hlenR : osR.length = j)
    (hallVA : AllFvarsL (fvsP ++ osA))
    (hagree : RestoreOpenAgree bad (fvsP ++ osA) (fvsP ++ osR))
    (hfreeDom : ∀ idx, bad idx →
      (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA).mentionsFvar idx = false)
    (hpinB : pin.looseBVarsBounded nP = true)
    (hp : R.pins.lookup n = some pin) (hrec : R.recMap.lookup n = none)
    (hwd : restoreWalk R (j + off) dA = .ok dR)
    (hx : Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA
      = Expr.mkAppN (.const n us) (fvsP ++ is)) :
    Expr.instSeq (fvsP ++ osR) (nP + j + off - 1) dR
      = Expr.mkAppN (Expr.instSeq fvsP (nP - 1) pin) is := by
  -- the auxiliary domain is the same spine, one substitution earlier
  have hfnA : (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA).getAppFn = .const n us := by
    rw [hx, Expr.getAppFn_mkAppN]
    rfl
  have hfn : dA.getAppFn = .const n us :=
    instSeq_getAppFn_const_inv _ hallVA _ _ hfnA
  have hargs : dA.getAppArgs.map (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) ·) = fvsP ++ is := by
    rw [← instSeq_getAppArgs _ hallVA (nP + j + off - 1) dA, hx, Expr.getAppArgs_mkAppN]
    rfl
  have hlenArgs : dA.getAppArgs.length = nP + is.length := by
    have h := congrArg List.length hargs
    simpa [hlenP] using h
  have hdAshape : Expr.mkAppN (.const n us) dA.getAppArgs = dA := by
    rw [← hfn]; exact Expr.mkAppN_getApp dA
  -- the walk fires the pin
  have hfire := restoreWalk_pin (R := R) (d := j + off) (us := us) hp hrec (hk.1 n pin hp)
    (show R.nP ≤ dA.getAppArgs.length by rw [hnP, hlenArgs]; omega)
  rw [hdAshape] at hfire
  obtain rfl : Expr.mkAppN (pin.liftLooseBVars (j + off) 0) (dA.getAppArgs.drop R.nP) = dR :=
    Except.ok.inj (hfire.symm.trans hwd)
  rw [Expr.instSeq_mkAppN]
  have hhead : Expr.instSeq (fvsP ++ osR) (nP + j + off - 1) (pin.liftLooseBVars (j + off) 0)
      = Expr.instSeq fvsP (nP - 1) pin := by
    have h := instSeq_liftLooseBVars_prefix_off fvsP osR off hallP.bounded
      (by rw [hlenP]; exact hpinB)
    rw [hlenP, hlenR] at h
    exact h
  have hargsR : (dA.getAppArgs.drop R.nP).map (Expr.instSeq (fvsP ++ osR) (nP + j + off - 1) ·)
      = is := by
    have hcongr : (dA.getAppArgs.drop R.nP).map (Expr.instSeq (fvsP ++ osR) (nP + j + off - 1) ·)
        = (dA.getAppArgs.drop R.nP).map (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) ·) := by
      refine List.map_congr_left ?_
      intro a ha
      refine (instSeq_congr_of_agree (fvsP ++ osA) (fvsP ++ osR) (nP + j + off - 1) a
        hagree (fun idx hbad => ?_)).symm
      have hmem : Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) a ∈ fvsP ++ is := by
        rw [← hargs]
        exact List.mem_map_of_mem (List.mem_of_mem_drop ha)
      have hall := (mentionsFvar_mkAppN_false (fvsP ++ is) (.const n us)
        (by rw [← hx]; exact hfreeDom idx hbad)).2
      exact hall _ hmem
    rw [hcongr, List.map_drop, hargs, hnP, ← hlenP, List.drop_left]
  rw [hhead, hargsR]

/-- `instSeq_forallE_at` with an offset. -/
theorem instSeq_forallE_off {V : List Expr} {n : Nat} (hV : V.length = n) (off : Nat)
    (d b : Expr) (m : BinderMeta) :
    Expr.instSeq V (n + off - 1) (.forallE d b m)
      = .forallE (Expr.instSeq V (n + off - 1) d) (Expr.instSeq V (n + off) b) m := by
  cases hno : n + off with
  | zero =>
    obtain rfl : V = [] := List.eq_nil_of_length_eq_zero (by omega)
    rfl
  | succ k =>
    rw [Expr.instSeq_forallE V (k + 1 - 1) d b m (by omega)]
    rfl

/-- **The reflexive-pin case.**  The auxiliary domain is a `∀`-prefix of
auxiliary-free domains over a pin's spine (a reflexive constructor's
field); the restored domain is the same prefix over the pin at the
parameter openers. -/
theorem restoreOpen_pinRefl_domain {R : RestoreTbl} (hk : R.KeysInAux) {nP j : Nat}
    (hnP : R.nP = nP) {bad : Nat → Prop} {fvsP osA osR : List Expr}
    (hlenP : fvsP.length = nP) (hallP : AllFvarsL fvsP) (hlenR : osR.length = j)
    (hallVA : AllFvarsL (fvsP ++ osA))
    (hagree : RestoreOpenAgree bad (fvsP ++ osA) (fvsP ++ osR))
    (hlenVA : (fvsP ++ osA).length = nP + j) (hlenVR : (fvsP ++ osR).length = nP + j) :
    ∀ (L off : Nat) (dA dR : Expr) (tbs : List (Expr × BinderMeta))
      {n : Name} {us : List Level} {pin : Expr} {is : List Expr},
      restoreWalk R (j + off) dA = .ok dR →
      (∀ idx, bad idx →
        (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA).mentionsFvar idx = false) →
      (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA).stripPis L
        = some (tbs, Expr.mkAppN (.const n us) (fvsP ++ is)) →
      (∀ b ∈ tbs, ∀ n' ∈ R.auxNames, b.1.mentionsConst n' = false) →
      pin.looseBVarsBounded nP = true →
      R.pins.lookup n = some pin → R.recMap.lookup n = none →
      (Expr.instSeq (fvsP ++ osR) (nP + j + off - 1) dR).stripPis L
        = some (tbs, Expr.mkAppN (Expr.instSeq fvsP (nP - 1) pin) is) := by
  intro L
  induction L with
  | zero =>
    intro off dA dR tbs n us pin is hwd hfreeD hstrip _ hpinB hp hrec
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstrip
    obtain ⟨rfl, hbody⟩ := hstrip
    rw [restoreOpen_pin_domain hk off hnP hlenP hallP hlenR hallVA hagree hfreeD
      hpinB hp hrec hwd hbody]
    rfl
  | succ L ih =>
    intro off dA dR tbs n us pin is hwd hfreeD hstrip htbs hpinB hp hrec
    -- the auxiliary domain has a binder
    obtain ⟨dA', bB', bm, rfl⟩ : ∃ dA' bB' bm, dA = .forallE dA' bB' bm := by
      cases hcr : Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA
      case forallE d b mm =>
        obtain ⟨d₀, b₀, he⟩ :=
          instSeq_forallE_inv _ hallVA (nP + j + off - 1) dA hcr
        exact ⟨d₀, b₀, mm, he⟩
      all_goals (rw [hcr] at hstrip; simp [Expr.stripPis] at hstrip)
    rw [instSeq_forallE_off hlenVA off dA' bB' bm] at hstrip hfreeD
    obtain ⟨dR', bBR', hwd', hwb', rfl⟩ := restoreWalk_forallE_inv hwd
    -- the binder's domain and the body, separately
    have hfreeDom : ∀ idx, bad idx →
        (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA').mentionsFvar idx = false := by
      intro idx hbadi
      have h := hfreeD idx hbadi
      rw [Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at h
      exact h.1
    have hfreeBody : ∀ idx, bad idx →
        (Expr.instSeq (fvsP ++ osA) (nP + j + off) bB').mentionsFvar idx = false := by
      intro idx hbadi
      have h := hfreeD idx hbadi
      rw [Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at h
      exact h.2
    -- peel the binder off the strip
    rw [Expr.stripPis] at hstrip
    cases hsb : (Expr.instSeq (fvsP ++ osA) (nP + j + off) bB').stripPis L with
    | none => rw [hsb] at hstrip; exact nomatch hstrip
    | some q =>
      rw [hsb] at hstrip
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip
      obtain ⟨rfl, hq2⟩ := hstrip
      -- the binder's domain is auxiliary-free, hence its own restoration
      have hdomFree : ∀ n' ∈ R.auxNames,
          (Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA').mentionsConst n' = false :=
        htbs _ List.mem_cons_self
      have hdAfree : ∀ n' ∈ R.auxNames, dA'.mentionsConst n' = false := fun n' hn' =>
        mentionsConst_instSeq_false _ _ (hdomFree n' hn')
      have hdr : dR' = dA' :=
        (Except.ok.inj ((restoreWalk_of_no_aux (j + off) dA' hdAfree).symm.trans hwd')).symm
      have hdomEq : Expr.instSeq (fvsP ++ osR) (nP + j + off - 1) dR'
          = Expr.instSeq (fvsP ++ osA) (nP + j + off - 1) dA' := by
        rw [hdr]
        exact (instSeq_congr_of_agree (fvsP ++ osA) (fvsP ++ osR) (nP + j + off - 1) dA'
          hagree hfreeDom).symm
      -- the body, one binder deeper
      have hih := ih (off + 1) bB' bBR' q.1
        (by rw [show j + (off + 1) = j + off + 1 from by omega]; exact hwb')
        (by
          intro idx hbadi
          rw [show nP + j + (off + 1) - 1 = nP + j + off from by omega]
          exact hfreeBody idx hbadi)
        (by
          rw [show nP + j + (off + 1) - 1 = nP + j + off from by omega, hsb, ← hq2])
        (fun b hb => htbs b (List.mem_cons_of_mem _ hb)) hpinB hp hrec
      rw [show nP + j + (off + 1) - 1 = nP + j + off from by omega] at hih
      rw [instSeq_forallE_off hlenVR off dR' bBR' bm, Expr.stripPis, hih, hdomEq]
      rfl

/-! ## The field telescope -/

/-- **The field induction.**  At depth `j` under the parameters — `j`
fields opened, the openers `osA`/`osR` agreeing away from the variables
the block's positivity facts keep out of sight — the restored
telescope opens to the same residual, one restored domain per
auxiliary domain. -/
theorem restoreOpenFields {R : RestoreTbl} (hk : R.KeysInAux) {nP : Nat} (hnP : R.nP = nP)
    (hpinB : ∀ n pin, R.pins.lookup n = some pin → pin.looseBVarsBounded nP = true)
    {fvsP : List Expr} (hlenP : fvsP.length = nP) (hallP : AllFvarsL fvsP)
    {xrest : Expr} (hxrest : ∀ n ∈ R.auxNames, xrest.mentionsConst n = false) :
    ∀ (m j : Nat) (bA bR : Expr) (osA osR : List Expr) (bad : Nat → Prop)
      (xFvsA : List Expr),
      osA.length = j → osR.length = j → AllFvarsL osA → AllFvarsL osR →
      RestoreOpenAgree bad osA osR →
      (∀ idx, bad idx → idx < nP + j) →
      restoreWalk R j bA = .ok bR →
      (∀ idx, bad idx →
        (Expr.instSeq (fvsP ++ osA) (nP + j - 1) bA).mentionsFvar idx = false) →
      openPisAtFvars m (Expr.instSeq (fvsP ++ osA) (nP + j - 1) bA) (nP + j)
        = some (xFvsA, xrest) →
      (∀ (k : Nat) (x : Expr), xFvsA[k]? = some x →
        (∃ n ∈ R.auxNames, x.fvarTypeD.mentionsConst n = true) →
        (∀ y ∈ xFvsA.drop (k + 1), y.fvarTypeD.mentionsFvar (nP + j + k) = false) ∧
          xrest.mentionsFvar (nP + j + k) = false) →
      ∃ xFvsR : List Expr,
        openPisAtFvars m (Expr.instSeq (fvsP ++ osR) (nP + j - 1) bR) (nP + j)
          = some (xFvsR, xrest) ∧
        xFvsR.length = xFvsA.length ∧
        ∀ (k : Nat) (x : Expr), xFvsA[k]? = some x →
          ∃ ty', xFvsR[k]? = some (.fvar (nP + j + k) ty') ∧
            ((∀ n ∈ R.auxNames, x.fvarTypeD.mentionsConst n = false) → ty' = x.fvarTypeD) ∧
            (∀ (n : Name) (us : List Level) (pin : Expr) (is : List Expr),
              x.fvarTypeD = Expr.mkAppN (.const n us) (fvsP ++ is) →
              R.pins.lookup n = some pin → R.recMap.lookup n = none →
              ty' = Expr.mkAppN (Expr.instSeq fvsP (nP - 1) pin) is) ∧
            (∀ (L : Nat) (tbs : List (Expr × BinderMeta)) (n : Name) (us : List Level)
              (pin : Expr) (is : List Expr),
              x.fvarTypeD.stripPis L = some (tbs, Expr.mkAppN (.const n us) (fvsP ++ is)) →
              (∀ b ∈ tbs, ∀ n' ∈ R.auxNames, b.1.mentionsConst n' = false) →
              R.pins.lookup n = some pin → R.recMap.lookup n = none →
              ty'.stripPis L
                = some (tbs, Expr.mkAppN (Expr.instSeq fvsP (nP - 1) pin) is)) := by
  intro m
  induction m with
  | zero =>
    intro j bA bR osA osR bad xFvsA hlenA hlenR hallA hallR hagree hbadlt hwalk hfree hopA _
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hopA
    obtain ⟨rfl, hrest⟩ := hopA
    -- the residual mentions no auxiliary name, so the walk was the identity
    have hbAfree : ∀ n ∈ R.auxNames, bA.mentionsConst n = false := by
      intro n hn
      exact mentionsConst_instSeq_false _ _ (by rw [hrest]; exact hxrest n hn)
    have hbr : bR = bA :=
      (Except.ok.inj ((restoreWalk_of_no_aux j bA hbAfree).symm.trans hwalk)).symm
    refine ⟨[], ?_, rfl, fun k x hx => absurd hx (by simp)⟩
    rw [hbr, ← instSeq_congr_of_agree (fvsP ++ osA) (fvsP ++ osR) (nP + j - 1) bA
      (hagree.prefix fvsP) hfree, hrest]
    rfl
  | succ m ih =>
    intro j bA bR osA osR bad xFvsA hlenA hlenR hallA hallR hagree hbadlt hwalk hfree hopA hnodep
    have hlenVA : (fvsP ++ osA).length = nP + j := by
      rw [List.length_append, hlenP, hlenA]
    have hlenVR : (fvsP ++ osR).length = nP + j := by
      rw [List.length_append, hlenP, hlenR]
    have hallVA : AllFvarsL (fvsP ++ osA) := hallP.append hallA
    have hallVR : AllFvarsL (fvsP ++ osR) := hallP.append hallR
    -- the auxiliary telescope has a binder here
    obtain ⟨dA, bB, bm, rfl⟩ : ∃ dA bB bm, bA = .forallE dA bB bm := by
      cases hcr : Expr.instSeq (fvsP ++ osA) (nP + j - 1) bA
      case forallE d b mm =>
        obtain ⟨d₀, b₀, he⟩ :=
          instSeq_forallE_inv _ hallVA (nP + j - 1) bA hcr
        exact ⟨d₀, b₀, mm, he⟩
      all_goals (rw [hcr] at hopA; exact nomatch hopA)
    rw [instSeq_forallE_at hlenVA dA bB bm] at hopA hfree
    -- the walk's Π inversion
    obtain ⟨dR, bBR, hwd, hwb, rfl⟩ := restoreWalk_forallE_inv hwalk
    -- the two opened domains
    have hfreeDom : ∀ idx, bad idx →
        (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA).mentionsFvar idx = false := by
      intro idx hbadi
      have := hfree idx hbadi
      rw [Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at this
      exact this.1
    have hfreeBody : ∀ idx, bad idx →
        (Expr.instSeq (fvsP ++ osA) (nP + j) bB).mentionsFvar idx = false := by
      intro idx hbadi
      have := hfree idx hbadi
      rw [Expr.mentionsFvar_forallE, Bool.or_eq_false_iff] at this
      exact this.2
    -- an auxiliary-free domain restores to itself
    have hdomFree : (∀ n ∈ R.auxNames,
          (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA).mentionsConst n = false) →
        Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR
          = Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA := by
      intro hfreeC
      have hdAfree : ∀ n ∈ R.auxNames, dA.mentionsConst n = false := fun n hn =>
        mentionsConst_instSeq_false _ _ (hfreeC n hn)
      have hdr : dR = dA :=
        (Except.ok.inj ((restoreWalk_of_no_aux j dA hdAfree).symm.trans hwd)).symm
      rw [hdr]
      exact (instSeq_congr_of_agree (fvsP ++ osA) (fvsP ++ osR) (nP + j - 1) dA
        (hagree.prefix fvsP) hfreeDom).symm
    -- the opening step, on both sides
    rw [openPisAtFvars] at hopA
    cases hopA' : openPisAtFvars m
        ((Expr.instSeq (fvsP ++ osA) (nP + j) bB).instantiate1
          (.fvar (nP + j) (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA))) (nP + j + 1) with
    | none => rw [hopA'] at hopA; exact nomatch hopA
    | some p =>
      rw [hopA'] at hopA
      simp only [Option.some.injEq, Prod.mk.injEq] at hopA
      obtain ⟨rfl, rfl⟩ := hopA
      obtain ⟨tlA, rstA⟩ := p
      -- the two new openers, and the extended bad set
      have hconvA : Expr.instSeq
            (fvsP ++ (osA ++ [Expr.fvar (nP + j)
              (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA)])) (nP + (j + 1) - 1) bB
          = (Expr.instSeq (fvsP ++ osA) (nP + j) bB).instantiate1
              (Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA)) := by
        rw [← List.append_assoc, show nP + (j + 1) - 1 = nP + j from by omega,
          instSeq_snoc_at hlenVA _ bB]
      have hconvR : Expr.instSeq
            (fvsP ++ (osR ++ [Expr.fvar (nP + j)
              (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR)])) (nP + (j + 1) - 1) bBR
          = (Expr.instSeq (fvsP ++ osR) (nP + j) bBR).instantiate1
              (Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR)) := by
        rw [← List.append_assoc, show nP + (j + 1) - 1 = nP + j from by omega,
          instSeq_snoc_at hlenVR _ bBR]
      have hagree' : RestoreOpenAgree
          (fun idx => bad idx ∨ (idx = nP + j ∧
            (R.auxNames.any fun nn =>
              (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA).mentionsConst nn) = true))
          (osA ++ [Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA)])
          (osR ++ [Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR)]) := by
        refine (hagree.mono (fun idx h => Or.inl h)).snoc ?_
        rcases Bool.eq_false_or_eq_true (R.auxNames.any fun nn =>
          (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA).mentionsConst nn) with hany | hany
        · exact Or.inr ⟨nP + j, _, _, rfl, rfl, Or.inr ⟨rfl, hany⟩⟩
        · exact Or.inl (by rw [hdomFree (auxNames_mention_false hany)])
      have hfree' : ∀ idx,
          (bad idx ∨ (idx = nP + j ∧
            (R.auxNames.any fun nn =>
              (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA).mentionsConst nn) = true)) →
          (Expr.instSeq (fvsP ++ (osA ++ [Expr.fvar (nP + j)
              (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA)])) (nP + (j + 1) - 1)
            bB).mentionsFvar idx = false := by
        intro idx hidx
        rw [hconvA]
        rcases hidx with hidx | ⟨rfl, hany⟩
        · refine mentionsFvar_instantiate1_of_false ?_ (hfreeBody idx hidx)
          have hne : (nP + j == idx) = false := by
            have hlt := hbadlt idx hidx
            simp only [beq_eq_false_iff_ne, ne_eq]
            omega
          rw [Expr.mentionsFvar_fvar, hne, hfreeDom idx hidx]
          rfl
        · obtain ⟨nn, hnn, hmen⟩ := List.any_eq_true.mp hany
          obtain ⟨hlater, hrst⟩ := hnodep 0 _ rfl ⟨nn, hnn, hmen⟩
          exact openPisAtFvars_mentionsFvar_false m hopA'
            (fun y hy => by simpa using hlater y (by simpa using hy))
            (by simpa using hrst)
      obtain ⟨xFvsR, hopR, hlenEq, hclaims⟩ := ih (j + 1) bB bBR
        (osA ++ [Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA)])
        (osR ++ [Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR)])
        (fun idx => bad idx ∨ (idx = nP + j ∧
          (R.auxNames.any fun nn =>
            (Expr.instSeq (fvsP ++ osA) (nP + j - 1) dA).mentionsConst nn) = true))
        tlA (by simp [hlenA]) (by simp [hlenR])
        (hallA.append (AllFvarsL.singleton _ _)) (hallR.append (AllFvarsL.singleton _ _))
        hagree'
        (by
          intro idx hidx
          rcases hidx with hidx | ⟨rfl, -⟩
          · have := hbadlt idx hidx; omega
          · omega)
        hwb hfree'
        (by rw [hconvA, show nP + (j + 1) = nP + j + 1 from by omega]; exact hopA')
        (by
          intro k x hx haux
          obtain ⟨h1, h2⟩ := hnodep (k + 1) x (by simpa using hx) haux
          rw [show nP + (j + 1) + k = nP + j + (k + 1) from by omega]
          exact ⟨fun y hy => h1 y (by simpa using hy), h2⟩)
      refine ⟨Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR) :: xFvsR,
        ?_, by simp [hlenEq], ?_⟩
      · rw [instSeq_forallE_at hlenVR dR bBR bm, openPisAtFvars]
        rw [show (Expr.instSeq (fvsP ++ osR) (nP + j) bBR).instantiate1
              (Expr.fvar (nP + j) (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR))
            = Expr.instSeq (fvsP ++ (osR ++ [Expr.fvar (nP + j)
                (Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR)])) (nP + (j + 1) - 1) bBR
          from hconvR.symm]
        rw [show nP + j + 1 = nP + (j + 1) from by omega, hopR]
      · intro k x hx
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          obtain rfl := hx
          refine ⟨Expr.instSeq (fvsP ++ osR) (nP + j - 1) dR, by simp, ?_, ?_, ?_⟩
          · intro hfreeC
            exact hdomFree hfreeC
          · intro nn us pin is hxx hp hrec
            exact restoreOpen_pin_domain hk 0 hnP hlenP hallP hlenR hallVA
              (hagree.prefix fvsP) hfreeDom (hpinB nn pin hp) hp hrec hwd hxx
          · intro L tbs nn us pin is hstrip htbs hp hrec
            exact restoreOpen_pinRefl_domain hk hnP hlenP hallP hlenR hallVA
              (hagree.prefix fvsP) hlenVA hlenVR L 0 dA dR tbs hwd hfreeDom hstrip htbs
              (hpinB nn pin hp) hp hrec
        | succ k =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨ty', hk', ha, hb, hc⟩ := hclaims k x hx
          refine ⟨ty', ?_, ha, hb, hc⟩
          rw [List.getElem?_cons_succ, hk',
            show nP + (j + 1) + k = nP + j + (k + 1) from by omega]

/-! ## The theorem -/

/-- **The restored constructor, opened.**  `restoreNested` leaves the
parameter prefix alone, so the restored type opens at the SAME
parameter variables; the field telescope opens to one variable per
auxiliary field and to the SAME residual; and each restored domain is
the auxiliary one when that mentions no auxiliary name, and the pin at
the parameter openers applied to the index arguments when the
auxiliary one is a pin's spine.

`hpinB` is the pins' own closure fact (`pinsClosed`): a pin lives in
the block's parameter context.  With it the pin clause is an EQUALITY,
not an equality up to annotations — the parameter openers the two
sides instantiate at are literally the same `fvsP`. -/
theorem restoreNested_opened {R : RestoreTbl} (hk : R.KeysInAux) {nP nF : Nat}
    (hnP : R.nP = nP)
    (hpinB : ∀ n pin, R.pins.lookup n = some pin → pin.looseBVarsBounded nP = true)
    {tyA tyR : Expr} {fvsP : List Expr} {crestA : Expr} {xFvsA : List Expr} {xrest : Expr}
    (hopP : openPisAtFvars nP tyA 0 = some (fvsP, crestA))
    (hopX : openPisAtFvars nF crestA nP = some (xFvsA, xrest))
    (hres : restoreNested R tyA = .ok tyR)
    (hxrest : ∀ n ∈ R.auxNames, xrest.mentionsConst n = false)
    (hnodep : ∀ (i : Nat) (x : Expr), xFvsA[i]? = some x →
      (∃ n ∈ R.auxNames, x.fvarTypeD.mentionsConst n = true) →
      (∀ y ∈ xFvsA.drop (i + 1), y.fvarTypeD.mentionsFvar (nP + i) = false) ∧
        xrest.mentionsFvar (nP + i) = false) :
    ∃ (crestR : Expr) (xFvsR : List Expr),
      openPisAtFvars nP tyR 0 = some (fvsP, crestR) ∧
      openPisAtFvars nF crestR nP = some (xFvsR, xrest) ∧
      xFvsR.length = xFvsA.length ∧
      ∀ (i : Nat) (x : Expr), xFvsA[i]? = some x →
        ∃ ty', xFvsR[i]? = some (.fvar (nP + i) ty') ∧
          ((∀ n ∈ R.auxNames, x.fvarTypeD.mentionsConst n = false) → ty' = x.fvarTypeD) ∧
          (∀ (n : Name) (us : List Level) (pin : Expr) (is : List Expr),
            x.fvarTypeD = Expr.mkAppN (.const n us) (fvsP ++ is) →
            R.pins.lookup n = some pin → R.recMap.lookup n = none →
            ty' = Expr.mkAppN (Expr.instSeq fvsP (nP - 1) pin) is) ∧
            (∀ (L : Nat) (tbs : List (Expr × BinderMeta)) (n : Name) (us : List Level)
              (pin : Expr) (is : List Expr),
              x.fvarTypeD.stripPis L = some (tbs, Expr.mkAppN (.const n us) (fvsP ++ is)) →
              (∀ b ∈ tbs, ∀ n' ∈ R.auxNames, b.1.mentionsConst n' = false) →
              R.pins.lookup n = some pin → R.recMap.lookup n = none →
              ty'.stripPis L
                = some (tbs, Expr.mkAppN (Expr.instSeq fvsP (nP - 1) pin) is)) := by
  -- the parameter prefix, read off the opener
  obtain ⟨bs, bodyA, hstrip, hlenP, hidx, -⟩ := Verify.openPisAtFvars_stripPis nP hopP
  have hallP : AllFvarsL fvsP := by
    intro v hv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hv
    have hilt : i < nP := by
      rw [← hlenP]
      rcases Nat.lt_or_ge i fvsP.length with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none hge] at hi; exact nomatch hi
    obtain ⟨ty, hty⟩ := hidx i hilt
    rw [hi] at hty
    exact ⟨0 + i, ty, Option.some.inj hty⟩
  have hbslen : bs.length = nP := Expr.stripPis_length nP hstrip
  have htyA : tyA = mkPisB bs bodyA := stripPis_mkPisB nP hstrip
  -- the walk under the prefix, and the rebuilt telescope
  obtain ⟨bodyR, hwalk0, htyR⟩ := restoreNested_pis (R := R) (e := tyA) (e' := tyR)
    (bs := bs) (body := bodyA) (by rw [hnP]; exact hstrip)
    (by
      intro hpos
      rw [hnP] at hpos
      cases bs with
      | nil =>
        rw [← hbslen] at hpos
        simp at hpos
      | cons b bs' => exact ⟨b.1, mkPisB bs' bodyA, b.2, by rw [htyA]; rfl⟩)
    hres
  rw [mkPisB_eq_foldr] at htyR
  -- the two openings of the prefix
  obtain ⟨fvs, hlenfvs, hallfvs, hlaw⟩ := openPisAtFvars_mkPisB nP bs hbslen 0
  have hlawA := hlaw bodyA
  rw [← htyA, hopP] at hlawA
  simp only [Option.some.injEq, Prod.mk.injEq] at hlawA
  obtain ⟨rfl, rfl⟩ := hlawA
  have hlawR : openPisAtFvars nP tyR 0
      = some (fvsP, Expr.instSeq fvsP (nP - 1) bodyR) := by
    rw [htyR]; exact hlaw bodyR
  -- the field telescope
  obtain ⟨xFvsR, hopR, hlenEq, hclaims⟩ := restoreOpenFields hk hnP hpinB hlenP hallP
    hxrest nF 0 bodyA bodyR [] [] (fun _ => False) xFvsA rfl rfl
    (fun v hv => absurd hv (by simp)) (fun v hv => absurd hv (by simp))
    ⟨rfl, fun k v w hv _ => absurd hv (by simp)⟩
    (fun idx h => absurd h (by simp))
    hwalk0 (fun idx h => absurd h (by simp))
    (by rw [List.append_nil, Nat.add_zero]; exact hopX)
    (by
      intro i x hx haux
      rw [Nat.add_zero]
      exact hnodep i x hx haux)
  rw [List.append_nil, Nat.add_zero] at hopR
  refine ⟨Expr.instSeq fvsP (nP - 1) bodyR, xFvsR, hlawR, hopR, hlenEq, ?_⟩
  intro i x hx
  obtain ⟨ty', hk', ha, hb, hc⟩ := hclaims i x hx
  rw [Nat.add_zero] at hk'
  exact ⟨ty', hk', ha, hb, hc⟩

end ConLeche
