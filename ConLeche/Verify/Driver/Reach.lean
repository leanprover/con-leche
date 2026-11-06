module

public import ConLeche.Driver.Reach
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Frontend.ModelIO
import ConLeche.Verify.Cached.GuardsC

/-!
# The reach's context: closed, well formed

What `ConLeche/Driver/Reach.lean` gives, proved:

* `needsGo_spec`, `constsResolve_of_needs`, `recordReads_scoped` — **what a record reads**:
  where every name `recordReads d` lists is stored in `R`, the record is
  `RecordScoped R` (`ConLeche/Modular.lean`), and its tables' structures are stored;
* `reachGo_inv`, `reachGo_closed` — **the reach's closure**: at every outcome of the
  worklist that is an accept, on any snapshot, every name a context record reads is
  installed by a context record, so every context record is `RecordScoped` in the
  context (`streamEnv` of the records);
* `constOk_wf`, `tableOk_wf`, `ctx_envWF` — **the context is well formed**: a closed list of
  validated records (`recordOk`) installs an `EnvWF` environment;
* `reach_ok` — the three at every accepting outcome of `reach`.

That a copy read is the specification's constant at its position is
`ConLeche/Verify/Frontend/Olean/Present.lean`'s (`entryWith_of_view`, `stmtWith_of_view`).
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean

/-! ## What an expression reads -/

/-- **`Expr.needs` is what `constsResolve` asks.** -/
theorem constsResolve_of_needs {R : Env} :
    ∀ {e : Expr}, (∀ n ∈ e.needs, (R.find? n).isSome = true) → e.constsResolve R = true
  | .bvar _, _ | .sort _, _ => rfl
  | .lit (.natVal _), h => by
    simp only [Expr.needs, litNeeds, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h
    simp [Expr.constsResolve, h]
  | .lit (.strVal _), h => by
    simp only [Expr.needs, litNeeds, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at h
    simp [Expr.constsResolve, h]
  | .const n _, h => by simpa [Expr.needs, Expr.constsResolve] using h
  | .fvar _ ty, h => by
    simp only [Expr.constsResolve]; exact constsResolve_of_needs (by simpa [Expr.needs] using h)
  | .app f a, h => by
    simp only [Expr.needs, List.mem_append] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_of_needs fun n hn => h n (.inl hn),
      constsResolve_of_needs fun n hn => h n (.inr hn)⟩
  | .lam ty b, h => by
    simp only [Expr.needs, List.mem_append] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_of_needs fun n hn => h n (.inl hn),
      constsResolve_of_needs fun n hn => h n (.inr hn)⟩
  | .forallE ty b, h => by
    simp only [Expr.needs, List.mem_append] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_of_needs fun n hn => h n (.inl hn),
      constsResolve_of_needs fun n hn => h n (.inr hn)⟩
  | .letE ty v b, h => by
    simp only [Expr.needs, List.mem_append] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨constsResolve_of_needs fun n hn => h n (.inl (.inl hn)),
      constsResolve_of_needs fun n hn => h n (.inl (.inr hn))⟩,
      constsResolve_of_needs fun n hn => h n (.inr hn)⟩
  | .proj s _ x, h => by
    simp only [Expr.needs, List.mem_cons, forall_eq_or_imp] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨h.1, constsResolve_of_needs h.2⟩

theorem mem_appendList {α : Type} {a : α} {xs : Array α} {l : List α} :
    a ∈ xs ++ l ↔ a ∈ xs ∨ a ∈ l := by
  simp only [Array.mem_def, Array.toList_appendList, List.mem_append]

/-- An expression's names are among `acc`. -/
@[expose] def Covers (acc : Array Name) (e : Expr) : Prop := ∀ n ∈ e.needs, n ∈ acc

/-- **The walk's invariant**: every subterm walked has its names among the names so far. -/
@[expose] def NeedsInv (x : NeedsSt) : Prop := ∀ e, x.1.contains e = true → Covers x.2 e

theorem Covers.mono {a b : Array Name} {e : Expr} (h : Covers a e) (hs : ∀ n ∈ a, n ∈ b) :
    Covers b e := fun n hn => hs n (h n hn)

private theorem needsInv_insert {seen : Std.HashSet Expr} {acc : Array Name} {e : Expr}
    (hi : NeedsInv (seen, acc)) (hc : Covers acc e) : NeedsInv (seen.insert e, acc) := by
  intro k hk
  simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hk
  rcases hk with rfl | hk
  · exact hc
  · exact hi k hk

/-- What the walk of one expression gives. -/
abbrev NeedsStep (x y : NeedsSt) (e : Expr) : Prop :=
  NeedsInv y ∧ (∀ n ∈ x.2, n ∈ y.2) ∧ Covers y.2 e

private theorem step_compound {seen s' : Std.HashSet Expr} {acc a' : Array Name} {e : Expr}
    (hi : NeedsInv (s', a')) (hs : ∀ n ∈ acc, n ∈ a') (hc : Covers a' e) :
    NeedsStep (seen, acc) (s'.insert e, a') e :=
  ⟨needsInv_insert hi hc, hs, hc⟩

/-- **The memoized walk covers the expression**, keeps the invariant and only adds names. -/
theorem needsGo_spec :
    ∀ (e : Expr) (seen : Std.HashSet Expr) (acc : Array Name), NeedsInv (seen, acc) →
      NeedsStep (seen, acc) (needsGo seen acc e) e := by
  intro e
  induction e with
  | bvar i => intro seen acc hi; exact ⟨hi, fun _ h => h, fun n hn => by simp [Expr.needs] at hn⟩
  | sort u => intro seen acc hi; exact ⟨hi, fun _ h => h, fun n hn => by simp [Expr.needs] at hn⟩
  | const n us =>
    intro seen acc hi
    refine ⟨fun k hk => (hi k hk).mono fun _ h => Array.mem_push_of_mem _ h,
      fun _ h => Array.mem_push_of_mem _ h, fun m hm => ?_⟩
    simp only [Expr.needs, List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm; exact Array.mem_push_self
  | lit l =>
    intro seen acc hi
    have hs : ∀ n ∈ acc, n ∈ acc ++ litNeeds l := fun n h => mem_appendList.2 (.inl h)
    refine ⟨fun k hk => (hi k hk).mono hs, hs, fun m hm => ?_⟩
    exact mem_appendList.2 (.inr (by simpa [Expr.needs] using hm))
  | fvar i ty ih =>
    intro seen acc hi
    rw [needsGo]
    split
    · rename_i hc; exact ⟨hi, fun _ h => h, hi _ hc⟩
    · obtain ⟨h1, h2, h3⟩ := ih seen acc hi
      exact step_compound h1 h2 (by simpa [Covers, Expr.needs] using h3)
  | app f a ihf iha =>
    intro seen acc hi
    rw [needsGo]
    split
    · rename_i hc; exact ⟨hi, fun _ h => h, hi _ hc⟩
    · obtain ⟨h1, h2, h3⟩ := ihf seen acc hi
      obtain ⟨h4, h5, h6⟩ := iha _ _ h1
      refine step_compound h4 (fun n h => h5 n (h2 n h)) fun n hn => ?_
      simp only [Expr.needs, List.mem_append] at hn
      rcases hn with hn | hn
      · exact h5 n (h3 n hn)
      · exact h6 n hn
  | lam ty b iht ihb =>
    intro seen acc hi
    rw [needsGo]
    split
    · rename_i hc; exact ⟨hi, fun _ h => h, hi _ hc⟩
    · obtain ⟨h1, h2, h3⟩ := iht seen acc hi
      obtain ⟨h4, h5, h6⟩ := ihb _ _ h1
      refine step_compound h4 (fun n h => h5 n (h2 n h)) fun n hn => ?_
      simp only [Expr.needs, List.mem_append] at hn
      rcases hn with hn | hn
      · exact h5 n (h3 n hn)
      · exact h6 n hn
  | forallE ty b iht ihb =>
    intro seen acc hi
    rw [needsGo]
    split
    · rename_i hc; exact ⟨hi, fun _ h => h, hi _ hc⟩
    · obtain ⟨h1, h2, h3⟩ := iht seen acc hi
      obtain ⟨h4, h5, h6⟩ := ihb _ _ h1
      refine step_compound h4 (fun n h => h5 n (h2 n h)) fun n hn => ?_
      simp only [Expr.needs, List.mem_append] at hn
      rcases hn with hn | hn
      · exact h5 n (h3 n hn)
      · exact h6 n hn
  | letE ty v b iht ihv ihb =>
    intro seen acc hi
    rw [needsGo]
    split
    · rename_i hc; exact ⟨hi, fun _ h => h, hi _ hc⟩
    · obtain ⟨h1, h2, h3⟩ := iht seen acc hi
      obtain ⟨h4, h5, h6⟩ := ihv _ _ h1
      obtain ⟨h7, h8, h9⟩ := ihb _ _ h4
      refine step_compound h7 (fun n h => h8 n (h5 n (h2 n h))) fun n hn => ?_
      simp only [Expr.needs, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact h8 n (h5 n (h3 n hn))
      · exact h8 n (h6 n hn)
      · exact h9 n hn
  | proj s i x ih =>
    intro seen acc hi
    rw [needsGo]
    split
    · rename_i hc; exact ⟨hi, fun _ h => h, hi _ hc⟩
    · have hi' : NeedsInv (seen, acc.push s) :=
        fun k hk => (hi k hk).mono fun _ h => Array.mem_push_of_mem _ h
      obtain ⟨h1, h2, h3⟩ := ih seen _ hi'
      refine step_compound h1 (fun n h => h2 n (Array.mem_push_of_mem _ h)) fun n hn => ?_
      simp only [Expr.needs, List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact h2 n Array.mem_push_self
      · exact h3 n hn

/-! ## What a record reads -/

theorem NeedsSt.expr_spec {x : NeedsSt} (hi : NeedsInv x) (e : Expr) :
    NeedsStep x (x.expr e) e :=
  needsGo_spec e x.1 x.2 hi

theorem NeedsSt.names_spec {x : NeedsSt} (hi : NeedsInv x) (ns : List Name) :
    NeedsInv (x.names ns) ∧ (∀ n ∈ x.2, n ∈ (x.names ns).2) ∧ ∀ n ∈ ns, n ∈ (x.names ns).2 := by
  have hs : ∀ n ∈ x.2, n ∈ (x.names ns).2 := fun n h => mem_appendList.2 (.inl h)
  exact ⟨fun k hk => (hi k hk).mono hs, hs, fun n h => mem_appendList.2 (.inr h)⟩

/-- `x` grows into `y`, keeping the invariant. -/
abbrev Grows (x y : NeedsSt) : Prop := NeedsInv y ∧ ∀ n ∈ x.2, n ∈ y.2

theorem Grows.trans {x y z : NeedsSt} (h₁ : Grows x y) (h₂ : Grows y z) : Grows x z :=
  ⟨h₂.1, fun n h => h₂.2 n (h₁.2 n h)⟩

theorem foldl_expr_spec :
    ∀ (es : List Expr) {x : NeedsSt}, NeedsInv x →
      Grows x (es.foldl NeedsSt.expr x) ∧ ∀ e ∈ es, Covers (es.foldl NeedsSt.expr x).2 e
  | [], x, hi => ⟨⟨hi, fun _ h => h⟩, by simp⟩
  | e :: es, x, hi => by
    obtain ⟨h1, h2, h3⟩ := x.expr_spec hi e
    obtain ⟨⟨h4, h5⟩, h6⟩ := foldl_expr_spec es h1
    refine ⟨⟨h4, fun n h => h5 n (h2 n h)⟩, fun e' he' => ?_⟩
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact h3.mono h5
    · exact h6 e' he'

/-- **A rule's names are among `acc`**: its right-hand side's, its constructor, a nested
datum's pins'. -/
@[expose] def RuleCovered (acc : Array Name) (r : RecRule) : Prop :=
  Covers acc r.rhs ∧ r.ctor ∈ acc ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ p ∈ pins, Covers acc p

/-- **A constant's laws' names are among `acc`** (`EntryScoped`'s). -/
@[expose] def ConstCovered (acc : Array Name) (ci : ConstantInfo) : Prop :=
  Covers acc ci.toConstantVal.type ∧
  (∀ cv v h, ci = .defnInfo cv v h → Covers acc v) ∧
  (∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ r ∈ rules, RuleCovered acc r) ∧
  (∀ cv caps, ci = .indInfo cv caps →
    (∀ m ∈ caps.all, m ∈ acc) ∧ (caps.eta = true → caps.etaCtor ∈ acc)) ∧
  ∀ d ∈ pinFootprint ci.toConstantVal.name, d ∈ acc

/-- **A table's names are among `acc`**: its structure, its constructor, its bodies'. -/
@[expose] def TableCovered (acc : Array Name) (t : ProjTable) : Prop :=
  t.structName ∈ acc ∧ t.ctor ∈ acc ∧ ∀ b ∈ t.bodies.toList, Covers acc b

theorem RuleCovered.mono {a b : Array Name} {r : RecRule} (h : RuleCovered a r)
    (hs : ∀ n ∈ a, n ∈ b) : RuleCovered b r :=
  ⟨h.1.mono hs, hs _ h.2.1, fun l p hf q hq => (h.2.2 l p hf q hq).mono hs⟩

theorem ConstCovered.mono {a b : Array Name} {ci : ConstantInfo} (h : ConstCovered a ci)
    (hs : ∀ n ∈ a, n ∈ b) : ConstCovered b ci :=
  ⟨h.1.mono hs, fun cv v hh e => (h.2.1 cv v hh e).mono hs,
    fun cv mI rP isK rules e r hr => (h.2.2.1 cv mI rP isK rules e r hr).mono hs,
    fun cv caps e => ⟨fun m hm => hs _ ((h.2.2.2.1 cv caps e).1 m hm),
      fun he => hs _ ((h.2.2.2.1 cv caps e).2 he)⟩,
    fun d hd => hs _ (h.2.2.2.2 d hd)⟩

theorem TableCovered.mono {a b : Array Name} {t : ProjTable} (h : TableCovered a t)
    (hs : ∀ n ∈ a, n ∈ b) : TableCovered b t :=
  ⟨hs _ h.1, hs _ h.2.1, fun x hx => (h.2.2 x hx).mono hs⟩

theorem NeedsSt.rule_spec {x : NeedsSt} (hi : NeedsInv x) (r : RecRule) :
    Grows x (x.rule r) ∧ RuleCovered (x.rule r).2 r := by
  obtain ⟨h1, h2, h3⟩ := x.expr_spec hi r.rhs
  obtain ⟨h4, h5, h6⟩ := (x.expr r.rhs).names_spec h1 [r.ctor]
  have base : Grows x ((x.expr r.rhs).names [r.ctor]) ∧
      RuleCovered ((x.expr r.rhs).names [r.ctor]).2 { r with fire := .plain } :=
    ⟨⟨h4, fun n h => h5 n (h2 n h)⟩, h3.mono h5, h6 _ (by simp), fun _ _ hf => nomatch hf⟩
  unfold NeedsSt.rule
  split
  · rename_i lvls pins hf
    obtain ⟨⟨h7, h8⟩, h9⟩ := foldl_expr_spec pins h4
    refine ⟨⟨h7, fun n h => h8 n (h5 n (h2 n h))⟩, (h3.mono h5).mono h8, h8 _ (h6 _ (by simp)),
      fun l p hf' q hq => ?_⟩
    rw [hf] at hf'
    cases hf'
    exact h9 q hq
  · rename_i hn
    exact ⟨base.1, base.2.1, base.2.2.1, fun l p hf => absurd hf (hn l p)⟩

theorem foldl_rule_spec :
    ∀ (rs : List RecRule) {x : NeedsSt}, NeedsInv x →
      Grows x (rs.foldl NeedsSt.rule x) ∧ ∀ r ∈ rs, RuleCovered (rs.foldl NeedsSt.rule x).2 r
  | [], x, hi => ⟨⟨hi, fun _ h => h⟩, by simp⟩
  | r :: rs, x, hi => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := x.rule_spec hi r
    obtain ⟨⟨h4, h5⟩, h6⟩ := foldl_rule_spec rs h1
    refine ⟨⟨h4, fun n h => h5 n (h2 n h)⟩, fun r' hr' => ?_⟩
    simp only [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact h3.mono h5
    · exact h6 r' hr'

theorem NeedsSt.const_spec {x : NeedsSt} (hi : NeedsInv x) (ci : ConstantInfo) :
    Grows x (x.const ci) ∧ ConstCovered (x.const ci).2 ci := by
  obtain ⟨h1, h2, h3⟩ := x.expr_spec hi ci.toConstantVal.type
  -- what the middle part gives, a fold of the type's state `y` and the footprint
  have fin : ∀ y : NeedsSt, NeedsInv y → (∀ n ∈ (x.expr ci.toConstantVal.type).2, n ∈ y.2) →
      x.const ci = y.names (pinFootprint ci.toConstantVal.name) →
      (∀ cv v h, ci = .defnInfo cv v h → Covers y.2 v) →
      (∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ r ∈ rules, RuleCovered y.2 r) →
      (∀ cv caps, ci = .indInfo cv caps →
        (∀ m ∈ caps.all, m ∈ y.2) ∧ (caps.eta = true → caps.etaCtor ∈ y.2)) →
      Grows x (x.const ci) ∧ ConstCovered (x.const ci).2 ci := by
    intro y m1 m2 hc m3 m4 m5
    obtain ⟨k1, k2, k3⟩ := y.names_spec m1 (pinFootprint ci.toConstantVal.name)
    rw [hc]
    exact ⟨⟨k1, fun n h => k2 n (m2 n (h2 n h))⟩, (h3.mono m2).mono k2,
      fun cv v hh e => (m3 cv v hh e).mono k2,
      fun cv mI rP isK rules e r hr => (m4 cv mI rP isK rules e r hr).mono k2,
      fun cv caps e => ⟨fun m hm => k2 _ ((m5 cv caps e).1 m hm),
        fun he => k2 _ ((m5 cv caps e).2 he)⟩, k3⟩
  cases ci with
  | defnInfo cv v hh =>
    obtain ⟨g1, g2, g3⟩ := (x.expr _).expr_spec h1 v
    refine fin _ g1 g2 rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e; exact g3
    · intro _ _ _ _ _ e; cases e
    · intro _ _ e; cases e
  | recInfo cv mI rP isK rules =>
    obtain ⟨⟨g1, g2⟩, g3⟩ := foldl_rule_spec rules h1
    refine fin _ g1 g2 rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e; exact g3
    · intro _ _ e; cases e
  | indInfo cv caps =>
    obtain ⟨g1, g2, g3⟩ := (x.expr _).names_spec h1
      (caps.all ++ if caps.eta then [caps.etaCtor] else [])
    refine fin _ g1 g2 rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e
    · intro _ _ e
      cases e
      exact ⟨fun m hm => g3 m (List.mem_append_left _ hm),
        fun he => g3 _ (List.mem_append_right _ (by simp [he]))⟩
  | axiomInfo cv =>
    refine fin _ h1 (fun _ h => h) rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e
    · intro _ _ e; cases e
  | thmInfo cv =>
    refine fin _ h1 (fun _ h => h) rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e
    · intro _ _ e; cases e
  | ctorInfo cv _ _ =>
    refine fin _ h1 (fun _ h => h) rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e
    · intro _ _ e; cases e

theorem NeedsSt.table_spec {x : NeedsSt} (hi : NeedsInv x) (t : ProjTable) :
    Grows x (x.table t) ∧ TableCovered (x.table t).2 t := by
  obtain ⟨h1, h2, h3⟩ := x.names_spec hi [t.structName, t.ctor]
  obtain ⟨⟨h4, h5⟩, h6⟩ := foldl_expr_spec t.bodies.toList h1
  exact ⟨⟨h4, fun n h => h5 n (h2 n h)⟩, h5 _ (h3 _ (by simp)), h5 _ (h3 _ (by simp)), h6⟩

theorem foldl_const_spec :
    ∀ (cs : List ConstantInfo) {x : NeedsSt}, NeedsInv x →
      Grows x (cs.foldl NeedsSt.const x) ∧ ∀ c ∈ cs, ConstCovered (cs.foldl NeedsSt.const x).2 c
  | [], x, hi => ⟨⟨hi, fun _ h => h⟩, by simp⟩
  | c :: cs, x, hi => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := x.const_spec hi c
    obtain ⟨⟨h4, h5⟩, h6⟩ := foldl_const_spec cs h1
    refine ⟨⟨h4, fun n h => h5 n (h2 n h)⟩, fun c' hc' => ?_⟩
    simp only [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact h3.mono h5
    · exact h6 c' hc'

theorem foldl_table_spec :
    ∀ (ts : List ProjTable) {x : NeedsSt}, NeedsInv x →
      Grows x (ts.foldl NeedsSt.table x) ∧ ∀ t ∈ ts, TableCovered (ts.foldl NeedsSt.table x).2 t
  | [], x, hi => ⟨⟨hi, fun _ h => h⟩, by simp⟩
  | t :: ts, x, hi => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := x.table_spec hi t
    obtain ⟨⟨h4, h5⟩, h6⟩ := foldl_table_spec ts h1
    refine ⟨⟨h4, fun n h => h5 n (h2 n h)⟩, fun t' ht' => ?_⟩
    simp only [List.mem_cons] at ht'
    rcases ht' with rfl | ht'
    · exact h3.mono h5
    · exact h6 t' ht'

/-- **`recordReads` lists every name a record's constants and tables read.** -/
theorem recordReads_covers (d : Declaration) :
    (∀ ci ∈ declConstants d, ConstCovered (recordReads d) ci) ∧
    ∀ t ∈ declTables d, TableCovered (recordReads d) t := by
  have h0 : NeedsInv (({} : Std.HashSet Expr), (#[] : Array Name)) := fun k hk => by simp at hk
  obtain ⟨⟨h1, _⟩, h2⟩ := foldl_const_spec (declConstants d) h0
  obtain ⟨⟨_, h4⟩, h5⟩ := foldl_table_spec (declTables d) h1
  exact ⟨fun ci hc => (h2 ci hc).mono h4, h5⟩

/-- **Where every name a record reads is stored, the record is `RecordScoped`.** -/
theorem recordReads_scoped {R : Env} {d : Declaration}
    (h : ∀ n ∈ recordReads d, (R.find? n).isSome = true) : RecordScoped R d := by
  obtain ⟨hc, ht⟩ := recordReads_covers d
  have cov : ∀ {e : Expr}, Covers (recordReads d) e → e.constsResolve R = true :=
    fun hv => constsResolve_of_needs fun n hn => h n (hv n hn)
  refine ⟨fun ci hci => ?_, fun t hti => ?_⟩
  · obtain ⟨c1, c2, c3, c4, c5⟩ := hc ci hci
    refine ⟨cov c1, fun cv v hh e => cov (c2 cv v hh e), ?_, fun cv caps e => ?_,
      fun x hx => h x (c5 x hx)⟩
    · intro cv mI rP isK rules e r hr
      obtain ⟨r1, r2, r3⟩ := c3 cv mI rP isK rules e r hr
      exact ⟨cov r1, h _ r2, fun lvls pins hf p hp => cov (r3 lvls pins hf p hp)⟩
    · exact ⟨fun m hm => h m ((c4 cv caps e).1 m hm), fun he => h _ ((c4 cv caps e).2 he)⟩
  · obtain ⟨t1, t2, t3⟩ := ht t hti
    exact ⟨h _ t2, fun b hb => cov (t3 b hb)⟩

/-- The structure of a record's table is among its reads. -/
theorem recordReads_table {d : Declaration} {t : ProjTable} (h : t ∈ declTables d) :
    t.structName ∈ recordReads d :=
  ((recordReads_covers d).2 t h).1

end ConLeche.Driver

/-! ## The worklist's closure -/

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean

/-- **The worklist's invariant**: every name a record read so far reads has been pushed;
every pushed name is stored or still to read; every stored name is a record's. -/
@[expose] def ReachInv (L : ReachLog) : Prop :=
  (∀ d ∈ L.ctx, ∀ y ∈ recordReads d, L.seen.contains y = true) ∧
  (∀ y, L.seen.contains y = true → L.stored.contains y = true ∨ y ∈ L.stack) ∧
  (∀ y, L.stored.contains y = true → ∃ d ∈ L.ctx, y ∈ declNames d)

theorem pushNames_spec :
    ∀ (ys : List Name) (seen : Std.HashSet Name) (stack : List Name),
      (∀ y ∈ ys, (pushNames seen stack ys).1.contains y = true) ∧
      (∀ y, (pushNames seen stack ys).1.contains y = true →
        seen.contains y = true ∨ y ∈ (pushNames seen stack ys).2) ∧
      (∀ y ∈ stack, y ∈ (pushNames seen stack ys).2) ∧
      (∀ y, seen.contains y = true → (pushNames seen stack ys).1.contains y = true)
  | [], seen, stack => ⟨by simp, fun y h => .inl h, fun _ h => h, fun _ h => h⟩
  | y :: ys, seen, stack => by
    simp only [pushNames]
    split
    · rename_i hy
      obtain ⟨a, b, c, d⟩ := pushNames_spec ys seen stack
      refine ⟨fun z hz => ?_, b, c, d⟩
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact d _ hy
      · exact a z hz
    · rename_i hy
      obtain ⟨a, b, c, d⟩ := pushNames_spec ys (seen.insert y) (y :: stack)
      have hins : ∀ z, seen.contains z = true → (seen.insert y).contains z = true := fun z h => by
        simp [Std.HashSet.contains_insert, h]
      refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => c z (List.mem_cons_of_mem _ hz),
        fun z h => d z (hins z h)⟩
      · simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact d _ (by simp [Std.HashSet.contains_insert])
        · exact a z hz
      · rcases b z hz with h | h
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
          rcases h with rfl | h
          · exact .inr (c _ (List.mem_cons_self))
          · exact .inl h
        · exact .inr h

theorem foldl_insert_contains :
    ∀ (l : List Name) (s : Std.HashSet Name) (y : Name),
      (l.foldl (fun s n => s.insert n) s).contains y = true ↔ s.contains y = true ∨ y ∈ l
  | [], s, y => by simp
  | n :: l, s, y => by
    simp only [List.foldl_cons, foldl_insert_contains l, Std.HashSet.contains_insert,
      Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h

/-- **A record added keeps the invariant**, where it declares the name popped. -/
theorem ReachInv.add {L : ReachLog} {x : Name} {rest : List Name} (hi : ReachInv L)
    (hs : L.stack = x :: rest) {d : Declaration} (hx : x ∈ declNames d) (h : Name) :
    ReachInv (L.add d h (recordReads d).toList rest) := by
  obtain ⟨i1, i2, i3⟩ := hi
  obtain ⟨p1, p2, p3, p4⟩ := pushNames_spec (recordReads d).toList L.seen rest
  simp only [ReachLog.add]
  refine ⟨fun d' hd' y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rcases Array.mem_push.1 hd' with hd' | rfl
    · exact p4 y (i1 d' hd' y hy)
    · exact p1 y (Array.mem_toList_iff.2 hy)
  · rcases p2 y hy with hy | hy
    · rcases i2 y hy with h' | h'
      · exact .inl ((foldl_insert_contains _ _ _).2 (.inl h'))
      · rw [hs] at h'
        rcases List.mem_cons.1 h' with rfl | h'
        · exact .inl ((foldl_insert_contains _ _ _).2 (.inr hx))
        · exact .inr (p3 y h')
    · exact .inr hy
  · rcases (foldl_insert_contains _ _ _).1 hy with hy | hy
    · obtain ⟨d', hd', hy'⟩ := i3 y hy
      exact ⟨d', Array.mem_push_of_mem _ hd', hy'⟩
    · exact ⟨d, Array.mem_push_self, hy⟩

/-- A name popped that is stored: the invariant without it on the stack. -/
theorem ReachInv.skip {L : ReachLog} {x : Name} {rest : List Name} (hi : ReachInv L)
    (hs : L.stack = x :: rest) (hx : L.stored.contains x = true) :
    ReachInv { L with stack := rest } := by
  obtain ⟨i1, i2, i3⟩ := hi
  refine ⟨i1, fun y hy => ?_, i3⟩
  rcases i2 y hy with h | h
  · exact .inl h
  · rw [hs] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl hx
    · exact .inr h

/-- **The worklist's closure**: at every accepting outcome, on any snapshot, the invariant
holds with nothing left to read. -/
theorem reachGo_inv (env : ReachEnv) (fs : FS) :
    ∀ (fuel : Nat) (L : ReachLog) (c : ReachCache) {L' : ReachLog} {c' : ReachCache},
      ReachInv L → (reachGo env fuel L c : ModelIO _) fs (.ok (.ok (L', c'))) →
        ReachInv L' ∧ L'.stack = [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro L c L' c' hi h
    rw [reachGo] at h
    cases hs : L.stack with
    | nil =>
      simp only [hs, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hi, hs⟩
    | cons x rest => simp [hs] at h
  | succ fuel ih =>
    intro L c L' c' hi h
    rw [reachGo] at h
    cases hs : L.stack with
    | nil =>
      simp only [hs, ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hi, hs⟩
    | cons x rest =>
      simp only [hs] at h
      split at h
      · rename_i hx
        exact ih _ _ (hi.skip hs hx) h
      · simp only [ModelIO.bind_ok] at h
        obtain ⟨⟨c₁, r⟩, -, h⟩ := h
        rcases r with e | ⟨d, hm⟩
        · simp at h
        · simp only at h
          split at h
          · simp at h
          · rename_i hx
            split at h
            · simp at h
            · simp only [ModelIO.bind_ok] at h
              obtain ⟨⟨c₂, r⟩, -, h⟩ := h
              rcases r with e | u
              · simp at h
              · simp only at h
                exact ih _ _ (hi.add hs (by simpa using hx) hm) h

/-- The constants of a list's environment are its records'. -/
theorem mem_streamEnv_consts {ci : ConstantInfo} :
    ∀ (ds : List Declaration) (env : Env),
      ci ∈ (streamEnv ds env).consts ↔ (∃ d ∈ ds, ci ∈ declConstants d) ∨ ci ∈ env.consts
  | [], env => by simp [streamEnv]
  | d :: ds, env => by
    simp only [streamEnv, List.foldl_cons] at *
    rw [show List.foldl (fun e pd => e.pushDelta (declConstants pd) (declTables pd))
        (env.pushDelta (declConstants d) (declTables d)) ds =
      streamEnv ds (env.pushDelta (declConstants d) (declTables d)) from rfl,
      mem_streamEnv_consts ds]
    simp only [Env.pushDelta, List.mem_append, List.mem_reverse, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-- The tables of a list's environment are its records'. -/
theorem mem_streamEnv_tables {t : ProjTable} :
    ∀ (ds : List Declaration) (env : Env),
      t ∈ (streamEnv ds env).tables ↔ (∃ d ∈ ds, t ∈ declTables d) ∨ t ∈ env.tables
  | [], env => by simp [streamEnv]
  | d :: ds, env => by
    simp only [streamEnv, List.foldl_cons] at *
    rw [show List.foldl (fun e pd => e.pushDelta (declConstants pd) (declTables pd))
        (env.pushDelta (declConstants d) (declTables d)) ds =
      streamEnv ds (env.pushDelta (declConstants d) (declTables d)) from rfl,
      mem_streamEnv_tables ds]
    simp only [Env.pushDelta, List.mem_append, List.mem_reverse, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-- A name a record of a list declares is stored in the list's environment. -/
theorem streamEnv_find_of_mem {ds : List Declaration} {d : Declaration} (hd : d ∈ ds)
    {y : Name} (hy : y ∈ declNames d) : ((streamEnv ds).find? y).isSome = true := by
  simp only [declNames, List.mem_map] at hy
  obtain ⟨ci, hci, rfl⟩ := hy
  simp only [Env.find?, List.find?_isSome]
  exact ⟨ci, (mem_streamEnv_consts ds _).2 (.inl ⟨d, hd, hci⟩), by
    cases ci <;> simp [ConstantInfo.name]⟩

/-- **The reach's closure, at its records**: at an accepting outcome of the worklist from
a state satisfying the invariant, every name a context record reads is stored in the
context, and every context record is `RecordScoped` there. -/
theorem reachGo_closed (env : ReachEnv) (fs : FS) {fuel : Nat} {L L' : ReachLog}
    {c c' : ReachCache} (hi : ReachInv L)
    (h : (reachGo env fuel L c : ModelIO _) fs (.ok (.ok (L', c')))) :
    ∀ d ∈ L'.ctx.toList, (∀ y ∈ recordReads d, ((streamEnv L'.ctx.toList).find? y).isSome = true) ∧
      RecordScoped (streamEnv L'.ctx.toList) d := by
  obtain ⟨⟨i1, i2, i3⟩, hs⟩ := reachGo_inv env fs fuel L c hi h
  have hr : ∀ d ∈ L'.ctx.toList, ∀ y ∈ recordReads d,
      ((streamEnv L'.ctx.toList).find? y).isSome = true := by
    intro d hd y hy
    rcases i2 y (i1 d (Array.mem_toList_iff.1 hd) y hy) with h' | h'
    · obtain ⟨d', hd', hy'⟩ := i3 y h'
      exact streamEnv_find_of_mem (Array.mem_toList_iff.2 hd') hy'
    · rw [hs] at h'; cases h'
  exact fun d hd => ⟨hr d hd, recordReads_scoped (hr d hd)⟩

end ConLeche.Driver

/-! ## The context is well formed -/

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Frontend.Olean

theorem exprOk_iff {lps : List Name} {k : Nat} {e : Expr} :
    exprOk lps k e = true ↔
      e.hasFvar = false ∧ e.allLevelParamsDefined lps = true ∧ e.looseBVarsBounded k = true := by
  unfold exprOk
  rw [Expr.allLevelParamsDefinedC_spec]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨fun ⟨⟨a, c⟩, b⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, c⟩, b⟩⟩

/-- A nested rule's datum, validated, reads off its recursor's type wherever its pins
resolve. -/
theorem nestedOk_read {res : Expr → Bool} {lps : List Name} {ty : Expr} {mI rP : Nat}
    {lvls : List Level} {pins : List Expr} (h : nestedOk lps ty mI rP lvls pins = true)
    (hr : ∀ pin ∈ pins, res pin = true) :
    NestedRead res lps ty mI rP pins.length lvls pins := by
  unfold nestedOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hle, hl⟩, hp⟩, hm⟩ := h
  refine ⟨hle, hl, fun pin hpin => ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := exprOk_iff.1 (hp pin hpin)
    exact ⟨a, b, hr pin hpin, c⟩
  · split at hm
    · rename_i pre dom body hs
      split at hm
      · rename_i D ls hD
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        obtain ⟨rfl, ha⟩ := hm
        exact ⟨pre, dom, body, D, hs, hD, ha, rfl⟩
      · simp at hm
    · simp at hm

/-- **A validated constant is `ConstWF`** wherever its laws' names resolve. -/
theorem constOk_wf {env : Env} {c : ConstantInfo} (h : constOk c = true)
    (hr : EntryScoped env c) : ConstWF env c := by
  obtain ⟨hr1, hr2, hr3, -, -⟩ := hr
  cases c with
  | defnInfo cv v hint =>
    simp only [constOk, Bool.and_eq_true] at h
    obtain ⟨a, b, c⟩ := exprOk_iff.1 h.1
    obtain ⟨a', b', c'⟩ := exprOk_iff.1 h.2
    refine ⟨a, b, hr1, c, ?_, ?_⟩
    · intro cv' v' h' e
      cases e
      exact ⟨a', b', hr2 _ _ _ rfl, c'⟩
    · intro _ _ _ _ _ e; cases e
  | recInfo cv mI rP isK rules =>
    simp only [constOk, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨a, b, c⟩ := exprOk_iff.1 h.1
    refine ⟨a, b, hr1, c, ?_, ?_⟩
    · intro _ _ _ e; cases e
    intro cv' mI' rP' isK' rules' e
    cases e
    intro r hrm
    have hrule := h.2 r hrm
    unfold ruleOk at hrule
    simp only [Bool.and_eq_true] at hrule
    obtain ⟨a', b', c'⟩ := exprOk_iff.1 hrule.1
    obtain ⟨hres, -, hpins⟩ := hr3 _ _ _ _ _ rfl r hrm
    refine ⟨a', b', hres, c', fun lvls pins hf => ?_⟩
    have hn := hrule.2
    rw [hf] at hn
    exact nestedOk_read hn (hpins lvls pins hf)
  | axiomInfo cv | thmInfo cv | indInfo cv _ | ctorInfo cv _ _ =>
    obtain ⟨a, b, c⟩ := exprOk_iff.1 h
    refine ⟨a, b, hr1, c, ?_, ?_⟩
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e

/-- **A validated table is `TableWF`** where its structure is stored and its bodies
resolve. -/
theorem tableOk_wf {env : Env} {t : ProjTable} (h : tableOk t = true)
    (hs : (env.find? t.structName).isSome = true)
    (hr : ∀ b ∈ t.bodies.toList, b.constsResolve env = true) : TableWF env t := by
  unfold tableOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  refine ⟨hs, h.1, fun i b hb => ?_⟩
  have hm : b ∈ t.bodies := Array.mem_of_getElem? hb
  obtain ⟨a, b', c⟩ := exprOk_iff.1 (h.2 b hm)
  exact ⟨a, b', hr b (Array.mem_toList_iff.2 hm), c⟩

/-- **A closed list of validated records installs a well-formed environment**: where every
record passes `recordOk` and every name a record reads is stored, `streamEnv` of the list
is `EnvWF`. -/
theorem ctx_envWF {ds : List Declaration} (hok : ∀ d ∈ ds, recordOk d = true)
    (hcl : ∀ d ∈ ds, ∀ y ∈ recordReads d, ((streamEnv ds).find? y).isSome = true) :
    EnvWF (streamEnv ds) := by
  have hsc : ∀ d ∈ ds, RecordScoped (streamEnv ds) d := fun d hd => recordReads_scoped (hcl d hd)
  have hd' : ∀ d ∈ ds, (∀ c ∈ declConstants d, constOk c = true ∧ litShapeOk c = true) ∧
      ∀ t ∈ declTables d, tableOk t = true := by
    intro d hd
    have h := hok d hd
    simp only [recordOk, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨h.1, h.2⟩
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun t ht => ?_⟩
  · rcases (mem_streamEnv_consts ds _).1 hc with ⟨d, hd, hcd⟩ | h
    · exact constOk_wf ((hd' d hd).1 c hcd).1 ((hsc d hd).1 c hcd)
    · simp [Env.empty] at h
  · rcases (mem_streamEnv_consts ds _).1 hc with ⟨d, hd, hcd⟩ | h
    · exact ((hd' d hd).1 c hcd).2
    · simp [Env.empty] at h
  · rcases (mem_streamEnv_tables ds _).1 ht with ⟨d, hd, htd⟩ | h
    · exact tableOk_wf ((hd' d hd).2 t htd) (hcl d hd _ (recordReads_table htd))
        ((hsc d hd).2 t htd).2
    · simp [Env.empty] at h

/-- The validation's pass is `recordOk` of every record. -/
theorem validateCtx_ok {ds : Array Declaration} {hs : Array Name}
    (h : validateCtx ds hs = .ok ()) : ∀ d ∈ ds.toList, recordOk d = true := by
  unfold validateCtx at h
  split at h
  · rename_i ha
    intro d hd
    exact (Array.all_eq_true_iff_forall_mem.1 ha) d (Array.mem_toList_iff.1 hd)
  · split at h <;> simp at h

/-- The worklist starts in its invariant. -/
theorem reachInv_init (rs : List Name) : ReachInv (ReachLog.init rs) := by
  refine ⟨fun d hd => by simp [ReachLog.init] at hd, fun z hz => ?_,
    fun z hz => by simp [ReachLog.init] at hz⟩
  rcases (pushNames_spec rs {} []).2.1 z hz with h' | h'
  · simp at h'
  · exact .inr h'

/-- **The reach's context is closed and well formed**: at every accepting outcome of
`reach`, on any snapshot, every context record is `RecordScoped` in the context, every
name it reads is stored there, and the context is `EnvWF`. -/
theorem reach_ok {sp : SearchPath} {m : Name} {wr : WorkerReads} {own : Std.HashSet Name}
    {roots : Array Name} {fs : FS} {r : Reach}
    (h : (reach sp m wr own roots : ModelIO _) fs (.ok (.ok r))) :
    (∀ d ∈ r.ctx.toList, RecordScoped (streamEnv r.ctx.toList) d) ∧
    (∀ d ∈ r.ctx.toList, ∀ y ∈ recordReads d, ((streamEnv r.ctx.toList).find? y).isSome = true) ∧
    EnvWF (streamEnv r.ctx.toList) := by
  unfold reach at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨⟨c, x⟩, -, h⟩ := h
  rcases x with e | extra
  · simp at h
  simp only at h
  generalize List.find? _ _ = q at h
  cases q with
  | some x => simp at h
  | none =>
    simp only [ModelIO.bind_ok] at h
    obtain ⟨y, hy, h⟩ := h
    rcases y with e | ⟨L, c'⟩
    · simp at h
    simp only at h
    cases hv : validateCtx L.ctx L.homes with
    | error e => simp [hv] at h
    | ok u =>
    cases hf : inferFlags (mkFEnv (streamEnv L.ctx.toList)) c'.pending.toList with
    | error e => simp [hv, hf] at h
    | ok u' =>
    simp only [hv, hf, ModelIO.pure_iff, Except.ok.injEq] at h
    subst h
    have hc := reachGo_closed _ fs (reachInv_init _) hy
    have hcl := fun d hd => (hc d hd).1
    exact ⟨fun d hd => (hc d hd).2, hcl, ctx_envWF (validateCtx_ok hv) hcl⟩

end ConLeche.Driver

