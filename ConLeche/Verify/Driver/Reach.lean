module

public import ConLeche.Driver.Reach
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Frontend.ModelIO
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.Cached.OpsC

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
* `readOrder_spec`, `readOrder_perm`, `readOrder_ordered` — **the read order**: the sorted
  records are the reach's, permuted, and every one is `RecordScoped` in the prefix ending with it
  (`ImportOk.ordered`);
* `reach_ok` — all of these at every accepting outcome of `reach`.

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
  (∀ cv caps, ci = .indInfo cv caps → ∀ m ∈ caps.all, m ∈ acc) ∧
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
    fun cv caps e m hm => hs _ (h.2.2.2.1 cv caps e m hm),
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
      (∀ cv caps, ci = .indInfo cv caps → ∀ m ∈ caps.all, m ∈ y.2) →
      Grows x (x.const ci) ∧ ConstCovered (x.const ci).2 ci := by
    intro y m1 m2 hc m3 m4 m5
    obtain ⟨k1, k2, k3⟩ := y.names_spec m1 (pinFootprint ci.toConstantVal.name)
    rw [hc]
    exact ⟨⟨k1, fun n h => k2 n (m2 n (h2 n h))⟩, (h3.mono m2).mono k2,
      fun cv v hh e => (m3 cv v hh e).mono k2,
      fun cv mI rP isK rules e r hr => (m4 cv mI rP isK rules e r hr).mono k2,
      fun cv caps e m hm => k2 _ (m5 cv caps e m hm), k3⟩
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
    obtain ⟨g1, g2, g3⟩ := (x.expr _).names_spec h1 caps.all
    refine fin _ g1 g2 rfl ?_ ?_ ?_
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e
    · intro _ _ e
      cases e
      exact g3
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
    · exact fun m hm => h m (c4 cv caps e m hm)
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

/-- **The worklist's invariant** from the roots `rs`: every name a record read so far reads
has been pushed; every pushed name is stored or still to read; every stored name is a record's;
every root has been pushed; the reads recorded are the records'. -/
@[expose] def ReachInv (rs : List Name) (L : ReachLog) : Prop :=
  (∀ d ∈ L.ctx, ∀ y ∈ recordReads d, L.seen.contains y = true) ∧
  (∀ y, L.seen.contains y = true → L.stored.contains y = true ∨ y ∈ L.stack) ∧
  (∀ y, L.stored.contains y = true → ∃ d ∈ L.ctx, y ∈ declNames d) ∧
  (∀ y ∈ rs, L.seen.contains y = true) ∧
  L.reads = L.ctx.map fun d => (recordReads d).toList

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
theorem ReachInv.add {rs : List Name} {L : ReachLog} {x : Name} {rest : List Name}
    (hi : ReachInv rs L) (hs : L.stack = x :: rest) {d : Declaration} (hx : x ∈ declNames d)
    (h : Name) : ReachInv rs (L.add d h (recordReads d).toList rest) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hi
  obtain ⟨p1, p2, p3, p4⟩ := pushNames_spec (recordReads d).toList L.seen rest
  simp only [ReachLog.add]
  refine ⟨fun d' hd' y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => p4 y (i4 y hy),
    by rw [i5, Array.map_push]⟩
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
theorem ReachInv.skip {rs : List Name} {L : ReachLog} {x : Name} {rest : List Name}
    (hi : ReachInv rs L) (hs : L.stack = x :: rest) (hx : L.stored.contains x = true) :
    ReachInv rs { L with stack := rest } := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hi
  refine ⟨i1, fun y hy => ?_, i3, i4, i5⟩
  rcases i2 y hy with h | h
  · exact .inl h
  · rw [hs] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl hx
    · exact .inr h

/-- Names pushed where the stack is empty: the invariant kept. -/
theorem ReachInv.push {rs : List Name} {L : ReachLog} (hi : ReachInv rs L) (hs : L.stack = [])
    (ns : List Name) :
    ReachInv rs { L with seen := (pushNames L.seen [] ns).1, stack := (pushNames L.seen [] ns).2 } := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hi
  obtain ⟨-, p2, -, p4⟩ := pushNames_spec ns L.seen []
  refine ⟨fun d hd y hy => p4 y (i1 d hd y hy), fun y hy => ?_, i3, fun y hy => p4 y (i4 y hy), i5⟩
  rcases p2 y hy with h | h
  · rcases i2 y h with h' | h'
    · exact .inl h'
    · rw [hs] at h'; cases h'
  · exact .inr h

/-- **The worklist's closure**: at every accepting outcome, on any snapshot, the invariant
holds with nothing left to read. -/
theorem reachGo_inv (env : ReachEnv ModelIO) (fs : FS) (rs : List Name) :
    ∀ (fuel : Nat) (L : ReachLog) (c : ReachCache) {L' : ReachLog} {c' : ReachCache} {ho ho' : HS},
      ReachInv rs L → (reachGo env fuel L c : ModelIO _) fs ho (.ok (.ok (L', c'))) ho' →
        ReachInv rs L' ∧ L'.stack = [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro L c L' c' ho ho' hi h
    rw [reachGo] at h
    cases hs : L.stack with
    | nil =>
      simp only [hs] at h
      split at h
      · simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        exact ⟨hi, hs⟩
      · simp at h
    | cons x rest => simp [hs] at h
  | succ fuel ih =>
    intro L c L' c' ho ho' hi h
    rw [reachGo] at h
    cases hs : L.stack with
    | nil =>
      simp only [hs] at h
      split at h
      · simp only [ModelIO.pure_iff, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        exact ⟨hi, hs⟩
      · simp only [ModelIO.bind_ok] at h
        obtain ⟨⟨c₁, r⟩, _, -, h⟩ := h
        rcases r with e | u
        · simp at h
        · simp only at h
          exact ih _ _ (hi.push hs _) h
    | cons x rest =>
      simp only [hs] at h
      split at h
      · rename_i hx
        exact ih _ _ (hi.skip hs hx) h
      · simp only [ModelIO.bind_ok] at h
        obtain ⟨⟨c₁, r⟩, _, -, h⟩ := h
        rcases r with e | ⟨d, hm⟩
        · simp at h
        · simp only at h
          split at h
          · simp at h
          · rename_i hx
            split at h
            · simp at h
            · simp only [ModelIO.bind_ok] at h
              obtain ⟨⟨c₂, r⟩, _, -, h⟩ := h
              rcases r with e | u
              · simp at h
              · simp only [ModelIO.bind_ok] at h
                obtain ⟨⟨c₃, r⟩, _, -, h⟩ := h
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
theorem reachGo_closed (env : ReachEnv ModelIO) (fs : FS) {rs : List Name} {fuel : Nat}
    {L L' : ReachLog} {c c' : ReachCache} (hi : ReachInv rs L)
    {ho ho' : HS} (h : (reachGo env fuel L c : ModelIO _) fs ho (.ok (.ok (L', c'))) ho') :
    ∀ d ∈ L'.ctx.toList, (∀ y ∈ recordReads d, ((streamEnv L'.ctx.toList).find? y).isSome = true) ∧
      RecordScoped (streamEnv L'.ctx.toList) d := by
  obtain ⟨⟨i1, i2, i3, -, -⟩, hs⟩ := reachGo_inv env fs rs fuel L c hi h
  have hr : ∀ d ∈ L'.ctx.toList, ∀ y ∈ recordReads d,
      ((streamEnv L'.ctx.toList).find? y).isSome = true := by
    intro d hd y hy
    rcases i2 y (i1 d (Array.mem_toList_iff.1 hd) y hy) with h' | h'
    · obtain ⟨d', hd', hy'⟩ := i3 y h'
      exact streamEnv_find_of_mem (Array.mem_toList_iff.2 hd') hy'
    · rw [hs] at h'; cases h'
  exact fun d hd => ⟨hr d hd, recordReads_scoped (hr d hd)⟩

/-- **The reach's closure, at its roots**: at an accepting outcome of the worklist from a state
satisfying the invariant from the roots `rs`, every root is stored in the context. -/
theorem reachGo_roots (env : ReachEnv ModelIO) (fs : FS) {rs : List Name} {fuel : Nat}
    {L L' : ReachLog} {c c' : ReachCache} (hi : ReachInv rs L)
    {ho ho' : HS} (h : (reachGo env fuel L c : ModelIO _) fs ho (.ok (.ok (L', c'))) ho') :
    ∀ y ∈ rs, ((streamEnv L'.ctx.toList).find? y).isSome = true := by
  obtain ⟨⟨-, i2, i3, i4, -⟩, hs⟩ := reachGo_inv env fs rs fuel L c hi h
  intro y hy
  rcases i2 y (i4 y hy) with h' | h'
  · obtain ⟨d', hd', hy'⟩ := i3 y h'
    exact streamEnv_find_of_mem (Array.mem_toList_iff.2 hd') hy'
  · rw [hs] at h'; cases h'

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
        simp only [Bool.and_eq_true, beq_iff_eq, Expr.liftLooseBVarsC_spec] at hm
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
  | ctorInfo cv _ _ _ =>
    simp only [constOk, Bool.and_eq_true] at h
    obtain ⟨a, b, c⟩ := exprOk_iff.1 h.1
    refine ⟨a, b, hr1, c, ?_, ?_⟩
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e
  | axiomInfo cv | thmInfo cv | indInfo cv _ =>
    obtain ⟨a, b, c⟩ := exprOk_iff.1 h
    refine ⟨a, b, hr1, c, ?_, ?_⟩
    · intro _ _ _ e; cases e
    · intro _ _ _ _ _ e; cases e

/-- **A validated constant's family name is its type's** (`CtorWF`). -/
theorem constOk_ctorWF {c : ConstantInfo} (h : constOk c = true) : CtorWF c := by
  cases c with
  | ctorInfo cv nP nF T =>
    simp only [constOk, Bool.and_eq_true] at h
    have h2 := h.2
    unfold ctorHeadOk at h2
    split at h2
    · rename_i T' us hT
      rw [beq_iff_eq] at h2
      subst h2
      exact CtorWF.of_head hT
    · exact nomatch h2
  | _ => exact CtorWF.of_not_ctor fun _ _ _ _ h => nomatch h

theorem blockRecs_not_ind {p : BlockShape} :
    ∀ {rs : List RecShape} {cv : ConstantVal} {caps : IndCaps},
      ConstantInfo.indInfo cv caps ∈ blockRecs p rs → False
  | [], _, _, h => by simp [blockRecs] at h
  | _ :: _, _, _, h => by
    simp only [blockRecs, List.mem_cons] at h
    rcases h with h | h
    · exact nomatch h
    · exact blockRecs_not_ind h

/-- A quotient pin keeps no sort fact. -/
theorem quotAt_indWF (k : QuotKind) (cv : ConstantVal) : IndWF (quotAt k cv) := by
  intro cv' caps h hn
  cases k <;> simp [quotAt, quotPin, ConstantInfo.atLps, BasisKind.decls, QuotKind.slot,
    quotBasis, quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] at h
  obtain ⟨-, rfl⟩ := h
  exact nomatch hn

/-- **Every former a record installs keeps its sort fact** (`IndWF`): the install records a
family as never zero exactly where its declared type ends in such a sort. -/
theorem declConstants_indWF {d : Declaration} {c : ConstantInfo} (h : c ∈ declConstants d) :
    IndWF c := by
  cases d with
  | defnDecl | thmDecl | opaqueDecl =>
    simp only [declConstants, List.mem_singleton] at h
    subst h; exact IndWF.of_not_ind fun _ _ h => nomatch h
  | axiomDecl cv =>
    simp only [declConstants] at h
    split at h
    · rw [List.mem_singleton] at h; subst h; exact quotAt_indWF _ _
    · split at h
      · simp at h
      · rw [List.mem_singleton] at h; subst h; exact IndWF.of_not_ind fun _ _ h => nomatch h
  | quotDecl k cv =>
    simp only [declConstants, List.mem_singleton] at h
    subst h; exact quotAt_indWF _ _
  | indDecl block nP =>
    simp only [declConstants] at h
    split at h
    · rename_i p _
      intro cv caps hc hnz
      subst hc
      simp only [blockConstants, blockFormers, List.mem_append, List.mem_map] at h
      rcases h with (⟨⟨cv', i⟩, hm, he⟩ | h) | h
      · simp only [ConstantInfo.indInfo.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [show (blockCapsAt p i (blockIsRec p)).neverZero =
            (formerZ (p.members.getD i default).declared).isNever by
          unfold blockCapsAt; split <;> rfl] at hnz
        rw [List.mem_zipIdx_iff_getElem?, List.getElem?_map] at hm
        obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hm
        rw [List.getD_eq_getElem?_getD, hm] at hnz
        exact hnz
      · simp only [blockCtors, List.mem_flatMap, List.mem_map] at h
        obtain ⟨g, -, c, -, hc⟩ := h
        exact nomatch hc
      · exact (blockRecs_not_ind h).elim
    · simp at h

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
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun t ht => ?_, fun c hc => ?_, fun c hc => ?_⟩
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
  · rcases (mem_streamEnv_consts ds _).1 hc with ⟨d, hd, hcd⟩ | h
    · exact declConstants_indWF hcd
    · simp [Env.empty] at h
  · rcases (mem_streamEnv_consts ds _).1 hc with ⟨d, hd, hcd⟩ | h
    · exact constOk_ctorWF ((hd' d hd).1 c hcd).1
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

/-! ## The read order -/

/-- **Positions in read order**: every record's reads are stored by itself or by an earlier
record. -/
@[expose] def OrderedBy (ds : Array Declaration) (rds : Array (List Name)) (o : List Nat) : Prop :=
  ∀ k (h : k < o.length), ∀ y ∈ rds.getD o[k] [],
    ∃ j ∈ o.take (k + 1), y ∈ declNames (ds.getD j default)

/-- **The read order's invariant**: the placed set is the order's, its positions in range and
distinct, in read order. -/
structure SortInv (ds : Array Declaration) (rds : Array (List Name)) (st : SortSt) : Prop where
  placed : ∀ j, st.placed.contains j = true ↔ j ∈ st.order.toList
  lt : ∀ j ∈ st.order.toList, j < ds.size
  nodup : st.order.toList.Nodup
  ordered : OrderedBy ds rds st.order.toList

/-- **`ownerMap` names a record storing the name.** -/
theorem ownerMap_spec {ds : Array Declaration} {y : Name} {j : Nat}
    (h : (ownerMap ds)[y]? = some j) : j < ds.size ∧ y ∈ declNames (ds.getD j default) := by
  let P : Std.HashMap Name Nat → Prop := fun m =>
    ∀ y j, m[y]? = some j → j < ds.size ∧ y ∈ declNames (ds.getD j default)
  have inner : ∀ (j : Nat), j < ds.size → ∀ (ns : List Name) (m : Std.HashMap Name Nat), P m →
      (∀ y ∈ ns, y ∈ declNames (ds.getD j default)) → P (ns.foldl (fun m y => m.insert y j) m) := by
    intro j hj ns
    induction ns with
    | nil => intro m hm _; exact hm
    | cons n ns ih =>
      intro m hm hns
      refine ih _ (fun y k hk => ?_) (fun y hy => hns y (List.mem_cons_of_mem _ hy))
      rw [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i he
        cases hk
        exact ⟨hj, (beq_iff_eq.1 he) ▸ hns n List.mem_cons_self⟩
      · exact hm y k hk
  have outer : ∀ (l : List Nat) (m : Std.HashMap Name Nat), P m → (∀ j ∈ l, j < ds.size) →
      P (l.foldl (fun m j => (declNames (ds.getD j default)).foldl
        (fun m y => m.insert y j) m) m) := by
    intro l
    induction l with
    | nil => intro m hm _; exact hm
    | cons j l ih =>
      intro m hm hl
      exact ih _ (inner j (hl j List.mem_cons_self) _ m hm (fun _ h => h))
        (fun k hk => hl k (List.mem_cons_of_mem _ hk))
  exact outer _ {} (fun y j h => by simp at h) (fun j hj => List.mem_range.1 hj) y j h

/-- A position placed at the end keeps the order, where every read of its record is stored by
a placed record or by itself. -/
theorem OrderedBy.push {ds : Array Declaration} {rds : Array (List Name)} {o : List Nat} {i : Nat}
    (h : OrderedBy ds rds o)
    (hc : ∀ y ∈ rds.getD i [],
      (∃ j ∈ o, y ∈ declNames (ds.getD j default)) ∨ y ∈ declNames (ds.getD i default)) :
    OrderedBy ds rds (o ++ [i]) := by
  intro k hk y hy
  rw [List.length_append, List.length_singleton] at hk
  by_cases hko : k < o.length
  · rw [List.getElem_append_left hko] at hy
    obtain ⟨j, hj, hyj⟩ := h k hko y hy
    exact ⟨j, by rw [List.take_append_of_le_length (by omega)]; exact hj, hyj⟩
  · have hk' : k = o.length := by omega
    subst hk'
    rw [List.getElem_append_right (by omega)] at hy
    simp only [Nat.sub_self, List.getElem_singleton] at hy
    rw [List.take_of_length_le (by simp)]
    rcases hc y hy with ⟨j, hj, hyj⟩ | hyi
    · exact ⟨j, List.mem_append_left _ hj, hyj⟩
    · exact ⟨i, List.mem_append_right _ (List.mem_singleton_self i), hyi⟩

/-- **A record placed at the end keeps the invariant**, where it is not placed yet and every
read of it is stored by a placed record or by itself. -/
theorem SortInv.push {ds : Array Declaration} {rds : Array (List Name)} {st : SortSt} {i : Nat}
    (hi : SortInv ds rds st) (hio : i ∉ st.order.toList) (hlt : i < ds.size)
    (hc : ∀ y ∈ rds.getD i [],
      (∃ j ∈ st.order.toList, y ∈ declNames (ds.getD j default)) ∨
        y ∈ declNames (ds.getD i default)) :
    SortInv ds rds { order := st.order.push i, placed := st.placed.insert i } := by
  constructor
  · intro j
    show (st.placed.insert i).contains j = true ↔ j ∈ (st.order.push i).toList
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hi.placed j,
      Array.toList_push, List.mem_append, List.mem_singleton]
    exact ⟨fun h => h.elim (fun h => Or.inr h.symm) Or.inl,
      fun h => h.elim Or.inr (fun h => Or.inl h.symm)⟩
  · intro j hj
    change j ∈ (st.order.push i).toList at hj
    rw [Array.toList_push] at hj
    rcases List.mem_append.1 hj with hj | hj
    · exact hi.lt j hj
    · rw [List.mem_singleton.1 hj]; exact hlt
  · show (st.order.push i).toList.Nodup
    rw [Array.toList_push]
    exact List.nodup_append.2 ⟨hi.nodup, by simp,
      fun a ha b hb => by rw [List.mem_singleton.1 hb]; rintro rfl; exact hio ha⟩
  · show OrderedBy ds rds (st.order.push i).toList
    rw [Array.toList_push]
    exact hi.ordered.push hc

/-- **The walk from one record** (`sortVisit`): the invariant kept, the order extended by the
record and records off the path, the record placed. -/
theorem sortVisit_spec {ds : Array Declaration} {rds : Array (List Name)}
    {owner : Std.HashMap Name Nat}
    (howner : ∀ y j, owner[y]? = some j → j < ds.size ∧ y ∈ declNames (ds.getD j default)) :
    ∀ (fuel i : Nat) (path : Std.HashSet Nat) (ys : List Name) (st st' : SortSt),
      sortVisit ds rds owner fuel i path ys st = .ok st' → SortInv ds rds st →
      path.contains i = true → (∀ p, path.contains p = true → p ∉ st.order.toList) →
      i < ds.size →
      (∀ y ∈ rds.getD i [], y ∉ ys →
        (∃ j ∈ st.order.toList, y ∈ declNames (ds.getD j default)) ∨
          y ∈ declNames (ds.getD i default)) →
      SortInv ds rds st' ∧ st.order.toList <+: st'.order.toList ∧
      (∀ x ∈ st'.order.toList, x ∈ st.order.toList ∨ x = i ∨ path.contains x = false) ∧
      i ∈ st'.order.toList := by
  intro fuel
  induction fuel with
  | zero => intro i path ys st st' h; rw [sortVisit] at h; simp at h
  | succ fuel ihf =>
    intro i path ys
    induction ys with
    | nil =>
      intro st st' h hi hpi hpath hlt hc
      rw [sortVisit] at h
      simp only [Except.ok.injEq] at h
      subst h
      have hio : i ∉ st.order.toList := hpath i hpi
      refine ⟨hi.push hio hlt fun y hy => hc y hy (by simp), ?_, fun x hx => ?_, ?_⟩
      · show st.order.toList <+: (st.order.push i).toList
        rw [Array.toList_push]; exact List.prefix_append _ _
      · change x ∈ (st.order.push i).toList at hx
        rw [Array.toList_push] at hx
        rcases List.mem_append.1 hx with hx | hx
        · exact .inl hx
        · exact .inr (.inl (List.mem_singleton.1 hx))
      · show i ∈ (st.order.push i).toList
        rw [Array.toList_push]; exact List.mem_append_right _ (List.mem_singleton_self i)
    | cons y ys ihy =>
      intro st st' h hi hpi hpath hlt hc
      rw [sortVisit] at h
      split at h
      · simp at h
      · rename_i j hj
        obtain ⟨hjlt, hyj⟩ := howner y j hj
        split at h
        · rename_i hskip
          refine ihy st st' h hi hpi hpath hlt fun z hz hzn => ?_
          by_cases hzy : z = y
          · subst hzy
            rcases Bool.or_eq_true _ _ ▸ hskip with he | hp
            · exact .inr (beq_iff_eq.1 he ▸ hyj)
            · exact .inl ⟨j, (hi.placed j).1 hp, hyj⟩
          · exact hc z hz (by simp [hzy, hzn])
        · rename_i hskip
          simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hskip
          split at h
          · simp at h
          · rename_i hnp
            simp only [Bool.not_eq_true] at hnp
            split at h
            · simp at h
            · rename_i st₁ h₁
              have hjo : j ∉ st.order.toList := fun hm => by
                rw [← hi.placed] at hm; rw [hm] at hskip; exact absurd hskip.2 (by simp)
              obtain ⟨i₁, p₁, x₁, m₁⟩ := ihf j (path.insert j) _ st st₁ h₁ hi
                (by simp [Std.HashSet.contains_insert])
                (fun p hp => by
                  simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hp
                  rcases hp with rfl | hp
                  · exact hjo
                  · exact hpath p hp)
                hjlt (fun z hz hzn => absurd hz hzn)
              have hpath₁ : ∀ p, path.contains p = true → p ∉ st₁.order.toList := fun p hp hm => by
                rcases x₁ p hm with h' | rfl | h'
                · exact hpath p hp h'
                · rw [hp] at hnp; cases hnp
                · simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at h'
                  rw [hp] at h'; cases h'.2
              obtain ⟨i₂, p₂, x₂, m₂⟩ := ihy st₁ st' h i₁ hpi hpath₁ hlt fun z hz hzn => by
                by_cases hzy : z = y
                · subst hzy; exact .inl ⟨j, m₁, hyj⟩
                · rcases hc z hz (by simp [hzy, hzn]) with ⟨k, hk, hzk⟩ | h'
                  · exact .inl ⟨k, p₁.subset hk, hzk⟩
                  · exact .inr h'
              refine ⟨i₂, p₁.trans p₂, fun x hx => ?_, m₂⟩
              rcases x₂ x hx with h' | h' | h'
              · rcases x₁ x h' with h'' | rfl | h''
                · exact .inl h''
                · exact .inr (.inr hnp)
                · simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at h''
                  exact .inr (.inr h''.2)
              · exact .inr (.inl h')
              · exact .inr (.inr h')

/-- **The walk over positions** (`sortFrom`): the invariant kept, every position of `l` placed. -/
theorem sortFrom_spec {ds : Array Declaration} {rds : Array (List Name)}
    {owner : Std.HashMap Name Nat}
    (howner : ∀ y j, owner[y]? = some j → j < ds.size ∧ y ∈ declNames (ds.getD j default))
    (fuel : Nat) :
    ∀ (l : List Nat) (st st' : SortSt), sortFrom ds rds owner fuel l st = .ok st' →
      SortInv ds rds st →
      (∀ i ∈ l, i < ds.size) →
      SortInv ds rds st' ∧ st.order.toList <+: st'.order.toList ∧ ∀ i ∈ l, i ∈ st'.order.toList
  | [], st, st', h, hi, _ => by
    simp only [sortFrom, Except.ok.injEq] at h; subst h
    exact ⟨hi, List.prefix_refl _, by simp⟩
  | i :: l, st, st', h, hi, hl => by
    simp only [sortFrom] at h
    split at h
    · rename_i hp
      obtain ⟨a, b, c⟩ := sortFrom_spec howner fuel l st st' h hi
        (fun k hk => hl k (List.mem_cons_of_mem _ hk))
      refine ⟨a, b, fun k hk => ?_⟩
      rcases List.mem_cons.1 hk with rfl | hk
      · exact b.subset ((hi.placed _).1 hp)
      · exact c k hk
    · rename_i hp
      split at h
      · simp at h
      · rename_i st₁ h₁
        obtain ⟨i₁, p₁, -, m₁⟩ := sortVisit_spec howner fuel i _ _ st st₁ h₁ hi
          (by simp [Std.HashSet.contains_insert])
          (fun p hp hm => by
            simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq,
              Std.HashSet.contains_empty, Bool.false_eq_true, or_false] at hp
            subst hp
            exact hp ((hi.placed _).2 hm))
          (hl i List.mem_cons_self) (fun z hz hzn => absurd hz hzn)
        obtain ⟨a, b, c⟩ := sortFrom_spec howner fuel l st₁ st' h i₁
          (fun k hk => hl k (List.mem_cons_of_mem _ hk))
        refine ⟨a, p₁.trans b, fun k hk => ?_⟩
        rcases List.mem_cons.1 hk with rfl | hk
        · exact b.subset m₁
        · exact c k hk

/-- **The read order** (`readOrder`): its positions are those of the records, each once, in
read order. -/
theorem readOrder_spec {ds : Array Declaration} {rds : Array (List Name)} {o : Array Nat}
    (h : readOrder ds rds = .ok o) :
    o.toList.Perm (List.range ds.size) ∧ OrderedBy ds rds o.toList := by
  unfold readOrder at h
  cases hs : sortFrom ds rds (ownerMap ds) (ds.size + 1) (List.range ds.size) {} with
  | error e => simp [hs, Except.map] at h
  | ok st =>
    simp only [hs, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨hi, -, hall⟩ := sortFrom_spec (fun _ _ h => ownerMap_spec h) _ _ {} st hs
      ⟨fun j => by simp, fun j hj => by simp at hj, by simp, fun k hk => by simp at hk⟩
      (fun j hj => List.mem_range.1 hj)
    refine ⟨(List.perm_ext_iff_of_nodup hi.nodup List.nodup_range).2 fun j =>
      ⟨fun hj => List.mem_range.2 (hi.lt j hj), hall j⟩, hi.ordered⟩

/-- **The records in read order** are the records, permuted. -/
theorem readOrder_perm {ds : Array Declaration} {rds : Array (List Name)} {o : Array Nat}
    (h : readOrder ds rds = .ok o) :
    (o.map (ds.getD · default)).toList.Perm ds.toList := by
  rw [Array.toList_map]
  have hr : (List.range ds.size).map (ds.getD · default) = ds.toList :=
    List.ext_getElem (by simp) fun k h₁ h₂ => by
      simp [Array.getElem?_eq_getElem (by simpa using h₂ : k < ds.size)]
  exact hr ▸ (readOrder_spec h).1.map _

/-- **The records in read order read only themselves and earlier records**: every one is
`RecordScoped` in the prefix of the list ending with it, where `rds` lists what each reads. -/
theorem readOrder_ordered {ds : Array Declaration} {rds : Array (List Name)} {o : Array Nat}
    (h : readOrder ds rds = .ok o)
    (hr : ∀ j < ds.size, rds.getD j [] = (recordReads (ds.getD j default)).toList) :
    ∀ k (hk : k < (o.map (ds.getD · default)).toList.length),
      RecordScoped (streamEnv ((o.map (ds.getD · default)).toList.take (k + 1)))
        (o.map (ds.getD · default)).toList[k] := by
  intro k hk
  have hko : k < o.toList.length := by simpa using hk
  refine recordReads_scoped fun y hy => ?_
  simp only [Array.toList_map, List.getElem_map] at hy ⊢
  have hlt : o.toList[k] < ds.size :=
    List.mem_range.1 ((readOrder_spec h).1.mem_iff.1 (List.getElem_mem hko))
  obtain ⟨j, hj, hyj⟩ := (readOrder_spec h).2 k hko y
    (by rw [hr _ hlt]; exact Array.mem_toList_iff.2 hy)
  rw [← List.map_take]
  exact streamEnv_find_of_mem (List.mem_map_of_mem hj) hyj

/-- The worklist starts in its invariant. -/
theorem reachInv_init (rs : List Name) : ReachInv rs (ReachLog.init rs) := by
  refine ⟨fun d hd => by simp [ReachLog.init] at hd, fun z hz => ?_,
    fun z hz => by simp [ReachLog.init] at hz, fun z hz => (pushNames_spec rs {} []).1 z hz,
    by simp [ReachLog.init]⟩
  rcases (pushNames_spec rs {} []).2.1 z hz with h' | h'
  · simp at h'
  · exact .inr h'

/-- A name stored in a list's environment is a record's. -/
theorem streamEnv_find_mem {ds : List Declaration} {y : Name}
    (h : ((streamEnv ds).find? y).isSome = true) : ∃ d ∈ ds, y ∈ declNames d := by
  simp only [Env.find?, List.find?_isSome] at h
  obtain ⟨ci, hci, hy⟩ := h
  rcases (mem_streamEnv_consts ds _).1 hci with ⟨d, hd, hcd⟩ | h'
  · refine ⟨d, hd, List.mem_map.2 ⟨ci, hcd, ?_⟩⟩
    simpa [ConstantInfo.name] using (beq_iff_eq.1 hy)
  · simp [Env.empty] at h'

/-- **The reach's context is closed, well formed and in read order**: at every accepting
outcome of `reach`, on any snapshot, every context record is `RecordScoped` in the prefix of the
context ending with it (`ImportOk.ordered`), so in the context, every name it reads is stored
there, the context is `EnvWF`, and every root that is not an own name is stored there. -/
theorem reach_ok {rd : OleanReads ModelIO} {m : Name} {wr : WorkerReads} {own : Std.HashSet Name}
    {roots : Array Name} {fs : FS} {r : Reach} {hs hs' : HS}
    (h : (reach rd m wr own roots : ModelIO _) fs hs (.ok (.ok r)) hs') :
    (∀ k (hk : k < r.ctx.toList.length),
      RecordScoped (streamEnv (r.ctx.toList.take (k + 1))) r.ctx.toList[k]) ∧
    (∀ d ∈ r.ctx.toList, RecordScoped (streamEnv r.ctx.toList) d) ∧
    (∀ d ∈ r.ctx.toList, ∀ y ∈ recordReads d, ((streamEnv r.ctx.toList).find? y).isSome = true) ∧
    EnvWF (streamEnv r.ctx.toList) ∧
    (∀ x ∈ roots, own.contains x = false → ((streamEnv r.ctx.toList).find? x).isSome = true) := by
  unfold reach at h
  simp only [ModelIO.bind_ok] at h
  obtain ⟨⟨c, x⟩, _, -, h⟩ := h
  rcases x with e | extra
  · simp at h
  simp only at h
  generalize List.find? _ _ = q at h
  cases q with
  | some x => simp at h
  | none =>
    simp only [ModelIO.bind_ok] at h
    obtain ⟨y, _, hy, h⟩ := h
    rcases y with e | ⟨L, c'⟩
    · simp at h
    simp only at h
    cases ho : readOrder L.ctx L.reads with
    | error e => simp [ho] at h
    | ok o =>
    simp only [ho] at h
    cases hv : validateCtx (o.map (L.ctx.getD · default)) (o.map (L.homes.getD · default)) with
    | error e => rw [hv] at h; simp at h
    | ok u =>
    cases hf : inferFlags (o.map (L.ctx.getD · default)).toList
      c'.pending.toList with
    | error e => rw [hv] at h; simp only at h; rw [hf] at h; simp at h
    | ok u' =>
    simp only [hv, hf, ModelIO.pure_iff, Except.ok.injEq] at h
    obtain ⟨h, -⟩ := h
    subst h
    simp only
    have hreads := (reachGo_inv _ fs _ _ _ _ (reachInv_init _) hy).1.2.2.2.2
    have hr : ∀ j < L.ctx.size,
        L.reads.getD j [] = (recordReads (L.ctx.getD j default)).toList := by
      intro j hj
      rw [hreads]
      simp [Array.getElem?_eq_getElem hj]
    have hperm := readOrder_perm ho
    have hord := readOrder_ordered ho hr
    have hcl : ∀ d ∈ (o.map (L.ctx.getD · default)).toList, ∀ y ∈ recordReads d,
        ((streamEnv (o.map (L.ctx.getD · default)).toList).find? y).isSome = true := by
      intro d hd y hy
      rw [Array.toList_map] at hd ⊢
      obtain ⟨j₀, hj₀, rfl⟩ := List.mem_map.1 hd
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj₀
      have hlt : o.toList[k] < L.ctx.size :=
        List.mem_range.1 ((readOrder_spec ho).1.mem_iff.1 (List.getElem_mem hk))
      obtain ⟨j, hj, hyj⟩ := (readOrder_spec ho).2 k hk y
        (by rw [hr _ hlt]; exact Array.mem_toList_iff.2 hy)
      exact streamEnv_find_of_mem (List.mem_map_of_mem (List.mem_of_mem_take hj)) hyj
    refine ⟨hord, fun d hd => recordReads_scoped (hcl d hd), hcl,
      ctx_envWF (validateCtx_ok hv) hcl, fun x hx hown => ?_⟩
    obtain ⟨d, hd, hxd⟩ := streamEnv_find_mem (reachGo_roots _ fs (reachInv_init _) hy x
      (List.mem_filter.2 ⟨by simp [hx], by simp [hown]⟩))
    exact streamEnv_find_of_mem (hperm.mem_iff.2 hd) hxd

end ConLeche.Driver

