module

public import ConLeche.Verify.Frontend.Olean.Kids
import ConLeche.Verify.Frontend.Olean.Nodes

public section

/-!
# The sparse decoder is the specification (task #421)

`sparseNameP r = nameP r` and `sparseExprP r = exprP r`
(`ConLeche/Frontend/Olean/Sparse.lean`), hence `sparseEntry_eq`: a
constant read with a memo of its own per root is the specification's.
`frontierExpr_eq`: over a frontier that holds only the specification's
values, a read is the specification's too; which objects the frontier holds
does not matter.

The invariant (`Good`): every value the memo and the frontier hold is the
specification's at its location.  `sGo` keeps it: an object is built
only after its kids are in the memo, and its node function, asked only
about its kids (`…Node_congr`), then answers as the specification's
does, and the memo it hands back stays good where it fails too (task
#565).  Where `sGo` fails, the specification fails at the object: a
shape the table does not list or a field that leads nowhere refutes
`MarkOK` (`KindOK.markOK`), a kid that fails refutes the object
(`KindOK.kid`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- Every value the memo holds is the specification's. -/
@[expose] def SM.Good (r : Region) (st : SM) : Prop :=
  (∀ c v, st.names[c]? = some v → nameAt r c = some v) ∧
  (∀ c v, st.levels[c]? = some v → levelAt r c = some v) ∧
  (∀ c v, st.lists[c]? = some v → levelsAt r c = some v) ∧
  (∀ c v, st.exprs[c]? = some v → exprAt r c = some v)

/-- The memo `b` holds everything `a` holds. -/
def SM.Sub (a b : SM) : Prop := ∀ k g, a.has k g = true → b.has k g = true

theorem SM.Sub.refl (a : SM) : SM.Sub a a := fun _ _ h => h

theorem SM.Sub.trans {a b c : SM} (h1 : SM.Sub a b) (h2 : SM.Sub b c) : SM.Sub a c :=
  fun k g h => h2 k g (h1 k g h)

/-! ## The frontier -/

/-- A table holds only the values of `spec`. -/
@[expose] def Table.Good {α : Type} (spec : Nat → Option α) (t : Table α) : Prop :=
  ∀ (i c : Nat) (v : α), t.keys[i]? = some c → t.vals[i]? = some v → spec c = some v

theorem Table.search_good {α : Type} {spec : Nat → Option α} {t : Table α} (ht : t.Good spec)
    {c : Nat} {lo hi : Nat} {v : α} (h : t.search c lo hi = some v) : spec c = some v := by
  induction hd : hi - lo using Nat.strongRecOn generalizing lo hi with
  | _ d ih =>
    rw [Table.search] at h
    split at h
    · rename_i hlt
      dsimp only at h
      have hm1 : (lo + hi) / 2 < hi := by omega
      have hm2 : lo ≤ (lo + hi) / 2 := by omega
      split at h
      · cases h
      · rename_i k hk
        split at h
        · rename_i hkc
          subst hkc
          exact ht _ _ _ hk h
        · split at h
          · exact ih _ (by omega) h rfl
          · exact ih _ (by omega) h rfl
    · cases h

theorem Table.get_good {α : Type} {spec : Nat → Option α} {t : Table α} (ht : t.Good spec)
    {c : Nat} {v : α} (h : t.get c = some v) : spec c = some v :=
  Table.search_good ht h

/-- **A frontier holds only the specification's values.**  Nothing else is
asked of it. -/
structure Frontier.Good (r : Region) (b : Frontier) : Prop where
  names : b.names.Good (nameAt r)
  levels : b.levels.Good (levelAt r)
  lists : b.lists.Good (levelsAt r)
  exprs : b.exprs.Good (exprAt r)

theorem Table.good_empty {α : Type} (spec : Nat → Option α) : Table.Good spec ({} : Table α) := by
  intro i c v h; simp at h

theorem Frontier.good_empty (r : Region) : Frontier.Good r {} :=
  ⟨Table.good_empty _, Table.good_empty _, Table.good_empty _, Table.good_empty _⟩

theorem SM.good_empty (r : Region) : SM.Good r {} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro c v h <;> simp at h

theorem kinds_ne' : kName ≠ kLevel ∧ kName ≠ kExpr ∧ kName ≠ kLevels ∧ kLevel ≠ kExpr ∧
    kLevel ≠ kLevels ∧ kExpr ≠ kLevels := by decide

theorem SM.has_name (st : SM) (g : Nat) : st.has kName g = st.names.contains g := by
  simp [SM.has]
theorem SM.has_level (st : SM) (g : Nat) : st.has kLevel g = st.levels.contains g := by
  simp [SM.has, kinds_ne'.1.symm]
theorem SM.has_levels (st : SM) (g : Nat) : st.has kLevels g = st.lists.contains g := by
  simp [SM.has, kinds_ne'.2.2.1.symm, kinds_ne'.2.2.2.2.1.symm]
theorem SM.has_expr (st : SM) (g : Nat) : st.has kExpr g = st.exprs.contains g := by
  simp [SM.has, kinds_ne'.2.1.symm, kinds_ne'.2.2.2.1.symm, kinds_ne'.2.2.2.2.2]

/-! ## What a held kid answers -/

theorem get_of_contains {α : Type} {m : Std.HashMap Nat α} {c : Nat} (h : m.contains c = true) :
    ∃ v, m[c]? = some v := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at h
  exact Option.isSome_iff_exists.mp h

/-- A kid the memo or the frontier holds answers as the specification. -/
theorem lookup_eq {α : Type} {spec : Nat → Option α} {m : Std.HashMap Nat α} {t : Table α}
    (hm : ∀ c v, m[c]? = some v → spec c = some v) (ht : t.Good spec) {c : Nat}
    (h : m.contains c = true ∨ (t.get c).isSome = true) : lookup m t c = spec c := by
  unfold lookup
  rcases h with h | h
  · obtain ⟨v, hv⟩ := get_of_contains h
    rw [hv, hm c v hv]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    cases e : m[c]? with
    | some w => exact (hm c w e).symm
    | none => rw [hv]; exact (Table.get_good ht hv).symm

theorem SM.holds_name (st : SM) (b : Frontier) (g : Nat) :
    st.holds b kName g = (st.names.contains g || (b.names.get g).isSome) := by
  simp [SM.holds, SM.has, Frontier.has]
theorem SM.holds_level (st : SM) (b : Frontier) (g : Nat) :
    st.holds b kLevel g = (st.levels.contains g || (b.levels.get g).isSome) := by
  simp [SM.holds, SM.has, Frontier.has, kinds_ne'.1.symm]
theorem SM.holds_levels (st : SM) (b : Frontier) (g : Nat) :
    st.holds b kLevels g = (st.lists.contains g || (b.lists.get g).isSome) := by
  simp [SM.holds, SM.has, Frontier.has, kinds_ne'.2.2.1.symm, kinds_ne'.2.2.2.2.1.symm]
theorem SM.holds_expr (st : SM) (b : Frontier) (g : Nat) :
    st.holds b kExpr g = (st.exprs.contains g || (b.exprs.get g).isSome) := by
  simp [SM.holds, SM.has, Frontier.has, kinds_ne'.2.1.symm, kinds_ne'.2.2.2.1.symm,
    kinds_ne'.2.2.2.2.2]

theorem SM.Good.name {r : Region} {st : SM} {b : Frontier} (hG : st.Good r) (hB : b.Good r) {c : Nat}
    (h : st.holds b kName c = true) : lookup st.names b.names c = nameAt r c :=
  lookup_eq hG.1 hB.names (by simpa [SM.holds_name] using h)
theorem SM.Good.level {r : Region} {st : SM} {b : Frontier} (hG : st.Good r) (hB : b.Good r) {c : Nat}
    (h : st.holds b kLevel c = true) : lookup st.levels b.levels c = levelAt r c :=
  lookup_eq hG.2.1 hB.levels (by simpa [SM.holds_level] using h)
theorem SM.Good.levels {r : Region} {st : SM} {b : Frontier} (hG : st.Good r) (hB : b.Good r) {c : Nat}
    (h : st.holds b kLevels c = true) : lookup st.lists b.lists c = levelsAt r c :=
  lookup_eq hG.2.2.1 hB.lists (by simpa [SM.holds_levels] using h)
theorem SM.Good.expr {r : Region} {st : SM} {b : Frontier} (hG : st.Good r) (hB : b.Good r) {c : Nat}
    (h : st.holds b kExpr c = true) : lookup st.exprs b.exprs c = exprAt r c :=
  lookup_eq hG.2.2.2 hB.exprs (by simpa [SM.holds_expr] using h)

/-! ## One object -/

theorem getElem?_insert_nat {α : Type} (m : Std.HashMap Nat α) (g c : Nat) (v : α) :
    (m.insert g v)[c]? = if g = c then some v else m[c]? := by
  rw [Std.HashMap.getElem?_insert]
  by_cases h : g = c <;> simp [h]

theorem good_ins {α : Type} {m : Std.HashMap Nat α} {spec : Nat → Option α} {g : Nat} {v : α}
    (hm : ∀ c w, m[c]? = some w → spec c = some w) (hg : spec g = some v) :
    ∀ c w, (m.insert g v)[c]? = some w → spec c = some w := by
  intro c w h
  rw [getElem?_insert_nat] at h
  split at h
  · subst_vars; cases h; exact hg
  · exact hm c w h

theorem SM.build_spec {r : Region} {b : Frontier} {k : UInt8} {g : Nat} {st : SM} (hk : IsKind k)
    (hG : st.Good r) (hB : b.Good r) (hkids : ∀ k' c, Kid r k g k' c → st.holds b k' c = true) :
    ∀ st' ok, SM.buildIn r b k g st = (st', ok) →
      st'.Good r ∧ SM.Sub st st' ∧ (ok = true → st'.has k g = true) ∧
      (ok = false → ¬ KindOK r k g) := by
  have sub_names : ∀ (v : Name), SM.Sub st { st with names := st.names.insert g v } := by
    intro v k' c h; unfold SM.has at h ⊢; repeat' split <;> simp_all [Std.HashMap.contains_insert]
  have sub_levels : ∀ (v : Level), SM.Sub st { st with levels := st.levels.insert g v } := by
    intro v k' c h; unfold SM.has at h ⊢; repeat' split <;> simp_all [Std.HashMap.contains_insert]
  have sub_lists : ∀ (v : List Level), SM.Sub st { st with lists := st.lists.insert g v } := by
    intro v k' c h; unfold SM.has at h ⊢; repeat' split <;> simp_all [Std.HashMap.contains_insert]
  have sub_exprs : ∀ (v : Expr), SM.Sub st { st with exprs := st.exprs.insert g v } := by
    intro v k' c h; unfold SM.has at h ⊢; repeat' split <;> simp_all [Std.HashMap.contains_insert]
  intro st' ok h
  rcases hk with rfl | rfl | rfl | rfl
  · have hn : (nameNode r g fun c _ => lookup st.names b.names c) = nameAt r g := by
      rw [nameAt]
      exact nameNode_congr fun c _ hc => hG.name hB (hkids _ _ hc)
    unfold SM.buildIn at h
    simp only [ite_true] at h
    rw [hn] at h
    cases e : nameAt r g with
    | none =>
      rw [e] at h; simp only at h; cases h
      refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
      have := hok.1 rfl
      rw [e] at this; cases this
    | some v =>
      rw [e] at h; simp only at h; cases h
      exact ⟨⟨good_ins hG.1 e, hG.2.1, hG.2.2.1, hG.2.2.2⟩, sub_names v,
        fun _ => by rw [SM.has_name]; simp [Std.HashMap.contains_insert], fun h => (by cases h)⟩
  · have hn : (levelNode r g (fun c _ => lookup st.levels b.levels c)
        (fun c _ => lookup st.names b.names c)) = levelAt r g := by
      rw [levelAt]
      exact levelNode_congr (fun c _ hc => hG.level hB (hkids _ _ hc)) (fun c _ hc => hG.name hB (hkids _ _ hc))
    unfold SM.buildIn at h
    simp only [kinds_ne'.1.symm, ite_false, ite_true] at h
    rw [hn] at h
    cases e : levelAt r g with
    | none =>
      rw [e] at h; simp only at h; cases h
      refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
      have := hok.2.1 rfl
      rw [e] at this; cases this
    | some v =>
      rw [e] at h; simp only at h; cases h
      exact ⟨⟨hG.1, good_ins hG.2.1 e, hG.2.2.1, hG.2.2.2⟩, sub_levels v,
        fun _ => by rw [SM.has_level]; simp [Std.HashMap.contains_insert], fun h => (by cases h)⟩
  · have hn : (exprNode r g (fun c _ => lookup st.exprs b.exprs c) (fun c _ => lookup st.names b.names c)
        (fun c _ => lookup st.levels b.levels c) (fun c _ => lookup st.lists b.lists c)) = exprAt r g := by
      rw [exprAt]
      exact exprNode_congr (fun c _ hc => hG.expr hB (hkids _ _ hc)) (fun c _ hc => hG.name hB (hkids _ _ hc))
        (fun c _ hc => hG.level hB (hkids _ _ hc)) (fun c _ hc => hG.levels hB (hkids _ _ hc))
    unfold SM.buildIn at h
    simp only [kinds_ne'.2.1.symm, kinds_ne'.2.2.2.1.symm, kinds_ne'.2.2.2.2.2, ite_false] at h
    rw [hn] at h
    cases e : exprAt r g with
    | none =>
      rw [e] at h; simp only at h; cases h
      refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
      have := hok.2.2.2 rfl
      rw [e] at this; cases this
    | some v =>
      rw [e] at h; simp only at h; cases h
      exact ⟨⟨hG.1, hG.2.1, hG.2.2.1, good_ins hG.2.2.2 e⟩, sub_exprs v,
        fun _ => by rw [SM.has_expr]; simp [Std.HashMap.contains_insert], fun h => (by cases h)⟩
  · have hn : (levelsNode r g (fun c _ => lookup st.lists b.lists c)
        (fun c _ => lookup st.levels b.levels c)) = levelsAt r g := by
      rw [levelsAt]
      exact levelsNode_congr (fun c _ hc => hG.levels hB (hkids _ _ hc)) (fun c _ hc => hG.level hB (hkids _ _ hc))
    unfold SM.buildIn at h
    simp only [kinds_ne'.2.2.1.symm, kinds_ne'.2.2.2.2.1.symm, ite_false, ite_true] at h
    rw [hn] at h
    cases e : levelsAt r g with
    | none =>
      rw [e] at h; simp only at h; cases h
      refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
      have := hok.2.2.1 rfl
      rw [e] at this; cases this
    | some v =>
      rw [e] at h; simp only at h; cases h
      exact ⟨⟨hG.1, hG.2.1, good_ins hG.2.2.1 e, hG.2.2.2⟩, sub_lists v,
        fun _ => by rw [SM.has_levels]; simp [Std.HashMap.contains_insert], fun h => (by cases h)⟩

/-! ## The recursion -/

/-- What `sGo` gives: the memo handed back is good and holds all it held; on success it
holds the object, on failure the specification fails at it. -/
@[expose] def SGoSpec (r : Region) (b : Frontier) (g : Nat) : Prop :=
  ∀ k st, IsKind k → st.Good r → ∀ st' ok, sGo r b k g st = (st', ok) →
    st'.Good r ∧ SM.Sub st st' ∧ (ok = true → st'.holds b k g = true) ∧
    (ok = false → ¬ KindOK r k g)

/-- What the memo holds, it holds together with the frontier. -/
theorem SM.Sub.holds {a c : SM} (h : SM.Sub a c) {b : Frontier} {k : UInt8} {g : Nat}
    (ha : a.holds b k g = true) : c.holds b k g = true := by
  simp only [SM.holds, Bool.or_eq_true] at ha ⊢
  exact ha.imp (h k g) id

theorem kidsGo_spec {r : Region} {b : Frontier} {k : UInt8} {g : Nat} (hk : IsKind k)
    (ih : ∀ c, c < g → SGoSpec r b c) {fs₀ : List (Nat × UInt8 × Bool)} (hfit : r.fits g = true)
    (hfs : kidTable k (r.tag g) (r.nobjs g) = some fs₀) :
    ∀ (fs : List (Nat × UInt8 × Bool)) (st : SM), (∀ f ∈ fs, f ∈ fs₀) → st.Good r →
      ∀ st' ok, kidsGo r b g fs st = (st', ok) → st'.Good r ∧ SM.Sub st st' ∧
        (ok = true → ∀ f ∈ fs, ∀ c, ¬ (f.2.2 = true ∧ r.fld g f.1 = 1) →
          r.down g (r.fld g f.1) = some c → st'.holds b f.2.1 c = true) ∧
        (ok = false → ¬ KindOK r k g)
  | [], st, _, hG => by
    intro st' ok h
    rw [kidsGo] at h; cases h
    exact ⟨hG, SM.Sub.refl _, fun _ _ hf => by simp at hf, fun h => (by cases h)⟩
  | (i, k', nil) :: fs, st, hsub, hG => by
    have hmem : (i, k', nil) ∈ fs₀ := hsub _ (by simp)
    have hsub' : ∀ f ∈ fs, f ∈ fs₀ := fun f hf => hsub f (by simp [hf])
    have hk' : IsKind k' := kidTable_kinds hfs _ hmem
    intro st' ok h
    rw [kidsGo] at h
    by_cases hnil : (nil && r.fld g i == 1) = true
    · simp only [hnil, ite_true] at h
      obtain ⟨hG', hS, hall, hf⟩ := kidsGo_spec hk ih hfit hfs fs st hsub' hG st' ok h
      refine ⟨hG', hS, fun hok f hm c hne hd => ?_, hf⟩
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · simp only [Bool.and_eq_true, beq_iff_eq] at hnil
        exact absurd ⟨hnil.1, hnil.2⟩ hne
      · exact hall hok f hm c hne hd
    · simp only [hnil, Bool.false_eq_true, ite_false] at h
      split at h
      · rename_i c hd
        have hlt : c < g := Region.down_lt hd
        have hkid : Kid r k g k' c := ⟨hfit, fs₀, hfs, i, nil, hmem, by
          intro ⟨e1, e2⟩; apply hnil; simp [e1, e2], hd⟩
        cases e1 : sGo r b k' c st with
        | mk st1 ok1 =>
        rw [e1] at h
        obtain ⟨hG1, hS1, hh1, hf1⟩ := ih c hlt k' st hk' hG st1 ok1 e1
        cases ok1
        · cases h
          exact ⟨hG1, hS1, fun h => (by cases h), fun _ hok => hf1 rfl (KindOK.kid hk hok hkid)⟩
        · simp only at h
          obtain ⟨hG', hS', hall, hf⟩ := kidsGo_spec hk ih hfit hfs fs st1 hsub' hG1 st' ok h
          refine ⟨hG', hS1.trans hS', fun hok f hm c' hne hd' => ?_, hf⟩
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · rw [hd] at hd'; cases hd'; exact hS'.holds (hh1 rfl)
          · exact hall hok f hm c' hne hd'
      · rename_i hd
        cases h
        refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
        obtain ⟨_, fs', hfs', hall⟩ := KindOK.markOK hk hok
        rw [hfs] at hfs'; cases hfs'
        rcases hall _ hmem with ⟨e1, e2⟩ | hs
        · apply hnil; simp only at e1 e2; simp [e1, e2]
        · simp [hd] at hs

theorem sGo_spec (r : Region) {b : Frontier} (hB : b.Good r) : ∀ g, SGoSpec r b g := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
  intro k st hk hG st' ok h
  rw [sGo] at h
  by_cases hh : st.holds b k g = true
  · simp only [hh, ite_true] at h
    cases h
    exact ⟨hG, SM.Sub.refl _, fun _ => hh, fun h => (by cases h)⟩
  · simp only [hh, Bool.false_eq_true, ite_false] at h
    by_cases hfit : r.fits g = true
    · simp only [hfit, ite_true] at h
      split at h
      · rename_i hnone
        cases h
        refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
        obtain ⟨_, fs', hfs', _⟩ := KindOK.markOK hk hok
        rw [hnone] at hfs'; cases hfs'
      · rename_i fs hfs
        cases e1 : kidsGo r b g fs st with
        | mk st1 ok1 =>
        rw [e1] at h
        obtain ⟨hG1, hS1, hall, hf1⟩ :=
          kidsGo_spec hk ih hfit hfs fs st (fun f hf => hf) hG st1 ok1 e1
        cases ok1
        · cases h
          exact ⟨hG1, hS1, fun h => (by cases h), fun _ => hf1 rfl⟩
        · simp only at h
          have hkids : ∀ k' c, Kid r k g k' c → st1.holds b k' c = true := by
            intro k' c ⟨_, fs', hfs', i, nil, hm, hne, hd⟩
            rw [hfs] at hfs'; cases hfs'
            exact hall rfl (i, k', nil) hm c hne hd
          obtain ⟨hG', hS', hh', hf'⟩ := SM.build_spec hk hG1 hB hkids st' ok h
          refine ⟨hG', hS1.trans hS', fun hok => ?_, hf'⟩
          simp only [SM.holds, hh' hok, Bool.true_or]
    · simp only [hfit, Bool.false_eq_true, ite_false] at h
      cases h
      refine ⟨hG, SM.Sub.refl _, fun h => (by cases h), fun _ hok => ?_⟩
      exact hfit (KindOK.markOK hk hok).1

/-! ## Roots -/

theorem isKind_name : IsKind kName := Or.inl rfl
theorem isKind_expr : IsKind kExpr := Or.inr (Or.inr (Or.inl rfl))

/-- **A read over a frontier is the specification**, whichever objects the
frontier holds, as long as they are the specification's values. -/
theorem frontierExpr_eq {r : Region} {b : Frontier} (hB : b.Good r) (c : Nat) :
    frontierExpr r b c = exprAt r c := by
  unfold frontierExpr
  cases e : sGo r b kExpr c {} with
  | mk st' ok =>
  obtain ⟨hG, -, hh, hn⟩ := sGo_spec r hB c kExpr {} isKind_expr (SM.good_empty r) st' ok e
  cases ok
  · simp only
    cases e2 : exprAt r c with
    | none => rfl
    | some w => exact absurd (KindOK.expr (by simp [e2])) (hn rfl)
  · exact hG.expr hB (hh rfl)

/-- **The sparse decoder reads a `Name` root as the specification.** -/
theorem sparseNameP_eq (r : Region) (v : UInt64) : sparseNameP r v = nameP r v := by
  unfold sparseNameP nameP
  split
  · rfl
  · cases hl : r.loc v with
    | none => rfl
    | some c =>
      simp only
      have hB := Frontier.good_empty r
      cases e : sGo r {} kName c {} with
      | mk st' ok =>
      obtain ⟨hG, -, hh, hn⟩ := sGo_spec r hB c kName {} isKind_name (SM.good_empty r) st' ok e
      cases ok
      · simp only
        cases e2 : nameAt r c with
        | none => rfl
        | some w => exact absurd (KindOK.name (by simp [e2])) (hn rfl)
      · exact hG.name hB (hh rfl)

/-- **The sparse decoder reads an `Expr` root as the specification.** -/
theorem sparseExprP_eq (r : Region) (v : UInt64) : sparseExprP r v = exprP r v := by
  unfold sparseExprP exprP
  cases hl : r.loc v with
  | none => rfl
  | some c => exact frontierExpr_eq (Frontier.good_empty r) c

/-- **A constant read sparsely is the specification's.** -/
theorem sparseEntry_eq (r : Region) (sk : CEntryF UInt64 UInt64) :
    sparseEntry r sk = sk.mapM (nameP r) (exprP r) := by
  unfold sparseEntry
  rw [show sparseNameP r = nameP r from funext (sparseNameP_eq r),
    show sparseExprP r = exprP r from funext (sparseExprP_eq r)]

end ConLeche.Frontend.Olean
