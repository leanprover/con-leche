module

public import Fragment.NestClass
public import Fragment.InstallRead3
public import Fragment.InstallScope

@[expose] public section

/-!
# The nested recursors' syntax, read

The container's constructors translated into the block's terms
(`classCtor`) are constructors **in the block's own sense**: each
translated field is in the block's scope (`classCtor_fieldScoped`), so
everything the block's readers say about a constructor's field context
— that fitting the generated context is fitting the fields
semantically (`fits_fieldCtx`), the inductive-hypothesis context, a
minor premise's conclusion — applies to the class's minor premises
verbatim.  What is specific to the class is the head of a minor's
conclusion (the container's constructor at the class's arguments) and
its motive (the class's), and the two recursors' contexts, which are
read here.

The syntactic facts are about the substitution `instChainAt` of the
class's arguments for the container's parameters: a term closed below
the container's parameters and `k` binders, not using the member's
parameter, becomes a term closed below the block's parameters and `k`
binders, mentioning the stored constants of the container's field and
of the class's arguments — the member's expression (which mentions the
block's own former) is never inserted, because the member's parameter
does not occur.
-/

namespace Fragment
open SetLib IndLib

universe u

namespace Expr

/-- Instantiating a variable the term does not use only lowers the
indices above it. -/
theorem inst_not_uses : ∀ (e a : Expr) (k : Nat), e.usesVar k = false →
    ∀ c ∈ (e.inst a k).consts, c ∈ e.consts
  | bvar i, a, k, hu, c, hc => by
    simp only [usesVar_bvar, decide_eq_false_iff_not] at hu
    rw [inst_bvar] at hc
    simp only [hu, if_false] at hc
    split at hc <;> simp at hc
  | sort _, _, _, _, _, hc => by simp at hc
  | const _ _, _, _, _, c, hc => by rw [inst_const] at hc; exact hc
  | app f b, a, k, hu, c, hc => by
    simp only [usesVar_app, Bool.or_eq_false_iff] at hu
    rw [inst_app, consts_app, List.mem_append] at hc
    rw [consts_app, List.mem_append]
    rcases hc with hc | hc
    · exact Or.inl (inst_not_uses f a k hu.1 c hc)
    · exact Or.inr (inst_not_uses b a k hu.2 c hc)
  | lam A _ b, a, k, hu, c, hc => by
    simp only [usesVar_lam, Bool.or_eq_false_iff] at hu
    rw [inst_lam, consts_lam, List.mem_append] at hc
    rw [consts_lam, List.mem_append]
    rcases hc with hc | hc
    · exact Or.inl (inst_not_uses A a k hu.1 c hc)
    · exact Or.inr (inst_not_uses b a (k + 1) hu.2 c hc)
  | pi A _ B, a, k, hu, c, hc => by
    simp only [usesVar_pi, Bool.or_eq_false_iff] at hu
    rw [inst_pi, consts_pi, List.mem_append] at hc
    rw [consts_pi, List.mem_append]
    rcases hc with hc | hc
    · exact Or.inl (inst_not_uses A a k hu.1 c hc)
    · exact Or.inr (inst_not_uses B a (k + 1) hu.2 c hc)

/-- A lifted term uses no variable in the gap the lifting opens. -/
theorem usesVar_liftN_gap : ∀ (a : Expr) (n k i : Nat), k ≤ i → i < k + n →
    (a.liftN n k).usesVar i = false
  | bvar m, n, k, i, h1, h2 => by
    simp only [liftN_bvar, usesVar_bvar, decide_eq_false_iff_not]
    split <;> omega
  | sort _, _, _, _, _, _ => rfl
  | const _ _, _, _, _, _, _ => rfl
  | app f b, n, k, i, h1, h2 => by
    simp [usesVar_liftN_gap f n k i h1 h2, usesVar_liftN_gap b n k i h1 h2]
  | lam A _ b, n, k, i, h1, h2 => by
    simp [usesVar_liftN_gap A n k i h1 h2, usesVar_liftN_gap b n (k + 1) (i + 1) (by omega) (by omega)]
  | pi A _ B, n, k, i, h1, h2 => by
    simp [usesVar_liftN_gap A n k i h1 h2, usesVar_liftN_gap B n (k + 1) (i + 1) (by omega) (by omega)]

/-- Instantiation at a higher index leaves the use of a lower variable
alone. -/
theorem usesVar_inst_lt : ∀ (e a : Expr) (i k : Nat), i < k →
    (e.inst a k).usesVar i = e.usesVar i
  | bvar j, a, i, k, hik => by
    rw [inst_bvar]
    by_cases h1 : j < k
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : j = k
      · rw [if_pos h2, usesVar_liftN_gap a k 0 i (Nat.zero_le _) (by omega)]
        simp only [usesVar_bvar]
        rw [show (decide (j = i)) = false by simp; omega]
      · rw [if_neg h2]
        simp only [usesVar_bvar]
        congr 1
        apply propext
        omega
  | sort _, _, _, _, _ => rfl
  | const _ _, _, _, _, _ => rfl
  | app f b, a, i, k, hik => by
    simp only [inst_app, usesVar_app, usesVar_inst_lt f a i k hik, usesVar_inst_lt b a i k hik]
  | lam A _ b, a, i, k, hik => by
    simp only [inst_lam, usesVar_lam, usesVar_inst_lt A a i k hik,
      usesVar_inst_lt b a (i + 1) (k + 1) (by omega)]
  | pi A _ B, a, i, k, hik => by
    simp only [inst_pi, usesVar_pi, usesVar_inst_lt A a i k hik,
      usesVar_inst_lt B a (i + 1) (k + 1) (by omega)]

/-- Instantiation keeps a term closed: closed below `j + 1` with the
argument closed below `j - k` (it is lifted by `k`), the instance is
closed below `j`. -/
theorem closedAt_inst : ∀ (e a : Expr) (k j : Nat), k ≤ j → e.closedAt (j + 1) = true →
    a.closedAt (j - k) = true → (e.inst a k).closedAt j = true
  | bvar i, a, k, j, hkj, he, ha => by
    simp only [closedAt_bvar, decide_eq_true_eq] at he
    rw [inst_bvar]
    by_cases h1 : i < k
    · rw [if_pos h1]; simp only [closedAt_bvar, decide_eq_true_eq]; omega
    · rw [if_neg h1]
      by_cases h2 : i = k
      · rw [if_pos h2]
        have := closedAt_liftN (n := k) (k := 0) ha
        rwa [Nat.sub_add_cancel hkj] at this
      · rw [if_neg h2]; simp only [closedAt_bvar, decide_eq_true_eq]; omega
  | sort _, _, _, _, _, _, _ => rfl
  | const _ _, _, _, _, _, _, _ => rfl
  | app f b, a, k, j, hkj, he, ha => by
    simp only [closedAt_app, Bool.and_eq_true] at he
    simp only [inst_app, closedAt_app, Bool.and_eq_true]
    exact ⟨closedAt_inst f a k j hkj he.1 ha, closedAt_inst b a k j hkj he.2 ha⟩
  | lam A _ b, a, k, j, hkj, he, ha => by
    simp only [closedAt_lam, Bool.and_eq_true] at he
    simp only [inst_lam, closedAt_lam, Bool.and_eq_true]
    exact ⟨closedAt_inst A a k j hkj he.1 ha,
      closedAt_inst b a (k + 1) (j + 1) (by omega) he.2 (by rwa [Nat.add_sub_add_right])⟩
  | pi A _ B, a, k, j, hkj, he, ha => by
    simp only [closedAt_pi, Bool.and_eq_true] at he
    simp only [inst_pi, closedAt_pi, Bool.and_eq_true]
    exact ⟨closedAt_inst A a k j hkj he.1 ha,
      closedAt_inst B a (k + 1) (j + 1) (by omega) he.2 (by rwa [Nat.add_sub_add_right])⟩

/-- Instantiation uses the level parameters of the term and the
argument. -/
theorem lparamsIn_inst {ps : List Name} : ∀ (e a : Expr) (k : Nat), e.lparamsIn ps = true →
    a.lparamsIn ps = true → (e.inst a k).lparamsIn ps = true
  | bvar i, a, k, _, ha => by
    rw [inst_bvar]
    split
    · rfl
    · split
      · rw [lparamsIn_liftN]; exact ha
      · rfl
  | sort _, _, _, he, _ => he
  | const _ _, _, _, he, _ => he
  | app f b, a, k, he, ha => by
    simp only [lparamsIn_app, Bool.and_eq_true] at he
    simp only [inst_app, lparamsIn_app, Bool.and_eq_true]
    exact ⟨lparamsIn_inst f a k he.1 ha, lparamsIn_inst b a k he.2 ha⟩
  | lam A _ b, a, k, he, ha => by
    simp only [lparamsIn_lam, Bool.and_eq_true] at he
    simp only [inst_lam, lparamsIn_lam, Bool.and_eq_true]
    exact ⟨⟨lparamsIn_inst A a k he.1.1 ha, he.1.2⟩, lparamsIn_inst b a (k + 1) he.2 ha⟩
  | pi A _ B, a, k, he, ha => by
    simp only [lparamsIn_pi, Bool.and_eq_true] at he
    simp only [inst_pi, lparamsIn_pi, Bool.and_eq_true]
    exact ⟨⟨lparamsIn_inst A a k he.1.1 ha, he.1.2⟩, lparamsIn_inst B a (k + 1) he.2 ha⟩

/-- Level instantiation touches no variable. -/
theorem usesVar_instL (ps : List Name) (ls : List Level) : ∀ (e : Expr) (i : Nat),
    (e.instL ps ls).usesVar i = e.usesVar i
  | bvar _, _ => rfl
  | sort _, _ => rfl
  | const _ _, _ => rfl
  | app f a, i => by simp only [instL_app, usesVar_app, usesVar_instL ps ls f i, usesVar_instL ps ls a i]
  | lam A _ b, i => by
    simp only [instL_lam, usesVar_lam, usesVar_instL ps ls A i, usesVar_instL ps ls b (i + 1)]
  | pi A _ B, i => by
    simp only [instL_pi, usesVar_pi, usesVar_instL ps ls A i, usesVar_instL ps ls B (i + 1)]

/-- The substitution chain keeps a term closed: closed below the
substituted binders, `d` and `j`, with every argument closed below
`j`, the result is closed below `d + j`. -/
theorem closedAt_instChainAt : ∀ (as : List Expr) (e : Expr) (d j : Nat),
    e.closedAt (d + as.length + j) = true → (∀ a ∈ as, a.closedAt j = true) →
    (instChainAt e as d).closedAt (d + j) = true
  | [], e, d, j, he, _ => by simpa using he
  | a :: as, e, d, j, he, has => by
    rw [instChainAt_cons]
    refine closedAt_instChainAt as _ d j ?_ fun b hb => has b (List.mem_cons_of_mem a hb)
    refine closedAt_inst e a (d + as.length) (d + as.length + j) (by omega) ?_ ?_
    · rw [show d + as.length + j + 1 = d + (a :: as).length + j by simp; omega]; exact he
    · rw [Nat.add_sub_cancel_left]; exact has a List.mem_cons_self

/-- The substitution chain mentions the constants of the term and of
the arguments. -/
theorem consts_instChainAt : ∀ (as : List Expr) (e : Expr) (d : Nat) (c : Name),
    c ∈ (instChainAt e as d).consts → c ∈ e.consts ∨ ∃ a ∈ as, c ∈ a.consts
  | [], _, _, _, hc => Or.inl hc
  | a :: as, e, d, c, hc => by
    rw [instChainAt_cons] at hc
    rcases consts_instChainAt as _ d c hc with h | ⟨b, hb, h⟩
    · rcases consts_inst h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, h⟩

/-- The substitution chain, when the term does not use the `p`-th
binder (outermost first): the constants are the term's and those of
the OTHER arguments — the `p`-th is never inserted. -/
theorem consts_instChainAt_skip : ∀ (as : List Expr) (e : Expr) (d p : Nat), p < as.length →
    e.usesVar (d + as.length - 1 - p) = false →
    ∀ c ∈ (instChainAt e as d).consts,
      c ∈ e.consts ∨ ∃ i b, as[i]? = some b ∧ i ≠ p ∧ c ∈ b.consts
  | [], _, _, _, hp, _, _, _ => by simp at hp
  | a :: as, e, d, 0, _, hu, c, hc => by
    rw [instChainAt_cons] at hc
    rw [show d + (a :: as).length - 1 - 0 = d + as.length by simp] at hu
    rcases consts_instChainAt as _ d c hc with h | ⟨b, hb, h⟩
    · exact Or.inl (inst_not_uses e a _ hu c h)
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
      exact Or.inr ⟨i + 1, b, by simpa using hi, by omega, h⟩
  | a :: as, e, d, p + 1, hp, hu, c, hc => by
    rw [instChainAt_cons] at hc
    have hp' : p < as.length := by simp at hp; omega
    have hu' : (e.inst a (d + as.length)).usesVar (d + as.length - 1 - p) = false := by
      rw [usesVar_inst_lt _ _ _ _ (by omega)]
      rw [show d + (a :: as).length - 1 - (p + 1) = d + as.length - 1 - p by simp; omega] at hu
      exact hu
    rcases consts_instChainAt_skip as _ d p hp' hu' c hc with h | ⟨i, b, hi, hip, h⟩
    · rcases consts_inst h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨0, a, rfl, by omega, h⟩
    · exact Or.inr ⟨i + 1, b, by simpa using hi, by omega, h⟩

/-- The substitution chain uses the level parameters of the term and
the arguments. -/
theorem lparamsIn_instChainAt {ps : List Name} : ∀ (as : List Expr) (e : Expr) (d : Nat),
    e.lparamsIn ps = true → (∀ a ∈ as, a.lparamsIn ps = true) →
    (instChainAt e as d).lparamsIn ps = true
  | [], _, _, he, _ => he
  | a :: as, e, d, he, has => by
    rw [instChainAt_cons]
    exact lparamsIn_instChainAt as _ d (lparamsIn_inst e a _ he (has a List.mem_cons_self))
      fun b hb => has b (List.mem_cons_of_mem a hb)

end Expr

/-! ## Level instantiation keeps a term over the substitutes' parameters -/

namespace Level

theorem paramsIn_lookupLevel {ps qs : List Name} {ls : List Level} (hl : ∀ l ∈ ls, l.paramsIn qs = true)
    (hlen : ls.length = ps.length) {n : Name} (hn : n ∈ ps) :
    (lookupLevel ps ls n).paramsIn qs = true := by
  induction ps generalizing ls with
  | nil => simp at hn
  | cons p ps ih =>
    cases ls with
    | nil => simp at hlen
    | cons l ls =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [lookupLevel, List.zip_cons_cons, List.lookup_cons]
      by_cases h : n = p
      · subst h; simp only [beq_self_eq_true]; exact hl l List.mem_cons_self
      · have hb : (n == p) = false := by simpa using h
        rw [hb]
        have := ih (fun l' hl' => hl l' (List.mem_cons_of_mem l hl')) hlen
          (List.mem_of_ne_of_mem h hn)
        simpa [lookupLevel] using this

theorem paramsIn_subst {ps qs : List Name} {ls : List Level} (hl : ∀ l ∈ ls, l.paramsIn qs = true)
    (hlen : ls.length = ps.length) : ∀ {l : Level}, l.paramsIn ps = true →
    (subst ps ls l).paramsIn qs = true
  | zero, _ => rfl
  | succ l, h => by simpa [subst] using paramsIn_subst hl hlen (l := l) h
  | max a b, h => by
    simp only [paramsIn_max, Bool.and_eq_true] at h
    simp [subst, paramsIn_subst hl hlen h.1, paramsIn_subst hl hlen h.2]
  | imax a b, h => by
    simp only [paramsIn_imax, Bool.and_eq_true] at h
    simp [subst, paramsIn_subst hl hlen h.1, paramsIn_subst hl hlen h.2]
  | param n, h => by
    rw [paramsIn_param, List.contains_iff_mem] at h
    exact paramsIn_lookupLevel hl hlen h

end Level

namespace PropWhen

theorem paramsIn_substL {ps qs : List Name} {ls : List Level} (hl : ∀ l ∈ ls, l.paramsIn qs = true)
    (hlen : ls.length = ps.length) : ∀ {pw : PropWhen}, pw.paramsIn ps = true →
    (substL ps ls pw).paramsIn qs = true
  | never, _ => rfl
  | whenZero s, h => by
    simp only [paramsIn_whenZero, List.all_eq_true, List.contains_iff_mem] at h
    rw [substL]
    suffices key : ∀ L : List Name, (∀ n ∈ L, n ∈ ps) →
        (L.foldr (fun q acc => (Level.zeroness (Level.lookupLevel ps ls q)).inter acc) always).paramsIn qs
          = true from key s.list h
    intro L
    induction L with
    | nil => intro _; rfl
    | cons n L ih =>
      intro hL
      simp only [List.foldr_cons]
      have h1 := IndSpec.Level.zeroness_paramsIn (ps := qs)
        (Level.paramsIn_lookupLevel hl hlen (hL n List.mem_cons_self))
      have h2 := ih fun m hm => hL m (List.mem_cons_of_mem n hm)
      rw [IndSpec.PropWhen.paramsIn_iff] at h1 h2 ⊢
      intro t ht m hm
      cases hz : Level.zeroness (Level.lookupLevel ps ls n) with
      | never => rw [hz] at ht; simp [inter] at ht
      | whenZero u =>
        rw [hz] at ht
        cases hw : L.foldr (fun q acc => (Level.zeroness (Level.lookupLevel ps ls q)).inter acc) always with
        | never => rw [hw] at ht; simp [inter] at ht
        | whenZero w =>
          rw [hw] at ht
          simp only [inter, whenZero.injEq] at ht
          subst ht
          rcases ParamSet.mem_union.mp hm with hm | hm
          · exact h1 u hz m hm
          · exact h2 w hw m hm

end PropWhen

namespace Expr

/-- Level instantiation keeps a term over the substitutes' parameters. -/
theorem lparamsIn_instL {ps qs : List Name} {ls : List Level} (hl : ∀ l ∈ ls, l.paramsIn qs = true)
    (hlen : ls.length = ps.length) : ∀ {e : Expr}, e.lparamsIn ps = true →
    (e.instL ps ls).lparamsIn qs = true
  | bvar _, _ => rfl
  | sort u, h => by
    rw [lparamsIn_sort] at h
    rw [instL_sort, lparamsIn_sort]
    exact Level.paramsIn_subst hl hlen h
  | const _ us, h => by
    simp only [lparamsIn_const, List.all_eq_true] at h
    simp only [instL_const, lparamsIn_const, List.all_eq_true, List.mem_map]
    rintro _ ⟨u, hu, rfl⟩
    exact Level.paramsIn_subst hl hlen (h u hu)
  | app f a, h => by
    simp only [lparamsIn_app, Bool.and_eq_true] at h
    simp [lparamsIn_instL hl hlen h.1, lparamsIn_instL hl hlen h.2]
  | lam A pw b, h => by
    simp only [lparamsIn_lam, Bool.and_eq_true] at h
    simp [lparamsIn_instL hl hlen h.1.1, PropWhen.paramsIn_substL hl hlen h.1.2,
      lparamsIn_instL hl hlen h.2]
  | pi A pw B, h => by
    simp only [lparamsIn_pi, Bool.and_eq_true] at h
    simp [lparamsIn_instL hl hlen h.1.1, PropWhen.paramsIn_substL hl hlen h.1.2,
      lparamsIn_instL hl hlen h.2]

end Expr

/-! ## The translated constructors are in the block's scope -/

namespace IndSpec

variable (S : IndSpec) {env : Env} (N : NestInfo)

theorem length_classArgs (hlen : N.args.length + 1 = N.nPK) (hpK : N.p < N.nPK) (o : Nat) :
    (S.classArgs N o).length = N.nPK := by
  have hp : N.p ≤ N.args.length := by omega
  simp [classArgs, List.length_take, List.length_drop, Nat.min_eq_left hp]
  omega

/-- An argument of the class other than the member is one of the
container's other arguments, lifted. -/
theorem classArgs_getElem?_ne (hlen : N.args.length + 1 = N.nPK) (hpK : N.p < N.nPK) (o : Nat)
    {i : Nat} (hi : i < N.nPK) (hip : i ≠ N.p) :
    ∃ a ∈ N.args, (S.classArgs N o)[i]? = some (Expr.liftN o a) := by
  have hp : N.p ≤ N.args.length := by omega
  have hlt1 : ((N.args.take N.p).map (Expr.liftN o ·)).length = N.p := by
    simp [List.length_take, Nat.min_eq_left hp]
  unfold classArgs
  by_cases hlt : i < N.p
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by rw [hlt1]; exact hlt),
      List.getElem?_map, List.getElem?_take_of_lt hlt]
    obtain ⟨a, ha⟩ : ∃ a, N.args[i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨a, List.mem_of_getElem? ha, by rw [ha]; rfl⟩
  · have hgt : N.p < i := by omega
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_map, List.getElem?_drop]
    simp only [List.length_append, hlt1, List.length_singleton]
    obtain ⟨a, ha⟩ : ∃ a, N.args[N.p + (i - (N.p + 1))]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨a, List.mem_of_getElem? ha, by rw [ha]; rfl⟩

/-- The class's arguments are closed under the block's parameters. -/
theorem classArgs_closedAt (hS : S.Scoped env) (hN : S.nest = some N) (o : Nat) :
    ∀ a ∈ S.classArgs N o, a.closedAt (S.nP + o) = true := by
  have hNS := hS.2.2.2.2.2.2 N hN
  intro a ha
  have hlift : ∀ e, e.closedAt S.nP = true → (Expr.liftN o e).closedAt (S.nP + o) = true :=
    fun e he => Expr.closedAt_liftN (n := o) (k := 0) he
  simp only [classArgs, List.mem_append, List.mem_map, List.mem_singleton] at ha
  rcases ha with (⟨b, hb, rfl⟩ | rfl) | ⟨b, hb, rfl⟩
  · exact hlift b (hNS.2.2.2.2.2.2.1 b (List.mem_of_mem_take hb)).1
  · refine Expr.closedAt_mkAppN rfl fun e he => ?_
    rcases List.mem_append.mp he with he | he
    · exact Expr.closedAt_varsAt (by omega) e he
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact hlift b (hNS.2.2.2.2.2.2.2.1 b hb).1
  · exact hlift b (hNS.2.2.2.2.2.2.1 b (List.mem_of_mem_drop hb)).1

/-- The class's arguments use the block's level parameters. -/
theorem classArgs_lparamsIn' (hS : S.Scoped env) (hN : S.nest = some N) (o : Nat) :
    ∀ a ∈ S.classArgs N o, a.lparamsIn S.lparams = true :=
  S.lparamsIn_classArgs hS hN o

/-- **A translated field is in the block's scope.** -/
theorem classField_scoped (hS : S.Scoped env) (hN : S.nest = some N) (hKS : N.KS.Scoped env)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) {i : Nat} {f : Field} (hi : c.fields[i]? = some f) :
    S.fieldScoped env (c.fields.length - 1 - i) (S.classField N (c.fields.length - 1 - i) f) := by
  have hNS := hS.2.2.2.2.2.2 N hN
  have hpos := hNS.2.2.2.2.2.2.2.2.1
  have hpf := positive_field N hpos hc (List.drop_zero (l := c.fields)) hi
  have hlen := hNS.2.2.2.2.1
  have hpK : N.p < N.nPK := hpos.2.1
  obtain ⟨k, hk⟩ : ∃ k, c.fields.length - 1 - i = k := ⟨_, rfl⟩
  have hsc0 := (hKS.2.2.2.1 c hc).1 i _ hi
  rw [hk] at hsc0 hpf ⊢
  cases f with
  | ordinary A =>
    rcases hpf with rfl | ⟨hu, -⟩
    · simp only [classField, NestInfo.isMember, beq_self_eq_true, if_true, fieldScoped]
      refine ⟨fun _ _ hT => by simp at hT, by simpa using hNS.2.2.2.2.2.1, fun e he => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      have hb' := hNS.2.2.2.2.2.2.2.1 b hb
      exact ⟨Expr.closedAt_liftN (n := k) (k := 0) hb'.1, by rw [Expr.consts_liftN]; exact hb'.2.1,
        by rw [Expr.lparamsIn_liftN]; exact hb'.2.2⟩
    · rw [classField, if_neg (by rw [isMember_false_of_usesVar N hu]; exact Bool.false_ne_true)]
      have hsc : Expr.Scoped env N.KS.lparams (N.KS.nP + k) A := hsc0
      have hnPK : N.KS.nP = N.nPK := rfl
      have hargs : (S.classArgs N 0).length = N.nPK := S.length_classArgs N hlen hpK 0
      refine ⟨?_, ?_, ?_⟩
      · -- closed
        have := Expr.closedAt_instChainAt (S.classArgs N 0) (A.instL N.KS.lparams N.lsK) k S.nP
          (by rw [Expr.closedAt_instL, hargs]
              exact Expr.closedAt_mono (by rw [hnPK]; omega) hsc.1)
          (fun a ha => by simpa using S.classArgs_closedAt N hS hN 0 a ha)
        rwa [Nat.add_comm] at this
      · -- constants: the member's expression is never inserted
        intro d hd
        rcases Expr.consts_instChainAt_skip (S.classArgs N 0) _ k N.p (by omega)
          (by rw [hargs, Expr.usesVar_instL]; exact hu) d hd with h | ⟨j, b, hj, hjp, h⟩
        · rw [Expr.consts_instL] at h
          exact hsc.2.1 d h
        · have hjl : j < N.nPK := by
            rw [← hargs]; exact (List.getElem?_eq_some_iff.mp hj).1
          obtain ⟨a, ha, he⟩ := S.classArgs_getElem?_ne N hlen hpK 0 hjl hjp
          rw [he] at hj
          cases hj
          rw [Expr.consts_liftN] at h
          exact (hNS.2.2.2.2.2.2.1 a ha).2.1 d h
      · -- level parameters
        refine Expr.lparamsIn_instChainAt _ _ _ ?_ (S.classArgs_lparamsIn' N hS hN 0)
        exact Expr.lparamsIn_instL hNS.2.2.2.1 hNS.2.2.1 hsc.2.2
  | reflexive _ _ => simp [classField, fieldScoped, hN]
  | container => exact hpf.elim

/-- **The translated constructor's fields are in the block's scope**,
so the block's readers read its context. -/
theorem classCtor_fieldScoped (hS : S.Scoped env) (hN : S.nest = some N) (hKS : N.KS.Scoped env)
    {c : CtorSpec} (hc : c ∈ N.K.ctors) :
    ∀ i f, (S.classCtor N c).fields[i]? = some f →
      S.fieldScoped env ((S.classCtor N c).fields.length - 1 - i) f := by
  intro i f hf
  simp only [classCtor] at hf ⊢
  rw [S.classFields_getElem?, Option.map_eq_some_iff] at hf
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  rw [S.length_classFields]
  exact S.classField_scoped N hS hN hKS hc hf₀

/-! ## The sets of the two recursors -/

section Sets

variable {V : Type u} [IndLibCompat V] (M : Name → List Nat → V)

/-- **`T.rec`'s set** at its levels `lsr`: the abstraction over its
context — the parameters, the two motives, both minor lists, the
indices, the major — of `T.rec`'s semantic value. -/
noncomputable def recSetN (N : NestInfo) (lsr : List Nat) : V :=
  let ψr := valOf S.recLparams lsr
  let ls := S.lparams.map ψr
  let q := S.q.holds ψr
  lamCtx (S.M₂ M) ψr q base (S.recCtxN N) fun ρ' =>
    S.recSemN M ls N q (readEnv S.nP (shiftE (1 + S.nI + S.oN N) 0 ρ'))
      ⟨ρ' (S.nI + S.oN N), ρ' (S.nI + S.oN N - 1),
        readEnv S.n (shiftE (1 + S.nI + N.nK) 0 ρ'), readEnv N.nK (shiftE (1 + S.nI) 0 ρ')⟩
      (readEnv S.nI (shiftE 1 0 ρ')) (ρ' 0)

/-- **`T.rec_1`'s set** at its levels: the abstraction over its context
— the same prefix, the major at the class — of `T.rec_1`'s semantic
value. -/
noncomputable def rec1Set (N : NestInfo) (lsr : List Nat) : V :=
  let ψr := valOf S.recLparams lsr
  let ls := S.lparams.map ψr
  let q := S.q.holds ψr
  lamCtx (S.M₂ M) ψr q base (S.rec1Ctx N) fun ρ' =>
    S.rec1Sem M ls N q (readEnv S.nP (shiftE (1 + S.oN N) 0 ρ'))
      ⟨ρ' (S.oN N), ρ' (S.oN N - 1),
        readEnv S.n (shiftE (1 + N.nK) 0 ρ'), readEnv N.nK (shiftE 1 0 ρ')⟩
      (ρ' 0)

/-- **The model of the installed nested block**: the two recursors on
top of the former and the constructors. -/
noncomputable def M₃N (N : NestInfo) : Name → List Nat → V :=
  fun n ls' =>
    if n = N.aux then S.rec1Set M N ls'
    else if n = S.recName then S.recSetN M N ls' else S.M₂ M n ls'

end Sets

/-! ## The nested recursors' contexts, read

What the readers say about the generated contexts of the two
recursors: the extras' context, both recursors' contexts, the rules'
contexts and the minor premises, with the class's minors' conclusion
read through the container's constructor's set. -/

section Readings

variable {V : Type u} [IndLibCompat V] {M : Name → List Nat → V} {φ : Name → Nat} {env : Env}
  {M' : Name → List Nat → V} {φ' : Name → Nat}

/-! ### Small pieces -/

/-- The two values at the end of a pushed list, by position. -/
theorem getD_append_two {vs : List V} (a b : V) :
    (vs ++ [a, b]).getD vs.length pt = a ∧ (vs ++ [a, b]).getD (vs.length + 1) pt = b := by
  constructor
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; rfl

omit [IndLibCompat V] in
/-- A list splits at any length it has. -/
theorem exists_split {l : List V} {a : Nat} (h : a ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = a :=
  ⟨l.take a, l.drop a, (List.take_append_drop _ _).symm, by simp [List.length_take]; omega⟩

/-- Pointwise equivalent relations relate the same lists. -/
theorem ListRel_iff {α β : Type _} {R R' : α → β → Prop} (h : ∀ a b, R a b ↔ R' a b)
    {l : List α} {l' : List β} : ListRel R l l' ↔ ListRel R' l l' :=
  ⟨ListRel.mono (fun a b => (h a b).mp), ListRel.mono (fun a b => (h a b).mpr)⟩

/-- Distinct level parameters read back the concrete levels assigned
to them positionally. -/
theorem map_valOf_eq : ∀ {ps : List Name}, ps.Nodup → ∀ {ls : List Nat}, ls.length = ps.length →
    ps.map (valOf ps ls) = ls
  | [], _, [], _ => rfl
  | [], _, _ :: _, hlen => by simp at hlen
  | _ :: _, _, [], hlen => by simp at hlen
  | p :: ps, hnd, l :: ls, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨by simp [valOf], ?_⟩
    calc ps.map (valOf (p :: ps) (l :: ls)) = ps.map (valOf ps ls) := by
          refine List.map_congr_left fun n hn => ?_
          have hne : (n == p) = false := by
            have : n ≠ p := fun h => hp (h ▸ hn)
            simpa using this
          simp [valOf, List.zip_cons_cons, List.lookup_cons, hne]
      _ = ls := map_valOf_eq hnd' hlen

/-- The nested hypothesis typing is the plain one at the extras' two
motives. -/
theorem IhTypedN_iff {ls : List Nat} {q : Bool} {ps : List V} {ex : RecEx V} {fs : List V}
    {kf : Nat × Field} {ih : V} :
    S.IhTypedN M ls q ps ex fs kf ih ↔ S.IhTyped M ls q ps ex.m ex.m1 fs kf ih := by
  obtain ⟨k, f⟩ := kf
  cases f <;> exact Iff.rfl

/-! ### The generated contexts, entry by entry -/

/-- A context of one generated entry per constructor, as a recursion
(innermost first): the later constructors' entries, then this one
outermost — `minorsFrom` for any generator. -/
def ctxFrom (T : CtorSpec → Nat → Expr) : List CtorSpec → Nat → List Expr
  | [], _ => []
  | c :: cs, j => ctxFrom T cs (j + 1) ++ [T c j]

theorem ctxFrom_eq (T : CtorSpec → Nat → Expr) : ∀ (cs : List CtorSpec) (j : Nat),
    ((List.range cs.length).map fun i => T (cs.getD i ⟨"", [], []⟩) (j + i)).reverse
      = ctxFrom T cs j
  | [], _ => rfl
  | c :: cs, j => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
    simp only [ctxFrom, List.getD_cons_zero, Nat.add_zero]
    congr 1
    rw [← ctxFrom_eq T cs (j + 1)]
    congr 1
    apply List.map_congr_left
    intro i _
    simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]

theorem length_ctxFrom (T : CtorSpec → Nat → Expr) :
    ∀ (cs : List CtorSpec) (j : Nat), (ctxFrom T cs j).length = cs.length
  | [], _ => rfl
  | _ :: cs, j => by simp [ctxFrom, length_ctxFrom T cs (j + 1)]

theorem minorsCtxN_eq : S.minorsCtxN = ctxFrom S.minorTyN S.ctors 0 := by
  rw [minorsCtxN, ← ctxFrom_eq]
  simp [n]

theorem minorsCtxK_eq : S.minorsCtxK N = ctxFrom (S.minorTyK N) N.K.ctors 0 := by
  rw [minorsCtxK, ← ctxFrom_eq]
  simp [NestInfo.nK]

theorem length_minorsCtxN : S.minorsCtxN.length = S.n := by
  rw [minorsCtxN_eq, length_ctxFrom]; rfl

theorem length_minorsCtxK : (S.minorsCtxK N).length = N.nK := by
  rw [minorsCtxK_eq, length_ctxFrom]; rfl

theorem length_extrasN : (S.extrasN N).length = S.oN N := by
  simp only [extrasN, List.length_append, length_minorsCtxK, length_minorsCtxN, List.length_cons,
    List.length_nil, oN]
  omega

theorem length_recCtxN : (S.recCtxN N).length = 1 + S.nI + S.oN N + S.nP := by
  simp only [recCtxN, List.length_cons, List.length_append, length_indicesAt, length_extrasN, nP]
  omega

theorem length_rec1Ctx : (S.rec1Ctx N).length = 1 + S.oN N + S.nP := by
  simp only [rec1Ctx, List.length_cons, List.length_append, length_extrasN, nP]
  omega

/-- **A context of one entry per constructor, read**: each value is a
member of its entry under the values before it. -/
theorem fits_ctxFrom (T : CtorSpec → Nat → Expr) :
    ∀ (cs : List CtorSpec) (j : Nat) (E : Nat → V) (minsI : List V),
      FitsVals M' φ' E (ctxFrom T cs j) minsI →
      ∀ i c, cs[i]? = some c →
        minsI.getD (cs.length - 1 - i) pt ∈ˢ
          interp M' φ' (consList (minsI.drop (cs.length - i)) E) (T c (j + i))
  | [], _, _, _, _, i, _, h => by simp at h
  | c :: cs, j, E, minsI, hfit, i, c', hc' => by
    have hlen := FitsVals_length M' φ' hfit
    simp only [ctxFrom, List.length_append, length_ctxFrom, List.length_singleton] at hlen
    obtain ⟨minsI', v, rfl⟩ : ∃ minsI' v, minsI = minsI' ++ [v] := by
      rcases List.eq_nil_or_concat minsI with h | ⟨l, v, h⟩
      · subst h; simp at hlen
      · exact ⟨l, v, by simpa [List.concat_eq_append] using h⟩
    have hl' : minsI'.length = (ctxFrom T cs (j + 1)).length := by
      rw [length_ctxFrom]; simp at hlen; omega
    obtain ⟨h1, h2⟩ := (FitsVals_append M' φ' hl').mp hfit
    have hl'' : minsI'.length = cs.length := by rw [hl', length_ctxFrom]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc'
      subst hc'
      have hd : (minsI' ++ [v]).drop ((c :: cs).length - 0) = [] := by
        simp [hl'']
      rw [hd, consList_nil, show (c :: cs).length - 1 - 0 = minsI'.length by simp [hl''],
        getD_append_length, Nat.add_zero]
      simpa [FitsVals] using h1.2
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc'
      have hi : i < cs.length := (List.getElem?_eq_some_iff.mp hc').1
      have ih := fits_ctxFrom T cs (j + 1) (cons v E) minsI' h2 i c' hc'
      rw [show (c :: cs).length - 1 - (i + 1) = cs.length - 1 - i by simp only [List.length_cons]; omega,
        show (c :: cs).length - (i + 1) = cs.length - i by simp only [List.length_cons]; omega,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD, List.drop_append_of_le_length (by omega), consList_append,
        show j + (i + 1) = j + 1 + i by omega]
      exact ih

theorem ihCtxAt_eq (c : CtorSpec) (o : Nat) :
    S.ihCtxAt c o = S.ihCtxAux c.fields.length o c.recFields 0 := by
  rw [ihCtxAt, ← ihCtxAux_eq]
  simp

/-! ### The class's motive -/

/-- The class's motive's type, read: the product over the class into
the elimination universe. -/
theorem Reader.read_motiveTy1 (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (hN : S.nest = some N) {ps : List V} {m : V} {ρ : Nat → V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps)) :
    interp M' φ' (cons m (consList ps ρ)) (S.motiveTy1 N)
      = piSet (S.classAt M (S.lparams.map φ) N ps) fun _ => univ (Level.eval φ' S.ℓ) := by
  unfold motiveTy1
  rw [interp_mkPis, PropWhen.holds_never, piCtx_cons, piCtx_nil, piR_false]
  have := R.classTy_fit hS hN (vs := [m]) (k := 1) (ps := ps) (ρ := ρ) rfl hps hp hidx
  rw [consList_cons, consList_nil] at this
  rw [this]
  rfl

/-- **The class's motive's typing**: a member of its type sends a
member of the class into the elimination universe. -/
theorem Reader.motive1Ok_of_mem (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (hN : S.nest = some N) {ps : List V} {m m1 : V} {ρ : Nat → V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps))
    (hm1 : m1 ∈ˢ interp M' φ' (cons m (consList ps ρ)) (S.motiveTy1 N)) :
    ∀ t, t ∈ˢ S.classAt M (S.lparams.map φ) N ps →
      appList m1 [t] ∈ˢ (univ (Level.eval φ' S.ℓ) : V) := by
  intro t ht
  rw [Reader.read_motiveTy1 S N hS R hN hps hp hidx] at hm1
  rw [appList_cons, appList_nil]
  exact app_mem_piSet hm1 ht

/-! ### The two recursors' contexts -/

/-- **Values fitting `T.rec`'s context**: the parameters fit, the two
motives are in their types, both minor lists fit, the indices fit and
the major is in the fibre — and conversely. -/
theorem Reader.fits_recCtxN_iff (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    {ρ : Nat → V} {t : V} {is minsK mins : List V} {m1 m : V} {ps : List V}
    (hi : is.length = S.nI) (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n)
    (hps : ps.length = S.nP) :
    FitsVals M' φ' ρ (S.recCtxN N) (t :: is ++ minsK ++ mins ++ [m1, m] ++ ps) ↔
      FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps ∧
      m ∈ˢ interp M' φ' (consList ps ρ) S.motiveTy ∧
      m1 ∈ˢ interp M' φ' (cons m (consList ps ρ)) (S.motiveTy1 N) ∧
      FitsVals M' φ' (consList [m1, m] (consList ps ρ)) S.minorsCtxN mins ∧
      FitsVals M' φ' (consList (mins ++ [m1, m]) (consList ps ρ)) (S.minorsCtxK N) minsK ∧
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices is ∧
      t ∈ˢ S.Fam M (S.lparams.map φ) ps is := by
  have hosl : (minsK ++ mins ++ [m1, m]).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have e1 : t :: is ++ minsK ++ mins ++ [m1, m] = (t :: is) ++ (minsK ++ mins ++ [m1, m]) := by simp
  have e2 : consList mins (consList [m1, m] (consList ps ρ))
      = consList (mins ++ [m1, m]) (consList ps ρ) := by
    rw [consList_append]
  unfold recCtxN extrasN
  rw [FitsVals_append M' φ' (by simp [hi, hminsK, hmins, length_indicesAt, length_minorsCtxN,
      length_minorsCtxK]),
    e1, FitsVals_append M' φ' (by simp [hi, length_indicesAt]),
    FitsVals_append M' φ' (by simp [hminsK, hmins, length_minorsCtxN, length_minorsCtxK]),
    FitsVals_append M' φ' (by simp [hminsK, length_minorsCtxK]), e2, FitsVals_cons]
  simp only [FitsVals_cons, FitsVals_nil_nil, true_and, consList_cons, consList_nil]
  unfold indicesAt
  rw [FitsVals_liftCtx_liftN M' φ' _ _ _ hosl, R.fits_indices hS hps, R.fits_params hS]
  constructor
  · rintro ⟨hp, ⟨⟨hm, hm1⟩, hmn, hmnK⟩, his, ht⟩
    refine ⟨hp, hm, hm1, hmn, hmnK, his, ?_⟩
    rwa [R.read_famVars hS hosl hps hp his] at ht
  · rintro ⟨hp, hm, hm1, hmn, hmnK, his, ht⟩
    refine ⟨hp, ⟨⟨hm, hm1⟩, hmn, hmnK⟩, his, ?_⟩
    rwa [R.read_famVars hS hosl hps hp his]

/-- **Values fitting `T.rec_1`'s context**: as for `T.rec`, with the
major in the class. -/
theorem Reader.fits_rec1Ctx_iff (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (hN : S.nest = some N) {ρ : Nat → V} {t : V} {minsK mins : List V} {m1 m : V} {ps : List V}
    (hminsK : minsK.length = N.nK) (hmins : mins.length = S.n) (hps : ps.length = S.nP)
    (hidx : ∀ ps', FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps' →
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps') S.indices
        (S.memberIdx M (S.lparams.map φ) N ps')) :
    FitsVals M' φ' ρ (S.rec1Ctx N) (t :: minsK ++ mins ++ [m1, m] ++ ps) ↔
      FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps ∧
      m ∈ˢ interp M' φ' (consList ps ρ) S.motiveTy ∧
      m1 ∈ˢ interp M' φ' (cons m (consList ps ρ)) (S.motiveTy1 N) ∧
      FitsVals M' φ' (consList [m1, m] (consList ps ρ)) S.minorsCtxN mins ∧
      FitsVals M' φ' (consList (mins ++ [m1, m]) (consList ps ρ)) (S.minorsCtxK N) minsK ∧
      t ∈ˢ S.classAt M (S.lparams.map φ) N ps := by
  have hosl : (minsK ++ mins ++ [m1, m]).length = S.oN N := by
    simp only [List.length_append, List.length_cons, List.length_nil, hminsK, hmins, oN]; omega
  have e1 : t :: minsK ++ mins ++ [m1, m] = t :: (minsK ++ mins ++ [m1, m]) := by simp
  have e2 : consList mins (consList [m1, m] (consList ps ρ))
      = consList (mins ++ [m1, m]) (consList ps ρ) := by
    rw [consList_append]
  unfold rec1Ctx extrasN
  rw [FitsVals_append M' φ' (by simp [hminsK, hmins, length_minorsCtxN, length_minorsCtxK]),
    e1, FitsVals_cons,
    FitsVals_append M' φ' (by simp [hminsK, hmins, length_minorsCtxN, length_minorsCtxK]),
    FitsVals_append M' φ' (by simp [hminsK, length_minorsCtxK]), e2]
  simp only [FitsVals_cons, FitsVals_nil_nil, true_and, consList_cons, consList_nil]
  rw [R.fits_params hS]
  constructor
  · rintro ⟨hp, ⟨⟨hm, hm1⟩, hmn, hmnK⟩, ht⟩
    refine ⟨hp, hm, hm1, hmn, hmnK, ?_⟩
    rw [R.classTy_fit hS hN hosl hps hp (hidx ps hp)] at ht
    exact ht
  · rintro ⟨hp, hm, hm1, hmn, hmnK, ht⟩
    refine ⟨hp, ⟨⟨hm, hm1⟩, hmn, hmnK⟩, ?_⟩
    rw [R.classTy_fit hS hN hosl hps hp (hidx ps hp)]
    exact ht

/-- Any list fitting `T.rec`'s context splits as the major, the
indices, the class's minors, the block's minors, the two motives and
the parameters. -/
theorem fits_recCtxN_split (N : NestInfo) {ρ : Nat → V} {vs : List V}
    (h : FitsVals M' φ' ρ (S.recCtxN N) vs) :
    ∃ (t : V) (is minsK mins : List V) (m1 m : V) (ps : List V),
      vs = t :: is ++ minsK ++ mins ++ [m1, m] ++ ps ∧ is.length = S.nI ∧ minsK.length = N.nK ∧
        mins.length = S.n ∧ ps.length = S.nP := by
  have hl := FitsVals_length M' φ' h
  rw [length_recCtxN] at hl
  simp only [oN] at hl
  cases vs with
  | nil => simp at hl; omega
  | cons t rest =>
    simp only [List.length_cons] at hl
    obtain ⟨is, r₁, rfl, hi⟩ := exists_split (l := rest) (a := S.nI) (by omega)
    obtain ⟨minsK, r₂, rfl, hminsK⟩ := exists_split (l := r₁) (a := N.nK) (by simp at hl; omega)
    obtain ⟨mins, r₃, rfl, hmins⟩ := exists_split (l := r₂) (a := S.n) (by simp at hl; omega)
    obtain ⟨m1, m, ps, rfl⟩ : ∃ m1 m ps, r₃ = m1 :: m :: ps := by
      match r₃, (by simp at hl; omega : 2 ≤ r₃.length) with
      | m1 :: m :: ps, _ => exact ⟨m1, m, ps, rfl⟩
    refine ⟨t, is, minsK, mins, m1, m, ps, by simp, hi, hminsK, hmins, ?_⟩
    simp at hl; omega

/-- Any list fitting `T.rec_1`'s context splits likewise. -/
theorem fits_rec1Ctx_split (N : NestInfo) {ρ : Nat → V} {vs : List V}
    (h : FitsVals M' φ' ρ (S.rec1Ctx N) vs) :
    ∃ (t : V) (minsK mins : List V) (m1 m : V) (ps : List V),
      vs = t :: minsK ++ mins ++ [m1, m] ++ ps ∧ minsK.length = N.nK ∧
        mins.length = S.n ∧ ps.length = S.nP := by
  have hl := FitsVals_length M' φ' h
  rw [length_rec1Ctx] at hl
  simp only [oN] at hl
  cases vs with
  | nil => simp at hl; omega
  | cons t rest =>
    simp only [List.length_cons] at hl
    obtain ⟨minsK, r₂, rfl, hminsK⟩ := exists_split (l := rest) (a := N.nK) (by omega)
    obtain ⟨mins, r₃, rfl, hmins⟩ := exists_split (l := r₂) (a := S.n) (by simp at hl; omega)
    obtain ⟨m1, m, ps, rfl⟩ : ∃ m1 m ps, r₃ = m1 :: m :: ps := by
      match r₃, (by simp at hl; omega : 2 ≤ r₃.length) with
      | m1 :: m :: ps, _ => exact ⟨m1, m, ps, rfl⟩
    refine ⟨t, minsK, mins, m1, m, ps, by simp, hminsK, hmins, ?_⟩
    simp at hl; omega

/-! ### The translated fields, semantically -/

/-- **The class's arguments, read** under `k` values above the
parameters: the container's other arguments read under the
parameters, the family's fibre at the member's index values as the
member (`classTy_fit` without the head). -/
theorem Reader.classArgs_read (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (hN : S.nest = some N) {k : Nat} {vs ps : List V} {ρ : Nat → V}
    (hk : vs.length = k) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps)) :
    (S.classArgs N k).map (interp M' φ' (consList vs (consList ps ρ)))
      = S.classArgsV M (S.lparams.map φ) N ps
          (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) := by
  have hNS := hS.2.2.2.2.2.2 N hN
  have hsh : shiftE k 0 (consList vs (consList ps ρ)) = consList ps ρ := shiftE_consList' hk _
  have hread : ∀ e ∈ N.args, interp M' φ' (consList vs (consList ps ρ)) (e.liftN k)
      = interp M (S.ψ (S.lparams.map φ)) (envP ps) e := by
    intro e he
    rw [interp_liftN, hsh]
    have := R.read (hNS.2.2.2.2.2.2.1 e he) (vs := []) (ps := ps) (ρ := ρ) (by simp [hps])
    simpa using this
  unfold classArgs classArgsV
  simp only [List.map_append, List.map_map, List.map_singleton]
  congr 1
  · congr 1
    · exact List.map_congr_left fun e he => hread e (List.mem_of_mem_take he)
    · congr 1
      refine R.famAt_fit hS (o := k) (es := N.idx.map (Expr.liftN k ·)) (ρ'' := consList vs (consList ps ρ))
        (ps := ps) (by rw [← hk, shiftE_consList, readEnv_consList hps]) ?_ hp hidx
      unfold memberIdx idxVals
      congr 1
      rw [List.map_map]
      refine List.map_congr_left fun e he => ?_
      simp only [Function.comp]
      rw [interp_liftN, hsh]
      have := R.read (hNS.2.2.2.2.2.2.2.1 e he) (vs := []) (ps := ps) (ρ := ρ) (by simp [hps])
      simpa using this
  · exact List.map_congr_left fun e he => hread e (List.mem_of_mem_drop he)

/-- **A translated field's set is the block's own field set** at the
family's fibre at the member and no restriction: the member field
ranges over that fibre (its index expressions, lifted over the earlier
fields, read as the member's), a container field over the class at it
(both guards hold), an ordinary field over its domain. -/
theorem classFieldSet_classField (hN : S.nest = some N) (ls : List Nat) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hg : S.ContGood M ls)
    {vs : List V} {k : Nat} (hk : vs.length = k) (f₀ : Field) :
    S.classFieldSet M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps vs
        (S.classField N k f₀)
      = S.fieldSet M ls (S.bound M ls) (S.Mem M ls) ps vs (S.classField N k f₀) := by
  cases f₀ with
  | ordinary A =>
    simp only [classField]
    split
    · simp only [classFieldSet, fieldSet, piCtx_nil]
      rw [S.idxVals_liftN M ls ps hk]
      rfl
    · rfl
  | reflexive _ _ =>
    simp only [classField, classFieldSet, fieldSet, hN]
    rw [sep_true trivial, sep_true ⟨hp, hg⟩]
    rfl
  | container =>
    simp only [classField, classFieldSet, fieldSet, hN]
    rw [sep_true trivial, sep_true ⟨hp, hg⟩]
    rfl

/-- **Fitting a translated constructor at the family's fibre is fitting
it in the block's own sense.** -/
theorem ClassFits_iff_FitsFields (hN : S.nest = some N) (ls : List Nat) {ps : List V}
    (hp : FitsVals M (S.ψ ls) base S.params ps) (hg : S.ContGood M ls) :
    ∀ (fields : List Field) {fs : List V},
      S.ClassFits M ls N (S.Fam M ls ps (S.memberIdx M ls N ps)) (fun _ => True) ps
          (S.classFields N fields) fs ↔
        S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps (S.classFields N fields) fs
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | f :: rest, v :: vs => by
    simp only [classFields_cons, ClassFits, FitsFields]
    rw [ClassFits_iff_FitsFields hN ls hp hg rest]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rwa [S.classFieldSet_classField N hN ls hp hg (k := rest.length)
        ((S.FitsFields_length M ls h1).trans (S.length_classFields N rest)) f] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rwa [S.classFieldSet_classField N hN ls hp hg (k := rest.length)
        ((S.FitsFields_length M ls h1).trans (S.length_classFields N rest)) f]

/-! ### The hypotheses' context of any scoped constructor

`Read.lean`'s `read_ihTy` and `fits_ihCtxAux` ask the constructor to be
one of the block's; the translated container constructors are not, but
their fields are in the block's scope (`classCtor_fieldScoped`), which
is all those readings use. -/

/-- `read_ihTy` for any constructor whose fields are in scope. -/
theorem Reader.read_ihTy' (R : S.Reader (env := env) M φ M' φ') {c : CtorSpec}
    (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {kf : Nat × Field} (hkf : kf ∈ c.recFields)
    {l o : Nat} {ihsE fs os ps : List V} {ρ : Nat → V}
    (hi : ihsE.length = l) (hf : fs.length = c.fields.length) (ho : os.length = o) (hpos : 0 < o)
    (ho2 : kf.2 = .container → 2 ≤ o) (hps : ps.length = S.nP) :
    interp M' φ' (consList ihsE (consList fs (consList os (consList ps ρ))))
        (S.ihTy c.fields.length kf.1 l o kf.2)
      = ihSet S M φ (S.q.holds φ') ps (os.getD (o - 1) pt) (os.getD (o - 2) pt) fs kf := by
  obtain ⟨hpos', hk, hrec⟩ := mem_recFields hkf
  obtain ⟨k, f⟩ := kf
  have hsc := hsc _ f hpos'
  rw [show c.fields.length - 1 - (c.fields.length - 1 - k) = k by omega] at hsc
  have hkd : fs.drop (c.fields.length - k) = earlier fs k := by simp [earlier, hf]
  -- the motive, sitting above the hypotheses, the fields and the extras
  have hhead : consList ihsE (consList fs (consList os (consList ps ρ)))
      (c.fields.length + l + o - 1) = os.getD (o - 1) pt := by
    rw [show c.fields.length + l + o - 1 = ((o - 1) + c.fields.length) + l by omega, ← hi,
      consList_ge, ← hf, consList_ge, consList_getD (by omega)]
  -- the field, sitting above the hypotheses
  have hfv : consList ihsE (consList fs (consList os (consList ps ρ)))
      (c.fields.length - 1 - k + l) = fieldVal fs k := by
    rw [← hi, consList_ge, consList_getD (by omega), fieldVal, hf]
  cases f with
  | ordinary _ => simp [Field.isRec] at hrec
  | container =>
    have ho2' := ho2 rfl
    have hhead1 : consList ihsE (consList fs (consList os (consList ps ρ)))
        (c.fields.length + l + o - 2) = os.getD (o - 2) pt := by
      rw [show c.fields.length + l + o - 2 = ((o - 2) + c.fields.length) + l by omega, ← hi,
        consList_ge, ← hf, consList_ge, consList_getD (by omega)]
    simp only [ihTy, ihSet]
    rw [interp_mkAppN_appList, interp_bvar, List.map_singleton, interp_bvar, hhead1, hfv]
  | reflexive tele es =>
    simp only [ihTy, ihSet]
    rw [interp_mkPis, R.piCtx_liftCtx_atCtx hi hf ho (by omega) hps _ tele hsc.1, hkd]
    refine piCtx_congr M _ fun ys hys => ?_
    have hl := FitsVals_length M _ hys
    rw [readEnv_consList hl, interp_mkAppN_appList, interp_bvar, List.map_append, List.map_map,
      List.map_singleton, interp_mkAppN_appList, interp_bvar, interp_varsAt, shiftE_zero_zero,
      readEnv_consList hl]
    rw [show c.fields.length + l + o - 1 + tele.length = c.fields.length + l + o - 1 + ys.length by
      rw [hl], consList_ge, hhead]
    rw [show c.fields.length - 1 - k + l + tele.length = c.fields.length - 1 - k + l + ys.length by
      rw [hl], consList_ge, hfv]
    congr 2
    unfold idxVals
    rw [List.reverse_reverse]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp]
    rw [interp_atCtx M' φ' ρ e (k := k) hl hi hf ho (by omega), hkd,
      ← consList_append ys (earlier fs k) (consList ps ρ),
      ← consList_append ys (earlier fs k) (envP ps)]
    exact R.read (hsc.2.2 e he) (by simp [earlier, hf, hps, hl]; omega)

/-- `fits_ihCtxAux` for any constructor whose fields are in scope. -/
theorem Reader.fits_ihCtxAux' (R : S.Reader (env := env) M φ M' φ') {c : CtorSpec}
    (hsc : ∀ i f, c.fields[i]? = some f → S.fieldScoped env (c.fields.length - 1 - i) f)
    {o : Nat} {fs os ps : List V} {ρ : Nat → V}
    (hf : fs.length = c.fields.length) (ho : os.length = o) (hpos : 0 < o)
    (ho2 : (∃ i : Nat, c.fields[i]? = some Field.container) → 2 ≤ o) (hps : ps.length = S.nP) :
    ∀ (L : List (Nat × Field)), (∀ kf ∈ L, kf ∈ c.recFields) →
      ∀ (ihs : List V) {l : Nat} {ihsE : List V}, ihsE.length = l →
        (FitsVals M' φ' (consList ihsE (consList fs (consList os (consList ps ρ))))
            (S.ihCtxAux c.fields.length o L l) ihs.reverse ↔
          ListRel (S.IhTyped M (S.lparams.map φ) (S.q.holds φ') ps (os.getD (o - 1) pt)
            (os.getD (o - 2) pt) fs) L ihs)
  | [], _, [], _, _, _ => by simp [ihCtxAux, ListRel]
  | [], _, _ :: _, _, _, _ => by
    constructor
    · intro h; have := FitsVals_length M' φ' h; simp [ihCtxAux] at this
    · intro h; exact h.elim
  | _ :: _, _, [], _, _, _ => by
    constructor
    · intro h; have := FitsVals_length M' φ' h; simp [ihCtxAux] at this
    · intro h; exact h.elim
  | kf :: rest, hL, ih :: ihs', l, ihsE, hi => by
    have hkf := hL kf List.mem_cons_self
    have hrest : ∀ kf' ∈ rest, kf' ∈ c.recFields := fun kf' h => hL kf' (List.mem_cons_of_mem kf h)
    have hrec := (mem_recFields hkf).2.2
    simp only [ihCtxAux, List.reverse_cons, ListRel]
    have hread := Reader.read_ihTy' S R hsc hkf (ρ := ρ) hi hf ho hpos
      (fun hcont => ho2 ⟨_, by rw [← hcont]; exact (mem_recFields hkf).1⟩) hps
    have ih := Reader.fits_ihCtxAux' R hsc (ρ := ρ) hf ho hpos ho2 hps rest hrest ihs' (l := l + 1)
      (ihsE := ih :: ihsE) (by simp [hi])
    constructor
    · intro h
      have hlen := FitsVals_length M' φ' h
      simp only [List.length_append, List.length_reverse, List.length_singleton,
        length_ihCtxAux] at hlen
      obtain ⟨h1, h2⟩ := (FitsVals_append M' φ' (by simp [length_ihCtxAux]; omega)).mp h
      refine ⟨?_, ih.mp h2⟩
      rw [IhTyped_iff hrec, ← hread]
      exact h1.2
    · rintro ⟨h1, h2⟩
      refine (FitsVals_append M' φ' (by rw [length_ihCtxAux, List.length_reverse, ListRel.length' h2])).mpr
        ⟨⟨trivial, ?_⟩, ih.mpr h2⟩
      rw [IhTyped_iff hrec, ← hread] at h1
      exact h1

/-! ### The class's minors' conclusion -/

/-- **The container's constructor applied to the class's arguments
and fields**, read: the tagged tuple of the fields — the container's
constructor's set is its graph (the block law), applied by β at the
instantiation (`ClassFits_iff` puts the fields in the container's own
telescope).  The container's constructors are stored (`hcst`), so the
reader agrees with the old model on them. -/
theorem Reader.classCtorApp_eq (hS : S.Scoped env) (R : S.Reader (env := env) M φ M' φ')
    (hN : S.nest = some N) (hf : S.NestFacts M (S.lparams.map φ) N) (hKS : N.KS.Scoped env)
    (hctor : ∀ j c, N.K.ctors[j]? = some c → ∀ ls', M c.name ls' = N.KS.ctorSet M ls' j c)
    (hcst : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome)
    (hz : S.z (S.lparams.map φ) = false)
    {j : Nat} {c : CtorSpec} (hc : N.K.ctors[j]? = some c) {o nIh : Nat}
    {ihsE fs os ps : List V} {ρ : Nat → V} (hi : ihsE.length = nIh)
    (hfl : fs.length = (S.classCtor N c).fields.length) (ho : os.length = o) (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps))
    (hfit : S.ClassFits M (S.lparams.map φ) N
      (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) (fun _ => True) ps
      (S.classCtor N c).fields fs) :
    interp M' φ' (consList ihsE (consList fs (consList os (consList ps ρ))))
        (Expr.mkAppN (.const c.name N.lsK)
          (S.classArgs N (nIh + (S.classCtor N c).fields.length + o) ++
            Expr.varsAt nIh (S.classCtor N c).fields.length))
      = tag j (tuple fs.reverse) := by
  have hNS := hS.2.2.2.2.2.2 N hN
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hzK : N.KS.z (S.lsK (S.lparams.map φ) N) = false := by rw [hf.z_eq]; exact hz
  have hlenF : fs.length = c.fields.length := by
    rw [hfl]; exact S.length_classFields N c.fields
  -- the container's model is the model: its former's set is already its family's graph
  have hM₁ : N.KS.M₁ M = M := by
    funext n ls'
    simp only [M₁]
    split
    · rename_i h; subst h; exact (hf.fam ls').symm
    · rfl
  -- the member set and the container's parameter values
  have hX : S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps) ∈ˢ
      (univ (S.u₀ (S.lparams.map φ)) : V) := S.Fam_mem_univ M _ _ _
  have hpK := hf.argsFit ps hp (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) hX
  have hpsK : (S.psK M (S.lparams.map φ) N ps (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps))).length = N.KS.nP := by
    have := FitsVals_length M _ hpK; simpa [nP] using this
  -- the fields fit the container's own constructor at the instantiation
  have hfitF : N.KS.FitsFields M (S.lsK (S.lparams.map φ) N) (N.KS.bound M (S.lsK (S.lparams.map φ) N))
      (N.KS.Mem M (S.lsK (S.lparams.map φ) N)) (S.psK M (S.lparams.map φ) N ps (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps))) c.fields fs := by
    have := hfit
    simp only [classCtor] at this
    rwa [S.ClassFits_iff M (S.lparams.map φ) N hf hNS.2.2.2.2.1 hNS.2.2.1 hKS hcm (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) (fun _ => True) hp hX hz
      (P := N.KS.Mem M (S.lsK (S.lparams.map φ) N)) (fun _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
      (List.drop_zero (l := c.fields))] at this
  -- the container's own reader: the model itself at the container's valuation
  have hlsK : (S.lsK (S.lparams.map φ) N).length = N.KS.lparams.length := by
    simp only [IndSpec.lsK, List.length_map]; exact hNS.2.2.1
  have hmapK : N.KS.lparams.map (N.KS.ψ (S.lsK (S.lparams.map φ) N)) = S.lsK (S.lparams.map φ) N :=
    map_valOf_eq hKS.2.2.2.2.2.1 hlsK
  have RK : N.KS.ReaderG (env := env) M (N.KS.ψ (S.lsK (S.lparams.map φ) N)) M
      (N.KS.ψ (S.lsK (S.lparams.map φ) N)) :=
    { agree := fun _ _ _ => rfl
      fam := fun ls' => hf.fam ls'
      val := fun _ _ => rfl
      good := fun _ h => by simp [NestInfo.KS, IndBase.spec] at h }
  have hscK : ∀ i f, c.fields[i]? = some f → N.KS.fieldScoped env (c.fields.length - 1 - i) f :=
    (hKS.2.2.2.1 c hcm).1
  have hidxK : ∀ k f, c.fields[c.fields.length - 1 - k]? = some f → k < c.fields.length →
      IdxFitAt N.KS M (N.KS.ψ (S.lsK (S.lparams.map φ) N)) (S.psK M (S.lparams.map φ) N ps (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)))
        (earlier fs k) f := by
    intro k f hkf _
    have hpf := positive_field N hf.positive hcm (List.drop_zero (l := c.fields)) hkf
    cases f with
    | ordinary _ => trivial
    | reflexive tele es =>
      obtain ⟨rfl, rfl⟩ := hpf
      intro ys _
      simp only [idxVals, List.map_nil, List.reverse_nil]
      rw [show N.KS.indices = [] from hf.positive.1]
      trivial
    | container => exact hpf.elim
  have hfitC : FitsVals M (N.KS.ψ (S.lsK (S.lparams.map φ) N)) base
      (N.KS.fieldCtx c.fields ++ N.KS.params) (fs ++ S.psK M (S.lparams.map φ) N ps (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps))) :=
    (FitsVals_append _ _ (by rw [hlenF, N.KS.length_fieldCtx])).mpr ⟨hpK,
      RK.fits_fieldCtx_of_idx hKS hscK (ρ := base) hpsK (by rw [hmapK]; exact hpK)
        (by rw [hmapK]; exact hfitF) hidxK⟩
  -- the application, read
  have henv : consList ihsE (consList fs (consList os (consList ps ρ)))
      = consList (ihsE ++ fs ++ os) (consList ps ρ) := consList_three _ _ _ _
  have hlen3 : (ihsE ++ fs ++ os).length = nIh + (S.classCtor N c).fields.length + o := by
    simp [hi, hfl, ho]; omega
  rw [interp_mkAppN_appList, interp_const, ← R.agree _ (hcst j c hc), R.lsK_eq hS hN, hctor j c hc,
    List.map_append, interp_varsAt, shiftE_consList' hi, readEnv_consList hfl, henv,
    Reader.classArgs_read S N hS R hN hlen3 hps hp hidx]
  unfold ctorSet
  rw [hM₁, hzK]
  have hargs : S.classArgsV M (S.lparams.map φ) N ps
      (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) ++ fs.reverse
      = (fs ++ S.psK M (S.lparams.map φ) N ps
          (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps))).reverse := by
    simp [psK]
  rw [hargs, appList_lamCtx_false hfitC, consList_append, readEnv_consList hlenF]
  simp [ctorVal, hzK, KS_tagOf]

/-- **The block's minors' typing gives `MinorOkN`** for every
constructor of the block, from the minors fitting their context (two
motives above them): `minorOk`'s argument with the extras `2 + j`
deep — the class's motive sits between the block's and the minors,
and a container field's hypothesis reads it. -/
theorem Reader₂.minorOkN_of_fits (hS : S.Scoped env) (R₂ : S.Reader₂ (env := env) M φ M' φ')
    (hfresh : env.find? S.name = none) {ps : List V} {ρ : Nat → V}
    {m1 m : V} {mins : List V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hmins : mins.length = S.n)
    (hwdC : ∀ c ∈ S.ctors, CtxWD M' φ' (consList ps ρ) (S.fieldCtx c.fields))
    (hres : ∀ c ∈ S.ctors, ∀ fs, S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
        (S.Mem M (S.lparams.map φ)) ps c.fields fs →
      FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
        (S.idxVals M (S.lparams.map φ) (consList fs (envP ps)) c.idx))
    (hmot : ∀ is, FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices is →
      ∀ t, t ∈ˢ S.Fam M (S.lparams.map φ) ps is →
        appList m (is.reverse ++ [t]) ∈ˢ (univ (Level.eval φ' S.ℓ) : V))
    (hnr : S.NoRecDep) (hb : S.DomsBounded M (S.lparams.map φ) ps)
    (hcb : S.ContInBound M (S.lparams.map φ) ps)
    (hmn : FitsVals M' φ' (consList [m1, m] (consList ps ρ)) S.minorsCtxN mins) :
    ∀ j c, S.ctors[j]? = some c →
      ∀ fs, S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
          (S.Mem M (S.lparams.map φ)) ps c.fields fs →
        ∀ ihs, ListRel (S.IhTypedN M (S.lparams.map φ) (S.q.holds φ') ps ⟨m, m1, mins, []⟩ fs)
            c.recFields ihs →
          appList (S.minorAt mins j) (fs.reverse ++ ihs) ∈ˢ
            appList m ((S.idxVals M (S.lparams.map φ) (consList fs (envP ps)) c.idx).reverse ++
              [S.ctorVal (S.lparams.map φ) j fs]) ∧
          SpineOk (S.minorAt mins j) (fs.reverse ++ ihs) := by
  intro j c hc fs hfit ihs hihs
  have hcm : c ∈ S.ctors := List.mem_of_getElem? hc
  have hj : j < S.n := (List.getElem?_eq_some_iff.mp hc).1
  have R := R₂.R
  have hsc := (hS.2.2.2.1 c hcm).1
  -- the minor, from its context
  obtain ⟨minsE, hminsE, hmem⟩ : ∃ minsE : List V, minsE.length = j ∧
      S.minorAt mins j ∈ˢ interp M' φ' (consList minsE (consList [m1, m] (consList ps ρ)))
        (S.minorTyN c j) := by
    refine ⟨mins.drop (S.n - j), by simp [hmins]; omega, ?_⟩
    rw [minorsCtxN_eq] at hmn
    have := fits_ctxFrom S.minorTyN S.ctors 0 _ mins hmn j c hc
    rw [Nat.zero_add] at this
    exact this
  have henv : consList minsE (consList [m1, m] (consList ps ρ))
      = consList (minsE ++ [m1, m]) (consList ps ρ) := by
    rw [consList_append]
  have hos : (minsE ++ [m1, m]).length = 2 + j := by simp [hminsE]; omega
  have hgetm : (minsE ++ [m1, m]).getD (2 + j - 1) pt = m := by
    rw [show 2 + j - 1 = minsE.length + 1 by omega]; exact (getD_append_two _ _).2
  have hgetm1 : (minsE ++ [m1, m]).getD (2 + j - 2) pt = m1 := by
    rw [show 2 + j - 2 = minsE.length by omega]; exact (getD_append_two _ _).1
  -- fitting the field context in the reader is fitting the fields semantically
  have hfieldsF : ∀ fs', FitsVals M' φ' (consList minsE (consList [m1, m] (consList ps ρ)))
      (S.fieldCtxAt c (2 + j)) fs' ↔
      S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
        (S.Mem M (S.lparams.map φ)) ps c.fields fs' := by
    intro fs'
    unfold fieldCtxAt
    rw [henv, FitsVals_liftCtx_liftN M' φ' _ _ _ hos]
    exact (R.fits_fieldCtx hS hsc hps hp (hwdC c hcm)).1
  -- the conclusion's value at any fitting fields and hypotheses
  have hconcl : ∀ fs' ihsR, fs'.length = c.fields.length → ihsR.length = c.recFields.length →
      S.FitsFields M (S.lparams.map φ) (S.bound M (S.lparams.map φ))
        (S.Mem M (S.lparams.map φ)) ps c.fields fs' →
      interp M' φ' (consList ihsR (consList fs' (consList minsE (consList [m1, m] (consList ps ρ)))))
          (Expr.mkAppN (.bvar (c.recFields.length + c.fields.length + (2 + j) - 1))
            (c.idx.map (Expr.atCtx c.fields.length c.fields.length c.recFields.length (2 + j) 0) ++
              [Expr.mkAppN (.const c.name S.lvls)
                (Expr.varsAt (c.recFields.length + c.fields.length + (2 + j)) S.nP ++
                  Expr.varsAt c.recFields.length c.fields.length)]))
        = appList m ((S.idxVals M (S.lparams.map φ) (consList fs' (envP ps)) c.idx).reverse ++
            [S.ctorVal (S.lparams.map φ) j fs']) := by
    intro fs' ihsR hf' hi' hfit'
    have := R₂.read_concl hS hfresh hc (ihsE := ihsR) (os := minsE ++ [m1, m]) (ρ := ρ) hi' hf' hos
      (by omega) hps hp hfit' ((R.fits_fieldCtx hS hsc hps hp (hwdC c hcm)).2 hfit')
    rw [← henv, hgetm] at this
    exact this
  -- the minor's type, read
  unfold minorTyN at hmem
  rw [interp_mkPis] at hmem
  have hlenI : ihs.reverse.length = (S.ihCtxAt c (2 + j)).length := by
    rw [List.length_reverse, ihCtxAt_eq, length_ihCtxAux, ListRel.length' hihs]
  have hf := S.FitsFields_length M _ hfit
  have hihs' : ListRel (S.IhTyped M (S.lparams.map φ) (S.q.holds φ') ps m m1 fs) c.recFields ihs :=
    (ListRel_iff fun _ _ => S.IhTypedN_iff).mp hihs
  have hfitAll : FitsVals M' φ' (consList minsE (consList [m1, m] (consList ps ρ)))
      (S.ihCtxAt c (2 + j) ++ S.fieldCtxAt c (2 + j)) (ihs.reverse ++ fs) := by
    refine (FitsVals_append M' φ' hlenI).mpr ⟨(hfieldsF fs).mpr hfit, ?_⟩
    rw [ihCtxAt_eq, henv]
    have := (Reader.fits_ihCtxAux' S R.toReader hsc (os := minsE ++ [m1, m]) (ρ := ρ) hf hos (by omega)
      (fun _ => by omega) hps c.recFields (fun _ h => h) ihs (l := 0) (ihsE := []) rfl).mpr
    rw [hgetm, hgetm1] at this
    exact this hihs'
  have hG : S.q.holds φ' = true → ∀ ws, FitsVals M' φ' (consList minsE (consList [m1, m] (consList ps ρ)))
      (S.ihCtxAt c (2 + j) ++ S.fieldCtxAt c (2 + j)) ws →
      interp M' φ' (consList ws (consList minsE (consList [m1, m] (consList ps ρ))))
        (Expr.mkAppN (.bvar (c.recFields.length + c.fields.length + (2 + j) - 1))
          (c.idx.map (Expr.atCtx c.fields.length c.fields.length c.recFields.length (2 + j) 0) ++
            [Expr.mkAppN (.const c.name S.lvls)
              (Expr.varsAt (c.recFields.length + c.fields.length + (2 + j)) S.nP ++
                Expr.varsAt c.recFields.length c.fields.length)])) ∈ˢ (univ 0 : V) :=
    fun hq ws hws => by
      -- at a proposition: the conclusion is a truth value
      obtain ⟨ihsR, fs', rfl, hl₁⟩ : ∃ ihsR fs', ws = ihsR ++ fs' ∧
          ihsR.length = (S.ihCtxAt c (2 + j)).length := by
        have hl := FitsVals_length M' φ' hws
        refine ⟨ws.take (S.ihCtxAt c (2 + j)).length, ws.drop (S.ihCtxAt c (2 + j)).length,
          (List.take_append_drop _ _).symm, ?_⟩
        simp at hl; simp [hl]
      obtain ⟨hwsF, hwsI⟩ := (FitsVals_append M' φ' hl₁).mp hws
      have hfit' := (hfieldsF fs').mp hwsF
      have hf' := S.FitsFields_length M _ hfit'
      have hi' : ihsR.length = c.recFields.length := by rw [hl₁, ihCtxAt_eq, length_ihCtxAux]
      rw [consList_append, hconcl fs' ihsR hf' hi' hfit']
      have hz := (S.q_holds φ')
      rw [hq, Bool.true_eq, beq_iff_eq] at hz
      rw [← hz]
      exact hmot _ (hres c hcm fs' hfit') _
        (S.ctorVal_mem_Fam M _ hc hfit' hnr hb hcb)
  have key := appList_mem_of_piCtx M' φ' hmem hfitAll
  have key₂ := spineOk_of_piCtx M' φ' hmem hfitAll hG
  rw [List.reverse_append, List.reverse_reverse, consList_append,
    hconcl fs ihs.reverse hf (by rw [List.length_reverse, ListRel.length' hihs]) hfit] at key
  rw [List.reverse_append, List.reverse_reverse] at key₂
  exact ⟨key, key₂⟩

/-- **The class's minors' typing gives `MinorOkK`** for every
constructor of the container, from the class's minors fitting their
context: `minorOk`'s argument for the translated constructor (its
fields are in the block's scope), the extras `2 + n + j` deep, the
conclusion's head the container's constructor at the class's
arguments (`classCtorApp_eq`) under the class's motive. -/
theorem Reader₂.minorOkK_of_fits (hS : S.Scoped env) (R₂ : S.Reader₂ (env := env) M φ M' φ')
    (hN : S.nest = some N)
    (hf : S.NestFacts M (S.lparams.map φ) N) (hKS : N.KS.Scoped env)
    (hctor : ∀ j c, N.K.ctors[j]? = some c → ∀ ls', M c.name ls' = N.KS.ctorSet M ls' j c)
    (hcst : ∀ (j : Nat) (c : CtorSpec), N.K.ctors[j]? = some c → (env.find? c.name).isSome)
    (hz : S.z (S.lparams.map φ) = false)
    {ps : List V} {ρ : Nat → V} {m1 m : V} {mins minsK : List V} (hps : ps.length = S.nP)
    (hp : FitsVals M (S.ψ (S.lparams.map φ)) base S.params ps)
    (hmins : mins.length = S.n) (hminsK : minsK.length = N.nK)
    (hwdC : ∀ c ∈ N.K.ctors, CtxWD M' φ' (consList ps ρ) (S.fieldCtx (S.classCtor N c).fields))
    (hidx : FitsVals M (S.ψ (S.lparams.map φ)) (envP ps) S.indices
      (S.memberIdx M (S.lparams.map φ) N ps))
    (hmot1 : ∀ t, t ∈ˢ S.classAt M (S.lparams.map φ) N ps →
        appList m1 [t] ∈ˢ (univ (Level.eval φ' S.ℓ) : V))
    (hmnK : FitsVals M' φ' (consList (mins ++ [m1, m]) (consList ps ρ)) (S.minorsCtxK N) minsK) :
    ∀ j c, N.K.ctors[j]? = some c →
      ∀ fs, S.ClassFits M (S.lparams.map φ) N
          (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) (fun _ => True) ps
          (S.classCtor N c).fields fs →
        ∀ ihs, ListRel (S.IhTypedN M (S.lparams.map φ) (S.q.holds φ') ps ⟨m, m1, mins, minsK⟩ fs)
            (S.classCtor N c).recFields ihs →
          appList (minorKAt N minsK j) (fs.reverse ++ ihs) ∈ˢ appList m1 [tag j (tuple fs.reverse)] ∧
          SpineOk (minorKAt N minsK j) (fs.reverse ++ ihs) := by
  intro j c hc fs hfit ihs hihs
  have hcm : c ∈ N.K.ctors := List.mem_of_getElem? hc
  have hj : j < N.nK := (List.getElem?_eq_some_iff.mp hc).1
  have R := R₂.R
  have hNS := hS.2.2.2.2.2.2 N hN
  have hsc := S.classCtor_fieldScoped N hS hN hKS hcm
  have hcl := S.classLaws_of M (S.lparams.map φ) N hf hNS.2.2.2.2.1 hNS.2.2.1 hKS hN hz hp
  -- the minor, from its context
  obtain ⟨minsE, hminsE, hmem⟩ : ∃ minsE : List V, minsE.length = j ∧
      minorKAt N minsK j ∈ˢ interp M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
        (S.minorTyK N c j) := by
    refine ⟨minsK.drop (N.nK - j), by simp [hminsK]; omega, ?_⟩
    rw [minorsCtxK_eq] at hmnK
    have := fits_ctxFrom (S.minorTyK N) N.K.ctors 0 _ minsK hmnK j c hc
    rw [Nat.zero_add] at this
    exact this
  have henv : consList minsE (consList (mins ++ [m1, m]) (consList ps ρ))
      = consList (minsE ++ mins ++ [m1, m]) (consList ps ρ) := by
    simp [consList_append]
  have hos : (minsE ++ mins ++ [m1, m]).length = 2 + S.n + j := by simp [hminsE, hmins]; omega
  have hgetm : (minsE ++ mins ++ [m1, m]).getD (2 + S.n + j - 1) pt = m := by
    rw [show 2 + S.n + j - 1 = (minsE ++ mins).length + 1 by simp [hminsE, hmins]; omega]
    exact (getD_append_two _ _).2
  have hgetm1 : (minsE ++ mins ++ [m1, m]).getD (2 + S.n + j - 2) pt = m1 := by
    rw [show 2 + S.n + j - 2 = (minsE ++ mins).length by simp [hminsE, hmins]; omega]
    exact (getD_append_two _ _).1
  -- fitting the field context in the reader is fitting the translated constructor
  have hfieldsF : ∀ fs', FitsVals M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
      (S.fieldCtxAt (S.classCtor N c) (2 + S.n + j)) fs' ↔
      S.ClassFits M (S.lparams.map φ) N
        (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) (fun _ => True) ps
        (S.classCtor N c).fields fs' := by
    intro fs'
    unfold fieldCtxAt
    rw [henv, FitsVals_liftCtx_liftN M' φ' _ _ _ hos, (R.fits_fieldCtx hS hsc hps hp (hwdC c hcm)).1]
    exact (S.ClassFits_iff_FitsFields N hN (S.lparams.map φ) hp R.good c.fields).symm
  -- the conclusion's value at any fitting fields and hypotheses
  have hconcl : ∀ fs' ihsR, fs'.length = (S.classCtor N c).fields.length →
      ihsR.length = (S.classCtor N c).recFields.length →
      S.ClassFits M (S.lparams.map φ) N
        (S.Fam M (S.lparams.map φ) ps (S.memberIdx M (S.lparams.map φ) N ps)) (fun _ => True) ps
        (S.classCtor N c).fields fs' →
      interp M' φ' (consList ihsR (consList fs' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))))
          (Expr.mkAppN (.bvar ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
              (2 + S.n + j) - 2))
            [Expr.mkAppN (.const c.name N.lsK)
              (S.classArgs N ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
                  (2 + S.n + j)) ++
                Expr.varsAt (S.classCtor N c).recFields.length (S.classCtor N c).fields.length)])
        = appList m1 [tag j (tuple fs'.reverse)] := by
    intro fs' ihsR hf' hi' hfit'
    rw [interp_mkAppN_appList, interp_bvar, List.map_singleton, henv,
      Reader.classCtorApp_eq S N hS R.toReader hN hf hKS hctor hcst hz hc (o := 2 + S.n + j) hi' hf' hos hps hp
        hidx hfit']
    rw [show (S.classCtor N c).recFields.length + (S.classCtor N c).fields.length + (2 + S.n + j) - 2
        = ((2 + S.n + j - 2) + (S.classCtor N c).fields.length) + (S.classCtor N c).recFields.length by
        omega,
      ← hi', consList_ge, ← hf', consList_ge, consList_getD (by omega), hgetm1]
  -- the minor's type, read
  unfold minorTyK at hmem
  rw [interp_mkPis] at hmem
  have hlenI : ihs.reverse.length = (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length := by
    rw [List.length_reverse, ihCtxAt_eq, length_ihCtxAux, ListRel.length' hihs]
  have hf := S.ClassFits_length M _ N hfit
  have hihs' : ListRel (S.IhTyped M (S.lparams.map φ) (S.q.holds φ') ps m m1 fs)
      (S.classCtor N c).recFields ihs :=
    (ListRel_iff fun _ _ => S.IhTypedN_iff).mp hihs
  have hfitAll : FitsVals M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
      (S.ihCtxAt (S.classCtor N c) (2 + S.n + j) ++ S.fieldCtxAt (S.classCtor N c) (2 + S.n + j))
      (ihs.reverse ++ fs) := by
    refine (FitsVals_append M' φ' hlenI).mpr ⟨(hfieldsF fs).mpr hfit, ?_⟩
    rw [ihCtxAt_eq, henv]
    have := (Reader.fits_ihCtxAux' S R.toReader hsc (os := minsE ++ mins ++ [m1, m]) (ρ := ρ) hf hos (by omega)
      (fun _ => by omega) hps (S.classCtor N c).recFields (fun _ h => h) ihs (l := 0) (ihsE := [])
      rfl).mpr
    rw [hgetm, hgetm1] at this
    exact this hihs'
  have hG : S.q.holds φ' = true →
      ∀ ws, FitsVals M' φ' (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ)))
        (S.ihCtxAt (S.classCtor N c) (2 + S.n + j) ++ S.fieldCtxAt (S.classCtor N c) (2 + S.n + j)) ws →
      interp M' φ' (consList ws (consList minsE (consList (mins ++ [m1, m]) (consList ps ρ))))
        (Expr.mkAppN (.bvar ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
            (2 + S.n + j) - 2))
          [Expr.mkAppN (.const c.name N.lsK)
            (S.classArgs N ((S.classCtor N c).recFields.length + (S.classCtor N c).fields.length +
                (2 + S.n + j)) ++
              Expr.varsAt (S.classCtor N c).recFields.length (S.classCtor N c).fields.length)])
        ∈ˢ (univ 0 : V) :=
    fun hq ws hws => by
      -- at a proposition: the conclusion is a truth value
      obtain ⟨ihsR, fs', rfl, hl₁⟩ : ∃ ihsR fs', ws = ihsR ++ fs' ∧
          ihsR.length = (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length := by
        have hl := FitsVals_length M' φ' hws
        refine ⟨ws.take (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length,
          ws.drop (S.ihCtxAt (S.classCtor N c) (2 + S.n + j)).length,
          (List.take_append_drop _ _).symm, ?_⟩
        simp at hl; simp [hl]
      obtain ⟨hwsF, hwsI⟩ := (FitsVals_append M' φ' hl₁).mp hws
      have hfit' := (hfieldsF fs').mp hwsF
      have hf' := S.ClassFits_length M _ N hfit'
      have hi' : ihsR.length = (S.classCtor N c).recFields.length := by
        rw [hl₁, ihCtxAt_eq, length_ihCtxAux]
      rw [consList_append, hconcl fs' ihsR hf' hi' hfit']
      have hz' := (S.q_holds φ')
      rw [hq, Bool.true_eq, beq_iff_eq] at hz'
      rw [← hz']
      exact hmot1 _ (hcl.intro _ (S.Fam_mem_univ M _ _ _) j c fs' hc hfit')
  have key := appList_mem_of_piCtx M' φ' hmem hfitAll
  have key₂ := spineOk_of_piCtx M' φ' hmem hfitAll hG
  rw [List.reverse_append, List.reverse_reverse, consList_append,
    hconcl fs ihs.reverse hf (by rw [List.length_reverse, ListRel.length' hihs]) hfit] at key
  rw [List.reverse_append, List.reverse_reverse] at key₂
  exact ⟨key, key₂⟩

end Readings

end IndSpec

end Fragment
