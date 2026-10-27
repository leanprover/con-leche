module

public import ConLeche.Verify.Modular.Local
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# What a context entry's laws read (task #370)

From a unit's verified read sets (`lawsOk`) to the scoping facts
`ConLeche.Modular.LocalOk` asks of a context entry: `EntryScoped`,
`EntryProjs`, `BlockIn`.
-/

namespace ConLeche.Cached.Mod

open ConLeche ConLeche.Modular

/-! ## The walks' specifications -/

/-- A resolution walk against one index carries over to an environment
that stores every name the index stores. -/
theorem constsResolve_of_F {fe : FEnv} {R : Env}
    (hsub : ∀ d, (fe.find? d).isSome = true → (R.find? d).isSome = true) :
    ∀ e : Expr, Expr.constsResolveF fe e = true → e.constsResolve R = true := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit l =>
    cases l with
    | natVal _ =>
      intro h
      simp only [Expr.constsResolveF, Bool.and_eq_true] at h
      simp only [Expr.constsResolve, Bool.and_eq_true]
      exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, hsub _ h.2⟩
    | strVal _ =>
      intro h
      simp only [Expr.constsResolveF, Bool.and_eq_true] at h
      simp only [Expr.constsResolve, Bool.and_eq_true]
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsub _ h1, hsub _ h2⟩, hsub _ h3⟩, hsub _ h4⟩, hsub _ h5⟩, hsub _ h6⟩,
        hsub _ h7⟩, hsub _ h8⟩, hsub _ h9⟩, hsub _ h10⟩
  | const n _ => intro h; exact hsub n h
  | fvar _ ty ih => intro h; exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s _ e ih =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨hsub s h.1, ih h.2⟩

/-- The projection walk carries over to a context that stores every
admitted structure as a type former. -/
theorem projsFormer_of_projsIn {P : Name → Bool} {C : Env}
    (hsub : ∀ s, P s = true → ∃ cv caps, C.find? s = some (.indInfo cv caps)) :
    ∀ e : Expr, Expr.projsIn P e = true → Expr.projsFormer C e = true := by
  intro e
  induction e with
  | proj s _ e ih =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    obtain ⟨cv, caps, hf⟩ := hsub s h.1
    rw [hf]
    exact ⟨rfl, ih h.2⟩
  | app f a ihf iha =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | _ => intro _; simp [Expr.projsFormer]

/-! ## Read sets -/

/-- A name the read set's index finds is one of its names. -/
theorem dvOf_find? {r : ReadSet} {d : Name} (h : ((dvOf r).find? d).isSome = true) :
    r.d.contains d = true := by
  unfold dvOf FEnv.find? at h
  simp only at h
  cases hd : r.d[d]? with
  | none =>
    rw [hd] at h
    simp at h
  | some x => rw [Std.HashMap.contains_eq_isSome_getElem? (m := r.d), hd]; rfl

/-- **What a verified read set gives**: if every name of it is good, the
laws read only good names. -/
structure LawsGood (R C : Env) (r : ReadSet) : Prop where
  d : ∀ n, r.d.contains n = true → (R.find? n).isSome = true
  fi : ∀ n, r.fi.contains n = true → ∃ cv caps, C.find? n = some (.indInfo cv caps)
  fc : ∀ n, r.fc.contains n = true → ∃ cv nP nF, C.find? n = some (.ctorInfo cv nP nF)

theorem lawsOk_spec {r : ReadSet} {l : Laws} (h : lawsOk r l = true) :
    (∀ e ∈ l.es, Expr.constsResolveF (dvOf r) e = true) ∧
    (∀ e ∈ l.es, Expr.projsIn r.fi.contains e = true) ∧
    (∀ n ∈ l.ns, ((dvOf r).find? n).isSome = true) ∧
    (∀ n ∈ l.fi, r.fi.contains n = true) ∧ (∀ n ∈ l.fc, r.fc.contains n = true) := by
  unfold lawsOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, h3, h4, h5⟩
  · rw [← constsResolveFC_spec]; exact h1 e he
  · rw [← projsInC_eq]; exact h2 e he

/-- **A verified read set of good names gives the entry's scoping
facts**, the table read being the one the context presents. -/
theorem laws_entry {R C : Env} {n : Name} {ci : ConstantInfo} {t : Option ProjTable}
    {r : ReadSet} (hl : lawsOk r (lawsOf t ci) = true) (hg : LawsGood R C r)
    (ht : ∀ cv caps, ci = .indInfo cv caps → ∀ T, C.findTable? n = some T → t = some T)
    (hn : ci.name = n) :
    EntryScoped R C n ci ∧ EntryProjs C n ci ∧ BlockIn C n ci := by
  obtain ⟨hes, hps, hns, hfi, hfc⟩ := lawsOk_spec hl
  have hR : ∀ d, ((dvOf r).find? d).isSome = true → (R.find? d).isSome = true :=
    fun d h => hg.d d (dvOf_find? h)
  have cr : ∀ e ∈ (lawsOf t ci).es, e.constsResolve R = true :=
    fun e he => constsResolve_of_F hR e (hes e he)
  have pf : ∀ e ∈ (lawsOf t ci).es, Expr.projsFormer C e = true := fun e he =>
    projsFormer_of_projsIn (fun s hs => hg.fi s hs) e (hps e he)
  have nm : ∀ d ∈ (lawsOf t ci).ns, (R.find? d).isSome = true := fun d hd => hR d (hns d hd)
  have fi : ∀ d ∈ (lawsOf t ci).fi, ∃ cv caps, C.find? d = some (.indInfo cv caps) :=
    fun d hd => hg.fi d (hfi d hd)
  have fc : ∀ d ∈ (lawsOf t ci).fc, ∃ cv nP nF, C.find? d = some (.ctorInfo cv nP nF) :=
    fun d hd => hg.fc d (hfc d hd)
  subst hn
  unfold EntryScoped EntryProjs
  cases ci with
  | defnInfo cv v hint =>
    simp only [lawsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at cr pf nm
    refine ⟨⟨cr.1, fun cv' v' h' he => ?_, fun _ _ _ _ he => (nomatch he),
      fun _ _ he => (nomatch he), nm⟩, ⟨pf.1, fun cv' v' h' he => ?_,
      fun _ _ _ _ he => (nomatch he), fun _ _ he => (nomatch he)⟩, trivial⟩
    · cases he; exact cr.2
    · cases he; exact pf.2
  | recInfo cv mI rP rules =>
    simp only [lawsOf, List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map] at cr pf nm fc
    refine ⟨⟨cr _ (.inl rfl), fun _ _ _ he => (nomatch he), fun cv' mI' rP' rules' he rl hrl => ?_,
      fun _ _ he => (nomatch he), fun d hd => nm d (.inr hd)⟩, ⟨pf _ (.inl rfl),
      fun _ _ _ he => (nomatch he), fun cv' mI' rP' rules' he rl hrl => ?_,
      fun _ _ he => (nomatch he)⟩, fun rl hrl => fc _ ⟨rl, hrl, rfl⟩⟩
    · cases he
      refine ⟨cr _ (.inr ⟨rl, hrl, .inl rfl⟩), nm _ (.inl ⟨rl, hrl, rfl⟩),
        fun lvls pins hf p hp => cr _ (.inr ⟨rl, hrl, .inr ?_⟩)⟩
      rw [hf]; exact hp
    · cases he
      refine ⟨pf _ (.inr ⟨rl, hrl, .inl rfl⟩), fun lvls pins hf p hp => pf _ (.inr ⟨rl, hrl, .inr ?_⟩)⟩
      rw [hf]; exact hp
  | indInfo cv caps =>
    have htc := ht cv caps rfl
    cases t with
    | none =>
      simp only [lawsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.mem_append]
        at cr pf nm fi fc
      refine ⟨⟨cr, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
        fun cv' caps' he => ?_, fun d hd => nm d (by simp [hd])⟩,
        ⟨pf, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
        fun cv' caps' he T hT => ?_⟩, ?_⟩
      · cases he
        refine ⟨fun m hm => nm m (by simp [hm]), fun c hc => nm c (by simp [hc]),
          fun he => nm _ (by simp [he]), fun T hT => ?_⟩
        exact absurd (htc T hT) (by simp)
      · cases he; exact absurd (htc T hT) (by simp)
      · refine ⟨fun m hm => fi m hm, fun c hc => fc c (by simp [hc]),
          fun he => fc _ (by simp [he]), fun T hT => absurd (htc T hT) (by simp)⟩
    | some T₀ =>
      simp only [lawsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        List.mem_append] at cr pf nm fi fc
      refine ⟨⟨cr.1, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
        fun cv' caps' he => ?_, fun d hd => nm d (by simp [hd])⟩,
        ⟨pf.1, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
        fun cv' caps' he T hT => ?_⟩, ?_⟩
      · cases he
        refine ⟨fun m hm => nm m (by simp [hm]), fun c hc => nm c (by simp [hc]),
          fun he => nm _ (by simp [he]), fun T hT => ?_⟩
        have := htc T hT
        simp only [Option.some.injEq] at this
        subst this
        exact ⟨nm _ (by simp), fun b hb => cr.2 b hb⟩
      · cases he
        have := htc T hT
        simp only [Option.some.injEq] at this
        subst this
        exact fun b hb => pf.2 b hb
      · refine ⟨fun m hm => fi m hm, fun c hc => fc c (by simp [hc]),
          fun he => fc _ (by simp [he]), fun T hT => ?_⟩
        have := htc T hT
        simp only [Option.some.injEq] at this
        subst this
        exact fc _ (by simp)
  | ctorInfo cv nP nF =>
    simp only [lawsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at cr pf nm fi
    refine ⟨⟨cr, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
      fun _ _ he => (nomatch he), nm⟩, ⟨pf, fun _ _ _ he => (nomatch he),
      fun _ _ _ _ he => (nomatch he), fun _ _ he => (nomatch he)⟩, ?_⟩
    intro T us hT
    apply fi
    simp [hT]
  | axiomInfo cv =>
    simp only [lawsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at cr pf nm
    exact ⟨⟨cr, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
      fun _ _ he => (nomatch he), nm⟩, ⟨pf, fun _ _ _ he => (nomatch he),
      fun _ _ _ _ he => (nomatch he), fun _ _ he => (nomatch he)⟩, trivial⟩
  | thmInfo cv =>
    simp only [lawsOf, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at cr pf nm
    exact ⟨⟨cr, fun _ _ _ he => (nomatch he), fun _ _ _ _ he => (nomatch he),
      fun _ _ he => (nomatch he), nm⟩, ⟨pf, fun _ _ _ he => (nomatch he),
      fun _ _ _ _ he => (nomatch he), fun _ _ he => (nomatch he)⟩, trivial⟩

end ConLeche.Cached.Mod
