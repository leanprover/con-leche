module

public import ConLeche.Verify.Modular.Dev
import ConLeche.Verify.Modular.Local
import ConLeche.Verify.Modular.Interface
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# What a context entry's laws read (task #370)

From a unit's verified read sets (`lawsOk`) to the two halves of the
local checks: a module's interface (`ifaceOf`) checked once, at its home
(`RunOk.interfaceOk`: its presentations refine its installed constants,
and what their laws read is stored there and listed in their footprint),
and each importer's checks (`RunOk.importOk`: its context is made of its
sources' presentations, their footprints good in it — the gates — and its
projections and blocks within it).  `RunOk.localOk` derives
`ConLeche.Modular.LocalOk` from both (`LocalOk.of_interface`).
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

/-! ## The entries of a context -/

variable {mode : CheckMode} {S : Store} {M : Array ModData}

theorem readsOk_spec {h : Nat} {fe : FEnv} {u : Unit'} {lvl2 : Bool} {G : Array (Nat × UInt8)}
    {r : ReadSet} (hr : readsOk S h fe u lvl2 G r = true) :
    (∀ d, r.d.contains d = true →
      (if lvl2 then read2Ok S h fe d else read1Ok S h fe u G d) = true) ∧
    (∀ d, r.fi.contains d = true →
      (if lvl2 then full2Ok S h fe u .ind d else full1Ok S h fe u G .ind d) = true) ∧
    (∀ d, r.fc.contains d = true →
      (if lvl2 then full2Ok S h fe u .ctor d else full1Ok S h fe u G .ctor d) = true) := by
  unfold readsOk at hr
  simp only [Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  refine ⟨fun d hd => ?_, fun d hd => h2 d (Std.HashSet.mem_toList.mpr
      (Std.HashSet.mem_iff_contains.mpr hd)),
    fun d hd => h3 d (Std.HashSet.mem_toList.mpr (Std.HashSet.mem_iff_contains.mpr hd))⟩
  have hmem : (d, r.d.getD d default) ∈ r.d.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
    exact Std.HashMap.getElem?_eq_some_getD_of_contains hd
  exact h1 _ hmem

/-- **Good read sets**: at the level module `i` loads the home `h`, every
name of a read set checked against `h`'s view is good in `i`. -/
theorem RunOk.lawsGood (hR : RunOk mode S M) {i h : Nat} (hi : i < M.size) (hh : h < M.size)
    {lvl2 : Bool} {G : Array (Nat × UInt8)} {r : ReadSet}
    (hl : lvlAt (S.lvl i) h = (if lvl2 then 2 else 1))
    (hG : ∀ p ∈ G, lvlAt (S.lvl i) p.1 ≥ p.2)
    (hr : readsOk S h M[h].fe M[h].unit lvl2 G r = true) :
    LawsGood (readsAlike (devOf S M) i h) (devOf S M i).context r := by
  obtain ⟨hd, hfi, hfc⟩ := readsOk_spec hr
  rw [devOf_of_lt hi]
  refine ⟨fun d hd' => ?_, fun d hd' => ?_, fun d hd' => ?_⟩
  · apply readsAlike_find?
    have := hd d hd'
    cases lvl2 with
    | true => exact hR.good2 hi hh hl this
    | false => exact hR.good1 hi hh hl hG this
  · have := hfi d hd'
    obtain ⟨x, hx, hw⟩ := by
      cases lvl2 with
      | true => exact hR.full2 hi hh hl this
      | false => exact hR.full1 hi hh hl hG this
    show ∃ cv caps, (ctxOf (S.mb i)).find? d = some (.indInfo cv caps)
    rw [hx]
    cases x with
    | indInfo cv caps => exact ⟨cv, caps, rfl⟩
    | _ => cases hw
  · have := hfc d hd'
    obtain ⟨x, hx, hw⟩ := by
      cases lvl2 with
      | true => exact hR.full2 hi hh hl this
      | false => exact hR.full1 hi hh hl hG this
    show ∃ cv nP nF, (ctxOf (S.mb i)).find? d = some (.ctorInfo cv nP nF)
    rw [hx]
    cases x with
    | ctorInfo cv nP nF => exact ⟨cv, nP, nF, rfl⟩
    | _ => cases hw

theorem unitOk_spec {h : Nat} {fe : FEnv} {flagged : Name → Bool} {u : Unit'} {r : Reads}
    (hu : unitOk S h fe flagged u r = true) :
    (∀ (j : Nat) (ci : ConstantInfo) (t : Option ProjTable),
      u.slot.prv.priv[j]? = some ci → u.slot.prv.tbls[j]? = some t →
      lawsOk r.all2 (lawsOf t ci) = true) ∧
    readsOk S h fe u true #[] r.all2 = true ∧
    (∀ (j : Nat) (ci : ConstantInfo) (g v : Array (Nat × UInt8)) (t : Option ProjTable),
      j < u.slot.prv.priv.size → u.slot.exp.at1[j]? = some (some ci) → u.slot.exp.g1[j]? = some g →
      u.slot.exp.v1[j]? = some v → u.slot.exp.tbls[j]? = some t → g.isEmpty = true →
      v.isEmpty = true → lawsOk r.all1 (lawsOf t ci) = true) ∧
    readsOk S h fe u false #[] r.all1 = true ∧
    (∀ (j : Nat) (ci : ConstantInfo) (g v : Array (Nat × UInt8)) (t : Option ProjTable),
      j < u.slot.prv.priv.size → u.slot.exp.at1[j]? = some (some ci) →
      u.slot.exp.g1[j]? = some g → u.slot.exp.v1[j]? = some v → u.slot.exp.tbls[j]? = some t →
      (g.isEmpty && v.isEmpty) = false → ∃ rt rf, (j, rt, rf) ∈ r.gated ∧
        lawsOk rt (lawsOf t (if v.isEmpty then ci else asAxiom ci)) = true ∧
        readsOk S h fe u false g rt = true ∧
        (v.isEmpty = false → lawsOk rf (lawsOf t ci) = true ∧
          readsOk S h fe u false (g ++ v) rf = true)) := by
  unfold unitOk at hu
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hu
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hu
  refine ⟨fun j ci t hc ht => ?_, h3, fun j ci g v t hj ha hg hv ht hge hve => ?_, h5,
    fun j ci g v t hj ha hg hv ht hgv => ?_⟩
  · have hj : j < u.slot.prv.priv.size := by
      rcases Nat.lt_or_ge j u.slot.prv.priv.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hc; cases hc
    have := h2 j hj
    rw [hc, ht] at this
    exact this
  · have := h4 j hj
    rw [ha, hg, hv, ht] at this
    simp only [hge, hve, Bool.and_self, Bool.not_true, Bool.false_or] at this
    exact this
  · have := h6 j hj
    rw [ha, hg, hv, ht] at this
    simp only [hgv, Bool.false_or, Array.any_eq_true] at this
    obtain ⟨k, hk, hk'⟩ := this
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hk'
    obtain ⟨⟨⟨hj', hl⟩, hrd⟩, hrest⟩ := hk'
    refine ⟨r.gated[k].2.1, r.gated[k].2.2, ?_, ?_, hrd, fun hve => ?_⟩
    · rw [← hj']; exact Array.getElem_mem hk
    · exact hl
    · rcases hrest with h' | h'
      · rw [hve] at h'; cases h'
      · exact h'

/-- The table a context presents for a type former: the home's, at the
viewer's level of it. -/
theorem ctx_findTable_slot {i h j : Nat} {n : Name} {cv : ConstantVal} {caps : IndCaps}
    (hp : (S.mb i).pick? n = some (h, j, .indInfo cv caps)) {T : ProjTable}
    (hT : (ctxOf (S.mb i)).findTable? n = some T) (hl : h < (S.lvl i).size)
    (hs : h < S.slots.size) :
    (if lvlAt (S.lvl i) h == 2 then (S.slot h).prv.tbls[j]? else (S.slot h).exp.tbls[j]?).join =
      some T := by
  rw [ctxOf_findTable?] at hT
  obtain ⟨h', j', cv', caps', hp', -, hs', hl', hsel⟩ := MBase.findTable?_some' hT
  rw [hp] at hp'
  simp only [Option.some.injEq, Prod.mk.injEq] at hp'
  obtain ⟨rfl, rfl, -⟩ := hp'
  have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs
  rw [hsl] at hsel
  rw [lvlAt_eq hl]
  exact hsel

/-! ## The interface, checked at its home -/

/-- A name a home's read checks accept is stored in its own environment. -/
theorem RunOk.read_home (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {lvl2 : Bool}
    {G : Array (Nat × UInt8)} {d : Name}
    (hr : (if lvl2 then read2Ok S h M[h].fe d else read1Ok S h M[h].fe M[h].unit G d) = true) :
    ((envAt M[h].fe (ctxOf (S.mb h))).find? d).isSome = true := by
  cases ht : target h M[h].fe d with
  | none => cases lvl2 <;> simp [read2Ok, read1Ok, ht] at hr
  | some t =>
    rw [← hR.fe_find? hh]
    rcases hR.target_cases hh ht with ⟨-, p, -, -, hf⟩ | ⟨-, ci, -, hf⟩ <;> rw [hf] <;> rfl

/-- A name a home's full read checks accept is stored in its own
environment, of the wanted kind. -/
theorem RunOk.full_home (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {lvl2 : Bool}
    {G : Array (Nat × UInt8)} {w : Want} {d : Name}
    (hr : (if lvl2 then full2Ok S h M[h].fe M[h].unit w d
      else full1Ok S h M[h].fe M[h].unit G w d) = true) :
    ∃ x, (envAt M[h].fe (ctxOf (S.mb h))).find? d = some x ∧ w.ok x = true := by
  cases ht : target h M[h].fe d with
  | none => cases lvl2 <;> simp [full2Ok, full1Ok, ht] at hr
  | some t =>
    obtain ⟨t1, t2⟩ := t
    have hb := (hR.finalCanon hh).base
    rcases hR.target_cases hh ht with ⟨ht1, p, hp, -, hf⟩ | ⟨hne, ci, hpk, hf⟩
    · simp only at ht1 hp
      subst ht1
      refine ⟨p, by rw [← hR.fe_find? hh, hf], ?_⟩
      rw [hR.slot t1 hh] at hp
      cases lvl2 <;> simp [full2Ok, full1Ok, ht, hp] at hr
      · exact hr.1.2
      · exact hr.2
    · simp only at hne hpk
      refine ⟨ci, by rw [← hR.fe_find? hh, hf], ?_⟩
      cases lvl2 <;> simp [full2Ok, full1Ok, ht, hb, hpk, hne] at hr
      · exact hr.1
      · exact hr

/-- **A home's read set, checked, gives good names in the home**: the
names it reads are stored in its own environment and listed, the type
formers and constructors stored as such. -/
theorem RunOk.lawsGood_home (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {lvl2 : Bool}
    {G : Array (Nat × UInt8)} {r : ReadSet} (hr : readsOk S h M[h].fe M[h].unit lvl2 G r = true) :
    LawsGood (readsIn (envAt M[h].fe (ctxOf (S.mb h))) r.d.keys)
      (envAt M[h].fe (ctxOf (S.mb h))) r := by
  obtain ⟨hd, hfi, hfc⟩ := readsOk_spec hr
  refine ⟨fun d hd' => readsIn_isSome (hR.read_home hh (hd d hd'))
      (Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_contains.mpr hd')), fun d hd' => ?_,
    fun d hd' => ?_⟩
  · obtain ⟨x, hx, hw⟩ := hR.full_home hh (hfi d hd')
    rw [hx]
    cases x with
    | indInfo cv caps => exact ⟨cv, caps, rfl⟩
    | _ => cases hw
  · obtain ⟨x, hx, hw⟩ := hR.full_home hh (hfc d hd')
    rw [hx]
    cases x with
    | ctorInfo cv nP nF => exact ⟨cv, nP, nF, rfl⟩
    | _ => cases hw

theorem lawsOf_axiomInfo (t t' : Option ProjTable) (cv : ConstantVal) :
    lawsOf t (.axiomInfo cv) = lawsOf t' (.axiomInfo cv) := rfl

/-- **The presentations of a home's constant**: each is the constant or
the assumption of its statement; a presented type former carries the
home's table; and each was checked against a read set whose names are its
footprint. -/
theorem RunOk.presOf_spec (hR : RunOk mode S M) {h : Nat} (hh : h < M.size) {j : Nat}
    {c : ConstantInfo} {e : Presented} (hc : (S.slot h).prv.priv[j]? = some c)
    (he : e ∈ presOf S h M[h] j) :
    (e.ci = c ∨ (e.ci = asAxiom c ∧ hideable c = true)) ∧
    (∀ cv caps, e.ci = .indInfo cv caps →
      e.table = M[h].fe.env.tables.find? (·.structName == c.name)) ∧
    ∃ (r : ReadSet) (lvl2 : Bool) (G : Array (Nat × UInt8)), e.reads = r.d.keys ∧
      lawsOk r (lawsOf e.table e.ci) = true ∧ readsOk S h M[h].fe M[h].unit lvl2 G r = true := by
  obtain ⟨hA2, hR2, hA1, hR1, hGt⟩ := unitOk_spec (hR.unit h hh)
  rw [← hR.slot h hh] at hA2 hA1 hGt
  obtain ⟨h1, h2, h3, h4, -, -, h7, hj⟩ := shapeOk_spec (hR.shape hh)
  obtain ⟨st, -, hat1, hstiff, hvst, -, -, hpt, het⟩ := hj j c hc
  have hjp : j < (S.slot h).prv.priv.size := by
    rcases Nat.lt_or_ge j (S.slot h).prv.priv.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hc; cases hc
  have hgj : (S.slot h).exp.g1[j]? = some (S.slot h).exp.g1[j] :=
    Array.getElem?_eq_getElem (by rw [← h3]; exact hjp)
  have hvj : (S.slot h).exp.v1[j]? = some (S.slot h).exp.v1[j] :=
    Array.getElem?_eq_getElem (by rw [← h4]; exact hjp)
  -- the home's table of a presented former
  have hX : ∀ a, (a = c ∨ (a = asAxiom c ∧ hideable c = true)) →
      (S.slot h).exp.at1[j]? = some (some a) → ∀ cv caps, a = .indInfo cv caps →
      (if st then M[h].fe.env.tables.find? (·.structName == c.name) else none) =
        M[h].fe.env.tables.find? (·.structName == c.name) := by
    intro a ha hat cv caps hind
    have : a = c := by
      rcases ha with rfl | ⟨rfl, -⟩
      · rfl
      · unfold asAxiom at hind; cases hind
    subst this
    rw [(hstiff.mpr hat)]; rfl
  unfold presOf at he
  rw [hc] at he
  simp only [List.mem_cons] at he
  rcases he with rfl | he
  · refine ⟨.inl rfl, fun cv caps _ => by rw [hpt]; rfl,
      (S.slot h).prv.priv.size |> fun _ => ⟨M[h].reads.all2, true, #[], rfl, ?_, hR2⟩⟩
    have := hA2 j c _ hc hpt
    rw [hpt]
    exact this
  -- the exported level
  have hA : ∀ a, (S.slot h).exp.at1[j]? = some (some a) →
      (a = c ∨ (a = asAxiom c ∧ hideable c = true)) := by
    intro a ha
    rcases hat1 with h' | h' | ⟨h', hh'⟩ <;> rw [h'] at ha <;> cases ha
    · exact .inl rfl
    · exact .inr ⟨rfl, hh'⟩
  cases hat : (S.slot h).exp.at1[j]? with
  | none => rw [hat] at he; simp at he
  | some x =>
    cases x with
    | none => rw [hat] at he; simp at he
    | some a =>
      have ha := hA a hat
      rw [hat, hgj, hvj, het] at he
      simp only at he
      split at he
      · -- ungated
        rename_i hun
        simp only [List.mem_singleton] at he
        subst he
        simp only [Bool.and_eq_true] at hun
        refine ⟨ha, fun cv caps hind => hX a ha hat cv caps hind,
          ⟨M[h].reads.all1, false, #[], rfl, ?_, hR1⟩⟩
        exact hA1 j a _ _ _ hjp hat hgj hvj het hun.1 hun.2
      · rename_i hun
        cases hx : M[h].reads.gated.find? (gatedOk S h M[h] j a (S.slot h).exp.g1[j]
            (S.slot h).exp.v1[j] (if st then M[h].fe.env.tables.find? (·.structName == c.name)
              else none)) with
        | none => rw [hx] at he; simp at he
        | some x =>
          rw [hx] at he
          obtain ⟨j', rt, rf⟩ := x
          simp only at he
          have hok := Array.find?_some hx
          unfold gatedOk at hok
          simp only [Bool.and_eq_true, Bool.or_eq_true] at hok
          obtain ⟨⟨⟨-, hlt⟩, hrt⟩, hrest⟩ := hok
          have hve : (S.slot h).exp.v1[j].isEmpty = false → a = c ∧ hideable c = true := by
            intro hve
            rcases hvst _ hvj with h' | ⟨hst', hh'⟩
            · rw [hve] at h'; cases h'
            · rw [hst'] at hstiff
              have := hstiff.mp rfl
              rw [hat] at this
              cases this
              exact ⟨rfl, hh'⟩
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · cases hv : (S.slot h).exp.v1[j].isEmpty with
            | true =>
              simp only [hv, ↓reduceIte] at hlt ⊢
              exact ⟨ha, fun cv caps hind => hX a ha hat cv caps hind,
                ⟨rt, false, _, rfl, hlt, hrt⟩⟩
            | false =>
              simp only [hv, Bool.false_eq_true, ↓reduceIte] at hlt ⊢
              obtain ⟨rfl, hh'⟩ := hve hv
              refine ⟨.inr ⟨rfl, hh'⟩, (fun cv caps hind => by unfold asAxiom at hind; cases hind),
                ⟨rt, false, _, rfl, ?_, hrt⟩⟩
              unfold asAxiom at hlt ⊢
              rw [lawsOf_axiomInfo none]
              exact hlt
          · cases hv : (S.slot h).exp.v1[j].isEmpty with
            | true => simp [hv] at he
            | false =>
              simp only [hv, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at he
              subst he
              rcases hrest with h' | ⟨hlf, hrf⟩
              · rw [hv] at h'; cases h'
              · exact ⟨ha, fun cv caps hind => hX a ha hat cv caps hind,
                  ⟨rf, false, _, rfl, hlf, hrf⟩⟩

/-- A name of a home's interface is the name of one of its constants,
presented. -/
theorem iface_mem {h : Nat} (hh : h < M.size) {n : Name} {e : Presented}
    (he : e ∈ ifaceOf S h M[h] n) :
    ∃ j c, (S.slot h).prv.priv[j]? = some c ∧ c.name = n ∧ e ∈ presOf S h M[h] j := by
  unfold ifaceOf at he
  rw [List.mem_flatMap] at he
  obtain ⟨j, -, he⟩ := he
  cases hc : (S.slot h).prv.priv[j]? with
  | none => rw [hc] at he; simp at he
  | some c =>
    rw [hc] at he
    simp only [Option.map_some, beq_iff_eq, Option.some.injEq] at he
    split at he
    · rename_i hn; exact ⟨j, c, hc, hn, he⟩
    · simp at he

/-- **The interface of every module of a run is checked once** (by its
unit's check, `unitOk`, at its home). -/
theorem RunOk.interfaceOk (hR : RunOk mode S M) (b : Nat) : InterfaceOk (devOf S M) b := by
  by_cases hb : b < M.size
  case neg =>
    have hd := devOf_of_ge (S := S) hb
    refine ⟨fun n e he => ?_, fun n e he => ?_, fun n e he => ?_, fun n e he => ?_⟩ <;>
      (rw [hd] at he; simp [emptyModule] at he)
  have hd := devOf_of_lt (S := S) hb
  have hown : (devOf S M b).own = envAt M[b].fe (ctxOf (S.mb b)) := by rw [hd]; rfl
  have hmem : ∀ n e, e ∈ (devOf S M b).iface n →
      ∃ j c, (S.slot b).prv.priv[j]? = some c ∧ c.name = n ∧ e ∈ presOf S b M[b] j :=
    fun n e he => iface_mem hb (by rw [hd] at he; exact he)
  have hname : ∀ {e : Presented} {c : ConstantInfo},
      (e.ci = c ∨ (e.ci = asAxiom c ∧ hideable c = true)) → e.ci.name = c.name := by
    intro e c hci
    rcases hci with h' | ⟨h', -⟩ <;> rw [h'] <;> rfl
  refine ⟨fun n e he => ?_, fun n e he cv caps hce => ?_, fun n e he => ?_,
    fun n e he cv mI rP rules hce r hr cvj nP nF hcj T us hT => ?_⟩
  · obtain ⟨j, c, hc, rfl, he'⟩ := hmem n e he
    obtain ⟨hci, -, -⟩ := hR.presOf_spec hb hc he'
    refine ⟨c, by rw [hown]; exact hR.own_find? hb hc, ?_⟩
    rcases hci with h' | ⟨h', hhide⟩
    · rw [h']; exact .inl rfl
    · rw [h']; exact .inr ⟨not_pinned_of_hideable hhide, rfl⟩
  · obtain ⟨j, c, hc, rfl, he'⟩ := hmem n e he
    obtain ⟨-, htab, -⟩ := hR.presOf_spec hb hc he'
    rw [htab cv caps hce, hown, hR.own_findTable? hb hc]
  · obtain ⟨j, c, hc, rfl, he'⟩ := hmem n e he
    obtain ⟨hci, htab, r, l2, G, hre, hlaw, hrd⟩ := hR.presOf_spec hb hc he'
    rw [hre, hown]
    refine (laws_entry hlaw (hR.lawsGood_home hb hrd) (fun cv caps hce T hT => ?_)
      (hname hci)).1
    rw [htab cv caps hce, ← hR.own_findTable? hb hc]
    exact hT
  · obtain ⟨j, c, hc, rfl, he'⟩ := hmem n e he
    obtain ⟨hci, -, -⟩ := hR.presOf_spec hb hc he'
    have hcrec : c = .recInfo cv mI rP rules := by
      rcases hci with h' | ⟨h', -⟩
      · rw [← h', hce]
      · rw [hce] at h'; unfold asAxiom at h'; cases h'
    subst hcrec
    rw [hown] at hcj ⊢
    -- the unit's recursor check
    have hu := hR.unit b hb
    unfold unitOk at hu
    simp only [Bool.and_eq_true] at hu
    have hrf := hu.1.1.1.1.1.2
    rw [← hR.slot b hb, Array.all_eq_true] at hrf
    have hjs : j < (S.slot b).prv.priv.size := by
      rcases Nat.lt_or_ge j (S.slot b).prv.priv.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hc; cases hc
    have := hrf j hjs
    have hpj : (S.slot b).prv.priv[j] = .recInfo cv mI rP rules := by
      rw [Array.getElem?_eq_getElem hjs] at hc
      exact Option.some.inj hc
    rw [hpj] at this
    unfold recFamOk at this
    simp only [List.all_eq_true] at this
    have hr' := this r hr
    have hcj' : M[b].fe.find? r.ctor = some (.ctorInfo cvj nP nF) := by
      rw [hR.fe_find? hb]; exact hcj
    rw [hcj'] at hr'
    simp only at hr'
    rw [hT] at hr'
    simp only at hr'
    revert hr'
    cases hfT : M[b].fe.find? T with
    | none => intro h'; cases h'
    | some cT =>
      intro h'
      cases cT with
      | indInfo cvT capsT =>
        refine ⟨cvT, capsT, ?_⟩
        rw [← hR.fe_find? hb]; exact hfT
      | _ => cases h'

/-! ## The importer's checks -/

/-- **A context constant is a presentation of its source's interface**,
with that presentation's table, checked against a read set of names
good in the importer. -/
theorem RunOk.ctx_pres (hR : RunOk mode S M) {i : Nat} (hi : i < M.size) {n : Name}
    {ci : ConstantInfo} (hf : (devOf S M i).context.find? n = some ci) :
    ci.name = n ∧ ∃ e ∈ (devOf S M ((devOf S M i).src n)).iface n, e.ci = ci ∧
      (devOf S M i).context.findTable? n = formerTable ci e.table ∧
      ∃ r : ReadSet, e.reads = r.d.keys ∧ lawsOk r (lawsOf e.table e.ci) = true ∧
        LawsGood (readsAlike (devOf S M) i ((devOf S M i).src n)) (devOf S M i).context r := by
  have hf' := hf
  rw [devOf_of_lt hi] at hf'
  obtain ⟨h, j, hp, hat, hcn, hlt, hl, hlv⟩ := hR.ctx_entry hi hf'
  have hh : h < M.size := Nat.lt_trans hlt hi
  have hs : h < S.slots.size := by rw [hR.slots]; exact hh
  have hsrc : (devOf S M i).src n = h := by
    rw [devOf_of_lt hi]
    show (match (S.mb i).pick? n with
      | some (h, _, _) => h
      | none => 0) = h
    rw [hp]
  rw [hsrc]
  refine ⟨hcn, ?_⟩
  have hctx : (devOf S M i).context = ctxOf (S.mb i) := by rw [devOf_of_lt hi]; rfl
  have hif : (devOf S M h).iface n = ifaceOf S h M[h] n := by rw [devOf_of_lt hh]; rfl
  rw [hif]
  obtain ⟨c, hc, hcname⟩ := hR.at?_name hat hh
  rw [hcn] at hcname
  have hjp : j < (S.slot h).prv.priv.size := by
    rcases Nat.lt_or_ge j (S.slot h).prv.priv.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hc; cases hc
  have hin : ∀ e ∈ presOf S h M[h] j, e ∈ ifaceOf S h M[h] n := by
    intro e he
    unfold ifaceOf
    rw [List.mem_flatMap]
    refine ⟨j, List.mem_range.mpr hjp, ?_⟩
    simp only [hc, Option.map_some, hcname, beq_self_eq_true, ↓reduceIte]
    exact he
  obtain ⟨hA2, hR2, hA1, hR1, hGt⟩ := unitOk_spec (hR.unit h hh)
  rw [← hR.slot h hh] at hA2 hA1 hGt
  obtain ⟨h1, h2, h3, h4, -, -, h7, hj⟩ := shapeOk_spec (hR.shape hh)
  obtain ⟨st, -, -, hstiff, hvst, -, -, hpt, het⟩ := hj j c hc
  -- the context's table: the home's, at the viewer's level, for a former
  have htabC : ∀ t : Option ProjTable,
      ((if lvlAt (S.lvl i) h == 2 then (S.slot h).prv.tbls[j]? else (S.slot h).exp.tbls[j]?)
        = some t) → (∀ cv caps, ci = .indInfo cv caps →
          t = M[h].fe.env.tables.find? (·.structName == c.name)) →
      (devOf S M i).context.findTable? n = formerTable ci t := by
    intro t ht hX
    rw [hctx, ctxOf_findTable?]
    unfold MBase.findTable?
    rw [hp]
    revert hX
    cases ci with
    | indInfo cvI capsI =>
      intro hX
      simp only [formerTable]
      have hs' : h < (S.mb i).slots.size := (MBase.at?_some hat).2.1
      simp only [hs', ↓reduceDIte]
      have hsl : (S.mb i).slots[h].get = S.slot h := Store.slot_eq S hs'
      have hl' : h < (S.mb i).lvl.size := hl
      simp only [hl', ↓reduceDIte, hsl]
      have hlv' : (S.mb i).lvl[h] = lvlAt (S.lvl i) h := by
        unfold lvlAt; simp only [hl, ↓reduceDIte]; rfl
      rw [hlv', ht, hX cvI capsI rfl]
      simp only [Option.join_some]
      cases hq : M[h].fe.env.tables.find? (·.structName == c.name) with
      | none => rfl
      | some t' =>
        have := List.find?_some hq
        simp only [beq_iff_eq] at this
        simp [this, hcname]
    | _ => intro _; rfl
  rcases hlv with hl1 | hl2
  · -- the exported level
    obtain ⟨a, ha, hg, hv⟩ := at?_lvl1 hat hl1
    have hja : j < (S.slot h).exp.at1.size := by rw [← h1]; exact hjp
    have hgj : (S.slot h).exp.g1[j]? = some (S.slot h).exp.g1[j] :=
      Array.getElem?_eq_getElem (by rw [← h3]; exact hjp)
    have hvj : (S.slot h).exp.v1[j]? = some (S.slot h).exp.v1[j] :=
      Array.getElem?_eq_getElem (by rw [← h4]; exact hjp)
    have ht' : (if lvlAt (S.lvl i) h == 2 then (S.slot h).prv.tbls[j]?
        else (S.slot h).exp.tbls[j]?) = some (if st then M[h].fe.env.tables.find?
          (·.structName == c.name) else none) := by
      rw [hl1]; simp only [show ((1 : UInt8) == 2) = false from rfl, Bool.false_eq_true,
        ↓reduceIte, het]
    -- a former at the exported level is presented as stored
    have hX : ∀ cv caps, ci = .indInfo cv caps →
        (if st then M[h].fe.env.tables.find? (·.structName == c.name) else none) =
          M[h].fe.env.tables.find? (·.structName == c.name) := by
      intro cv caps hind
      have hac : a = c := by
        rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · obtain ⟨c', hc', hci'⟩ := hR.at?_home hat hh
          rw [hc] at hc'; cases hc'
          rcases hci' with h' | ⟨h', -⟩
          · exact h'
          · rw [hind] at h'; unfold asAxiom at h'; cases h'
        · cases hind
      subst hac
      rw [hstiff.mpr ha]; rfl
    rw [hgj] at hg
    rw [hvj] at hv
    simp only [Option.getD_some] at hg hv
    have hgG := gateOk_iff.mp hg
    have hpres := hin
    unfold presOf at hpres
    rw [hc] at hpres
    simp only [ha, hgj, hvj, het, List.mem_cons] at hpres
    by_cases hun : ((S.slot h).exp.g1[j].isEmpty && (S.slot h).exp.v1[j].isEmpty) = true
    · simp only [Bool.and_eq_true] at hun
      have hci : ci = a := by
        rcases hv with ⟨-, rfl⟩ | ⟨hvc, -⟩
        · rfl
        · rw [Array.isEmpty_iff.mp hun.2, gateOk_nil] at hvc; cases hvc
      subst hci
      refine ⟨⟨ci, (if st then M[h].fe.env.tables.find? (·.structName == c.name) else none), M[h].reads.all1.d.keys⟩,
        hpres _ (.inr (by simp [hun])), rfl, htabC _ ht' hX, M[h].reads.all1, rfl,
        hA1 j ci _ _ _ hjp ha hgj hvj het hun.1 hun.2,
        hR.lawsGood hi hh (lvl2 := false) hl1 (fun p hp => by simp at hp) hR1⟩
    · obtain ⟨rt, rf, hmem, hlt', hrt, hrf⟩ :=
        hGt j a _ _ _ hjp ha hgj hvj het (Bool.not_eq_true _ ▸ hun)
      have hfind : (M[h].reads.gated.find? (gatedOk S h M[h] j a (S.slot h).exp.g1[j]
          (S.slot h).exp.v1[j] (if st then M[h].fe.env.tables.find? (·.structName == c.name)
            else none))).isSome = true := by
        rw [Array.find?_isSome]
        refine ⟨(j, rt, rf), hmem, ?_⟩
        unfold gatedOk
        simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨⟨hlt', hrt⟩, ?_⟩
        cases hve : (S.slot h).exp.v1[j].isEmpty with
        | true => exact .inl rfl
        | false => exact .inr (hrf hve)
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hfind
      obtain ⟨j', rt', rf'⟩ := x
      have hok := Array.find?_some hx
      unfold gatedOk at hok
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hok
      obtain ⟨⟨⟨-, hlt''⟩, hrt'⟩, hrest⟩ := hok
      have hun' : ((S.slot h).exp.g1[j].isEmpty && (S.slot h).exp.v1[j].isEmpty) = false :=
        Bool.not_eq_true _ ▸ hun
      simp only [hun', Bool.false_eq_true, ↓reduceIte, hx, List.mem_cons] at hpres
      rcases hv with ⟨hvo, rfl⟩ | ⟨hvc, rfl⟩
      · cases hve : (S.slot h).exp.v1[j].isEmpty with
        | true =>
          simp only [hve, ↓reduceIte] at hlt'' hpres
          exact ⟨⟨ci, (if st then M[h].fe.env.tables.find? (·.structName == c.name) else none), rt'.d.keys⟩, hpres _ (.inr (.inl rfl)), rfl,
            htabC _ ht' hX, rt', rfl, hlt'', hR.lawsGood hi hh (lvl2 := false) hl1 hgG hrt'⟩
        | false =>
          simp only [hve, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hpres
          rcases hrest with h' | ⟨hlf, hrf'⟩
          · rw [hve] at h'; cases h'
          refine ⟨⟨ci, (if st then M[h].fe.env.tables.find? (·.structName == c.name) else none), rf'.d.keys⟩, hpres _ (.inr (.inr rfl)), rfl,
            htabC _ ht' hX, rf', rfl, hlf,
            hR.lawsGood hi hh (lvl2 := false) hl1 (fun p hp => ?_) hrf'⟩
          rcases Array.mem_append.mp hp with hp | hp
          · exact hgG p hp
          · exact gateOk_iff.mp hvo p hp
      · have hve : (S.slot h).exp.v1[j].isEmpty = false := by
          cases hq : (S.slot h).exp.v1[j].isEmpty with
          | false => rfl
          | true => rw [Array.isEmpty_iff.mp hq, gateOk_nil] at hvc; cases hvc
        simp only [hve, Bool.false_eq_true, ↓reduceIte] at hlt'' hpres
        refine ⟨⟨asAxiom a, none, rt'.d.keys⟩, hpres _ (.inr (.inl rfl)), rfl,
          by rw [htabC _ ht' (fun cv caps he => nomatch he)]; rfl,
          rt', rfl, ?_, hR.lawsGood hi hh (lvl2 := false) hl1 hgG hrt'⟩
        show lawsOk rt' (lawsOf none (asAxiom a)) = true
        exact hlt''
  · -- the private level
    have hpj := at?_lvl2 hat hl2
    have hcc : c = ci := by rw [hc] at hpj; exact Option.some.inj hpj
    subst hcc
    have ht' : ((if lvlAt (S.lvl i) h == 2 then (S.slot h).prv.tbls[j]?
        else (S.slot h).exp.tbls[j]?) = some (M[h].fe.env.tables.find? (·.structName == c.name))) := by
      rw [hl2]; simp only [show ((2 : UInt8) == 2) = true from rfl, ↓reduceIte, hpt]
    have hpres := hin
    unfold presOf at hpres
    rw [hc] at hpres
    refine ⟨⟨c, ((S.slot h).prv.tbls[j]?).join, M[h].reads.all2.d.keys⟩,
      hpres _ (List.mem_cons_self ..), rfl, ?_, M[h].reads.all2, rfl, ?_,
      hR.lawsGood hi hh (lvl2 := true) hl2 (fun p hp => by simp at hp) hR2⟩
    · rw [hpt]; exact htabC _ ht' fun _ _ _ => rfl
    · rw [hpt]; exact hA2 j c _ hc hpt

/-- **Every module of a run passes its importer's checks.** -/
theorem RunOk.importOk (hR : RunOk mode S M) (i : Nat) :
    ImportOk mode natOpPinSets (devOf S M) i := by
  by_cases hi : i < M.size
  case neg =>
    have hd := devOf_of_ge (S := S) hi
    refine { below := ?_, src_lt := ?_, nodup := ?_, accepted := ?_, compared_own := ?_,
             presented := ?_, projs := ?_, blocks := ?_, tables_mem := ?_, res_context := ?_,
             res_own := ?_ } <;>
      simp [hd, emptyModule, Env.find?, AcceptedFrom.nil]
  have hd := devOf_of_lt (S := S) hi
  have hent : ∀ n ci, (devOf S M i).context.find? n = some ci →
      EntryProjs (devOf S M i).context n ci ∧ BlockIn (devOf S M i).context n ci := by
    intro n ci hf
    obtain ⟨hn, e, -, rfl, ht, r, -, hlaw, hg⟩ := hR.ctx_pres hi hf
    refine (laws_entry hlaw hg (fun cv caps hce T hT => ?_) hn).2
    rw [ht, hce] at hT
    exact hT
  refine { below := ?_, src_lt := hR.src_lt hi, nodup := ?_, accepted := fun _ => hR.accepted hi,
           compared_own := ?_, presented := fun n ci hf => ?_,
           projs := fun n ci hf => (hent n ci hf).1, blocks := fun n ci hf => (hent n ci hf).2,
           tables_mem := ?_, res_context := hR.res_context hi, res_own := ?_ }
  · rw [hd]; exact hR.below i hi
  · rw [hd]; exact ctxOf_nodup _
  · rw [hd]; intro h; cases h
  · obtain ⟨-, e, he, hec, ht, r, hre, -, hg⟩ := hR.ctx_pres hi hf
    refine ⟨e, he, hec, ht, fun d hd' => ?_⟩
    rw [hre] at hd'
    exact of_readsAlike (hg.d d (Std.HashMap.mem_iff_contains.mp (Std.HashMap.mem_keys.mp hd')))
  · rw [hd]; exact ctxOf_tables_mem _
  · rw [hd]
    intro n ci hown hctx
    change (envAt M[i].fe (ctxOf (S.mb i))).find? n = some ci at hown
    change (ctxOf (S.mb i)).find? n = none at hctx
    show resOf S i M[i] n = _
    unfold resOf
    rw [ctxOf_find?] at hctx
    have hp : (S.mb i).pick? n = none := by
      cases hp : (S.mb i).pick? n with
      | none => rfl
      | some x =>
        obtain ⟨h, j, ci'⟩ := x
        unfold MBase.find? at hctx; rw [hp] at hctx; cases hctx
    rw [hp]
    simp only [hown]
    show _ = (if M[i].flags.contains n = true then _ else _)
    rfl

/-! ## The local checks -/

/-- **A modular run's checks are the local checks**: every interface
checked at its home, every importer's checks at the importer. -/
theorem RunOk.localOk (hR : RunOk mode S M) (i : Nat) :
    LocalOk mode natOpPinSets (devOf S M) i :=
  LocalOk.of_interface (fun b _ => hR.interfaceOk b) (hR.importOk i)

end ConLeche.Cached.Mod
