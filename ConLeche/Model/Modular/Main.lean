module

public import ConLeche.Model.Modular.Restrict
public import ConLeche.Model.Modular.Step

public section

/-!
# The modular theorem: one model of every module's own environment

The proof of `ConLeche.modular_model_exists` (`ConLeche/MainTheorem.lean`),
by induction over the modules of a development (`ConLeche/Modular.lean`):

* **the qualified names fit** (`Fits`): every constant a module's own
  environment stores refines the constant of the home module its
  qualified name names (or, for a proof, has the name's statement), and
  what an inductive kind's laws read resolves as at the home;
* **the context's model** (`ctxSrcOf`, then `CtxSrc.ctxModel`): read from
  the earlier modules' models, at the world's leaves;
* **the step** (`acceptedFrom_model`): the module's declarations
  installed on it, keeping the context's leaves, every flagged proof at
  the canonical proof;
* **the world grows** (`extendAt`) by the module's own ordinary
  constants.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Semantics ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

universe w

/-! ## Lookups -/

theorem find?_filter_name {l : List ConstantInfo} {p : Name → Bool} {n : Name} :
    (l.filter fun c => p c.name).find? (·.name == n) =
      if p n = true then l.find? (·.name == n) else none := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases hp : p c.name = true <;> by_cases hc : c.name = n <;>
      simp_all

section
variable (dev : Nat → Module)

theorem find?_readsAlike {ii bb : Nat} {d' : Name} {ci : ConstantInfo}
    (h : (readsAlike dev ii bb).find? d' = some ci) :
    (dev bb).own.find? d' = some ci ∧ ((dev ii).context.find? d').isSome = true ∧
      (dev ii).res d' = (dev bb).res d' := by
  have h' : List.find? (·.name == d') ((dev bb).own.consts.filter fun c =>
      ((dev ii).context.find? c.name).isSome && (dev ii).res c.name == (dev bb).res c.name)
      = some ci := h
  rw [find?_filter_name (p := fun x =>
      ((dev ii).context.find? x).isSome && (dev ii).res x == (dev bb).res x)] at h'
  have h := h'
  clear h'
  split at h
  · rename_i hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨h, hp.1, hp.2⟩
  · exact nomatch h

end

/-! ## Qualified names fit -/

section
variable (dev : Nat → Module)

/-- **What a qualified name says of a constant** module `j` stores
under `n`: an ordinary name is the home module, no later than `j`, whose
own constant this one refines — with the home's table, if it is a type
former, and, if it is an inductive kind, with what its laws read
resolved as at the home; a proof's name carries its level parameters
and statement, and is never an inductive kind or a pinned name. -/
@[expose] def KeyFits (j : Nat) (n : Name) (ci : ConstantInfo) : Key → Prop
  | .qual P n' => n' = n ∧ P ≤ j ∧ ∃ cp, (dev P).own.find? n = some cp ∧ Refines n ci cp ∧
      (ci.isFormer = true → (dev j).own.findTable? n = (dev P).own.findTable? n) ∧
      (ci.isIndKind = true → EntryScopedP (fun d => ((dev j).own.find? d).isSome = true →
        (dev j).res d = (dev P).res d) (dev j).own n ci)
  | .proof n' lps T => n' = n ∧ ci.toConstantVal.levelParams = lps ∧
      ci.toConstantVal.type = T ∧ ci.isIndKind = false ∧ n ∉ pinnedNames

/-- **Every constant of a module's own environment fits its qualified
name.** -/
@[expose] def Fits (j : Nat) : Prop :=
  ∀ n ci, (dev j).own.find? n = some ci → KeyFits dev j n ci ((dev j).res n)

theorem isIndKind_of_isFormer {ci : ConstantInfo} (h : ci.isFormer = true) :
    ci.isIndKind = true := by
  cases ci <;> simp_all [ConstantInfo.isFormer, ConstantInfo.isIndKind]

theorem constantVal_eq {a b : ConstantVal} (h1 : a.name = b.name)
    (h2 : a.levelParams = b.levelParams) (h3 : a.type = b.type) : a = b := by
  cases a; cases b; simp_all

/-- **Two constants of one qualified name** (in two modules' own
environments): one constant value; equal where both are inductive kinds
or the name is pinned; one table where both are type formers. -/
theorem fits_same {j j' : Nat} {n : Name} {ci ci' : ConstantInfo}
    (hj : Fits dev j) (hj' : Fits dev j') (hf : (dev j).own.find? n = some ci)
    (hf' : (dev j').own.find? n = some ci') (hk : (dev j).res n = (dev j').res n) :
    ci.toConstantVal = ci'.toConstantVal ∧
      (ci.isIndKind = true → ci'.isIndKind = true → ci = ci') ∧
      (n ∈ pinnedNames → ci = ci') ∧
      (ci.isFormer = true → ci'.isFormer = true →
        (dev j).own.findTable? n = (dev j').own.findTable? n) := by
  have h1 := hj n ci hf
  have h2 := hj' n ci' hf'
  rw [← hk] at h2
  revert h1 h2
  cases (dev j).res n with
  | qual P n' =>
    rintro ⟨-, -, cp, hcp, hr, htab, -⟩ ⟨-, -, cp', hcp', hr', htab', -⟩
    rw [hcp] at hcp'; obtain rfl := Option.some.inj hcp'
    refine ⟨hr.cv.trans hr'.cv.symm, fun hk1 hk2 => ?_, fun hp => ?_, fun hf1 hf2 => ?_⟩
    · rw [hr.eq_of_indKind hk1, hr'.eq_of_indKind hk2]
    · rw [hr.eq_of_pinned hp, hr'.eq_of_pinned hp]
    · rw [htab hf1, htab' hf2]
  | proof n' lps T =>
    rintro ⟨-, hl, ht, hki, hp⟩ ⟨-, hl', ht', hki', -⟩
    refine ⟨constantVal_eq ?_ (hl.trans hl'.symm) (ht.trans ht'.symm), fun h => ?_,
      fun h => absurd h hp, fun h => ?_⟩
    · exact (ConLeche.Env.find?_name hf).trans (ConLeche.Env.find?_name hf').symm
    · rw [hki] at h; exact nomatch h
    · rw [isIndKind_of_isFormer h] at hki; exact nomatch hki

end

/-! ## Extensions and footprints -/

theorem Extends.findTable? {E E' : Env} (h : Extends E E') (hnd : NodupNames E')
    {T : Name} (hT : (E.find? T).isSome = true) : E'.findTable? T = E.findTable? T := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
  have hT' : (E'.find? T).isSome = true := by rw [h.find? hnd hci]; rfl
  rw [ConLeche.Env.findTable?_of_isSome hT', ConLeche.Env.findTable?_of_isSome hT]
  obtain ⟨-, -, newQ, hQ, hQf⟩ := h
  rw [hQ, List.find?_append]
  have : newQ.find? (·.structName == T) = none := by
    rw [List.find?_eq_none]
    intro t ht hq
    have hn : t.structName = T := by simpa using hq
    have := hQf t ht
    rw [hn, hci] at this
    exact nomatch this
  rw [this, Option.none_or]

theorem EntryScopedP.table {p : Name → Prop} {C C' : Env} {n : Name} {ci : ConstantInfo}
    (h : EntryScopedP p C n ci) (ht : C'.findTable? n = C.findTable? n) :
    EntryScopedP p C' n ci := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, fun cv caps he => by
    obtain ⟨a, b, c, d⟩ := h4 cv caps he
    exact ⟨a, b, c, fun t htt => d t (by rw [← ht]; exact htt)⟩, h5⟩

theorem EntryScopedP.table' {p : Name → Prop} {C C' : Env} {n : Name} {ci : ConstantInfo}
    (h : EntryScopedP p C n ci)
    (ht : ∀ cv caps, ci = .indInfo cv caps → C'.findTable? n = C.findTable? n) :
    EntryScopedP p C' n ci := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, fun cv caps he => by
    obtain ⟨a, b, c, d⟩ := h4 cv caps he
    exact ⟨a, b, c, fun t htt => d t (by rw [← ht cv caps he]; exact htt)⟩, h5⟩

theorem EntryScopedP.and3 {p q r s : Name → Prop} {C : Env} {n : Name} {ci : ConstantInfo}
    (hpq : ∀ d, p d → q d → r d → s d) (hp : EntryScopedP p C n ci)
    (hq : EntryScopedP q C n ci) (hr : EntryScopedP r C n ci) : EntryScopedP s C n ci := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  obtain ⟨r1, r2, r3, r4, r5⟩ := hr
  refine ⟨Expr.constsAll_and3 hpq p1 q1 r1,
    fun cv v h he => Expr.constsAll_and3 hpq (p2 cv v h he) (q2 cv v h he) (r2 cv v h he),
    fun cv mI rP rules he x hx => ?_, fun cv caps he => ?_, fun d hd => hpq d (p5 d hd) (q5 d hd)
      (r5 d hd)⟩
  · obtain ⟨a1, a2, a3⟩ := p3 cv mI rP rules he x hx
    obtain ⟨b1, b2, b3⟩ := q3 cv mI rP rules he x hx
    obtain ⟨c1, c2, c3⟩ := r3 cv mI rP rules he x hx
    exact ⟨Expr.constsAll_and3 hpq a1 b1 c1, hpq _ a2 b2 c2, fun lvls pins hn y hy =>
      Expr.constsAll_and3 hpq (a3 lvls pins hn y hy) (b3 lvls pins hn y hy) (c3 lvls pins hn y hy)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := p4 cv caps he
    obtain ⟨b1, b2, b3, b4⟩ := q4 cv caps he
    obtain ⟨c1, c2, c3, c4⟩ := r4 cv caps he
    exact ⟨fun m hm => hpq m (a1 m hm) (b1 m hm) (c1 m hm),
      fun x hx => hpq x (a2 x hx) (b2 x hx) (c2 x hx),
      fun he' => hpq _ (a3 he') (b3 he') (c3 he'),
      fun t ht => ⟨hpq _ (a4 t ht).1 (b4 t ht).1 (c4 t ht).1, fun y hy =>
        Expr.constsAll_and3 hpq ((a4 t ht).2 y hy) ((b4 t ht).2 y hy) ((c4 t ht).2 y hy)⟩⟩

theorem Expr.constsAll_true {p : Name → Prop} (h : ∀ d, p d) :
    ∀ {e : Expr}, Expr.constsAll p e := by
  intro e
  induction e with
  | lit l => cases l <;> simp_all [Expr.constsAll]
  | _ => simp_all [Expr.constsAll]

theorem EntryScopedP.of_forall {p : Name → Prop} (h : ∀ d, p d) (C : Env) (n : Name)
    (ci : ConstantInfo) : EntryScopedP p C n ci :=
  ⟨Expr.constsAll_true h, fun _ _ _ _ => Expr.constsAll_true h,
    fun _ _ _ _ _ _ _ => ⟨Expr.constsAll_true h, h _, fun _ _ _ _ _ => Expr.constsAll_true h⟩,
    fun _ _ _ => ⟨fun m _ => h m, fun x _ => h x, fun _ => h _, fun _ _ =>
      ⟨h _, fun _ _ => Expr.constsAll_true h⟩⟩, fun d _ => h d⟩

/-! ## The literal guards read constant values -/

theorem tyOk_congr {F : Option ConstantInfo → Bool}
    (hF : ∀ ci ci', ci.toConstantVal = ci'.toConstantVal → F (some ci) = F (some ci'))
    {o o' : Option ConstantInfo} (h : o.map (·.toConstantVal) = o'.map (·.toConstantVal)) :
    F o = F o' := by
  cases o <;> cases o' <;> simp at h
  · rfl
  · exact hF _ _ h

theorem strLitSupported_congr {E E' : Env} (hnat : natLitSupported E = natLitSupported E')
    (h : ∀ n ∈ [stringName, stringOfListName, listName, listNilName, listConsName, charName,
      charOfNatName], (E.find? n).map (·.toConstantVal) = (E'.find? n).map (·.toConstantVal)) :
    strLitSupported E = strLitSupported E' := by
  unfold strLitSupported
  rw [hnat,
    tyOk_congr (F := stringTyOk) (fun a b hab => by simp [stringTyOk, hab]) (h _ (by simp)),
    tyOk_congr (F := stringOfListTyOk) (fun a b hab => by simp [stringOfListTyOk, hab]) (h _ (by simp)),
    tyOk_congr (F := listTyOk) (fun a b hab => by simp [listTyOk, hab]) (h _ (by simp)),
    tyOk_congr (F := listNilTyOk) (fun a b hab => by simp [listNilTyOk, hab]) (h _ (by simp)),
    tyOk_congr (F := listConsTyOk) (fun a b hab => by simp [listConsTyOk, hab]) (h _ (by simp)),
    tyOk_congr (F := charTyOk) (fun a b hab => by simp [charTyOk, hab]) (h _ (by simp)),
    tyOk_congr (F := charOfNatTyOk) (fun a b hab => by simp [charOfNatTyOk, hab]) (h _ (by simp))]

theorem natLitSupported_congr {E E' : Env}
    (h : ∀ n ∈ [natName, natZeroName, natSuccName], E.find? n = E'.find? n) :
    natLitSupported E = natLitSupported E' := by
  unfold natLitSupported
  rw [h natName (by simp), h natZeroName (by simp), h natSuccName (by simp)]

/-! ## The induction's invariant -/

variable {V : Type w} [SetTheory V] {μ : CheckMode} {pins : List NatOpPinSet}

/-- **A world of leaves**: closed, graded, every proof the canonical one. -/
@[expose] def WorldOk (V : Type w) [SetTheory V] (W : Key → (Name → Nat) → Term) : Prop :=
  (∀ k ψ, Term.Closed (W k ψ)) ∧ (∀ k ψ (ρ : Nat → V), WellDenoted V ρ (W k ψ)) ∧
    ∀ n lps T, W (.proof n lps T) = fun _ => .prf

/-- **The modules below `i`, done**: their qualified names fit, their own
environments extend their contexts, and each has a covered model at the
world's leaves read through its resolution. -/
structure Stage (V : Type w) [SetTheory V] (μ : CheckMode) (dev : Nat → Module)
    (W : Key → (Name → Nat) → Term) (i : Nat) : Prop where
  fits : ∀ j < i, Fits dev j
  ext : ∀ j < i, Extends (dev j).context (dev j).own
  model : ∀ j < i, ∃ mp : EnvModelM V μ (dev j).own, LfpCover mp [] ∧
    ConLeche.EtaFamiliesClosed (dev j).own ∧ NodupNames (dev j).own ∧
    ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = W ((dev j).res n)

section
variable {dev : Nat → Module} {W : Key → (Name → Nat) → Term} {i : Nat}

/-- The context's stored names, read through its own environment. -/
theorem ctx_find_own (hst : Stage V μ dev W (i + 1)) (hj : i < i + 1)
    (hnd : NodupNames (dev i).own) {n : Name} {ci : ConstantInfo}
    (hf : (dev i).context.find? n = some ci) : (dev i).own.find? n = some ci :=
  (hst.ext i hj).find? hnd hf

/-- A module's chosen model. -/
noncomputable def Stage.mod (hst : Stage V μ dev W i) (j : Nat) (hj : j < i) :
    EnvModelM V μ (dev j).own :=
  Classical.choose (hst.model j hj)

theorem Stage.mod_spec (hst : Stage V μ dev W i) (j : Nat) (hj : j < i) :
    LfpCover (hst.mod j hj) [] ∧ ConLeche.EtaFamiliesClosed (dev j).own ∧
      NodupNames (dev j).own ∧ ∀ n, ((dev j).own.find? n).isSome = true →
        (hst.mod j hj).base2.acval n = W ((dev j).res n) :=
  Classical.choose_spec (hst.model j hj)

/-- **A context entry and a source entry of one qualified name**: one
constant value; equal where both are inductive kinds or the name is
pinned; one table where both are type formers. -/
theorem ctx_same (hst : Stage V μ dev W i) (h : LocalOk μ pins dev i) {b : Nat} (hb : b < i)
    {d : Name} {cc ce : ConstantInfo} (hc : (dev i).context.find? d = some cc)
    (he : (dev b).own.find? d = some ce) (hk : (dev i).res d = (dev b).res d) :
    cc.toConstantVal = ce.toConstantVal ∧
      (cc.isIndKind = true → ce.isIndKind = true → cc = ce) ∧
      (d ∈ pinnedNames → cc = ce) ∧
      (cc.isFormer = true → ce.isFormer = true →
        (dev i).context.findTable? d = (dev b).own.findTable? d) := by
  have hcs : ((dev i).context.find? d).isSome = true := by rw [hc]; rfl
  have hs := h.src_lt d hcs
  obtain ⟨cs, hfs, hr⟩ := h.context_le d cc hc
  have hk' : (dev ((dev i).src d)).res d = (dev b).res d := (h.res_context d hcs).symm.trans hk
  obtain ⟨h1, h2, h3, h4⟩ := fits_same dev (hst.fits _ hs) (hst.fits b hb) hfs he hk'
  refine ⟨hr.cv.trans h1, fun hk1 hk2 => ?_, fun hp => ?_, fun hf1 hf2 => ?_⟩
  · have := hr.eq_of_indKind hk1; subst this; exact h2 hk1 hk2
  · rw [hr.eq_of_pinned hp]; exact h3 hp
  · have := hr.eq_of_indKind (isIndKind_of_isFormer hf1); subst this
    have ht := h.tables d cc hc
    rw [ht]
    cases cc with
    | indInfo _ _ => exact h4 hf1 hf2
    | _ => simp [ConstantInfo.isFormer] at hf1

end

section
variable {dev : Nat → Module} {W : Key → (Name → Nat) → Term} {i : Nat}

/-- A name the context stores and resolves as module `b` does, stored by
`b`, is read alike. -/
theorem readsAlike_of {b : Nat} {d : Name} {ci : ConstantInfo}
    (he : (dev b).own.find? d = some ci) (hc : ((dev i).context.find? d).isSome = true)
    (hk : (dev i).res d = (dev b).res d) : ((readsAlike dev i b).find? d).isSome = true := by
  have : List.find? (·.name == d) ((dev b).own.consts.filter fun c =>
      ((dev i).context.find? c.name).isSome && (dev i).res c.name == (dev b).res c.name)
      = some ci := by
    rw [find?_filter_name (p := fun x =>
      ((dev i).context.find? x).isSome && (dev i).res x == (dev b).res x)]
    simp only [hc, hk, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    exact he
  show (List.find? (·.name == d) ((dev b).own.consts.filter fun c =>
      ((dev i).context.find? c.name).isSome && (dev i).res c.name == (dev b).res c.name)).isSome
    = true
  rw [this]; rfl

/-- The entries on both sides of a name read alike. -/
theorem ctx_entries {b : Nat} {d : Name} (hR : ((readsAlike dev i b).find? d).isSome = true) :
    ∃ cc ce, (dev i).context.find? d = some cc ∧ (dev b).own.find? d = some ce ∧
      (dev i).res d = (dev b).res d := by
  obtain ⟨ce, hce⟩ := Option.isSome_iff_exists.mp hR
  obtain ⟨he, hc, hk⟩ := find?_readsAlike dev hce
  obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨cc, ce, hcc, he, hk⟩

theorem readAgree_of (hst : Stage V μ dev W i) (h : LocalOk μ pins dev i) {b : Nat} (hb : b < i) :
    ReadAgree (readsAlike dev i b) (dev i).context (dev b).own (fun n => W ((dev i).res n))
      (hst.mod b hb).base2.acval := by
  have hlf := (hst.mod_spec b hb).2.2.2
  have pinned_eq : ∀ d, ((readsAlike dev i b).find? d).isSome = true → d ∈ pinnedNames →
      (dev i).context.find? d = (dev b).own.find? d := by
    intro d hd hp
    obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hd
    rw [hc, he, (ctx_same hst h hb hc he hk).2.2.1 hp]
  have hnat : (∀ n ∈ natLitNames, ((readsAlike dev i b).find? n).isSome = true ∧
      ((dev b).own.find? n).isSome = true) →
      natLitSupported (dev i).context = natLitSupported (dev b).own := by
    intro hn
    refine natLitSupported_congr fun d hd => pinned_eq d (hn d hd).1 ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact mem_pinned_of_reserved (by decide)
  refine ⟨fun d hR hE => ?_, fun T k hR hE hC hE' => ?_, hnat, fun hn => ?_⟩
  · obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hR
    refine ⟨cc, ce, hc, he, (ctx_same hst h hb hc he hk).1, ?_⟩
    show W ((dev i).res d) = _
    rw [hlf d (by rw [he]; rfl), hk]
  · obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hR
    obtain ⟨cv, caps, hC⟩ := hC
    obtain ⟨cv', caps', hE'⟩ := hE'
    rw [hc] at hC; obtain rfl := Option.some.inj hC
    rw [he] at hE'; obtain rfl := Option.some.inj hE'
    unfold Env.findProj?
    rw [(ctx_same hst h hb hc he hk).2.2.2 rfl rfl]
  · refine strLitSupported_congr (hnat fun n hn' => hn n (by
        simp only [natLitNames, strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hn' ⊢
        rcases hn' with rfl | rfl | rfl <;> simp)) fun d hd => ?_
    have hd' := hn d (by
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hd'.1
    rw [hc, he]
    simp [(ctx_same hst h hb hc he hk).1]

end

section
variable {dev : Nat → Module} {W : Key → (Name → Nat) → Term} {i : Nat}

/-- **What an inductive kind read alike reads is read alike**, where both
sides store it: both resolve it as the kind's home does. -/
theorem deep_of (hst : Stage V μ dev W i) (h : LocalOk μ pins dev i) {b : Nat} (hb : b < i)
    {c : Name} {ci : ConstantInfo} (hc : ((readsAlike dev i b).find? c).isSome = true)
    (hfc : (dev i).context.find? c = some ci) (hk : ci.isIndKind = true)
    (hE : ∃ ci', (dev b).own.find? c = some ci' ∧ ci'.isIndKind = true) :
    EntryScopedP (fun d => ((dev i).context.find? d).isSome = true →
      ((dev b).own.find? d).isSome = true → ((readsAlike dev i b).find? d).isSome = true)
      (dev i).context c ci := by
  have hcs : ((dev i).context.find? c).isSome = true := by rw [hfc]; rfl
  have hs := h.src_lt c hcs
  obtain ⟨cs, hfs, hr⟩ := h.context_le c ci hfc
  obtain rfl : ci = cs := hr.eq_of_indKind hk
  obtain ⟨cc, ce', hc', he', hkb⟩ := ctx_entries hc
  rw [hfc] at hc'; obtain rfl := Option.some.inj hc'
  obtain ⟨ce, hfe, hke⟩ := hE
  rw [hfe] at he'; obtain rfl := Option.some.inj he'
  obtain ⟨-, hsame, -, htabb⟩ := ctx_same hst h hb hfc hfe hkb
  obtain rfl := hsame hk hke
  have hks := h.res_context c hcs
  obtain ⟨-, -, -, htabs⟩ := ctx_same hst h hs hfc hfs hks
  have hFs := hst.fits _ hs c ci hfs
  have hFb := hst.fits b hb c ci hfe
  rw [← hks] at hFs
  rw [← hkb] at hFb
  revert hFs hFb
  cases hkey : (dev i).res c with
  | proof n' lps T =>
    rintro ⟨-, -, -, hki, -⟩; rw [hk] at hki; exact nomatch hki
  | qual P n' =>
    rintro ⟨-, -, -, -, -, -, hGs⟩ ⟨-, -, -, -, -, -, hGb⟩
    have hGs' := (hGs hk).table' (C' := (dev i).context) fun cv caps he => by
      subst he; exact htabs rfl rfl
    have hGb' := (hGb hk).table' (C' := (dev i).context) fun cv caps he => by
      subst he; exact htabb rfl rfl
    have hsc := entryScoped_iff.mp (h.scoping c ci hfc)
    refine EntryScopedP.and3 (fun d h1 h2 h3 hdC hdE => ?_) hsc hGs' hGb'
    obtain ⟨cd, ced, hcd, hed, hkd⟩ := ctx_entries h1
    have e1 := h2 (by rw [hed]; rfl)
    have e2 := h3 hdE
    obtain ⟨ceb, hceb⟩ := Option.isSome_iff_exists.mp hdE
    exact readsAlike_of hceb hdC (hkd.trans (e1.trans e2.symm))

end

section
variable {dev : Nat → Module} {W : Key → (Name → Nat) → Term} {i : Nat}

/-- Each name's source environment with its model (the empty one beyond
the modules done). -/
noncomputable def srcOf (hst : Stage V μ dev W i) (n : Name) : Σ E : Env, EnvModelM V μ E :=
  if h : (dev i).src n < i then ⟨(dev ((dev i).src n)).own, hst.mod _ h⟩
  else ⟨Env.empty, EnvModelM.empty V μ⟩

theorem srcOf_pos (hst : Stage V μ dev W i) {n : Name} (h : (dev i).src n < i) :
    srcOf hst n = ⟨(dev ((dev i).src n)).own, hst.mod _ h⟩ := by
  simp only [srcOf, h, ↓reduceDIte]

theorem srcOf_neg (hst : Stage V μ dev W i) {n : Name} (h : ¬ (dev i).src n < i) :
    srcOf hst n = ⟨Env.empty, EnvModelM.empty V μ⟩ := by
  simp only [srcOf, h, ↓reduceDIte]

/-- The part each source is read alike in. -/
noncomputable def readOf (dev : Nat → Module) (i : Nat) (n : Name) : Env :=
  if (dev i).src n < i then readsAlike dev i ((dev i).src n) else Env.empty

theorem readOf_pos {n : Name} (h : (dev i).src n < i) :
    readOf dev i n = readsAlike dev i ((dev i).src n) := by
  simp only [readOf, h, ↓reduceIte]

/-- **The context, read from its sources** (`CtxSrc`), from the local
checks and the modules done. -/
noncomputable def ctxSrcOf (hst : Stage V μ dev W i) (h : LocalOk μ pins dev i)
    (hW : WorldOk V W) : CtxSrc V μ (dev i).context (fun n => W ((dev i).res n)) where
  E n := (srcOf hst n).1
  m n := (srcOf hst n).2
  R n := readOf dev i n
  R_sub n d ci hR := by
    by_cases hs : (dev i).src n < i
    · rw [readOf_pos hs] at hR
      rw [srcOf_pos hst hs]
      obtain ⟨h1, h2, -⟩ := find?_readsAlike dev hR
      exact ⟨h1, h2⟩
    · simp only [readOf, hs, ↓reduceIte] at hR
      exact nomatch hR
  agree n hn := by
    have hs := h.src_lt n hn
    rw [readOf_pos hs, srcOf_pos hst hs]
    exact readAgree_of hst h hs
  entry n ci hf := by
    have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcOf_pos hst hs]
    exact h.context_le n ci hf
  self n hn := by
    have hs := h.src_lt n hn
    rw [readOf_pos hs]
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ci', hf', -⟩ := h.context_le n ci hci
    exact readsAlike_of hf' hn (h.res_context n hn)
  scope n ci hf := by
    have hs := h.src_lt n (by rw [hf]; rfl)
    rw [readOf_pos hs]
    exact h.scoping n ci hf
  same n d hR hk := by
    by_cases hs : (dev i).src n < i
    · rw [readOf_pos hs] at hR
      rw [srcOf_pos hst hs] at hk ⊢
      obtain ⟨cc, ce, hc, he, hkd⟩ := ctx_entries hR
      obtain ⟨-, hind, hpin, -⟩ := ctx_same hst h hs hc he hkd
      rw [hc, he]
      rcases hk with ⟨⟨c1, hc1, hk1⟩, c2, hc2, hk2⟩ | hp
      · rw [hc] at hc1; obtain rfl := Option.some.inj hc1
        rw [he] at hc2; obtain rfl := Option.some.inj hc2
        rw [hind hk1 hk2]
      · rw [hpin hp]
    · simp only [readOf, hs, ↓reduceIte] at hR
      exact nomatch hR
  deep n c ci hR hfc hk hE := by
    by_cases hs : (dev i).src n < i
    · simp only [readOf_pos hs] at hR ⊢
      rw [srcOf_pos hst hs] at hE ⊢
      exact deep_of hst h hs hR hfc hk hE
    · simp only [readOf, hs, ↓reduceIte] at hR
      exact nomatch hR
  cover n := by
    by_cases hs : (dev i).src n < i
    · rw [srcOf_pos hst hs]; exact (hst.mod_spec _ hs).1
    · rw [srcOf_neg hst hs]; exact lfpCover_empty
  eta n := by
    by_cases hs : (dev i).src n < i
    · rw [srcOf_pos hst hs]; exact (hst.mod_spec _ hs).2.1
    · rw [srcOf_neg hst hs]; exact ConLeche.EtaFamiliesClosed.empty
  recFam n cv mI rP rules hf r hr cvj nP nF hfc T us hh := by
    have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcOf_pos hst hs] at hfc ⊢
    exact h.recFam n cv mI rP rules hf r hr cvj nP nF hfc T us hh
  tables T ci hf := by
    have hs := h.src_lt T (by rw [hf]; rfl)
    rw [srcOf_pos hst hs]
    exact h.tables T ci hf
  projs := h.projs
  blocks := h.blocks
  tables_mem := h.tables_mem
  nodup := h.nodup
  closed n ψ := hW.1 _ ψ
  wd n ψ ρ := hW.2.1 _ ψ ρ

end

end ConLeche.Model.Modular
