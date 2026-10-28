module

public import ConLeche.Model.Modular.Instance
public import ConLeche.Model.Modular.Step

public section

/-!
# The modular theorem: one model of every module's own environment

The proof of `ConLeche.modular_model_exists` (`ConLeche/MainTheorem.lean`):
the generic theorem (`Development.modular`, `ConLeche/Modular/Generic.lean`)
at con-leche's models (`conlecheSemantics`, `Instance.lean`), for the
development a list of modules stands for (`toDev`).  What is left here is
syntax, no model: that the local checks (`LocalOk`) make every module
valid (`valid_of`).

* **The qualified names fit** (`Fits`, `fits_all`, by induction over the
  modules): every constant a module's own environment stores refines
  the constant of the home module its qualified name names (or, for a
  proof, has the name's statement), and what an inductive kind's laws
  read resolves as at the home.
* **A context reads from the modules before it** (`ctx_reads`): its
  sources are their own environments, and what it reads alike agrees
  there (`ctx_same`, `readAgreeS_of`, `deep_of`, from the fit); the
  modules before it refine the world (`before_ref`: a checked one is in
  it, a compared one reads from the modules before it).
* **The declarations are accepted** from the context (`AcceptedFrom`, the
  context reading from the own environment, `ext_reads`), and what they
  add is fresh: an own ordinary name's qualified name is its module's,
  which no earlier module's constant has (`key_le`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Semantics ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

universe w

/-! ## Lookups -/

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

/-! ## The context reads from the earlier modules -/

variable {V : Type w} [SetTheory V] {μ : CheckMode} {pins : List NatOpPinSet}

section
variable {dev : Nat → Module} {i : Nat}

/-- **A context entry and a source entry of one qualified name**: one
constant value; equal where both are inductive kinds or the name is
pinned; one table where both are type formers. -/
theorem ctx_same (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) {b : Nat} (hb : b < i)
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
  obtain ⟨h1, h2, h3, h4⟩ := fits_same dev (hfits _ hs) (hfits b hb) hfs he hk'
  refine ⟨hr.cv.trans h1, fun hk1 hk2 => ?_, fun hp => ?_, fun hf1 hf2 => ?_⟩
  · have := hr.eq_of_indKind hk1; subst this; exact h2 hk1 hk2
  · rw [hr.eq_of_pinned hp]; exact h3 hp
  · have := hr.eq_of_indKind (isIndKind_of_isFormer hf1); subst this
    have ht := h.tables d cc hc
    rw [ht]
    cases cc with
    | indInfo _ _ => exact h4 hf1 hf2
    | _ => simp [ConstantInfo.isFormer] at hf1

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

/-- **A context and an earlier module agree on what it reads alike**,
leaves aside. -/
theorem readAgreeS_of (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) {b : Nat}
    (hb : b < i) : ReadAgreeS (readsAlike dev i b) (dev i).context (dev b).own := by
  have pinned_eq : ∀ d, ((readsAlike dev i b).find? d).isSome = true → d ∈ pinnedNames →
      (dev i).context.find? d = (dev b).own.find? d := by
    intro d hd hp
    obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hd
    rw [hc, he, (ctx_same hfits h hb hc he hk).2.2.1 hp]
  have hnat : (∀ n ∈ natLitNames, ((readsAlike dev i b).find? n).isSome = true ∧
      ((dev b).own.find? n).isSome = true) →
      natLitSupported (dev i).context = natLitSupported (dev b).own := by
    intro hn
    refine natLitSupported_congr fun d hd => pinned_eq d (hn d hd).1 ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> exact mem_pinned_of_reserved (by decide)
  refine ⟨fun d hR hE => ?_, fun T k hR hE hC hE' => ?_, hnat, fun hn => ?_⟩
  · obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hR
    exact ⟨cc, ce, hc, he, (ctx_same hfits h hb hc he hk).1⟩
  · obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hR
    obtain ⟨cv, caps, hC⟩ := hC
    obtain ⟨cv', caps', hE'⟩ := hE'
    rw [hc] at hC; obtain rfl := Option.some.inj hC
    rw [he] at hE'; obtain rfl := Option.some.inj hE'
    unfold Env.findProj?
    rw [(ctx_same hfits h hb hc he hk).2.2.2 rfl rfl]
  · refine strLitSupported_congr (hnat fun n hn' => hn n (by
        simp only [natLitNames, strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hn' ⊢
        rcases hn' with rfl | rfl | rfl <;> simp)) fun d hd => ?_
    have hd' := hn d (by
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    obtain ⟨cc, ce, hc, he, hk⟩ := ctx_entries hd'.1
    rw [hc, he]
    simp [(ctx_same hfits h hb hc he hk).1]

end

section
variable {dev : Nat → Module} {i : Nat}

/-- **What an inductive kind read alike reads is read alike**, where both
sides store it: both resolve it as the kind's home does. -/
theorem deep_of (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) {b : Nat} (hb : b < i)
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
  obtain ⟨-, hsame, -, htabb⟩ := ctx_same hfits h hb hfc hfe hkb
  obtain rfl := hsame hk hke
  have hks := h.res_context c hcs
  obtain ⟨-, -, -, htabs⟩ := ctx_same hfits h hs hfc hfs hks
  have hFs := hfits _ hs c ci hfs
  have hFb := hfits b hb c ci hfe
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

/-! ## Modules as pieces -/

section
variable (dev : Nat → Module)

/-- Module `j`'s own environment as a piece. -/
@[expose] def ownPiece (j : Nat) : Piece := ⟨(dev j).own, (dev j).res⟩

/-- Module `j`'s context as a piece. -/
@[expose] def ctxPiece (j : Nat) : Piece := ⟨(dev j).context, (dev j).res⟩

/-- The modules before `i`, as pieces. -/
@[expose] def before (i : Nat) : PEnv := (List.range i).map (ownPiece dev)

/-- The source piece of a context name. -/
@[expose] def srcP (i : Nat) (n : Name) : Piece :=
  if (dev i).src n < i then ownPiece dev ((dev i).src n) else Piece.empty

end

section
variable {dev : Nat → Module} {i : Nat}

theorem srcP_pos {n : Name} (hs : (dev i).src n < i) :
    srcP dev i n = ownPiece dev ((dev i).src n) := by
  simp only [srcP, hs, ↓reduceIte]

theorem srcP_neg {n : Name} (hs : ¬ (dev i).src n < i) : srcP dev i n = Piece.empty := by
  simp only [srcP, hs, ↓reduceIte]

/-- **A context reads from the modules before it** (`PieceReads`), by the
local checks and the qualified names' fit. -/
theorem ctx_reads (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) :
    PieceReads (ctxPiece dev i) (before dev i) := by
  refine ⟨srcP dev i, fun n => ?_, ?_⟩
  · try dsimp only [ctxPiece] at *
    by_cases hs : (dev i).src n < i
    · rw [srcP_pos hs]; exact Or.inl (List.mem_map.mpr ⟨_, List.mem_range.mpr hs, rfl⟩)
    · rw [srcP_neg hs]; exact Or.inr rfl
  show CtxRead (dev i).context (fun n => (srcP dev i n).env)
    (fun n => readsAlikeP ⟨(dev i).context, (dev i).res⟩ (srcP dev i n))
  refine ⟨fun n d ci hR => ?_, fun n hn => ?_, fun n ci hf => ?_, fun n hn => ?_,
    fun n ci hf => ?_, fun n d hR hk => ?_, fun n cv mI rP rules hf r hr cvj nP nF hfc T us hh => ?_,
    fun n c ci hR hfc hk hE => ?_, fun T ci hf => ?_, h.projs, h.blocks, h.tables_mem, h.nodup⟩
  · try dsimp only [ctxPiece] at *
    by_cases hs : (dev i).src n < i
    · rw [srcP_pos hs] at hR ⊢
      obtain ⟨h1, h2, -⟩ := find?_readsAlike dev hR
      exact ⟨h1, h2⟩
    · rw [srcP_neg hs] at hR; exact nomatch hR
  · try dsimp only [ctxPiece] at *
    have hs := h.src_lt n hn
    rw [srcP_pos hs]
    exact readAgreeS_of hfits h hs
  · try dsimp only [ctxPiece] at *
    have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcP_pos hs]
    exact h.context_le n ci hf
  · try dsimp only [ctxPiece] at *
    have hs := h.src_lt n hn
    rw [srcP_pos hs]
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ci', hf', -⟩ := h.context_le n ci hci
    exact readsAlike_of hf' hn (h.res_context n hn)
  · try dsimp only [ctxPiece] at *
    have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcP_pos hs]
    exact h.scoping n ci hf
  · try dsimp only [ctxPiece] at *
    by_cases hs : (dev i).src n < i
    · rw [srcP_pos hs] at hR hk ⊢
      obtain ⟨cc, ce, hc, he, hkd⟩ := ctx_entries hR
      obtain ⟨-, hind, hpin, -⟩ := ctx_same hfits h hs hc he hkd
      show (dev i).context.find? d = (dev ((dev i).src n)).own.find? d
      rw [hc, he]
      rcases hk with ⟨⟨c1, hc1, hk1⟩, c2, hc2, hk2⟩ | hp
      · rw [hc] at hc1; obtain rfl := Option.some.inj hc1
        change (dev ((dev i).src n)).own.find? d = some c2 at hc2
        rw [he] at hc2; obtain rfl := Option.some.inj hc2
        rw [hind hk1 hk2]
      · rw [hpin hp]
    · rw [srcP_neg hs] at hR; exact nomatch hR
  · try dsimp only [ctxPiece] at *
    have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcP_pos hs] at hfc ⊢
    exact h.recFam n cv mI rP rules hf r hr cvj nP nF hfc T us hh
  · try dsimp only [ctxPiece] at *
    by_cases hs : (dev i).src n < i
    · rw [srcP_pos hs] at hR hE ⊢
      exact deep_of hfits h hs hR hfc hk hE
    · rw [srcP_neg hs] at hR; exact nomatch hR
  · try dsimp only [ctxPiece] at *
    have hs := h.src_lt T (by rw [hf]; rfl)
    rw [srcP_pos hs]
    exact h.tables T ci hf

/-- What a context's own part reads: the own environment filtered to the
context is the context. -/
theorem readsAlikeP_ext_find? {C E' : Env} {r : Name → Key} (hext : Extends C E')
    (hnd : NodupNames E') (d : Name) : (readsAlikeP ⟨C, r⟩ ⟨E', r⟩).find? d = C.find? d := by
  have h' : (readsAlikeP ⟨C, r⟩ ⟨E', r⟩).find? d = List.find? (·.name == d)
      (E'.consts.filter fun c => (C.find? c.name).isSome && r c.name == r c.name) := rfl
  rw [h', find?_filter_name (p := fun x => (C.find? x).isSome && r x == r x)]
  cases hc : C.find? d with
  | none => simp
  | some ci =>
    simp only [Option.isSome_some, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    exact hext.find? hnd hc

/-- **A context reads from the own environment extending it.** -/
theorem ext_reads (h : LocalOk μ pins dev i) {E' : Env} (hext : Extends (dev i).context E')
    (hnd : NodupNames E') : PieceReads (ctxPiece dev i) [⟨E', (dev i).res⟩] := by
  have hRC : ∀ d, (readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? d =
      (dev i).context.find? d := readsAlikeP_ext_find? hext hnd
  have hCE : ∀ d, ((dev i).context.find? d).isSome = true →
      (dev i).context.find? d = E'.find? d := by
    intro d hd
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hd
    rw [hci, hext.find? hnd hci]
  have hRsome : ∀ d, ((readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? d).isSome = true →
      ((dev i).context.find? d).isSome = true := fun d hd => by rw [← hRC d]; exact hd
  refine ⟨fun _ => ⟨E', (dev i).res⟩, fun _ => Or.inl (List.mem_singleton_self _), ?_⟩
  show CtxRead (dev i).context (fun _ => E')
    (fun _ => readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩)
  have hnat : (∀ n ∈ natLitNames,
      ((readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? n).isSome = true ∧
        (E'.find? n).isSome = true) → natLitSupported (dev i).context = natLitSupported E' :=
    fun hn => natLitSupported_congr fun d hd => hCE d (hRsome d (hn d hd).1)
  refine ⟨fun n d ci hR => ?_, fun n hn => ⟨fun d hR hE => ?_, fun T k hR hE hC hE' => ?_,
      hnat, fun hn => ?_⟩, fun n ci hf => ⟨ci, hext.find? hnd hf, Refines.refl n ci⟩,
    fun n hn => by show ((readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? n).isSome = true; rw [hRC]; exact hn,
    fun n ci hf => ?_, fun n d hR _ => hCE d (hRsome d hR),
    fun n cv mI rP rules hf r hr cvj nP nF hfc T us hh => ?_,
    fun n c ci _ _ _ _ => EntryScopedP.of_forall (fun d hdC _ => by
      show ((readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? d).isSome = true; rw [hRC]; exact hdC) _ c ci,
    fun T ci hf => ?_, h.projs, h.blocks, h.tables_mem, h.nodup⟩
  · change (readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? d = some ci at hR
    rw [hRC] at hR
    exact ⟨hext.find? hnd hR, by rw [hR]; rfl⟩
  · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hRsome d hR)
    exact ⟨ci, ci, hci, hext.find? hnd hci, rfl⟩
  · unfold Env.findProj?
    rw [hext.findTable? hnd (hRsome T hR)]
  · refine strLitSupported_congr (hnat fun n hn' => hn n (by
        simp only [natLitNames, strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hn' ⊢
        rcases hn' with rfl | rfl | rfl <;> simp)) fun d hd => ?_
    have hd' := hn d (by
      simp only [strLitNames, List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    rw [hCE d (hRsome d hd'.1)]
  · refine entryScoped_iff.mpr ((entryScoped_iff.mp (h.scoping n ci hf)).mono fun d hd => ?_)
    show ((readsAlikeP ⟨(dev i).context, (dev i).res⟩ ⟨E', (dev i).res⟩).find? d).isSome = true
    rw [hRC]
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hd
    exact (find?_readsAlike dev hc).2.1
  · obtain ⟨-, hctor, -⟩ := (h.scoping n _ hf).2.2.1 cv mI rP rules rfl r hr
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hctor
    have hCc := (find?_readsAlike dev hc).2.1
    have hfc' : (dev i).context.find? r.ctor = some (.ctorInfo cvj nP nF) := by
      rw [hCE _ hCc]; exact hfc
    obtain ⟨cvT, capsT, hT⟩ := h.blocks r.ctor _ hfc' T us hh
    exact ⟨cvT, capsT, hext.find? hnd hT⟩
  · have h1 := h.tables T ci hf
    have hT : ((dev i).context.find? T).isSome = true := by rw [hf]; rfl
    cases ci with
    | indInfo cv caps => exact (hext.findTable? hnd hT).symm
    | _ => exact h1

end

/-! ## Qualified names fit, module by module -/

section
variable {dev : Nat → Module}

/-- **A stored name resolves to a home no later than its module.** -/
theorem key_le {j : Nat} (hj : Fits dev j) {n : Name} (hn : ((dev j).own.find? n).isSome = true)
    {P : Nat} {n' : Name} (hk : (dev j).res n = .qual P n') : P ≤ j := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  have := hj n ci hci
  rw [hk] at this
  exact this.2.1

end

section
variable {dev : Nat → Module} {i : Nat}

/-- **A context constant fits its qualified name** in the module's own
environment, read from the source module's fit. -/
theorem fits_context (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i)
    (hext : Extends (dev i).context (dev i).own) (hnd : NodupNames (dev i).own)
    {n : Name} {cc : ConstantInfo} (hcn : (dev i).context.find? n = some cc) :
    KeyFits dev i n cc ((dev i).res n) := by
  have hcs : ((dev i).context.find? n).isSome = true := by rw [hcn]; rfl
  have hs := h.src_lt n hcs
  obtain ⟨cs, hfs, hr⟩ := h.context_le n cc hcn
  have hF := hfits _ hs n cs hfs
  rw [← h.res_context n hcs] at hF
  have htabC : (dev i).own.findTable? n = (dev i).context.findTable? n :=
    hext.findTable? hnd hcs
  revert hF
  cases (dev i).res n with
  | qual P n' =>
    rintro ⟨hn', hP, cp, hcp, hr2, htab, hind⟩
    refine ⟨hn', Nat.le_trans hP (Nat.le_of_lt hs), cp, hcp, hr.trans hr2, fun hfm => ?_,
      fun hki => ?_⟩
    · obtain rfl := hr.eq_of_indKind (isIndKind_of_isFormer hfm)
      rw [htabC, h.tables n cc hcn, ← htab hfm]
      cases cc with
      | indInfo _ _ => rfl
      | _ => simp [ConstantInfo.isFormer] at hfm
    · obtain rfl := hr.eq_of_indKind hki
      have hsc := (entryScoped_iff.mp (h.scoping n cc hcn)).table' (C' := (dev i).own)
        fun cv caps he => htabC
      have hin := (hind hki).table' (C' := (dev i).own) fun cv caps he => by
        subst he; rw [htabC, h.tables n _ hcn]
      refine EntryScopedP.and3 (fun d h1 h2 _ _ => ?_) hsc hin
        (EntryScopedP.of_forall (p := fun _ => True) (fun _ => trivial) _ n _)
      obtain ⟨ce, hce⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨he, -, hk⟩ := find?_readsAlike dev hce
      exact hk.trans (h2 (by rw [he]; rfl))
  | proof n' lps T =>
    rintro ⟨hn', hl, ht, hki, hp⟩
    refine ⟨hn', by rw [hr.cv]; exact hl, by rw [hr.cv]; exact ht, ?_, hp⟩
    cases hcc : cc.isIndKind with
    | false => rfl
    | true => obtain rfl := hr.eq_of_indKind hcc; rw [hki] at hcc; exact nomatch hcc

/-- **A module's own environment, without a model**: it extends the
context with unique names, and a flagged own name is stored by no
inductive kind at a name that is not pinned. -/
theorem own_facts (h : LocalOk μ pins dev i) :
    Extends (dev i).context (dev i).own ∧ NodupNames (dev i).own ∧
      ∀ n, (dev i).proofs n = true → (dev i).context.find? n = none →
        ((dev i).own.find? n).isSome = true →
        ∃ ci, (dev i).own.find? n = some ci ∧ ci.isIndKind = false ∧ n ∉ pinnedNames := by
  cases hc : (dev i).compared with
  | false =>
    obtain ⟨hnd, hext, hfl⟩ := acceptedFrom_syn (h.accepted hc) h.nodup
    exact ⟨hext, hnd, hfl⟩
  | true =>
    rw [h.compared_own hc]
    exact ⟨Extends.refl _, h.nodup, fun n _ h1 h2 => by rw [h1] at h2; exact nomatch h2⟩

/-- **Module `i`'s qualified names fit**, from the earlier modules'. -/
theorem fits_of (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) : Fits dev i := by
  obtain ⟨hext, hnd', hfl⟩ := own_facts h
  intro n ci hf
  cases hcn : (dev i).context.find? n with
  | some cc =>
    have hcc := hext.find? hnd' hcn
    rw [hf] at hcc; obtain rfl := Option.some.inj hcc
    exact fits_context hfits h hext hnd' hcn
  | none =>
    rw [h.res_own n ci hf hcn]
    unfold Module.ownKey
    cases hp : (dev i).proofs n with
    | true =>
      obtain ⟨ci', hf', hki, hpn⟩ := hfl n hp hcn (by rw [hf]; rfl)
      rw [hf] at hf'; obtain rfl := Option.some.inj hf'
      exact ⟨rfl, rfl, rfl, hki, hpn⟩
    | false =>
      exact ⟨rfl, Nat.le_refl i, ci, hf, Refines.refl n ci, fun _ => rfl,
        fun _ => EntryScopedP.of_forall (fun _ _ => rfl) _ n ci⟩

/-- **Every module's qualified names fit.** -/
theorem fits_all : ∀ i, (∀ j < i, LocalOk μ pins dev j) → ∀ j < i, Fits dev j
  | 0, _ => fun _ h => absurd h (Nat.not_lt_zero _)
  | i + 1, hok => by
    have ih := fits_all i fun j hj => hok j (Nat.lt_succ_of_lt hj)
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih j hj
    · exact fits_of ih (hok j (Nat.lt_succ_self j))

end

/-! ## The development over con-leche's models -/

section
variable (V μ) in
/-- **A development of modules as a development over con-leche's
models**: a module's context and own environment as pieces, its
declarations with its proof flags, no renaming (the resolution is the
pieces'). -/
@[expose] noncomputable def toDev (hμ : μ.isVerified = true) (pins : List NatOpPinSet)
    (dev : Nat → Module) : Development (conlecheSemantics V μ hμ pins) where
  ctx j := [ctxPiece dev j]
  decls j := ((dev j).decls, (dev j).proofs)
  own j := [ownPiece dev j]
  ren _ := id
  compared j := (dev j).compared

variable {dev : Nat → Module} {hμ : μ.isVerified = true}

/-- The world before module `i`, as a list. -/
@[expose] noncomputable def worldL (V : Type w) [SetTheory V] (μ : CheckMode)
    (hμ : μ.isVerified = true) (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat) : PEnv :=
  (toDev V μ hμ pins dev).world i

theorem worldL_succ (i : Nat) : worldL V μ hμ pins dev (i + 1) =
    if (dev i).compared then worldL V μ hμ pins dev i
    else worldL V μ hμ pins dev i ++ [ownPiece dev i] := rfl

theorem mem_world : ∀ {i : Nat} {p : Piece}, p ∈ worldL V μ hμ pins dev i ↔
    ∃ j < i, (dev j).compared = false ∧ p = ownPiece dev j
  | 0, p => by
    show p ∈ ([] : PEnv) ↔ _
    exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | i + 1, p => by
    have ih := mem_world (i := i) (p := p)
    rw [worldL_succ]
    cases hc : (dev i).compared with
    | true =>
      simp only [↓reduceIte]
      rw [ih]
      constructor
      · rintro ⟨j, hj, h1, h2⟩; exact ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩
      · rintro ⟨j, hj, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact ⟨j, hj, h1, h2⟩
        · rw [hc] at h1; exact nomatch h1
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton]
      rw [ih]
      constructor
      · rintro (⟨j, hj, h1, h2⟩ | h)
        · exact ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩
        · exact ⟨i, Nat.lt_succ_self i, hc, h⟩
      · rintro ⟨j, hj, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact Or.inl ⟨j, hj, h1, h2⟩
        · exact Or.inr h2

theorem world_sub {i : Nat} : ∀ p ∈ worldL V μ hμ pins dev i,
    p ∈ worldL V μ hμ pins dev (i + 1) := by
  intro p hp
  obtain ⟨j, hj, h1, h2⟩ := mem_world.mp hp
  exact mem_world.mpr ⟨j, Nat.lt_succ_of_lt hj, h1, h2⟩

/-- **The modules before `i` refine the world before `i`**: a checked
module is in it, a compared one reads from the modules before it. -/
theorem before_ref : ∀ i, (∀ j < i, LocalOk μ pins dev j) →
    Ref (before dev i) id (worldL V μ hμ pins dev i)
  | 0, _ => Ref.sub fun _ h => nomatch h
  | i + 1, hok => by
    have ih := before_ref i fun j hj => hok j (Nat.lt_succ_of_lt hj)
    have hb : before dev (i + 1) = before dev i ++ [ownPiece dev i] := by
      simp only [before, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [hb]
    have hsub : Ref (worldL V μ hμ pins dev i) id (worldL V μ hμ pins dev (i + 1)) :=
      Ref.sub world_sub
    refine Ref.union (Ref.trans (ρ := id) (σ := id) ih hsub) ?_
    cases hc : (dev i).compared with
    | false =>
      exact Ref.sub fun p hp => by
        rw [List.mem_singleton.mp hp]
        exact mem_world.mpr ⟨i, Nat.lt_succ_self i, hc, rfl⟩
    | true =>
      have h := hok i (Nat.lt_succ_self i)
      have hr := ctx_reads (fits_all i fun j hj => hok j (Nat.lt_succ_of_lt hj)) h
      have hpc : ownPiece dev i = ctxPiece dev i := by
        simp only [ownPiece, ctxPiece, h.compared_own hc]
      have hr' : Ref [ownPiece dev i] id (before dev i) :=
        Ref.reads fun p hp => by rw [List.mem_singleton.mp hp, hpc]; exact hr
      exact Ref.trans (ρ := id) (σ := id) (Ref.trans (ρ := id) (σ := id) hr' ih) hsub

/-- **Every module that passes its local checks is valid.** -/
theorem valid_of {i : Nat} (hok : ∀ j ≤ i, LocalOk μ pins dev j) :
    (toDev V μ hμ pins dev).Valid i := by
  have hok' : ∀ j < i, LocalOk μ pins dev j := fun j hj => hok j (Nat.le_of_lt hj)
  have h := hok i (Nat.le_refl i)
  have hfits := fits_all i hok'
  have hfi : Fits dev i := fits_of hfits h
  have hbr := before_ref (V := V) (μ := μ) (hμ := hμ) (pins := pins) i hok'
  have hcr : Ref [ctxPiece dev i] id (before dev i) :=
    Ref.reads fun p hp => by rw [List.mem_singleton.mp hp]; exact ctx_reads hfits h
  unfold Development.Valid
  show if (dev i).compared then Ref [ownPiece dev i] id _ else
    Ref [ctxPiece dev i] id _ ∧ AcceptsP μ pins [ctxPiece dev i] ((dev i).decls, (dev i).proofs)
      [ownPiece dev i] ∧ FreshP _ id [ctxPiece dev i] [ownPiece dev i]
  cases hc : (dev i).compared with
  | true =>
    simp only [↓reduceIte]
    have hpc : ownPiece dev i = ctxPiece dev i := by
      simp only [ownPiece, ctxPiece, h.compared_own hc]
    rw [hpc]
    exact Ref.trans (ρ := id) (σ := id) hcr hbr
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hext, hnd', -⟩ := own_facts h
    have hinj : ∀ n n', ((dev i).own.find? n).isSome = true →
        ((dev i).own.find? n').isSome = true → (dev i).res n = (dev i).res n' → n = n' := by
      intro n n' hn hn' hk
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      obtain ⟨ci', hci'⟩ := Option.isSome_iff_exists.mp hn'
      have h1 := hfi n ci hci
      have h2 := hfi n' ci' hci'
      rw [hk] at h1
      revert h1 h2
      cases (dev i).res n' with
      | qual P m => rintro ⟨rfl, -⟩ ⟨h2, -⟩; exact h2
      | proof m lps T => rintro ⟨rfl, -⟩ ⟨h2, -⟩; exact h2
    refine ⟨Ref.trans (ρ := id) (σ := id) hcr hbr,
      ⟨(dev i).context, (dev i).own, (dev i).res, rfl, rfl, h.accepted hc, ext_reads h hext hnd',
        hinj, fun n hn hcn hpk => ?_⟩, fun k k' _ _ hk => hk, fun _ _ => rfl, ?_⟩
    · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      have := h.res_own n ci hci hcn
      unfold Module.ownKey at this
      cases hp : (dev i).proofs n with
      | true => exact hp
      | false =>
        simp only [hp, Bool.false_eq_true, ↓reduceIte] at this
        change ((dev i).res n).isProof = true at hpk
        rw [this] at hpk; exact nomatch hpk
    · rintro k ⟨p, hp, n, hn, rfl⟩ hnot ⟨q, hq, m, hm, hkm⟩
      obtain rfl := List.mem_singleton.mp hp
      change ((dev i).own.find? n).isSome = true at hn
      change q.res m = (dev i).res n at hkm
      have hcn : (dev i).context.find? n = none := by
        cases hcn : (dev i).context.find? n with
        | none => rfl
        | some _ => exact absurd ⟨ctxPiece dev i, List.mem_singleton_self _, n,
            by rw [show (ctxPiece dev i).env = (dev i).context from rfl, hcn]; rfl, rfl⟩ hnot
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      have hown := h.res_own n ci hci hcn
      unfold Module.ownKey at hown
      show ((dev i).res n).isProof = true
      cases hp : (dev i).proofs n with
      | true => simp only [hp, ↓reduceIte] at hown; rw [hown]; rfl
      | false =>
        simp only [hp, Bool.false_eq_true, ↓reduceIte] at hown
        obtain ⟨j, hj, -, rfl⟩ := mem_world.mp hq
        have := key_le (hfits j hj) hm (hkm.trans hown)
        exact absurd (Nat.lt_of_le_of_lt this hj) (Nat.lt_irrefl _)

end

/-- **The modular theorem, at the leaves**: one world under which every
module up to `i` has a model of its own environment, read through its
resolution — the generic theorem (`Development.modular`) at con-leche's
models. -/
theorem modular_envModels (hμ : μ.isVerified = true) (dev : Nat → Module) (i : Nat)
    (hok : ∀ j ≤ i, LocalOk μ pins dev j) :
    ∃ W, WorldOk V W ∧ ∀ j ≤ i, ∃ mp : EnvModelM V μ (dev j).own,
      ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = W ((dev j).res n) := by
  obtain ⟨⟨m⟩, hr⟩ := (toDev V μ hμ pins dev).modular (i + 1) fun j hj =>
    valid_of fun k hk => hok k (Nat.le_trans hk (Nat.lt_succ_iff.mp hj))
  refine ⟨m.1, m.2.2.1, fun j hj => ?_⟩
  have hrj : Ref [ownPiece dev j] id (worldL V μ hμ pins dev (i + 1)) :=
    hr j (Nat.lt_succ_iff.mpr hj)
  obtain ⟨mp, -, -, -, hl⟩ := (restrictP hrj m).2.2.2 (ownPiece dev j) (List.mem_singleton_self _)
  exact ⟨mp, fun n hn => (hl n hn).trans
    (normalize_pos ⟨ownPiece dev j, List.mem_singleton_self _, n, hn, rfl⟩)⟩

end ConLeche.Model.Modular
