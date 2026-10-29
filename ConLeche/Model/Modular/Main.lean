module

public import ConLeche.Model.Modular.Instance
public import ConLeche.Model.Modular.Step

public section

/-!
# The modular theorem: a compatible family of models, one per module

The proof of `ConLeche.modular_model_exists` (`ConLeche/MainTheorem.lean`):
the generic theorem (`Development.modular`, `ConLeche/Modular/Generic.lean`)
at con-leche's models (`conlecheSemantics`, `Instance.lean`), for the
development a list of modules stands for (`toDev`: a module's context,
declarations and own environment, as its sources each earlier module's
own environment exposing what the module reads alike of it
(`alikeIn`), its keys).  What is left here is syntax, no model: that
the local checks (`LocalOk`) make every module valid (`valid_of`).

* **The keys fit** (`Fits`, `fits_all`, by induction over the modules):
  every constant a module's own environment stores refines the constant
  of the home module its key names (or, for a proof, has the key's
  statement), and what an inductive kind's laws read has the keys the
  home gives it.
* **A context is assembled from the modules before it** (`ctx_reads`,
  `ctx_assembled`): every name is read from its source's own
  environment, and what it reads under the source's keys agrees there
  (`ctx_same`, `readAgreeS_of`, `deep_of`, from the fit).
* **One copy** (`ctx_oneCopy`): a source exposes only names the module
  reads alike, so every copy there is interchangeable with the module's.
* **The declarations are accepted** from the context (`AcceptedFrom`),
  and a new name is declared by its module or flagged a proof
  (`key_own`).
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
      (dev ii).key d' = (dev bb).key d' := by
  have h' : List.find? (·.name == d') ((dev bb).own.consts.filter fun c =>
      ((dev ii).context.find? c.name).isSome && (dev ii).key c.name == (dev bb).key c.name)
      = some ci := h
  rw [find?_filter_name (p := fun x =>
      ((dev ii).context.find? x).isSome && (dev ii).key x == (dev bb).key x)] at h'
  have h := h'
  clear h'
  split at h
  · rename_i hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨h, hp.1, hp.2⟩
  · exact nomatch h

end

/-! ## The keys fit -/

section
variable (dev : Nat → Module)

/-- **What a key says of a constant** module `j` stores under `n`: an
ordinary constant's key is its home module, no later than `j`, whose own
constant this one refines — with the home's table, if it is a type
former, and, if it is an inductive kind, with what its laws read keyed
as at the home; a proof's key is its level parameters and statement,
and a proof is never an inductive kind or a pinned name. -/
@[expose] def KeyFits (j : Nat) (n : Name) (ci : ConstantInfo) : Key Stmt → Prop
  | .home P => P ≤ j ∧ ∃ cp, (dev P).own.find? n = some cp ∧ Refines n ci cp ∧
      (ci.isFormer = true → (dev j).own.findTable? n = (dev P).own.findTable? n) ∧
      (ci.isIndKind = true → EntryScopedP (fun d => ((dev j).own.find? d).isSome = true →
        (dev j).key d = (dev P).key d) (dev j).own n ci)
  | .proof s => ci.toConstantVal.levelParams = s.1 ∧
      ci.toConstantVal.type = s.2 ∧ ci.isIndKind = false ∧ n ∉ pinnedNames

/-- **Every constant of a module's own environment fits its key.** -/
@[expose] def Fits (j : Nat) : Prop :=
  ∀ n ci, (dev j).own.find? n = some ci → KeyFits dev j n ci ((dev j).key n)

theorem isIndKind_of_isFormer {ci : ConstantInfo} (h : ci.isFormer = true) :
    ci.isIndKind = true := by
  cases ci <;> simp_all [ConstantInfo.isFormer, ConstantInfo.isIndKind]

theorem constantVal_eq {a b : ConstantVal} (h1 : a.name = b.name)
    (h2 : a.levelParams = b.levelParams) (h3 : a.type = b.type) : a = b := by
  cases a; cases b; simp_all

/-- **Two constants of one name and key** (in two modules' own
environments): one constant value; equal where both are inductive kinds
or the name is pinned; one table where both are type formers. -/
theorem fits_same {j j' : Nat} {n : Name} {ci ci' : ConstantInfo}
    (hj : Fits dev j) (hj' : Fits dev j') (hf : (dev j).own.find? n = some ci)
    (hf' : (dev j').own.find? n = some ci') (hk : (dev j).key n = (dev j').key n) :
    ci.toConstantVal = ci'.toConstantVal ∧
      (ci.isIndKind = true → ci'.isIndKind = true → ci = ci') ∧
      (n ∈ pinnedNames → ci = ci') ∧
      (ci.isFormer = true → ci'.isFormer = true →
        (dev j).own.findTable? n = (dev j').own.findTable? n) := by
  have h1 := hj n ci hf
  have h2 := hj' n ci' hf'
  rw [← hk] at h2
  revert h1 h2
  cases (dev j).key n with
  | home P =>
    rintro ⟨-, cp, hcp, hr, htab, -⟩ ⟨-, cp', hcp', hr', htab', -⟩
    rw [hcp] at hcp'; obtain rfl := Option.some.inj hcp'
    refine ⟨hr.cv.trans hr'.cv.symm, fun hk1 hk2 => ?_, fun hp => ?_, fun hf1 hf2 => ?_⟩
    · rw [hr.eq_of_indKind hk1, hr'.eq_of_indKind hk2]
    · rw [hr.eq_of_pinned hp, hr'.eq_of_pinned hp]
    · rw [htab hf1, htab' hf2]
  | proof s =>
    rintro ⟨hl, ht, hki, hp⟩ ⟨hl', ht', hki', -⟩
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

/-- **A context entry and a source entry of one name and key**: one
constant value; equal where both are inductive kinds or the name is
pinned; one table where both are type formers. -/
theorem ctx_same (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) {b : Nat} (hb : b < i)
    {d : Name} {cc ce : ConstantInfo} (hc : (dev i).context.find? d = some cc)
    (he : (dev b).own.find? d = some ce) (hk : (dev i).key d = (dev b).key d) :
    cc.toConstantVal = ce.toConstantVal ∧
      (cc.isIndKind = true → ce.isIndKind = true → cc = ce) ∧
      (d ∈ pinnedNames → cc = ce) ∧
      (cc.isFormer = true → ce.isFormer = true →
        (dev i).context.findTable? d = (dev b).own.findTable? d) := by
  have hcs : ((dev i).context.find? d).isSome = true := by rw [hc]; rfl
  have hs := h.src_lt d hcs
  obtain ⟨cs, hfs, hr⟩ := h.context_le d cc hc
  have hk' : (dev ((dev i).src d)).key d = (dev b).key d := (h.key_context d hcs).symm.trans hk
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

/-- A name the context stores under module `b`'s key, stored by
`b`, is read alike. -/
theorem readsAlike_of {b : Nat} {d : Name} {ci : ConstantInfo}
    (he : (dev b).own.find? d = some ci) (hc : ((dev i).context.find? d).isSome = true)
    (hk : (dev i).key d = (dev b).key d) : ((readsAlike dev i b).find? d).isSome = true := by
  have : List.find? (·.name == d) ((dev b).own.consts.filter fun c =>
      ((dev i).context.find? c.name).isSome && (dev i).key c.name == (dev b).key c.name)
      = some ci := by
    rw [find?_filter_name (p := fun x =>
      ((dev i).context.find? x).isSome && (dev i).key x == (dev b).key x)]
    simp only [hc, hk, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    exact he
  show (List.find? (·.name == d) ((dev b).own.consts.filter fun c =>
      ((dev i).context.find? c.name).isSome && (dev i).key c.name == (dev b).key c.name)).isSome
    = true
  rw [this]; rfl

/-- The entries on both sides of a name read alike. -/
theorem ctx_entries {b : Nat} {d : Name} (hR : ((readsAlike dev i b).find? d).isSome = true) :
    ∃ cc ce, (dev i).context.find? d = some cc ∧ (dev b).own.find? d = some ce ∧
      (dev i).key d = (dev b).key d := by
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
sides store it: both key it as the kind's home does. -/
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
  have hks := h.key_context c hcs
  obtain ⟨-, -, -, htabs⟩ := ctx_same hfits h hs hfc hfs hks
  have hFs := hfits _ hs c ci hfs
  have hFb := hfits b hb c ci hfe
  rw [← hks] at hFs
  rw [← hkb] at hFb
  revert hFs hFb
  cases hkey : (dev i).key c with
  | proof s =>
    rintro ⟨-, -, hki, -⟩; rw [hk] at hki; exact nomatch hki
  | home P =>
    rintro ⟨-, -, -, -, -, hGs⟩ ⟨-, -, -, -, -, hGb⟩
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
variable {dev : Nat → Module} {i : Nat}

/-- **A context constant fits its key** in the module's own
environment, read from the source module's fit. -/
theorem fits_context (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i)
    (hext : Extends (dev i).context (dev i).own) (hnd : NodupNames (dev i).own)
    {n : Name} {cc : ConstantInfo} (hcn : (dev i).context.find? n = some cc) :
    KeyFits dev i n cc ((dev i).key n) := by
  have hcs : ((dev i).context.find? n).isSome = true := by rw [hcn]; rfl
  have hs := h.src_lt n hcs
  obtain ⟨cs, hfs, hr⟩ := h.context_le n cc hcn
  have hF := hfits _ hs n cs hfs
  rw [← h.key_context n hcs] at hF
  have htabC : (dev i).own.findTable? n = (dev i).context.findTable? n :=
    hext.findTable? hnd hcs
  revert hF
  cases (dev i).key n with
  | home P =>
    rintro ⟨hP, cp, hcp, hr2, htab, hind⟩
    refine ⟨Nat.le_trans hP (Nat.le_of_lt hs), cp, hcp, hr.trans hr2, fun hfm => ?_,
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
  | proof s =>
    rintro ⟨hl, ht, hki, hp⟩
    refine ⟨by rw [hr.cv]; exact hl, by rw [hr.cv]; exact ht, ?_, hp⟩
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

/-- **Module `i`'s keys fit**, from the earlier modules'. -/
theorem fits_of (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) : Fits dev i := by
  obtain ⟨hext, hnd', hfl⟩ := own_facts h
  intro n ci hf
  cases hcn : (dev i).context.find? n with
  | some cc =>
    have hcc := hext.find? hnd' hcn
    rw [hf] at hcc; obtain rfl := Option.some.inj hcc
    exact fits_context hfits h hext hnd' hcn
  | none =>
    rw [h.key_own n ci hf hcn]
    unfold Module.ownKey
    cases hp : (dev i).proofs n with
    | true =>
      obtain ⟨ci', hf', hki, hpn⟩ := hfl n hp hcn (by rw [hf]; rfl)
      rw [hf] at hf'; obtain rfl := Option.some.inj hf'
      exact ⟨rfl, rfl, hki, hpn⟩
    | false =>
      exact ⟨Nat.le_refl i, ci, hf, Refines.refl n ci, fun _ => rfl,
        fun _ => EntryScopedP.of_forall (fun _ _ => rfl) _ n ci⟩

/-- **Every module's keys fit.** -/
theorem fits_all : ∀ i, (∀ j < i, LocalOk μ pins dev j) → ∀ j < i, Fits dev j
  | 0, _ => fun _ h => absurd h (Nat.not_lt_zero _)
  | i + 1, hok => by
    have ih := fits_all i fun j hj => hok j (Nat.lt_succ_of_lt hj)
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact ih j hj
    · exact fits_of ih (hok j (Nat.lt_succ_self j))

end
/-! ## The context, assembled from the modules before it -/

section
variable (dev : Nat → Module)

/-- The own environment of the module a context name of module `i` is
read from, if it is earlier (the empty one otherwise). -/
@[expose] def srcE (i : Nat) (n : Name) : Env :=
  if (dev i).src n < i then (dev ((dev i).src n)).own else Env.empty

/-- What module `i`'s context reads of it under its keys. -/
@[expose] def srcR (i : Nat) (n : Name) : Env :=
  if (dev i).src n < i then readsAlike dev i ((dev i).src n) else Env.empty

end

section
variable {dev : Nat → Module} {i : Nat}

theorem srcE_pos {n : Name} (hs : (dev i).src n < i) :
    srcE dev i n = (dev ((dev i).src n)).own := by
  simp only [srcE, hs, ↓reduceIte]

theorem srcR_pos {n : Name} (hs : (dev i).src n < i) :
    srcR dev i n = readsAlike dev i ((dev i).src n) := by
  simp only [srcR, hs, ↓reduceIte]

theorem srcR_neg {n : Name} (hs : ¬ (dev i).src n < i) : srcR dev i n = Env.empty := by
  simp only [srcR, hs, ↓reduceIte]

/-- **A context reads from the modules before it** (`CtxRead`), by the
local checks and the keys' fit. -/
theorem ctx_reads (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) :
    CtxRead (dev i).context (srcE dev i) (srcR dev i) := by
  refine ⟨fun n d ci hR => ?_, fun n hn => ?_, fun n ci hf => ?_, fun n hn => ?_,
    fun n ci hf => ?_, fun n d hR hk => ?_, fun n cv mI rP rules hf r hr cvj nP nF hfc T us hh => ?_,
    fun n c ci hR hfc hk hE => ?_, fun T ci hf => ?_, h.projs, h.blocks, h.tables_mem, h.nodup⟩
  · by_cases hs : (dev i).src n < i
    · rw [srcR_pos hs] at hR
      rw [srcE_pos hs]
      obtain ⟨h1, h2, -⟩ := find?_readsAlike dev hR
      exact ⟨h1, h2⟩
    · rw [srcR_neg hs] at hR; exact nomatch hR
  · have hs := h.src_lt n hn
    rw [srcR_pos hs, srcE_pos hs]
    exact readAgreeS_of hfits h hs
  · have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcE_pos hs]
    exact h.context_le n ci hf
  · have hs := h.src_lt n hn
    rw [srcR_pos hs]
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ci', hf', -⟩ := h.context_le n ci hci
    exact readsAlike_of hf' hn (h.key_context n hn)
  · have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcR_pos hs]
    exact h.scoping n ci hf
  · by_cases hs : (dev i).src n < i
    · rw [srcR_pos hs] at hR
      rw [srcE_pos hs] at hk ⊢
      obtain ⟨cc, ce, hc, he, hkd⟩ := ctx_entries hR
      obtain ⟨-, hind, hpin, -⟩ := ctx_same hfits h hs hc he hkd
      rw [hc, he]
      rcases hk with ⟨⟨c1, hc1, hk1⟩, c2, hc2, hk2⟩ | hp
      · rw [hc] at hc1; obtain rfl := Option.some.inj hc1
        rw [he] at hc2; obtain rfl := Option.some.inj hc2
        rw [hind hk1 hk2]
      · rw [hpin hp]
    · rw [srcR_neg hs] at hR; exact nomatch hR
  · have hs := h.src_lt n (by rw [hf]; rfl)
    rw [srcE_pos hs] at hfc ⊢
    exact h.recFam n cv mI rP rules hf r hr cvj nP nF hfc T us hh
  · by_cases hs : (dev i).src n < i
    · rw [srcR_pos hs] at hR
      rw [srcE_pos hs] at hE
      rw [srcE_pos hs, srcR_pos hs]
      exact deep_of hfits h hs hR hfc hk hE
    · rw [srcR_neg hs] at hR; exact nomatch hR
  · have hs := h.src_lt T (by rw [hf]; rfl)
    rw [srcE_pos hs]
    exact h.tables T ci hf

end

/-! ## The development over con-leche's models -/

section
variable (dev : Nat → Module)

/-- **What module `i` reads alike of module `b`** (`readsAlike`): the
names it exposes in the view `i` reads of `b`. -/
@[expose] def alikeIn (i b : Nat) (d : Name) : Prop := ((readsAlike dev i b).find? d).isSome = true

end

section
variable (V μ) in
/-- **A development of modules as a development over con-leche's
models**: a module's context, declarations (flagged: its proofs new in
its context), own environment (both exposing every name), as its
sources each earlier module's own environment exposing what the module
reads alike of it, and its keys. -/
@[expose] noncomputable def toDev (hμ : μ.isVerified = true) (pins : List NatOpPinSet)
    (dev : Nat → Module) : Development (conlecheSemantics V μ hμ pins) Stmt where
  ctx j := ((dev j).context, fun _ => True)
  decls j := ((dev j).decls, fun n => (dev j).proofs n && ((dev j).context.find? n).isNone)
  own j := ((dev j).own, fun _ => True)
  sources j := (List.range j).map fun b => (b, ((dev b).own, alikeIn dev j b))
  key j := (dev j).key

variable {dev : Nat → Module} {hμ : μ.isVerified = true}

theorem mem_srcList {i : Nat} {x : Nat × (Env × (Name → Prop))} :
    x ∈ (List.range i).map (fun b => (b, ((dev b).own, alikeIn dev i b))) ↔
      x.1 < i ∧ x.2 = ((dev x.1).own, alikeIn dev i x.1) := by
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨List.mem_range.mp hb, rfl⟩
  · obtain ⟨b, E⟩ := x
    rintro ⟨hb, h⟩
    exact ⟨b, List.mem_range.mpr hb, by simp only at h; rw [h]⟩

theorem mem_toDev_sources {i : Nat} {x : Nat × (conlecheSemantics V μ hμ pins).Env} :
    x ∈ (toDev V μ hμ pins dev).sources i ↔
      x.1 < i ∧ x.2 = ((dev x.1).own, alikeIn dev i x.1) :=
  mem_srcList (dev := dev)

/-- The source a context name of module `i` is read from: its source
module's own environment, exposing what `i` reads alike of it. -/
@[expose] noncomputable def srcAt (i : Nat) (n : Name) (hs : (dev i).src n < i) :
    (toDev V μ hμ pins dev).Src i :=
  ⟨((dev i).src n, ((dev ((dev i).src n)).own, alikeIn dev i ((dev i).src n))),
    List.mem_map.mpr ⟨_, List.mem_range.mpr hs, rfl⟩⟩

/-- The source a context name of module `i` is read from, if its source
module is earlier. -/
@[expose] noncomputable def srcOpt (i : Nat) (n : Name) : Option ((toDev V μ hμ pins dev).Src i) :=
  if hs : (dev i).src n < i then some (srcAt i n hs) else none

theorem srcEnv_srcOpt (i : Nat) :
    srcEnv (fun x : (toDev V μ hμ pins dev).Src i => x.1.2.1) (srcOpt (V := V) (μ := μ) (hμ := hμ) (pins := pins) (dev := dev) i) =
      srcE dev i := by
  funext n
  by_cases hs : (dev i).src n < i
  · simp only [srcEnv, srcOpt, srcE, hs, ↓reduceDIte, ↓reduceIte, srcAt]
  · simp only [srcEnv, srcOpt, srcE, hs, ↓reduceDIte, ↓reduceIte]

/-- **A context is assembled from the sources.** -/
theorem ctx_assembled {i : Nat} (hfits : ∀ j < i, Fits dev j) (h : LocalOk μ pins dev i) :
    (toDev V μ hμ pins dev).Assembled i ((dev i).context, fun _ => True) := by
  refine AssembledC.reads (srcOpt (V := V) (μ := μ) (hμ := hμ) (pins := pins) (dev := dev) i) (srcR dev i) (fun n hn => ?_)
    (fun n d ci hR => ?_) ?_
  · have hs := h.src_lt n hn
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨ci', hf', -⟩ := h.context_le n ci hci
    exact ⟨trivial, srcAt i n hs, dite_eq_left hs, readsAlike_of hf' hn (h.key_context n hn)⟩
  · by_cases hs : (dev i).src n < i
    · rw [srcR_pos hs] at hR
      exact ⟨srcAt i n hs, dite_eq_left hs, by
        show ((readsAlike dev i ((dev i).src n)).find? d).isSome = true
        rw [hR]; rfl⟩
    · rw [srcR_neg hs] at hR; exact nomatch hR
  · rw [srcEnv_srcOpt]; exact ctx_reads hfits h

/-- **One copy**: a copy of a context name in a source, which `i` reads
alike, is interchangeable with `i`'s. -/
theorem ctx_oneCopy {i : Nat} (E : Env × (Name → Prop)) :
    (toDev V μ hμ pins dev).OneCopy i E := by
  intro n _ x hx hs
  rw [mem_toDev_sources] at hx
  obtain ⟨-, hx⟩ := hx
  have hs : ((readsAlike dev i x.1).find? n).isSome = true := by
    have := hs.2; rw [hx] at this; exact this
  obtain ⟨ce, hce⟩ := Option.isSome_iff_exists.mp hs
  exact Development.interchangeable_iff.mpr (find?_readsAlike dev hce).2.2

/-- **Every module that passes its local checks is valid.** -/
theorem valid_of {i : Nat} (hok : ∀ j ≤ i, LocalOk μ pins dev j) :
    (toDev V μ hμ pins dev).Valid i := by
  have h := hok i (Nat.le_refl i)
  have hfits := fits_all i fun j hj => hok j (Nat.le_of_lt hj)
  have hA := ctx_assembled (V := V) (hμ := hμ) hfits h
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨hb, hx⟩ := mem_toDev_sources.mp hx
    refine ⟨hb, ?_⟩
    rw [hx]
    exact AssembledC.self PUnit.unit rfl fun _ _ _ => trivial
  · cases hc : (dev i).compared with
    | true =>
      refine .inr ⟨?_, ctx_oneCopy _⟩
      show (toDev V μ hμ pins dev).Assembled i ((dev i).own, fun _ => True)
      rw [h.compared_own hc]; exact hA
    | false =>
      refine .inl ⟨hA, ctx_oneCopy _, ⟨(dev i).proofs, h.accepted hc, fun n hn => ?_⟩,
        fun n hn hC => ?_⟩
      · change ((dev i).proofs n && ((dev i).context.find? n).isNone) = true at hn
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
        exact hn
      · change ((dev i).own.find? n).isSome = true ∧ True at hn
        change ¬ (((dev i).context.find? n).isSome = true ∧ True) at hC
        have hcn : (dev i).context.find? n = none := by
          cases e : (dev i).context.find? n with
          | none => rfl
          | some _ => exact absurd ⟨by rw [e]; rfl, trivial⟩ hC
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn.1
        have hk := h.key_own n ci hci hcn
        unfold Module.ownKey at hk
        cases hp : (dev i).proofs n with
        | true =>
          simp only [hp, ↓reduceIte] at hk
          refine .inr ⟨⟨_, hk⟩, ?_⟩
          show ((dev i).proofs n && ((dev i).context.find? n).isNone) = true
          rw [hp, hcn]; rfl
        | false =>
          simp only [hp, Bool.false_eq_true, ↓reduceIte] at hk
          exact .inl hk

end

/-- **The modular theorem, at the leaves**: a compatible family of leaf
assignments, one per module up to `i`, each with a model of the module's
own environment reading it — the generic theorem
(`Development.modular`) at con-leche's models. -/
theorem modular_envModels (hμ : μ.isVerified = true) (dev : Nat → Module) (i : Nat)
    (hok : ∀ j ≤ i, LocalOk μ pins dev j) :
    ∃ a : Nat → Name → (Name → Nat) → Term,
      (∀ j ≤ i, ∃ mp : EnvModelM V μ (dev j).own,
        ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = a j n) ∧
      (∀ j ≤ i, ∀ j' ≤ i, ∀ n, ((dev j).own.find? n).isSome = true →
        ((dev j').own.find? n).isSome = true → (dev j).key n = (dev j').key n →
        a j n = a j' n) ∧
      ∀ j ≤ i, ∀ n s, ((dev j).own.find? n).isSome = true → (dev j).key n = .proof s →
        a j n = fun _ => .prf := by
  obtain ⟨m, hc, hp⟩ := (toDev V μ hμ pins dev).modular (i + 1) fun j hj =>
    valid_of fun k hk => hok k (Nat.le_trans hk (Nat.lt_succ_iff.mp hj))
  refine ⟨fun j => if hj : j < i + 1 then (m j hj).1 else fun _ => dfltLeaf,
    fun j hj => ?_, fun j hj j' hj' n hn hn' hk => ?_, fun j hj n s hn hk => ?_⟩
  · obtain ⟨mp, -, -, -, hl⟩ := (m j (Nat.lt_succ_of_le hj)).2.2
    exact ⟨mp, fun n hn => by dsimp only; rw [hl n hn, dite_eq_left (Nat.lt_succ_of_le hj)]⟩
  · dsimp only
    rw [dite_eq_left (Nat.lt_succ_of_le hj), dite_eq_left (Nat.lt_succ_of_le hj')]
    exact hc j j' _ _ n ⟨hn, trivial⟩ ⟨hn', trivial⟩ (Development.interchangeable_iff.mpr hk)
  · dsimp only
    rw [dite_eq_left (Nat.lt_succ_of_le hj)]
    exact hp j _ n s ⟨hn, trivial⟩ hk

end ConLeche.Model.Modular
