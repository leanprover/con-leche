module

public import ConLeche.Verify.Inductives.NestedLedger
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.EnvWF
import ConLeche.Verify.InferLemmas

public section

/-!
# The pins' LEAVES are the first former's openers (task #279 M-B′, DESIGN §M.28)

`DeclNestedRun`'s pins are the elimination's own terms, opened at the
block's parameter variables — the first former's openers `params`
(`elimNested_open`).  The model reads a pin's inference at that opened
frame, and for that every free-variable leaf of the pin — hereditarily,
through the leaves' own annotations — must be one of the openers WITH
its annotation (`pinsClosed`, K.3, bounds only the indices).  K.12
asserts it "by construction"; this file proves it from the definitions,
as one loop invariant beside the ledger's:

* `Expr.LeavesIn params e` — every leaf of `e` is an opener;
* `LeafInv params st` — every pin and every constructor type of the
  growing list satisfies it;
* the invariant holds at the start (the block's own constructors are
  annotated, hence closed), survives every mint (a copy's constructors
  are the container's CLOSED stored types instantiated at pins that
  satisfy it, closed again over the first former's fvar-free binders),
  and survives the worklist's rewrite (the walk's outputs replace a
  sub-term by the copy applied to `params` and the occurrence's own
  index arguments).

The containers' stored types are closed under `EnvWF`
(`ContainersClosed`, `containersClosed_of_wf`); the walk's inputs are
opened by `instPis` at the openers, which are a leaf-closed set
(`openPisAtFvars_leavesIn`, off `openPisAtFvars_leaves`).
-/

namespace ConLeche

/-! ## `LeavesIn` -/

/-- Every free-variable leaf of `e` (hereditarily) is one of the openers
`params`, annotation included. -/
@[expose] def Expr.LeavesIn (params : List Expr) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ params

namespace Expr

variable {params : List Expr}

theorem LeavesIn.of_not_hasFvar {e : Expr} (h : e.hasFvar = false) : LeavesIn params e := by
  intro l hl
  rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  exact nomatch hl

theorem leavesIn_app {f a : Expr} :
    LeavesIn params (.app f a) ↔ LeavesIn params f ∧ LeavesIn params a := by
  simp only [LeavesIn, fvarLeaves, List.mem_append]
  constructor
  · intro h; exact ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (hl | hl)
    · exact h1 l hl
    · exact h2 l hl

theorem leavesIn_lam {ty b : Expr} {m : BinderMeta} :
    LeavesIn params (.lam ty b m) ↔ LeavesIn params ty ∧ LeavesIn params b := by
  simp only [LeavesIn, fvarLeaves, List.mem_append]
  constructor
  · intro h; exact ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (hl | hl)
    · exact h1 l hl
    · exact h2 l hl

theorem leavesIn_forallE {ty b : Expr} {m : BinderMeta} :
    LeavesIn params (.forallE ty b m) ↔ LeavesIn params ty ∧ LeavesIn params b := by
  simp only [LeavesIn, fvarLeaves, List.mem_append]
  constructor
  · intro h; exact ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (hl | hl)
    · exact h1 l hl
    · exact h2 l hl

theorem leavesIn_letE {t v b : Expr} :
    LeavesIn params (.letE t v b) ↔
      LeavesIn params t ∧ LeavesIn params v ∧ LeavesIn params b := by
  simp only [LeavesIn, fvarLeaves, List.mem_append]
  constructor
  · intro h
    exact ⟨fun l hl => h l (Or.inl (Or.inl hl)), fun l hl => h l (Or.inl (Or.inr hl)),
      fun l hl => h l (Or.inr hl)⟩
  · rintro ⟨h1, h2, h3⟩ l ((hl | hl) | hl)
    · exact h1 l hl
    · exact h2 l hl
    · exact h3 l hl

theorem leavesIn_proj {s : Name} {i : Nat} {e : Expr} :
    LeavesIn params (.proj s i e) ↔ LeavesIn params e := by
  simp only [LeavesIn, fvarLeaves]

theorem leavesIn_fvar {i : Nat} {ty : Expr} :
    LeavesIn params (.fvar i ty) ↔ Expr.fvar i ty ∈ params ∧ LeavesIn params ty := by
  simp only [LeavesIn, fvarLeaves, List.mem_cons]
  constructor
  · intro h
    exact ⟨h (i, ty) (Or.inl rfl), fun l hl => h l (Or.inr hl)⟩
  · rintro ⟨h1, h2⟩ l (rfl | hl)
    · exact h1
    · exact h2 l hl

theorem leavesIn_const {n : Name} {us : List Level} : LeavesIn params (.const n us) := by
  intro l hl; simp [fvarLeaves] at hl

theorem leavesIn_bvar {i : Nat} : LeavesIn params (.bvar i) := by
  intro l hl; simp [fvarLeaves] at hl

theorem leavesIn_sort {u : Level} : LeavesIn params (.sort u) := by
  intro l hl; simp [fvarLeaves] at hl

theorem leavesIn_lit {l : Literal} : LeavesIn params (.lit l) := by
  intro l hl; simp [fvarLeaves] at hl

theorem LeavesIn.mkAppN {f : Expr} {args : List Expr} (hf : LeavesIn params f)
    (hargs : ∀ a ∈ args, LeavesIn params a) : LeavesIn params (mkAppN f args) := by
  intro l hl
  rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, hlx⟩
  · exact hf l h
  · exact hargs x hx l hlx

theorem LeavesIn.getAppArgs {e x : Expr} (he : LeavesIn params e) (hx : x ∈ e.getAppArgs) :
    LeavesIn params x :=
  fun l hl => he l (fvarLeaves_getAppArgs hx l hl)

theorem LeavesIn.instantiate1 {e a : Expr} (he : LeavesIn params e) (ha : LeavesIn params a)
    (k : Nat) : LeavesIn params (e.instantiate1 a k) := by
  intro l hl
  rcases fvarLeaves_instantiate1 e k hl with h | h
  · exact he l h
  · exact ha l h

theorem LeavesIn.instPis :
    ∀ {ty : Expr} {args : List Expr} {r : Expr}, Expr.instPis ty args = some r →
      LeavesIn params ty → (∀ a ∈ args, LeavesIn params a) → LeavesIn params r
  | ty, [], r, h, hty, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    exact hty
  | .forallE dom body m, a :: as, r, h, hty, hargs => by
    simp only [Expr.instPis] at h
    exact LeavesIn.instPis h ((leavesIn_forallE.mp hty).2.instantiate1 (hargs a List.mem_cons_self) 0)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
  | .bvar _, _ :: _, _, h, _, _ | .fvar _ _, _ :: _, _, h, _, _ | .sort _, _ :: _, _, h, _, _
  | .const _ _, _ :: _, _, h, _, _ | .app _ _, _ :: _, _, h, _, _
  | .lam _ _ _, _ :: _, _, h, _, _ | .letE _ _ _, _ :: _, _, h, _, _
  | .lit _, _ :: _, _, h, _, _ | .proj _ _ _, _ :: _, _, h, _, _ => by
    simp [Expr.instPis] at h

/-- Abstraction removes leaves and adds none. -/
theorem fvarLeaves_abstract1_sub :
    ∀ (e : Expr) (d k : Nat), ∀ l ∈ (e.abstract1 d k).fvarLeaves, l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | bvar i => intro d k l hl; simpa [abstract1] using hl
  | fvar idx ty _ =>
    intro d k l hl
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · exact hl
  | sort u => intro d k l hl; simpa [abstract1] using hl
  | const n us => intro d k l hl; simpa [abstract1] using hl
  | lit ll => intro d k l hl; simpa [abstract1] using hl
  | app f a ihf iha =>
    intro d k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihf d k l hl)
    · exact Or.inr (iha d k l hl)
  | lam ty b m ihty ihb =>
    intro d k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty d k l hl)
    · exact Or.inr (ihb d (k + 1) l hl)
  | forallE ty b m ihty ihb =>
    intro d k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · exact Or.inl (ihty d k l hl)
    · exact Or.inr (ihb d (k + 1) l hl)
  | letE t v b iht ihv ihb =>
    intro d k l hl
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · exact Or.inl (Or.inl (iht d k l hl))
    · exact Or.inl (Or.inr (ihv d k l hl))
    · exact Or.inr (ihb d (k + 1) l hl)
  | proj s i x ih =>
    intro d k l hl
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih d k l hl

theorem LeavesIn.abstract1 {e : Expr} (he : LeavesIn params e) (d k : Nat) :
    LeavesIn params (e.abstract1 d k) :=
  fun l hl => he l (fvarLeaves_abstract1_sub e d k l hl)

theorem LeavesIn.instantiateLevelParams {e : Expr} (h : e.hasFvar = false) (ks : List Name)
    (us : List Level) : LeavesIn params (e.instantiateLevelParams ks us) :=
  .of_not_hasFvar (by rw [hasFvar_instantiateLevelParams]; exact h)

end Expr

open Expr in
theorem LeavesIn.closeTelescope {params : List Expr} :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) {body : Expr},
      (∀ b ∈ bs, LeavesIn params b.1) → LeavesIn params body →
      LeavesIn params (closeTelescope bs i body)
  | [], _, _, _, hb => hb
  | (_dom, _bm) :: bs, i, _body, hbs, hb =>
    leavesIn_forallE.mpr ⟨hbs _ List.mem_cons_self,
      (LeavesIn.closeTelescope bs (i + 1) (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb)
        |>.abstract1 i 0⟩

open Expr in
/-- A stripped telescope's binder domains and body have the type's leaves. -/
theorem stripPis_leavesIn {params : List Expr} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → LeavesIn params e →
      (∀ b ∈ bs, LeavesIn params b.1) ∧ LeavesIn params body
  | 0, e, bs, body, h, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun b hb => nomatch hb), he⟩
  | n + 1, e, bs, body, h, he => by
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, r₀⟩, h₀, h₁⟩ := h
      simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨hty, hb⟩ := leavesIn_forallE.mp he
      obtain ⟨hbs, hbody⟩ := stripPis_leavesIn n h₀ hb
      refine ⟨fun x hx => ?_, hbody⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hty
      · exact hbs x hx
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [Expr.stripPis] at h

/-- **The openers are a leaf-closed set**: an opener's annotation
mentions earlier openers only, which are openers again. -/
theorem openPisAtFvars_leavesIn {k : Nat} {e : Expr} {d : Nat} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars k e d = some (fvs, body)) (he : e.hasFvar = false) :
    ∀ x ∈ fvs, Expr.LeavesIn fvs x := by
  intro x hx l hl
  rcases ConLeche.Verify.openPisAtFvars_leaves k h l (Or.inr ⟨x, hx, hl⟩) with h' | h'
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar he] at h'
    exact nomatch h'
  · exact h'

/-! ## The containers' stored types are closed -/

/-- What the elimination copies out of a container is closed: every
member's stored former and constructor types have no free variable. -/
@[expose] def ContainersClosed (env : Env) : Prop :=
  ∀ (I : Name) (ci : ContainerInfo), containerInfo? env I = some ci →
    ∀ J ∈ ci.members, J.type.hasFvar = false ∧ ∀ c ∈ J.ctors, c.type.hasFvar = false

/-- `Option`'s `do`-bind, inverted at a `some`. -/
theorem bindOption_eq_some_iff {α β : Type} {x : Option α} {f : α → Option β} {b : β} :
    (x >>= f) = some b ↔ ∃ a, x = some a ∧ f a = some b := Option.bind_eq_some_iff

/-- **`containerInfo?` reads stored constants**: every member's type is
a stored inductive's, every constructor's a stored constructor's. -/
theorem containerInfo?_stored {env : Env} {I : Name} {ci : ContainerInfo}
    (h : containerInfo? env I = some ci) :
    ∀ J ∈ ci.members,
      (∃ (cvC : ConstantVal) (caps : IndCaps),
        env.find? J.name = some (.indInfo cvC caps) ∧ J.type = cvC.type ∧
          J.lps = cvC.levelParams) ∧
      ∀ c ∈ J.ctors, ∃ (cvc : ConstantVal) (nPc nF : Nat),
        env.find? c.name = some (.ctorInfo cvc nPc nF) ∧ c.type = cvc.type := by
  unfold containerInfo? at h
  split at h
  · exact nomatch h
  simp only [bindOption_eq_some_iff] at h
  obtain ⟨cT, hfT, h⟩ := h
  split at h
  · next cvT caps =>
    simp only [bindOption_eq_some_iff] at h
    obtain ⟨cR, hfR, h⟩ := h
    split at h
    · next cvR mI rP rules =>
      split at h
      · next hle =>
        simp only [bindOption_eq_some_iff] at h
        obtain ⟨nP, hnP, h⟩ := h
        obtain ⟨p, hstrip, h⟩ := h
        obtain ⟨_, recBody⟩ := p
        simp only at h
        split at h
        · next hnames =>
          simp only [bindOption_eq_some_iff] at h
          obtain ⟨members, hmapM, h⟩ := h
          simp only [Option.some.injEq] at h
          subst h
          intro J hJ
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hJ
          obtain ⟨hlen, hall⟩ := optionMapM_getElem? hmapM
          have hiC : i < (containerMembersGo env nP (rP + 1) 0 recBody).length := by
            rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
          obtain ⟨J', hJ', hf⟩ := hall i _ (List.getElem?_eq_getElem hiC)
          obtain rfl : J = J' := Option.some.inj (hi.symm.trans hJ')
          simp only [bindOption_eq_some_iff] at hf
          obtain ⟨cC, hfC, hf⟩ := hf
          split at hf
          · next cvC capsC =>
            simp only [bindOption_eq_some_iff] at hf
            obtain ⟨cRc, hfRc, hf⟩ := hf
            split at hf
            · next _ _ rPc rulesC =>
              split at hf
              · next hlps =>
                simp only [bindOption_eq_some_iff] at hf
                obtain ⟨ctors, hctors, hf⟩ := hf
                simp only [Option.some.injEq] at hf
                subst hf
                refine ⟨⟨cvC, capsC, hfC, rfl, rfl⟩, fun c hc => ?_⟩
                obtain ⟨l, hl⟩ := List.getElem?_of_mem hc
                obtain ⟨hlenc, hallc⟩ := optionMapM_getElem? hctors
                have hlr : l < rulesC.length := by
                  rw [← hlenc]; exact (List.getElem?_eq_some_iff.mp hl).1
                obtain ⟨c', hc', hg⟩ := hallc l _ (List.getElem?_eq_getElem hlr)
                obtain rfl : c = c' := Option.some.inj (hl.symm.trans hc')
                split at hg
                · next cvc nPc nF hfc =>
                  split at hg
                  · simp only [Option.some.injEq] at hg
                    subst hg
                    exact ⟨cvc, nPc, nF, hfc, rfl⟩
                  · exact nomatch hg
                · exact nomatch hg
              · exact nomatch hf
            · exact nomatch hf
          · exact nomatch hf
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- Under `EnvWF` the containers are closed. -/
theorem containersClosed_of_wf {env : Env} (hwf : EnvWF env) : ContainersClosed env := by
  intro I ci hci J hJ
  obtain ⟨⟨cvC, caps, hfC, hty, -⟩, hctors⟩ := containerInfo?_stored hci J hJ
  refine ⟨by rw [hty]; exact (hwf _ (List.mem_of_find?_eq_some hfC)).1, fun c hc => ?_⟩
  obtain ⟨cvc, nPc, nF, hfc, hty'⟩ := hctors c hc
  rw [hty']
  exact (hwf _ (List.mem_of_find?_eq_some hfc)).1

/-! ## The invariant -/

/-- Every pin and every constructor type of the growing list has its
leaves among the openers. -/
structure LeafInv (params : List Expr) (st : ElimState) : Prop where
  pins : ∀ q ∈ st.pins, Expr.LeavesIn params q.pin
  ctors : ∀ t ∈ st.types, ∀ c ∈ t.ctors, Expr.LeavesIn params c.2.1

open Expr in
/-- A mint keeps the invariant: the new pins are the container applied
to arguments of the walked term, the new copies' constructors are the
container's closed stored types at those arguments, closed over the
first former's binders. -/
theorem mkCopies_leafInv {env : Env} {params : List Expr} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {I : Name} {base size : Nat}
    (hpbs : ∀ b ∈ pbs, LeavesIn params b.1) (hDs : ∀ D ∈ Ds, LeavesIn params D) :
    ∀ {members : List ContainerMember} {st st' : ElimState} {got : Option Name},
      mkCopies env pbs lvls Ds I base size members st = .ok (st', got) →
      (∀ J ∈ members, J.type.hasFvar = false ∧ ∀ c ∈ J.ctors, c.type.hasFvar = false) →
      LeafInv params st → LeafInv params st' := by
  intro members st st' got hmk hcl hinv
  obtain ⟨copies, hclen, hty, hpin, hall⟩ := mkCopies_spec hmk
  refine ⟨fun q hq => ?_, fun t ht c hc => ?_⟩
  · rw [hpin] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hinv.pins q hq
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
      rw [List.getElem?_zipWith] at hi
      split at hi
      · next hc hJ =>
        obtain rfl := Option.some.inj hi
        exact LeavesIn.mkAppN leavesIn_const hDs
      · exact nomatch hi
  · rw [hty] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hinv.ctors t ht c hc
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem ht
      have hiJ : i < members.length := by
        rw [← hclen]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨copy, hcopy, hmkc, -⟩ := hall i _ (List.getElem?_eq_getElem hiJ)
      obtain rfl : t = copy := Option.some.inj (hi.symm.trans hcopy)
      obtain ⟨-, -, -, hctors⟩ := mkCopy_inv hmkc
      obtain ⟨l, hl⟩ := List.getElem?_of_mem hc
      have hlJ : l < members[i].ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hl).1
        rw [(mkCopy_inv hmkc).2.2.1] at this
        exact this
      obtain ⟨cI, hcI, hl'⟩ := hctors l _ (List.getElem?_eq_getElem hlJ)
      obtain rfl := Option.some.inj (hl.symm.trans hl')
      have hJcl := hcl _ (List.getElem_mem hiJ)
      show LeavesIn params (closeTelescope pbs 0 cI)
      refine LeavesIn.closeTelescope pbs 0 hpbs (LeavesIn.instPis hcI ?_ hDs)
      exact LeavesIn.instantiateLevelParams (hJcl.2 _ (List.getElem_mem hlJ)) _ _

open Expr in
/-- A fired replacement: the state keeps the invariant and the answer
has its leaves among the openers. -/
theorem replaceIfNested_leaves {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} (hcc : ContainersClosed env)
    (hpbs : ∀ b ∈ pbs, LeavesIn params b.1) (hpar : ∀ p ∈ params, LeavesIn params p)
    {st st' : ElimState} {e r : Expr}
    (h : replaceIfNested env blvls params pbs st e = .ok (some (r, st')))
    (he : LeavesIn params e) (hinv : LeafInv params st) :
    LeafInv params st' ∧ LeavesIn params r := by
  have hidx : ∀ (n : Nat), ∀ a ∈ e.getAppArgs.drop n, LeavesIn params a :=
    fun n a ha => he.getAppArgs (List.mem_of_mem_drop ha)
  have hans : ∀ (aux : Name) (n : Nat),
      LeavesIn params (Expr.mkAppN (Expr.mkAppN (.const aux blvls) params) (e.getAppArgs.drop n)) :=
    fun aux n => (LeavesIn.mkAppN leavesIn_const hpar).mkAppN (hidx n)
  unfold replaceIfNested at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · next I lvls hfn =>
      split at h
      · split at h
        · exact nomatch h
        · split at h
          · split at h
            · exact nomatch h
            · exact nomatch h
          · next ci hci =>
            split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · next nested hocc =>
                split at h
                · exact nomatch h
                · split at h
                  · next q hq =>
                    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact ⟨hinv, hans _ _⟩
                  · split at h
                    · exact nomatch h
                    · next p hmk =>
                      obtain ⟨stq, gotq⟩ := p
                      split at h
                      · exact nomatch h
                      · next auxI hgot =>
                        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq,
                          Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        refine ⟨mkCopies_leafInv hpbs ?_ hmk (hcc I ci hci) hinv, hans _ _⟩
                        exact fun D hD => he.getAppArgs (List.mem_of_mem_take hD)
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

open Expr in
/-- **The walk keeps the invariant**, and its output has its leaves among
the openers whenever its input has. -/
theorem replaceAllNested_leaves {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} (hcc : ContainersClosed env)
    (hpbs : ∀ b ∈ pbs, LeavesIn params b.1) (hpar : ∀ p ∈ params, LeavesIn params p) :
    ∀ (e : Expr) {st : ElimState} {r : Expr × ElimState},
      replaceAllNested env blvls params pbs st e = .ok r → LeavesIn params e →
      LeafInv params st → LeafInv params r.2 ∧ LeavesIn params r.1 := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := leavesIn_app.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihf h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := iha h₂ ha hinv₁
            exact ⟨hinv₂, leavesIn_app.mpr ⟨hx₁, hx₂⟩⟩
  | lam ty b bm ihty ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := leavesIn_lam.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihty h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := ihb h₂ ha hinv₁
            exact ⟨hinv₂, leavesIn_lam.mpr ⟨hx₁, hx₂⟩⟩
  | forallE ty b bm ihty ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            obtain rfl := Except.ok.inj h
            obtain ⟨hf, ha⟩ := leavesIn_forallE.mp he
            obtain ⟨hinv₁, hx₁⟩ := ihty h₁ hf hinv
            obtain ⟨hinv₂, hx₂⟩ := ihb h₂ ha hinv₁
            exact ⟨hinv₂, leavesIn_forallE.mpr ⟨hx₁, hx₂⟩⟩
  | letE ty v b ihty ihv ihb =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          split at h
          · contradiction
          · next x₂ st₂ h₂ =>
            split at h
            · contradiction
            · next x₃ st₃ h₃ =>
              obtain rfl := Except.ok.inj h
              obtain ⟨h1, h2, h3⟩ := leavesIn_letE.mp he
              obtain ⟨hinv₁, hx₁⟩ := ihty h₁ h1 hinv
              obtain ⟨hinv₂, hx₂⟩ := ihv h₂ h2 hinv₁
              obtain ⟨hinv₃, hx₃⟩ := ihb h₃ h3 hinv₂
              exact ⟨hinv₃, leavesIn_letE.mpr ⟨hx₁, hx₂, hx₃⟩⟩
  | proj s i x ihx =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · split at h
        · contradiction
        · next x₁ st₁ h₁ =>
          obtain rfl := Except.ok.inj h
          obtain ⟨hinv₁, hx₁⟩ := ihx h₁ (leavesIn_proj.mp he) hinv
          exact ⟨hinv₁, leavesIn_proj.mpr hx₁⟩
  | bvar i =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | fvar idx ty _ =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | sort u =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | const n us =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩
  | lit l =>
    intro st r h he hinv
    unfold replaceAllNested at h
    simp only at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hinv, he⟩
    · split at h
      · contradiction
      · next r' hr' =>
        obtain rfl := Except.ok.inj h
        exact replaceIfNested_leaves hcc hpbs hpar hr' he hinv
      · obtain rfl := Except.ok.inj h
        exact ⟨hinv, he⟩

open Expr in
/-- One type's constructors rewritten: the invariant is kept and the
rewritten constructors have their leaves among the openers. -/
theorem elimCtors_leaves {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} (hcc : ContainersClosed env)
    (hpbs : ∀ b ∈ pbs₀, LeavesIn params b.1) (hpar : ∀ p ∈ params, LeavesIn params p) :
    ∀ {cs : List (Name × Expr × Nat)} {st : ElimState}
      {r : List (Name × Expr × Nat) × ElimState},
      elimCtors env blvls nP params pbs₀ cs st = .ok r →
      (∀ c ∈ cs, LeavesIn params c.2.1) → LeafInv params st →
      LeafInv params r.2 ∧ ∀ c ∈ r.1, LeavesIn params c.2.1
  | [], st, r, h, _, hinv => by
    simp only [elimCtors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hinv, fun c hc => nomatch hc⟩
  | (c, cty, nF) :: rest, st, r, h, hcs, hinv => by
    simp only [elimCtors, bind, Except.bind] at h
    split at h
    · next pbs rest₀ hstrip =>
      split at h
      · next cbody hinst =>
        split at h
        · contradiction
        · next q st₁ hq =>
          split at h
          · contradiction
          · next rest' st₂ hrest =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            have hcty : LeavesIn params cty := hcs _ List.mem_cons_self
            obtain ⟨hpbs', -⟩ := stripPis_leavesIn nP hstrip hcty
            obtain ⟨hinv₁, hbody⟩ := replaceAllNested_leaves hcc hpbs hpar _ hq
              (LeavesIn.instPis hinst hcty hpar) hinv
            obtain ⟨hinv₂, hrest'⟩ := elimCtors_leaves hcc hpbs hpar hrest
              (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hinv₁
            refine ⟨hinv₂, fun c' hc' => ?_⟩
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact LeavesIn.closeTelescope pbs 0 hpbs' hbody
            · exact hrest' c' hc'
      · contradiction
    · contradiction

open Expr in
/-- The worklist keeps the invariant. -/
theorem elimLoop_leaves {env : Env} {blvls : List Level} {nP : Nat} {params : List Expr}
    {pbs₀ : List (Expr × BinderMeta)} (hcc : ContainersClosed env)
    (hpbs : ∀ b ∈ pbs₀, LeavesIn params b.1) (hpar : ∀ p ∈ params, LeavesIn params p) :
    ∀ {fuel qhead : Nat} {st st' : ElimState},
      elimLoop env blvls nP params pbs₀ fuel qhead st = .ok st' →
      LeafInv params st → LeafInv params st'
  | 0, _, _, _, h, _ => nomatch h
  | fuel + 1, qhead, st, st', h, hinv => by
    simp only [elimLoop] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact hinv
    · next t ht =>
      split at h
      · exact nomatch h
      · next cs' st₁ hcs =>
        have hmem : t ∈ st.types := List.mem_of_getElem? ht
        obtain ⟨hinv₁, hcs'⟩ := elimCtors_leaves hcc hpbs hpar hcs (hinv.ctors t hmem) hinv
        refine elimLoop_leaves hcc hpbs hpar h ⟨hinv₁.pins, fun t' ht' c hc => ?_⟩
        rcases List.mem_or_eq_of_mem_set ht' with ht' | rfl
        · exact hinv₁.ctors t' ht' c hc
        · exact hcs' c hc

open Expr in
/-- **THE PINS' LEAVES ARE THE OPENERS**: at the elimination's end every
pin has its free-variable leaves — hereditarily, with their
annotations — among the first former's openers `params`, given the
containers' stored types closed and the block's own types closed. -/
theorem elimNested_leaves {env : Env} {nP : Nat} {lps : List Name} {types : List AuxType}
    {st : ElimState} (hcc : ContainersClosed env) (h : elimNested env nP lps types = .ok st)
    (hty : ∀ t ∈ types, ∀ c ∈ t.ctors, c.2.1.hasFvar = false)
    (ht₀ : ∀ t₀ ∈ types.head?, t₀.type.hasFvar = false) :
    ∃ (t₀ : AuxType) (params : List Expr) (body : Expr),
      types.head? = some t₀ ∧ openPisAtFvars nP t₀.type 0 = some (params, body) ∧
      ∀ q ∈ st.pins, LeavesIn params q.pin := by
  unfold elimNested at h
  split at h
  · next t₀ hh =>
    split at h
    · next params body hop =>
      split at h
      · next pbs body₀ hstrip =>
        have hcl : t₀.type.hasFvar = false := ht₀ t₀ (by rw [hh]; exact rfl)
        have hpar : ∀ p ∈ params, LeavesIn params p := openPisAtFvars_leavesIn hop hcl
        have hpbs : ∀ b ∈ pbs, LeavesIn params b.1 :=
          (stripPis_leavesIn nP hstrip (LeavesIn.of_not_hasFvar hcl)).1
        have hinv₀ : LeafInv params ⟨types, [], 1⟩ :=
          ⟨(fun q hq => nomatch hq), fun t ht c hc => LeavesIn.of_not_hasFvar (hty t ht c hc)⟩
        exact ⟨t₀, params, body, hh, hop, (elimLoop_leaves hcc hpbs hpar h hinv₀).pins⟩
      · contradiction
    · contradiction
  · contradiction

end ConLeche
