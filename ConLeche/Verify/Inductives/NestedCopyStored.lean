module

public import ConLeche.Verify.Inductives.NestedRestoreWalk
public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedFacts
import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedFields
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.AbstractRange
public import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Inductives.FixRec

public section

/-!
# A copy's stored constructor against K.17's witness (task #279 M-D′, step (1), DESIGN §M.45)

The syntactic pieces the constructor read's Model half
(`copyWalkFacts_of_stored`, `Model/Inductives/CopyWalkFactsRun.lean`)
assembles around `restoreI_walk`:

* the pair K.17's witness compares — a copy's PROCESSED constructor
  (the block's, `b.ctors`) against its STORED one (`auxStoredAll`'s
  record) — is in `nestedCtorPairs` (`nestedCtorPairs_mem`,
  `ownCtors_mem`, `auxStored?_ctors`);
* the processed constructor, closed over the first former's binders,
  re-opens at the same openers to the walk's output
  (`openPisAtFvars_closeTelescope_leaves`), and the minted constructor
  `instPis`'d at those openers is the instantiated container
  constructor (`instPis_closeTelescope_leaves`);
* erasure equality between terms whose leaves are the openers is
  equality (`ErasedEq.eq_of_leavesIn`), and it transfers along a
  telescope's openers (`openers_erasedEq`);
* `whnf` is the identity on a term erasure-equal to a Π-tower over an
  inductive-headed application (`whnf_eq_of_erasedEq_pis_indApp`, from
  `whnf_forallE_eq` and task #305's `whnf_indApp_eq`);
* a level instantiation at DISTINCT parameters sends the parameter list
  to the level list (`map_subst_params_nodup`; the containers'
  `lps.Nodup` is K.21's record).
-/

namespace ConLeche

open Expr

variable {mode : CheckMode}

/-! ## The whnf witness's pairs -/

/-- A constructor of member `mIdx` is in that member's own list. -/
theorem ownCtors_mem {b : MutualBlock} {J : Nat} {c : MutualCtor} (hc : b.ctors[J]? = some c) :
    (J, c) ∈ b.ownCtors c.member := by
  unfold MutualBlock.ownCtors
  refine List.mem_filter.mpr ⟨?_, by simp⟩
  refine List.mem_map.mpr ⟨(c, J), ?_, rfl⟩
  refine List.mem_of_getElem? (i := J) ?_
  rw [List.getElem?_zipIdx, hc]
  simp

/-- The stored record's constructors, positionally against the
member's own constructors: each is FOUND at its name as a constructor. -/
theorem auxStored?_ctors {envAux : Env} {b : MutualBlock} {i : Nat} {a : AuxStored}
    (h : auxStored? envAux b i = some a) :
    ∀ (l : Nat) (J : Nat) (c : MutualCtor), (b.ownCtors i)[l]? = some (J, c) →
      ∃ x : ConstantVal × Nat × Nat, a.ctors[l]? = some x ∧
        envAux.find? c.cv.name = some (.ctorInfo x.1 x.2.1 x.2.2) := by
  unfold auxStored? at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨x, hf, ci, hci, h⟩ := h
  split at h
  · next cvTa caps =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ci', -, h⟩ := h
    split at h
    · next cvRa mI rP rules =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ctors, hctors, h⟩ := h
      simp only [pure, Option.some.injEq] at h
      subst h
      intro l J c hc
      obtain ⟨-, hall⟩ := optionMapM_getElem? hctors
      obtain ⟨y, hy, hfy⟩ := hall l (J, c) hc
      refine ⟨y, hy, ?_⟩
      simp only [Option.bind_eq_some_iff] at hfy
      obtain ⟨ci'', hci'', hfy⟩ := hfy
      split at hfy
      · next cvCa nP nF =>
        simp only [pure, Option.some.injEq] at hfy
        subst hfy
        exact hci''
      · exact nomatch hfy
    · exact nomatch h
  · exact nomatch h

/-- The pair of a member's `l`-th own constructor and the stored
record's `l`-th constructor is one the witness ran on. -/
theorem nestedCtorPairs_mem {b : MutualBlock} {stored : List AuxStored} {mIdx : Nat}
    {a : AuxStored} (hm : mIdx < b.k) (ha : stored[mIdx]? = some a) {l J : Nat}
    {c : MutualCtor} (hc : (b.ownCtors mIdx)[l]? = some (J, c)) {x : ConstantVal × Nat × Nat}
    (hx : a.ctors[l]? = some x) : (c, x) ∈ nestedCtorPairs b stored := by
  unfold nestedCtorPairs
  refine List.mem_flatMap.mpr ⟨mIdx, List.mem_range.mpr hm, ?_⟩
  rw [ha]
  refine List.mem_of_getElem? (i := l) ?_
  rw [List.getElem?_zip_eq_some]
  refine ⟨?_, hx⟩
  rw [List.getElem?_map, hc]
  rfl

/-! ## The processed constructor at the openers -/

/-- `instPis` is `instPisAt` without the domains. -/
theorem instPis_of_instPisAt :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) → Expr.instPis e args = some rest
  | [], e, ds, rest, h => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl
  | a :: as, .forallE dom body bm, ds, rest, h => by
    simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
    obtain ⟨⟨ds', rest'⟩, h', hds⟩ := h
    simp only [Prod.mk.injEq] at hds
    obtain ⟨-, rfl⟩ := hds
    exact instPis_of_instPisAt as h'
  | a :: as, .bvar _, _, _, h | a :: as, .fvar _ _, _, _, h | a :: as, .sort _, _, _, h
  | a :: as, .const _ _, _, _, h | a :: as, .app _ _, _, _, h | a :: as, .lam _ _ _, _, _, h
  | a :: as, .letE _ _ _, _, _, h | a :: as, .lit _, _, _, h | a :: as, .proj _ _ _, _, _, h =>
    nomatch h

/-- The openers of an opening are the variables `0 …`, in order. -/
theorem openers_shape {n : Nat} {T : Expr} {params : List Expr} {body : Expr}
    (hop : openPisAtFvars n T 0 = some (params, body)) :
    ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty := by
  intro i x hx
  obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis n hop
  have hi : i < n := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨ty, hty⟩ := hsh i hi
  rw [Nat.zero_add] at hty
  rw [hx] at hty
  exact ⟨ty, Option.some.inj hty⟩

/-- **The processed constructor re-opens at the openers**: a term
whose leaves are the first former's openers, closed over that former's
binders, opens at the same openers to itself (the bvar-form round trip
`openPisAtFvars_closeTelescope_strip` with consistency from the
leaves). -/
theorem openPisAtFvars_closeTelescope_leaves {n : Nat} {T : Expr}
    {pbs : List (Expr × BinderMeta)} {body₀ : Expr} {params : List Expr} {body : Expr}
    (hst : T.stripPis n = some (pbs, body₀)) (hop : openPisAtFvars n T 0 = some (params, body))
    (hnf : T.hasFvar = false) {e : Expr} (he : Expr.LeavesIn params e)
    (hb : e.looseBVarsBounded 0 = true) :
    openPisAtFvars n (closeTelescope pbs 0 e) 0 = some (params, e) := by
  refine openPisAtFvars_closeTelescope_strip n hst hop ?_ hb ?_
  · intro b hb'
    exact WScoped.of_not_hasFvar ((stripPis_not_hasFvar n hst hnf).1 b hb')
  · intro x hx idx ty hxe
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    obtain ⟨ty', hty'⟩ := openers_shape hop j x hj
    rw [hxe] at hty' hj
    obtain ⟨rfl, -⟩ := Expr.fvar.inj hty'
    exact fvarConsistent_of_leavesIn (openers_shape hop) hj he

/-- The minted constructor `instPis`'d at the openers is the
instantiated container constructor it was closed from. -/
theorem instPis_closeTelescope_leaves {n : Nat} {T : Expr}
    {pbs : List (Expr × BinderMeta)} {body₀ : Expr} {params : List Expr} {body : Expr}
    (hst : T.stripPis n = some (pbs, body₀)) (hop : openPisAtFvars n T 0 = some (params, body))
    (hnf : T.hasFvar = false) {e : Expr} (he : Expr.LeavesIn params e)
    (hb : e.looseBVarsBounded 0 = true) :
    Expr.instPis (closeTelescope pbs 0 e) params = some e :=
  instPis_of_instPisAt params
    (Verify.openPisAtFvars_instPisAt n (openPisAtFvars_closeTelescope_leaves hst hop hnf he hb))

/-! ## Erasure equality at the openers -/

/-- **Erasure-equal terms whose leaves are the openers are equal**: an
`fvar` leaf at index `i` is the opener `i` on both sides. -/
theorem Expr.ErasedEq.eq_of_leavesIn {params : List Expr}
    (hshape : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty) :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ → Expr.LeavesIn params e₁ → Expr.LeavesIn params e₂ →
      e₁ = e₂
  | .bvar _, .bvar _, h, _, _ => by rw [h]
  | .fvar i ty, .fvar j ty', h, h₁, h₂ => by
    have hij : i = j := h
    subst hij
    have hm₁ : Expr.fvar i ty ∈ params := h₁ (i, ty) (by simp [Expr.fvarLeaves])
    have hm₂ : Expr.fvar i ty' ∈ params := h₂ (i, ty') (by simp [Expr.fvarLeaves])
    obtain ⟨k₁, hk₁⟩ := List.getElem?_of_mem hm₁
    obtain ⟨k₂, hk₂⟩ := List.getElem?_of_mem hm₂
    obtain ⟨t₁, ht₁⟩ := hshape k₁ _ hk₁
    obtain ⟨t₂, ht₂⟩ := hshape k₂ _ hk₂
    have e1 : k₁ = i := (Expr.fvar.inj ht₁).1.symm
    have e2 : k₂ = i := (Expr.fvar.inj ht₂).1.symm
    subst e1
    subst e2
    rw [hk₁] at hk₂
    rw [(Expr.fvar.inj (Option.some.inj hk₂)).2]
  | .sort _, .sort _, h, _, _ => by rw [h]
  | .const _ _, .const _ _, h, _, _ => by rw [h.1, h.2]
  | .app f a, .app g b, h, h₁, h₂ => by
    rw [eq_of_leavesIn hshape h.1 (Expr.leavesIn_app.mp h₁).1 (Expr.leavesIn_app.mp h₂).1,
      eq_of_leavesIn hshape h.2 (Expr.leavesIn_app.mp h₁).2 (Expr.leavesIn_app.mp h₂).2]
  | .lam _ _ _, .lam _ _ _, h, h₁, h₂ => by
    rw [h.1, eq_of_leavesIn hshape h.2.1 (Expr.leavesIn_lam.mp h₁).1 (Expr.leavesIn_lam.mp h₂).1,
      eq_of_leavesIn hshape h.2.2 (Expr.leavesIn_lam.mp h₁).2 (Expr.leavesIn_lam.mp h₂).2]
  | .forallE _ _ _, .forallE _ _ _, h, h₁, h₂ => by
    rw [h.1, eq_of_leavesIn hshape h.2.1 (Expr.leavesIn_forallE.mp h₁).1
        (Expr.leavesIn_forallE.mp h₂).1,
      eq_of_leavesIn hshape h.2.2 (Expr.leavesIn_forallE.mp h₁).2 (Expr.leavesIn_forallE.mp h₂).2]
  | .letE _ _ _, .letE _ _ _, h, h₁, h₂ => by
    rw [eq_of_leavesIn hshape h.1 (Expr.leavesIn_letE.mp h₁).1 (Expr.leavesIn_letE.mp h₂).1,
      eq_of_leavesIn hshape h.2.1 (Expr.leavesIn_letE.mp h₁).2.1 (Expr.leavesIn_letE.mp h₂).2.1,
      eq_of_leavesIn hshape h.2.2 (Expr.leavesIn_letE.mp h₁).2.2 (Expr.leavesIn_letE.mp h₂).2.2]
  | .lit _, .lit _, h, _, _ => by rw [h]
  | .proj s i x, .proj s' i' x', h, h₁, h₂ => by
    rw [h.1, h.2.1, eq_of_leavesIn hshape h.2.2 (Expr.leavesIn_proj.mp h₁)
      (Expr.leavesIn_proj.mp h₂)]

/-- Erasure equality at a constant head, both ways. -/
theorem Expr.ErasedEq.getAppFn_const_iff :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ → ∀ {c : Name} {us : List Level},
      (e₁.getAppFn = .const c us ↔ e₂.getAppFn = .const c us)
  | .app f a, .app g b, he, c, us => getAppFn_const_iff (e₁ := f) (e₂ := g) he.1
  | .const n us', .const n' us'', he, c, us => by
    obtain ⟨rfl, rfl⟩ := he
    exact Iff.rfl
  | .bvar _, .bvar _, _, _, _ | .fvar _ _, .fvar _ _, _, _, _ | .sort _, .sort _, _, _, _
  | .lam _ _ _, .lam _ _ _, _, _, _ | .forallE _ _ _, .forallE _ _ _, _, _, _
  | .letE _ _ _, .letE _ _ _, _, _, _ | .lit _, .lit _, _, _, _
  | .proj _ _ _, .proj _ _ _, _, _, _ => by simp [Expr.getAppFn]

/-- The Π-prefix length is invariant under erasure equality. -/
theorem Expr.ErasedEq.piBinders_length' :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ → (e₁.piBinders).1.length = (e₂.piBinders).1.length
  | .forallE ty bd m, .forallE ty' bd' m', he => by
    simp only [Expr.piBinders, List.length_cons]
    rw [piBinders_length' he.2.2]
  | .bvar _, .bvar _, _ | .fvar _ _, .fvar _ _, _ | .sort _, .sort _, _ | .const _ _, .const _ _, _
  | .app _ _, .app _ _, _ | .lam _ _ _, .lam _ _ _, _ | .letE _ _ _, .letE _ _ _, _
  | .lit _, .lit _, _ | .proj _ _ _, .proj _ _ _, _ => Eq.refl _

/-- **The openers of erasure-equal telescopes are erasure-equal**,
position by position (each opener's annotation is its binder domain
instantiated at the earlier openers, `openPisAtFvars_binder`). -/
theorem openers_erasedEq {n : Nat} {e₁ e₂ : Expr} {d : Nat} {fvs₁ fvs₂ : List Expr}
    {o₁ o₂ : Expr} {bs₁ bs₂ : List (Expr × BinderMeta)} {r₁ r₂ : Expr}
    (hop₁ : openPisAtFvars n e₁ d = some (fvs₁, o₁)) (hop₂ : openPisAtFvars n e₂ d = some (fvs₂, o₂))
    (hs₁ : e₁.stripPis n = some (bs₁, r₁)) (hs₂ : e₂.stripPis n = some (bs₂, r₂))
    (hbs : ∀ (k : Nat) (b₁ b₂ : Expr × BinderMeta), bs₁[k]? = some b₁ → bs₂[k]? = some b₂ →
      Expr.ErasedEq b₁.1 b₂.1) :
    ∀ (k : Nat) (x₁ x₂ : Expr), fvs₁[k]? = some x₁ → fvs₂[k]? = some x₂ →
      Expr.ErasedEq x₁.fvarTypeD x₂.fvarTypeD := by
  have hlen₁ : fvs₁.length = n := Verify.openPisAtFvars_length n hop₁
  have hlen₂ : fvs₂.length = n := Verify.openPisAtFvars_length n hop₂
  have hlb₁ : bs₁.length = n := stripPis_length' n hs₁
  have hlb₂ : bs₂.length = n := stripPis_length' n hs₂
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro x₁ x₂ hx₁ hx₂
    have hk : k < n := by rw [← hlen₁]; exact (List.getElem?_eq_some_iff.mp hx₁).1
    obtain ⟨b₁, hb₁⟩ : ∃ b₁, bs₁[k]? = some b₁ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨b₂, hb₂⟩ : ∃ b₂, bs₂[k]? = some b₂ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h₁ := openPisAtFvars_binder n hop₁ hs₁ k b₁ hb₁
    have h₂ := openPisAtFvars_binder n hop₂ hs₂ k b₂ hb₂
    rw [hx₁] at h₁
    rw [hx₂] at h₂
    obtain rfl := Option.some.inj h₁
    obtain rfl := Option.some.inj h₂
    show Expr.ErasedEq (Expr.instSeq (fvs₁.take k) (k - 1) b₁.1) (Expr.instSeq (fvs₂.take k) (k - 1) b₂.1)
    refine instSeq_erasedEq_args _ _ _ (hbs k b₁ b₂ hb₁ hb₂) ?_ ?_
    · intro j y₁ y₂ hy₁ hy₂
      have hj : j < k := by
        have := (List.getElem?_eq_some_iff.mp hy₁).1
        rw [List.length_take] at this
        omega
      rw [List.getElem?_take_of_lt hj] at hy₁ hy₂
      have hE := ih j hj y₁ y₂ hy₁ hy₂
      obtain ⟨t₁, hy₁'⟩ := openPisAtFvars_fvar_shape hop₁ hy₁
      obtain ⟨t₂, hy₂'⟩ := openPisAtFvars_fvar_shape hop₂ hy₂
      subst hy₁'
      subst hy₂'
      show d + j = d + j
      rfl
    · rw [List.length_take, List.length_take, hlen₁, hlen₂]
where
  /-- an opener is a variable at its position -/
  openPisAtFvars_fvar_shape {n : Nat} {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr}
      (hop : openPisAtFvars n e d = some (fvs, o)) {j : Nat} {y : Expr} (hy : fvs[j]? = some y) :
      ∃ ty, y = .fvar (d + j) ty := by
    obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis n hop
    have hj : j < n := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨ty, hty⟩ := hsh j hj
    rw [hy] at hty
    exact ⟨ty, Option.some.inj hty⟩

/-! ## `whnf` at the container-recursive shapes -/

/-- **`whnf` is the identity on a term erasure-equal to a Π-tower over
an inductive-headed application**: a Π by `whnf_forallE_eq`, an
application of a stored inductive by `whnf_indApp_eq` (task #305). -/
theorem whnf_eq_of_erasedEq_pis_indApp {env : Env} {F d : Nat} {e e' X : Expr} {J : Name}
    {lvls : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hJ : env.find? J = some (.indInfo cv caps)) {n : Nat} {bs : List (Expr × BinderMeta)}
    {args : List Expr} (hX : Expr.ErasedEq e X)
    (hsX : X.stripPis n = some (bs, Expr.mkAppN (.const J lvls) args))
    (h : whnf mode env F d e = .ok e') : e' = e := by
  obtain ⟨bs', body', hs, -, -, hbody⟩ := Expr.ErasedEq.stripPis_inv n hX hsX
  cases n with
  | zero =>
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    have hfn : e.getAppFn = .const J lvls :=
      (Expr.ErasedEq.getAppFn_const_iff hbody).mpr (by rw [Expr.getAppFn_mkAppN]; rfl)
    have he : e = Expr.mkAppN (.const J lvls) e.getAppArgs := by
      have := Expr.mkAppN_getApp e
      rw [hfn] at this
      exact this.symm
    rw [he] at h
    rw [whnf_indApp_eq hJ h]
    exact he.symm
  | succ n =>
    match e, hs with
    | .forallE t b m, _ => exact whnf_forallE_eq h

/-! ## Levels at distinct parameters -/

/-- The parameter substitution's lookup at distinct parameters is
positional. -/
theorem Level.subst_go_nodup :
    ∀ (ks : List Name) (vs : List Level), ks.Nodup → ks.length = vs.length →
      ∀ (i : Nat) (k : Name) (v : Level), ks[i]? = some k → vs[i]? = some v →
        Level.subst.go ks vs k = v
  | [], _, _, _, i, k, v, hk, _ => nomatch hk
  | k' :: ks, [], _, hlen, _, _, _, _, _ => by simp at hlen
  | k' :: ks, v' :: vs, hnd, hlen, i, k, v, hk, hv => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hv
      subst hk
      subst hv
      simp [Level.subst.go]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hk hv
      have hne : k' ≠ k := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_of_getElem? hk)
      simp only [Level.subst.go, if_neg hne]
      exact subst_go_nodup ks vs (List.nodup_cons.mp hnd).2 (by simpa using hlen) i k v hk hv

/-- **A level instantiation at DISTINCT parameters sends the parameter
list to the level list.** -/
theorem map_subst_params_nodup {ks : List Name} {vs : List Level} (hnd : ks.Nodup)
    (hlen : ks.length = vs.length) :
    (ks.map Level.param).map (Level.subst ks vs) = vs := by
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  cases hk : ks[i]? with
  | none =>
    have hi : ks.length ≤ i := by
      have := List.getElem?_eq_none_iff.mp hk
      exact this
    rw [List.getElem?_eq_none_iff.mpr (by omega)]
    rfl
  | some k =>
    obtain ⟨v, hv⟩ : ∃ v, vs[i]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hk).1)⟩
    rw [hv]
    simp only [Option.map_some, Option.some.injEq]
    show Level.subst.go ks vs k = v
    exact Level.subst_go_nodup ks vs hnd hlen i k v hk hv


/-! ## `stripPis` through abstraction and instantiation -/

/-- `abstract1` keeps a telescope, abstracting binder `j` at cursor
`k + j` and the residual at `k + n`. -/
theorem stripPis_abstract1 {d : Nat} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr} (k : Nat),
      e.stripPis n = some (bs, r) →
      ∃ bs' : List (Expr × BinderMeta),
        (e.abstract1 d k).stripPis n = some (bs', r.abstract1 d (k + n)) ∧
        bs'.length = bs.length ∧
        ∀ (j : Nat) (b : Expr × BinderMeta), bs[j]? = some b →
          bs'[j]? = some (b.1.abstract1 d (k + j), b.2)
  | 0, e, bs, r, k, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis], rfl, fun j b hb => nomatch hb⟩
  | n + 1, e, bs, r, k, h => by
    match e, h with
    | .forallE dom body bm, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, r₀⟩, h₀, hbs⟩ := h
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨bs', h', hlen, hall⟩ := stripPis_abstract1 (d := d) n (k + 1) h₀
      refine ⟨(dom.abstract1 d k, bm) :: bs', ?_, by simp [hlen], ?_⟩
      · rw [show k + (n + 1) = k + 1 + n by omega]
        simp only [Expr.abstract1, Expr.stripPis, h', Option.map_some]
      · intro j b hb
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
          subst hb
          rfl
        | succ j =>
          simp only [List.getElem?_cons_succ] at hb ⊢
          rw [hall j b hb, show k + 1 + j = k + (j + 1) by omega]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- `closeTelescope` over `fvar`-free binders strips back to those
binders. -/
theorem stripPis_closeTelescope_of_not_hasFvar :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      (∀ b ∈ bs, b.1.hasFvar = false) →
      ∃ r, (closeTelescope bs i body).stripPis bs.length = some (bs, r)
  | [], _, body, _ => ⟨body, rfl⟩
  | (dom, bm) :: bs, i, body, hbs => by
    obtain ⟨r, hr⟩ := stripPis_closeTelescope_of_not_hasFvar bs (i + 1) body
      (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
    obtain ⟨bs', hr', hlen, hall⟩ := stripPis_abstract1 (d := i) bs.length 0 hr
    have hbs' : bs' = bs := by
      refine List.ext_getElem? fun j => ?_
      cases hb : bs[j]? with
      | none =>
        rw [List.getElem?_eq_none_iff] at hb ⊢
        omega
      | some b =>
        rw [hall j b hb, abstract1_eq_self_of_WScoped _ _
          (WScoped.of_not_hasFvar (hbs b (List.mem_cons_of_mem _ (List.mem_of_getElem? hb))))]
    rw [hbs'] at hr'
    refine ⟨r.abstract1 i (0 + bs.length), ?_⟩
    simp only [closeTelescope, List.length_cons, Expr.stripPis, hr', Option.map_some]

/-- `instPis` at closed arguments of a closed telescope is closed. -/
theorem instPis_looseBVarsBounded :
    ∀ (args : List Expr) {T r : Expr}, Expr.instPis T args = some r →
      T.looseBVarsBounded 0 = true → (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      r.looseBVarsBounded 0 = true
  | [], T, r, h, hT, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    rw [← h]; exact hT
  | a :: as, .forallE dom body bm, r, h, hT, hargs => by
    simp only [Expr.instPis] at h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hT
    exact instPis_looseBVarsBounded as h
      (looseBVarsBounded_instantiate1_gen (hargs a List.mem_cons_self) hT.2)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
  | a :: as, .bvar _, _, h, _, _ | a :: as, .fvar _ _, _, h, _, _ | a :: as, .sort _, _, h, _, _
  | a :: as, .const _ _, _, h, _, _ | a :: as, .app _ _, _, h, _, _
  | a :: as, .lam _ _ _, _, h, _, _ | a :: as, .letE _ _ _, _, h, _, _
  | a :: as, .lit _, _, h, _, _ | a :: as, .proj _ _ _, _, h, _, _ => by
    simp [Expr.instPis] at h

/-- `instSeq` keeps a telescope: binder `j` instantiated at cut `t + j`,
the residual at `t + n`. -/
theorem stripPis_instSeq (xs : List Expr) :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr} (t : Nat),
      xs.length ≤ t + 1 → e.stripPis n = some (bs, r) →
      ∃ bs' : List (Expr × BinderMeta),
        (Expr.instSeq xs t e).stripPis n = some (bs', Expr.instSeq xs (t + n) r) ∧
        bs'.length = bs.length ∧
        ∀ (j : Nat) (b : Expr × BinderMeta), bs[j]? = some b →
          bs'[j]? = some (Expr.instSeq xs (t + j) b.1, b.2)
  | 0, e, bs, r, t, _, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [Expr.stripPis], rfl, fun j b hb => nomatch hb⟩
  | n + 1, e, bs, r, t, hlen, h => by
    match e, h with
    | .forallE dom body bm, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, r₀⟩, h₀, hbs⟩ := h
      simp only [Prod.mk.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      obtain ⟨bs', h', hlen', hall⟩ := stripPis_instSeq xs n (t + 1) (by omega) h₀
      refine ⟨(Expr.instSeq xs t dom, bm) :: bs', ?_, by simp [hlen'], ?_⟩
      · rw [instSeq_forallE _ _ _ _ _ hlen]
        simp only [Expr.stripPis, h', Option.map_some]
        rw [show t + 1 + n = t + (n + 1) by omega]
      · intro j b hb
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
          subst hb
          rfl
        | succ j =>
          simp only [List.getElem?_cons_succ] at hb ⊢
          rw [hall j b hb, show t + 1 + j = t + (j + 1) by omega]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-- A non-`∀` has no Π-prefix. -/
theorem piBinders_eq_of_not_forallE {e : Expr}
    (h : ∀ (d b : Expr) (m : BinderMeta), e ≠ .forallE d b m) : e.piBinders = ([], e) := by
  cases e <;> first | rfl | exact absurd rfl (h _ _ _)

/-- `instSeq` at free variables makes no `∀`. -/
theorem instSeq_not_forallE {xs : List Expr} (hxs : Expr.AllFvars xs) (t : Nat) :
    ∀ (e : Expr), (∀ (d b : Expr) (m : BinderMeta), e ≠ .forallE d b m) →
      xs.length ≤ t + 1 →
      ∀ (d b : Expr) (m : BinderMeta), Expr.instSeq xs t e ≠ .forallE d b m
  | .bvar i, _, _, d, b, m, h => by
    rcases instSeq_bvar_fvars xs hxs t i with ⟨k, ty, h'⟩ | ⟨j, h'⟩ <;> rw [h'] at h <;> exact nomatch h
  | .fvar i ty, _, _, d, b, m, h => by rw [instSeq_eq_self xs t rfl] at h; exact nomatch h
  | .sort u, _, _, d, b, m, h => by rw [instSeq_eq_self xs t rfl] at h; exact nomatch h
  | .const n us, _, _, d, b, m, h => by rw [instSeq_eq_self xs t rfl] at h; exact nomatch h
  | .lit l, _, _, d, b, m, h => by rw [instSeq_eq_self xs t rfl] at h; exact nomatch h
  | .app f a, _, _, d, b, m, h => by rw [instSeq_app] at h; exact nomatch h
  | .lam d' b' m', _, hlen, d, b, m, h => by rw [instSeq_lam _ _ _ _ _ hlen] at h; exact nomatch h
  | .letE ty v b', _, hlen, d, b, m, h => by rw [instSeq_letE _ _ _ _ _ hlen] at h; exact nomatch h
  | .proj s i x, _, _, d, b, m, h => by rw [instSeq_proj] at h; exact nomatch h
  | .forallE _ _ _, hne, _, _, _, _, _ => absurd rfl (hne _ _ _)

/-- The Π-prefix through `instSeq` at free variables: the same length,
the residual instantiated past it. -/
theorem piBinders_instSeq {xs : List Expr} (hxs : Expr.AllFvars xs) :
    ∀ (e : Expr) (t : Nat), xs.length ≤ t + 1 →
      ((Expr.instSeq xs t e).piBinders).1.length = (e.piBinders).1.length ∧
      ((Expr.instSeq xs t e).piBinders).2
        = Expr.instSeq xs (t + (e.piBinders).1.length) (e.piBinders).2
  | .forallE dom body bm, t, hlen => by
    rw [instSeq_forallE _ _ _ _ _ hlen]
    obtain ⟨h1, h2⟩ := piBinders_instSeq hxs body (t + 1) (by omega)
    simp only [Expr.piBinders, List.length_cons]
    refine ⟨by rw [h1], ?_⟩
    rw [h2, show t + 1 + body.piBinders.1.length = t + (body.piBinders.1.length + 1) by omega]
  | .bvar i, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.bvar i)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.bvar i) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .fvar i ty, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.fvar i ty)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.fvar i ty) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .sort u, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.sort u)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.sort u) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .const n us, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.const n us)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.const n us) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .lit l, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.lit l)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.lit l) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .app f a, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.app f a)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.app f a) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .lam d b m, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.lam d b m)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.lam d b m) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .letE ty v b, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.letE ty v b)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.letE ty v b) (by simp) hlen)]
    exact ⟨rfl, rfl⟩
  | .proj s i x, t, hlen => by
    rw [piBinders_eq_of_not_forallE (e := (.proj s i x)) (by simp),
      piBinders_eq_of_not_forallE (instSeq_not_forallE hxs t (.proj s i x) (by simp) hlen)]
    exact ⟨rfl, rfl⟩

/-- A constant-headed spine has no Π-prefix. -/
theorem piBinders_eq_of_getAppFn_const {e : Expr} {c : Name} {us : List Level}
    (h : e.getAppFn = .const c us) : e.piBinders = ([], e) := by
  cases e <;> first | rfl | simp [Expr.getAppFn] at h

/-- **The field head through `instSeq`** at free variables: the same
constant and Π-length, the arguments instantiated past the prefix. -/
theorem fieldHeadAt_instSeq {xs : List Expr} (hxs : Expr.AllFvars xs) (e : Expr) (t : Nat)
    (hlen : xs.length ≤ t + 1) :
    fieldHeadAt (Expr.instSeq xs t e)
      = (fieldHeadAt e).map fun q => (q.1, q.2.1.map (Expr.instSeq xs (t + q.2.2)), q.2.2) := by
  obtain ⟨h1, h2⟩ := piBinders_instSeq hxs e t hlen
  unfold fieldHeadAt
  rcases hp : e.piBinders with ⟨bs, res⟩
  rcases hp' : (Expr.instSeq xs t e).piBinders with ⟨bs', res'⟩
  rw [hp, hp'] at h1 h2
  simp only at h1 h2
  subst h2
  dsimp only
  by_cases hc : ∃ (c : Name) (us : List Level), res.getAppFn = .const c us
  · obtain ⟨c, us, hfn⟩ := hc
    have hfn' : (Expr.instSeq xs (t + bs.length) res).getAppFn = .const c us :=
      (getAppFn_instSeq_const_iff hxs (by omega)).mpr hfn
    rw [hfn', hfn]
    simp only [Option.map_some, h1]
    have hsp := Expr.mkAppN_getApp res
    rw [hfn] at hsp
    have := congrArg (Expr.instSeq xs (t + bs.length)) hsp
    rw [instSeq_mkAppN, instSeq_eq_self _ _ (e := .const c us) rfl] at this
    rw [← this, Expr.getAppArgs_mkAppN]
    rfl
  · have hnc₁ : ∀ (n : Name) (us : List Level), res.getAppFn ≠ .const n us :=
      fun n us h => hc ⟨n, us, h⟩
    have hnc₂ : ∀ (n : Name) (us : List Level),
        (Expr.instSeq xs (t + bs.length) res).getAppFn ≠ .const n us := by
      intro n us h
      rw [getAppFn_instSeq_const_iff hxs (by omega)] at h
      exact hnc₁ n us h
    split
    · next C us h => exact absurd h (hnc₂ C us)
    · first
      | rfl
      | (split
         · next C us h => exact absurd h (hnc₁ C us)
         · rfl)

/-! ## Leaves and mentions along the walk -/

/-- **The walk's output has the input's leaves** (with the parameters'):
a fire's output is the copy at the parameters and the input's own index
arguments. -/
theorem replaceAllNested_leavesIn {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} (hpar : ∀ p ∈ params, Expr.LeavesIn params p) :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr},
      replaceAllNested env blvls params pbs st e = .ok (e', st') →
      Expr.LeavesIn params e → Expr.LeavesIn params e'
  | .app f a, st, st', e', h, he => by
    rcases replaceAllNested_app' h with ⟨rfl, -⟩ | hfire | ⟨-, f', a', st₁, hf, ha, rfl⟩
    · exact he
    · obtain ⟨I, lvls, ci, aux, -, -, -, hr, -⟩ := replaceIfNested_some hfire
      rw [hr]
      refine Expr.LeavesIn.mkAppN (Expr.LeavesIn.mkAppN Expr.leavesIn_const hpar) ?_
      intro x hx
      exact Expr.LeavesIn.getAppArgs he (List.mem_of_mem_drop hx)
    · exact Expr.leavesIn_app.mpr
        ⟨replaceAllNested_leavesIn hpar f hf (Expr.leavesIn_app.mp he).1,
          replaceAllNested_leavesIn hpar a ha (Expr.leavesIn_app.mp he).2⟩
  | .lam ty b bm, st, st', e', h, he => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_lam h
    exact Expr.leavesIn_lam.mpr
      ⟨replaceAllNested_leavesIn hpar ty hty (Expr.leavesIn_lam.mp he).1,
        replaceAllNested_leavesIn hpar b hb (Expr.leavesIn_lam.mp he).2⟩
  | .forallE ty b bm, st, st', e', h, he => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_forallE h
    exact Expr.leavesIn_forallE.mpr
      ⟨replaceAllNested_leavesIn hpar ty hty (Expr.leavesIn_forallE.mp he).1,
        replaceAllNested_leavesIn hpar b hb (Expr.leavesIn_forallE.mp he).2⟩
  | .letE ty v b, st, st', e', h, he => by
    obtain ⟨ty', v', b', st₁, st₂, hty, hv, hb, rfl⟩ := replaceAllNested_letE h
    exact Expr.leavesIn_letE.mpr
      ⟨replaceAllNested_leavesIn hpar ty hty (Expr.leavesIn_letE.mp he).1,
        replaceAllNested_leavesIn hpar v hv (Expr.leavesIn_letE.mp he).2.1,
        replaceAllNested_leavesIn hpar b hb (Expr.leavesIn_letE.mp he).2.2⟩
  | .proj s i x, st, st', e', h, he => by
    obtain ⟨x', hx, rfl⟩ := replaceAllNested_proj h
    exact Expr.leavesIn_proj.mpr (replaceAllNested_leavesIn hpar x hx (Expr.leavesIn_proj.mp he))
  | .bvar i, st, st', e', h, he => by
    rw [replaceAllNested_bvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .fvar i ty, st, st', e', h, he => by
    rw [replaceAllNested_fvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .sort u, st, st', e', h, he => by
    rw [replaceAllNested_sort] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .const c vs, st, st', e', h, he => by
    rw [replaceAllNested_const] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .lit l, st, st', e', h, he => by
    rw [replaceAllNested_lit] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he

/-- A resolving term mentions no fresh name, blindly or not. -/
theorem Expr.mentionsConstE_eq_false_of_fresh {env : Env} {T : Name} {e : Expr}
    (hr : e.constsResolve env = true) (hf : env.find? T = none) : e.mentionsConstE T = false := by
  cases hE : e.mentionsConstE T with
  | false => rfl
  | true =>
    have := Expr.not_mentionsConst_of_fresh hr hf
    rw [Expr.mentionsConst_of_mentionsConstE e hE] at this
    exact nomatch this

/-- The openers of a closed constant have bounded annotations, and so
does the opened body's every leaf. -/
theorem openPisAtFvars_leavesBounded {k : Nat} {e : Expr} {d : Nat} {fvs : List Expr}
    {body : Expr} (hop : openPisAtFvars k e d = some (fvs, body)) (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) :
    (∀ x ∈ fvs, Expr.LeavesBounded x.fvarTypeD) ∧ Expr.LeavesBounded body := by
  have hbnd := Verify.openPisAtFvars_bounded k hop hb
  have hleaf : ∀ l, (l ∈ body.fvarLeaves ∨ ∃ x ∈ fvs, l ∈ x.fvarLeaves) →
      Expr.looseBVarsBounded 0 l.2 = true := by
    intro l hl
    rcases Verify.openPisAtFvars_leaves k hop l hl with h | h
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hnf] at h
      exact nomatch h
    · have := hbnd.2 _ h
      exact this
  refine ⟨fun x hx l hl => hleaf l (Or.inr ⟨x, hx, ?_⟩), fun l hl => hleaf l (Or.inl hl)⟩
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis k hop
  obtain ⟨ty, hty⟩ := hsh j (by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hj).1)
  rw [hj] at hty
  obtain rfl := Option.some.inj hty
  simp only [Expr.fvarTypeD] at hl
  simp [Expr.fvarLeaves, hl]

/-! ## The pin round trip, up to erasure -/

/-- Closing then re-opening a binder body is the identity up to
erasure — no consistency needed. -/
theorem abstract1_instantiate1_erasedEq {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      Expr.ErasedEq ((e.abstract1 d k).instantiate1 (.fvar d ty) k) e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstract1, Expr.instantiate1]
    rw [if_neg (by omega), if_neg (by omega)]
    exact Expr.ErasedEq.rfl _
  | fvar idx ty' _ =>
    intro k _
    simp only [Expr.abstract1]
    split
    · next h => subst h; simp only [Expr.instantiate1, if_true]; exact rfl
    · exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam ty' b bm ihty ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, ihty k hb.1, ihb (k + 1) hb.2⟩
  | forallE ty' b bm ihty ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, ihty k hb.1, ihb (k + 1) hb.2⟩
  | letE ty' v b ihty ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihty k hb.1.1, ihv k hb.1.2, ihb (k + 1) hb.2⟩
  | proj s i x ih =>
    intro k hb
    exact ⟨rfl, rfl, ih k hb⟩
  | _ => intro k _; exact Expr.ErasedEq.rfl _

/-- **The pin round trip up to erasure**: a bvar-closed term abstracted
over a range and instantiated at variables of those indices is itself
up to erasure — whatever the annotations. -/
theorem instSeq_abstractRange_erasedEq :
    ∀ (ps : List Expr) (d : Nat) {e : Expr},
      (∀ (j : Nat) (x : Expr), ps[j]? = some x → ∃ ty, x = .fvar (d + j) ty) →
      e.looseBVarsBounded 0 = true →
      Expr.ErasedEq (Expr.instSeq ps (ps.length - 1) (e.abstractRange d ps.length 0)) e
  | [], d, e, _, _ => by
    show Expr.ErasedEq (e.abstractRange d 0 0) e
    rw [abstractRange_zero]; exact Expr.ErasedEq.rfl _
  | p :: ps, d, e, hps, hb => by
    obtain ⟨ty, rfl⟩ := hps 0 p rfl
    rw [List.length_cons, abstractRange_succ_outer, Nat.add_sub_cancel]
    show Expr.ErasedEq (Expr.instSeq ps (ps.length + 1 - 1 - 1)
      (((e.abstractRange (d + 1) ps.length 0).abstract1 d (0 + ps.length)).instantiate1
        (.fvar (d + 0) ty) ps.length)) e
    rw [show ps.length + 1 - 1 - 1 = ps.length - 1 by omega, Nat.zero_add]
    have h1 := abstract1_instantiate1_erasedEq (d := d + 0) (ty := ty)
      (e.abstractRange (d + 1) ps.length 0) ps.length
      (by have := looseBVarsBounded_abstractRange e (d + 1) ps.length 0 hb; simpa using this)
    have h2 := instSeq_abstractRange_erasedEq ps (d + 1) (e := e)
      (fun j x hx => by
        obtain ⟨ty', rfl⟩ := hps (j + 1) x (by simpa using hx)
        exact ⟨ty', by rw [show d + 1 + j = d + (j + 1) by omega]⟩) hb
    refine Expr.ErasedEq.trans ?_ h2
    exact instSeq_erasedEq_args ps ps (ps.length - 1) h1 (fun k a₁ a₂ h₁ h₂ => by
      rw [h₁] at h₂; obtain rfl := Option.some.inj h₂; exact Expr.ErasedEq.rfl _) rfl

/-- The run's table at ANY variables of the parameter indices finds
every pin at itself up to erasure. -/
theorem restoreTbl_instAt_lookup_erasedEq {p : NestedParts} {st : ElimState} {ps : List Expr}
    (hnodup : (st.pins.map (·.aux)).Nodup) (hlen : ps.length = p.nP)
    (hshape : ∀ (i : Nat) (x : Expr), ps[i]? = some x → ∃ ty, x = .fvar i ty)
    {q : NestedPin} (hq : q ∈ st.pins) (hclosed : q.pin.looseBVarsBounded 0 = true) :
    ∃ pin', ((restoreTbl p st).instAt ps).pins.lookup q.aux = some pin' ∧
      Expr.ErasedEq pin' q.pin := by
  show ∃ pin', ((st.pins.map fun q => (q.aux, Expr.abstractRange q.pin 0 p.nP 0)).map
      fun q => (q.1, Expr.instSeq ps (ps.length - 1) q.2)).lookup q.aux = some pin' ∧ _
  rw [List.lookup_map_snd, lookup_map_of_nodup hnodup hq]
  refine ⟨_, rfl, ?_⟩
  rw [← hlen]
  exact instSeq_abstractRange_erasedEq ps 0 (fun j x hx => by
    obtain ⟨ty, rfl⟩ := hshape j x hx
    exact ⟨ty, by rw [Nat.zero_add]⟩) hclosed


/-! ## `stripPis` under `instSeq`, inverted -/

/-- A telescope of an `instSeq` at free variables is a telescope of the
term: the instantiation makes no `∀`. -/
theorem stripPis_instSeq_inv {xs : List Expr} (hxs : Expr.AllFvars xs) :
    ∀ (n : Nat) {e : Expr} {bs' : List (Expr × BinderMeta)} {r' : Expr} (t : Nat),
      xs.length ≤ t + 1 → (Expr.instSeq xs t e).stripPis n = some (bs', r') →
      ∃ (bs : List (Expr × BinderMeta)) (r : Expr), e.stripPis n = some (bs, r)
  | 0, e, _, _, _, _, _ => ⟨[], e, rfl⟩
  | n + 1, .forallE dom body bm, bs', r', t, hlen, h => by
    rw [instSeq_forallE _ _ _ _ _ hlen] at h
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₁, r₁⟩, h₁, -⟩ := h
    obtain ⟨bs, r, hs⟩ := stripPis_instSeq_inv hxs n (t + 1) (by omega) h₁
    exact ⟨(dom, bm) :: bs, r, by simp [Expr.stripPis, hs]⟩
  | n + 1, .bvar i, bs', r', t, hlen, h => by
    exfalso
    rcases instSeq_bvar_fvars xs hxs t i with ⟨k, ty, h'⟩ | ⟨j, h'⟩ <;>
      rw [h'] at h <;> simp [Expr.stripPis] at h
  | n + 1, .fvar i ty, bs', r', t, hlen, h => by
    rw [instSeq_eq_self xs t rfl] at h; simp [Expr.stripPis] at h
  | n + 1, .sort u, bs', r', t, hlen, h => by
    rw [instSeq_eq_self xs t rfl] at h; simp [Expr.stripPis] at h
  | n + 1, .const c us, bs', r', t, hlen, h => by
    rw [instSeq_eq_self xs t rfl] at h; simp [Expr.stripPis] at h
  | n + 1, .lit l, bs', r', t, hlen, h => by
    rw [instSeq_eq_self xs t rfl] at h; simp [Expr.stripPis] at h
  | n + 1, .app f a, bs', r', t, hlen, h => by
    rw [instSeq_app] at h; simp [Expr.stripPis] at h
  | n + 1, .lam d b m, bs', r', t, hlen, h => by
    rw [instSeq_lam _ _ _ _ _ hlen] at h; simp [Expr.stripPis] at h
  | n + 1, .letE ty v b, bs', r', t, hlen, h => by
    rw [instSeq_letE _ _ _ _ _ hlen] at h; simp [Expr.stripPis] at h
  | n + 1, .proj s i x, bs', r', t, hlen, h => by
    rw [instSeq_proj] at h; simp [Expr.stripPis] at h

/-- Two openings compose (the `Verify` twin of `Model.openPisAtFvars_add`). -/
theorem openPisAtFvars_add' :
    ∀ (n : Nat) {m : Nat} {e : Expr} {d : Nat} {fvs fvs' : List Expr} {o o' : Expr},
      openPisAtFvars n e d = some (fvs, o) → openPisAtFvars m o (d + n) = some (fvs', o') →
      openPisAtFvars (n + m) e d = some (fvs ++ fvs', o')
  | 0, m, e, d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using h'
  | n + 1, m, .forallE dom body mb, d, fvs, fvs', o, o', h, h' => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs₁ e₁ h₁ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have h'' := openPisAtFvars_add' n h₁
        (by rw [show d + 1 + n = d + (n + 1) from by omega]; exact h')
      rw [show n + 1 + m = n + m + 1 from by omega]
      simp only [openPisAtFvars]
      rw [h'']
      rfl
    · exact nomatch h
  | n + 1, _, .bvar _, _, _, _, _, _, h, _ | n + 1, _, .fvar _ _, _, _, _, _, _, h, _
  | n + 1, _, .sort _, _, _, _, _, _, h, _ | n + 1, _, .const _ _, _, _, _, _, _, h, _
  | n + 1, _, .app _ _, _, _, _, _, _, h, _ | n + 1, _, .lam _ _ _, _, _, _, _, _, h, _
  | n + 1, _, .letE _ _ _, _, _, _, _, _, h, _ | n + 1, _, .lit _, _, _, _, _, _, h, _
  | n + 1, _, .proj _ _ _, _, _, _, _, _, h, _ => by simp [openPisAtFvars] at h

/-! ## The residual through the positivity normalisation -/

/-- `normFieldDomsM` opens the field telescope at the field variables
(each annotated by the ORIGINAL domain) and normalises each domain; the
residual is the opened residual. -/
theorem normFieldDomsM_inv {env : Env} {memberNames : List Name} {F : Nat} :
    ∀ {n i : Nat} {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      normFieldDomsM (m := CheckM) (fueledOps mode F) env memberNames i n e = .ok (bs, r) →
      ∃ fvs : List Expr, openPisAtFvars n e i = some (fvs, r) ∧ bs.length = n
  | 0, i, e, bs, r, h => by
    simp only [normFieldDomsM, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | n + 1, i, e, bs, r, h => by
    match e, h with
    | .forallE dom body bm, h =>
      simp only [normFieldDomsM, bind, Except.bind] at h
      obtain ⟨dom', -, h⟩ := exceptBind_ok h
      obtain ⟨⟨bs₁, r₁⟩, h₁, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨fvs, hop, hlen⟩ := normFieldDomsM_inv h₁
      refine ⟨.fvar i dom :: fvs, ?_, by simp [hlen]⟩
      simp only [openPisAtFvars, hop]
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [normFieldDomsM, throw, throwThe, MonadExceptOf.throw] at h

/-- The body of a closed telescope is the body abstracted over the
telescope's variables. -/
theorem closeTelescope_stripPis :
    ∀ (bs : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      ∃ bs' : List (Expr × BinderMeta),
        (closeTelescope bs i body).stripPis bs.length = some (bs', body.abstractRange i bs.length 0)
  | [], i, body => ⟨[], by simp [closeTelescope, Expr.stripPis, abstractRange_zero]⟩
  | (dom, bm) :: bs, i, body => by
    obtain ⟨bs₁, h₁⟩ := closeTelescope_stripPis bs (i + 1) body
    obtain ⟨bs₂, h₂, -, -⟩ := stripPis_abstract1 (d := i) bs.length 0 h₁
    refine ⟨(dom, bm) :: bs₂, ?_⟩
    rw [List.length_cons, abstractRange_succ_outer]
    simp only [closeTelescope, Expr.stripPis, h₂, Option.map_some, Nat.zero_add]

/-- **Closing then re-opening a telescope is the identity on the body up
to erasure** — no consistency needed, only bvar-closedness of the body. -/
theorem openPisAtFvars_closeTelescope_erasedEq (bs : List (Expr × BinderMeta)) (i : Nat)
    {body : Expr} (hb : body.looseBVarsBounded 0 = true) :
    ∃ (fvs : List Expr) (body' : Expr),
      openPisAtFvars bs.length (closeTelescope bs i body) i = some (fvs, body') ∧
      Expr.ErasedEq body' body ∧ fvs.length = bs.length := by
  obtain ⟨bs', hs⟩ := closeTelescope_stripPis bs i body
  obtain ⟨fvs, body', hop⟩ := openPisAtFvars_of_stripPis' bs.length i hs
  refine ⟨fvs, body', hop, ?_, Verify.openPisAtFvars_length _ hop⟩
  rw [Verify.openPisAtFvars_instSeq bs.length hop hs]
  obtain ⟨-, -, -, hlen, hsh, -⟩ := Verify.openPisAtFvars_stripPis bs.length hop
  have hlen' : fvs.length = bs.length := hlen
  rw [← hlen']
  exact instSeq_abstractRange_erasedEq fvs i (fun j x hx => by
    obtain ⟨ty, hty⟩ := hsh j (by rw [← hlen']; exact (List.getElem?_eq_some_iff.mp hx).1)
    rw [hx] at hty
    exact ⟨ty, Option.some.inj hty⟩) hb

/-- **The residual survives the positivity normalisation** up to
erasure: `normCtorValM` rebuilds the type over the normalised field
domains and the SAME opened residual, and a re-opening is that residual
with re-annotated variables. -/
theorem normCtorValM_residual {env : Env} {memberNames : List Name} {nP nF F : Nat}
    {cvC cvCa cvCa' : ConstantVal}
    (h : normCtorValM (m := CheckM) (fueledOps mode F) env memberNames nP nF cvC cvCa true
      = .ok cvCa')
    {fvsP : List Expr} {crest : Expr} {xFvs : List Expr} {xrest : Expr}
    (hop₁ : openPisAtFvars nP cvCa.type 0 = some (fvsP, crest))
    (hop₂ : openPisAtFvars nF crest nP = some (xFvs, xrest))
    (hb : cvCa.type.looseBVarsBounded 0 = true) :
    ∃ (fvs' : List Expr) (xrest' : Expr),
      openPisAtFvars (nP + nF) cvCa'.type 0 = some (fvs', xrest') ∧ Expr.ErasedEq xrest' xrest := by
  unfold normCtorValM at h
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  obtain ⟨cbs, _⟩ := q
  have hq' := unwrapOr_ok' hq
  try simp only at h
  obtain ⟨r, hr, h⟩ := exceptBind_ok h
  obtain ⟨fvsP', crest'⟩ := r
  have hr' := unwrapOr_ok' hr
  rw [hop₁] at hr'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr')
  try simp only at h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  obtain ⟨fbs, resid⟩ := u
  try simp only at h
  obtain ⟨fvs₂, hop₂', hlenF⟩ := normFieldDomsM_inv hu
  rw [hop₂] at hop₂'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hop₂')
  have hxb : xrest.looseBVarsBounded 0 = true :=
    (Verify.openPisAtFvars_bounded nF hop₂ (Verify.openPisAtFvars_bounded nP hop₁ hb).1).1
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fvsP ++ xFvs, xrest, openPisAtFvars_add' nP hop₁ (by rw [Nat.zero_add]; exact hop₂),
      Expr.ErasedEq.rfl _⟩
  · simp only [if_true] at h
    rw [checkConstantValPre_ok h]
    have hlenP : (List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2))
        fvsP cbs).length = nP := by
      rw [List.length_zipWith, Verify.openPisAtFvars_length _ hop₁, stripPis_length' _ hq']
      exact Nat.min_self _
    obtain ⟨fvs', body', hop, hE, -⟩ := openPisAtFvars_closeTelescope_erasedEq
      (List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2)) fvsP cbs ++ fbs)
      0 hxb
    rw [List.length_append, hlenP, hlenF] at hop
    exact ⟨fvs', body', hop, hE⟩

/-- The pre-graded constructor stage's INPUT is closed and bounded (the
front door validates and returns it). -/
theorem checkMutualCtor_pre_input {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx nF F : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa true = .ok (cvCa, sorts)) :
    cvC.type.hasFvar = false ∧ cvC.type.looseBVarsBounded 0 = true ∧
      cvC.type.constsResolve env = true := by
  unfold checkMutualCtor at h
  simp only [if_true] at h
  obtain ⟨cvCa₀, hfront, -⟩ := exceptBind_ok h
  have hff := FormerFront.of_pre hfront
  rw [checkConstantValPre_ok hfront] at hff
  exact ⟨hff.noFvar, hff.bounded, hff.resolve⟩


/-! ## Erasure equality through an opening -/

/-- Erasure equality transfers bvar bounds. -/
theorem Expr.ErasedEq.looseBVarsBounded_iff :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ → ∀ (k : Nat),
      (e₁.looseBVarsBounded k = true ↔ e₂.looseBVarsBounded k = true)
  | .bvar i, .bvar j, h, k => by
    have : i = j := h
    subst this; exact Iff.rfl
  | .fvar _ _, .fvar _ _, _, _ => Iff.rfl
  | .sort _, .sort _, _, _ => Iff.rfl
  | .const _ _, .const _ _, _, _ => Iff.rfl
  | .lit _, .lit _, _, _ => Iff.rfl
  | .app f a, .app g b, h, k => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    rw [looseBVarsBounded_iff h.1, looseBVarsBounded_iff h.2]
  | .lam _ _ _, .lam _ _ _, h, k => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    rw [looseBVarsBounded_iff h.2.1, looseBVarsBounded_iff h.2.2]
  | .forallE _ _ _, .forallE _ _ _, h, k => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    rw [looseBVarsBounded_iff h.2.1, looseBVarsBounded_iff h.2.2]
  | .letE _ _ _, .letE _ _ _, h, k => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    rw [looseBVarsBounded_iff h.1, looseBVarsBounded_iff h.2.1, looseBVarsBounded_iff h.2.2]
  | .proj _ _ _, .proj _ _ _, h, k => by
    simp only [Expr.looseBVarsBounded]
    exact looseBVarsBounded_iff h.2.2 k

/-- **Erasure equality transfers an opening**: the erasure-equal term
opens at the same variable count to an erasure-equal body, with
erasure-equal openers position by position. -/
theorem openPisAtFvars_erasedEq {n : Nat} {e₁ e₂ : Expr} {d : Nat} {fvs₁ : List Expr}
    {o₁ : Expr} (hE : Expr.ErasedEq e₁ e₂) (hop₁ : openPisAtFvars n e₁ d = some (fvs₁, o₁)) :
    ∃ (fvs₂ : List Expr) (o₂ : Expr), openPisAtFvars n e₂ d = some (fvs₂, o₂) ∧
      Expr.ErasedEq o₁ o₂ ∧ fvs₂.length = fvs₁.length ∧
      ∀ (k : Nat) (x₁ x₂ : Expr), fvs₁[k]? = some x₁ → fvs₂[k]? = some x₂ →
        Expr.ErasedEq x₁.fvarTypeD x₂.fvarTypeD := by
  obtain ⟨bs₁, r₁, hs₁, hlen₁, hsh₁, -⟩ := Verify.openPisAtFvars_stripPis n hop₁
  obtain ⟨bs₂, r₂, hs₂, hlenb, hbs, hr⟩ := Expr.ErasedEq.stripPis_inv n hE.symm hs₁
  obtain ⟨fvs₂, o₂, hop₂⟩ := openPisAtFvars_of_stripPis' n d hs₂
  refine ⟨fvs₂, o₂, hop₂, ?_, by rw [Verify.openPisAtFvars_length n hop₂, hlen₁], ?_⟩
  · rw [Verify.openPisAtFvars_instSeq n hop₁ hs₁, Verify.openPisAtFvars_instSeq n hop₂ hs₂]
    refine instSeq_erasedEq_args _ _ _ hr.symm ?_ ?_
    · intro k x₁ x₂ hx₁ hx₂
      obtain ⟨-, -, -, -, hsh₂, -⟩ := Verify.openPisAtFvars_stripPis n hop₂
      have hk : k < n := by rw [← hlen₁]; exact (List.getElem?_eq_some_iff.mp hx₁).1
      obtain ⟨t₁, ht₁⟩ := hsh₁ k hk
      obtain ⟨t₂, ht₂⟩ := hsh₂ k hk
      rw [hx₁] at ht₁
      rw [hx₂] at ht₂
      obtain rfl := Option.some.inj ht₁
      obtain rfl := Option.some.inj ht₂
      show d + k = d + k
      rfl
    · rw [Verify.openPisAtFvars_length n hop₂, hlen₁]
  · exact openers_erasedEq hop₁ hop₂ hs₁ hs₂ fun k b₁ b₂ hb₁ hb₂ => (hbs k b₂ b₁ hb₂ hb₁).1.symm

/-- **Erasure-equal terms are equal when one side's leaves are all
openers below `nP` and the other side's leaves below `nP` are openers.** -/
theorem Expr.ErasedEq.eq_of_leaves_below {params : List Expr} {nP : Nat}
    (hshape : ∀ (i : Nat) (x : Expr), params[i]? = some x → ∃ ty, x = .fvar i ty) :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
      (∀ l ∈ e₁.fvarLeaves, l.1 < nP → Expr.fvar l.1 l.2 ∈ params) →
      (∀ l ∈ e₂.fvarLeaves, l.1 < nP ∧ Expr.fvar l.1 l.2 ∈ params) →
      e₁ = e₂
  | .bvar _, .bvar _, h, _, _ => by rw [h]
  | .fvar i ty, .fvar j ty', h, h₁, h₂ => by
    have hij : i = j := h
    subst hij
    have hm₂ := h₂ (i, ty') (by simp [Expr.fvarLeaves])
    have hm₁ : Expr.fvar i ty ∈ params := h₁ (i, ty) (by simp [Expr.fvarLeaves]) hm₂.1
    obtain ⟨k₁, hk₁⟩ := List.getElem?_of_mem hm₁
    obtain ⟨k₂, hk₂⟩ := List.getElem?_of_mem hm₂.2
    obtain ⟨t₁, ht₁⟩ := hshape k₁ _ hk₁
    obtain ⟨t₂, ht₂⟩ := hshape k₂ _ hk₂
    have e1 : k₁ = i := (Expr.fvar.inj ht₁).1.symm
    have e2 : k₂ = i := (Expr.fvar.inj ht₂).1.symm
    subst e1
    subst e2
    rw [hk₁] at hk₂
    rw [(Expr.fvar.inj (Option.some.inj hk₂)).2]
  | .sort _, .sort _, h, _, _ => by rw [h]
  | .const _ _, .const _ _, h, _, _ => by rw [h.1, h.2]
  | .app f a, .app g b, h, h₁, h₂ => by
    simp only [Expr.fvarLeaves, List.mem_append] at h₁ h₂
    rw [eq_of_leaves_below hshape h.1 (fun l hl => h₁ l (Or.inl hl)) (fun l hl => h₂ l (Or.inl hl)),
      eq_of_leaves_below hshape h.2 (fun l hl => h₁ l (Or.inr hl)) (fun l hl => h₂ l (Or.inr hl))]
  | .lam _ _ _, .lam _ _ _, h, h₁, h₂ => by
    simp only [Expr.fvarLeaves, List.mem_append] at h₁ h₂
    rw [h.1, eq_of_leaves_below hshape h.2.1 (fun l hl => h₁ l (Or.inl hl)) (fun l hl => h₂ l (Or.inl hl)),
      eq_of_leaves_below hshape h.2.2 (fun l hl => h₁ l (Or.inr hl)) (fun l hl => h₂ l (Or.inr hl))]
  | .forallE _ _ _, .forallE _ _ _, h, h₁, h₂ => by
    simp only [Expr.fvarLeaves, List.mem_append] at h₁ h₂
    rw [h.1, eq_of_leaves_below hshape h.2.1 (fun l hl => h₁ l (Or.inl hl)) (fun l hl => h₂ l (Or.inl hl)),
      eq_of_leaves_below hshape h.2.2 (fun l hl => h₁ l (Or.inr hl)) (fun l hl => h₂ l (Or.inr hl))]
  | .letE _ _ _, .letE _ _ _, h, h₁, h₂ => by
    simp only [Expr.fvarLeaves, List.mem_append] at h₁ h₂
    rw [eq_of_leaves_below hshape h.1 (fun l hl => h₁ l (Or.inl (Or.inl hl)))
        (fun l hl => h₂ l (Or.inl (Or.inl hl))),
      eq_of_leaves_below hshape h.2.1 (fun l hl => h₁ l (Or.inl (Or.inr hl)))
        (fun l hl => h₂ l (Or.inl (Or.inr hl))),
      eq_of_leaves_below hshape h.2.2 (fun l hl => h₁ l (Or.inr hl)) (fun l hl => h₂ l (Or.inr hl))]
  | .lit _, .lit _, h, _, _ => by rw [h]
  | .proj s i x, .proj s' i' x', h, h₁, h₂ => by
    simp only [Expr.fvarLeaves] at h₁ h₂
    rw [h.1, h.2.1, eq_of_leaves_below hshape h.2.2 h₁ h₂]

/-- A blind mention of a telescope's body is a blind mention of the term. -/
theorem Expr.stripPis_mentionsConstE {T : Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → body.mentionsConstE T = true → e.mentionsConstE T = true
  | 0, e, bs, body, h, hm => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]; exact hm
  | n + 1, .forallE ty b m, bs, body, h, hm => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs⟩ := h
    simp only [Prod.mk.injEq] at hbs
    obtain ⟨-, rfl⟩ := hbs
    simp only [Expr.mentionsConstE, Bool.or_eq_true]
    exact Or.inr (Expr.stripPis_mentionsConstE n h₀ hm)
  | n + 1, .bvar _, _, _, h, _ | n + 1, .fvar _ _, _, _, h, _ | n + 1, .sort _, _, _, h, _
  | n + 1, .const _ _, _, _, h, _ | n + 1, .app _ _, _, _, h, _ | n + 1, .lam _ _ _, _, _, h, _
  | n + 1, .letE _ _ _, _, _, h, _ | n + 1, .lit _, _, _, h, _ | n + 1, .proj _ _ _, _, _, h, _ =>
    by simp [Expr.stripPis] at h

/-- The generic openers are variables. -/
theorem openFvars_allFvars (d k : Nat) : Expr.AllFvars (Verify.openFvars d k) := by
  intro a ha
  obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
  have hjn : j < k := by rw [← Verify.openFvars_length d k]; exact (List.getElem?_eq_some_iff.mp hj).1
  rw [Verify.openFvars_getElem? hjn] at hj
  exact ⟨_, _, (Option.some.inj hj).symm⟩

/-! ## Blind mentions through an opening -/

/-- A blind mention of an opened body or of an opener's annotation is a
blind mention of the term. -/
theorem openPisAtFvars_mentionsConstE {T : Name} :
    ∀ (k : Nat) (e : Expr) (j : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars k e j = some (fvs, body) →
      (body.mentionsConstE T = true ∨ ∃ x ∈ fvs, x.fvarTypeD.mentionsConstE T = true) →
      e.mentionsConstE T = true
  | 0, e, j, fvs, body, h, hm => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hm with hm | ⟨x, hx, -⟩
    · exact hm
    · exact nomatch hx
  | k + 1, .forallE dom b bm, j, fvs, body, h, hm => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs' body' hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.mentionsConstE, Bool.or_eq_true]
      rcases hm with hm | ⟨x, hx, hxm⟩
      · have := openPisAtFvars_mentionsConstE k _ _ hrec (Or.inl hm)
        rw [Expr.mentionsConstE_instantiate1_fvar] at this
        exact Or.inr this
      · rcases List.mem_cons.mp hx with rfl | hx'
        · exact Or.inl hxm
        · have := openPisAtFvars_mentionsConstE k _ _ hrec (Or.inr ⟨x, hx', hxm⟩)
          rw [Expr.mentionsConstE_instantiate1_fvar] at this
          exact Or.inr this
    · exact nomatch h
  | k + 1, .bvar _, _, _, _, h, _ | k + 1, .fvar _ _, _, _, _, h, _ | k + 1, .sort _, _, _, _, h, _
  | k + 1, .const _ _, _, _, _, h, _ | k + 1, .app _ _, _, _, _, h, _
  | k + 1, .lam _ _ _, _, _, _, h, _ | k + 1, .letE _ _ _, _, _, _, h, _
  | k + 1, .lit _, _, _, _, h, _ | k + 1, .proj _ _ _, _, _, _, h, _ => by
    simp [openPisAtFvars] at h

/-- A term blind-mentions a name only through its opened body or an
opener's annotation. -/
theorem mentionsConstE_of_openPis {T : Name} :
    ∀ (k : Nat) (e : Expr) (j : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars k e j = some (fvs, body) → e.mentionsConstE T = true →
      body.mentionsConstE T = true ∨ ∃ x ∈ fvs, x.fvarTypeD.mentionsConstE T = true
  | 0, e, j, fvs, body, h, hm => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl hm
  | k + 1, .forallE dom b bm, j, fvs, body, h, hm => by
    simp only [openPisAtFvars] at h
    split at h
    · next fvs' body' hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.mentionsConstE, Bool.or_eq_true] at hm
      rcases hm with hm | hm
      · exact Or.inr ⟨.fvar j dom, List.mem_cons_self, hm⟩
      · have hm' : (b.instantiate1 (.fvar j dom)).mentionsConstE T = true := by
          rw [Expr.mentionsConstE_instantiate1_fvar]; exact hm
        rcases mentionsConstE_of_openPis k _ _ hrec hm' with h1 | ⟨x, hx, hxm⟩
        · exact Or.inl h1
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hxm⟩
    · exact nomatch h
  | k + 1, .bvar _, _, _, _, h, _ | k + 1, .fvar _ _, _, _, _, h, _ | k + 1, .sort _, _, _, _, h, _
  | k + 1, .const _ _, _, _, _, h, _ | k + 1, .app _ _, _, _, _, h, _
  | k + 1, .lam _ _ _, _, _, _, h, _ | k + 1, .letE _ _ _, _, _, _, h, _
  | k + 1, .lit _, _, _, _, h, _ | k + 1, .proj _ _ _, _, _, _, h, _ => by
    simp [openPisAtFvars] at h

/-- The blind mentions of a spine: the head or an argument. -/
theorem mentionsConstE_mkAppN_iff {T : Name} :
    ∀ (args : List Expr) (f : Expr),
      (Expr.mkAppN f args).mentionsConstE T = true ↔
        f.mentionsConstE T = true ∨ ∃ a ∈ args, a.mentionsConstE T = true
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    show (Expr.mkAppN (.app f a) as).mentionsConstE T = true ↔ _
    rw [mentionsConstE_mkAppN_iff as]
    simp only [Expr.mentionsConstE, Bool.or_eq_true, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨b, hb, hbm⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, h⟩
      · exact Or.inr ⟨b, Or.inr hb, hbm⟩
    · rintro (h | ⟨b, rfl | hb, hbm⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hbm)
      · exact Or.inr ⟨b, hb, hbm⟩

/-- The blind mentions of a constant-headed spine: the head or an argument. -/
theorem mentionsConstE_mkAppN_const_iff {T : Name} (c : Name) (us : List Level) (args : List Expr) :
    (Expr.mkAppN (.const c us) args).mentionsConstE T = true ↔
      c = T ∨ ∃ a ∈ args, a.mentionsConstE T = true := by
  rw [mentionsConstE_mkAppN_iff]
  simp [Expr.mentionsConstE]

/-! ## K.15's group coherence, read -/

/-- Every member of a recovered group recovers a group of the same
parameter count and the same member names. -/
theorem containerGroupOk_inv {env : Env} {ci : ContainerInfo}
    (h : containerGroupOk env ci = true) :
    ∀ J ∈ ci.members, ∃ ci' : ContainerInfo, containerInfo? env J.name = some ci' ∧
      ci'.nP = ci.nP ∧ ci'.members.map (·.name) = ci.members.map (·.name) := by
  intro J hJ
  unfold containerGroupOk at h
  rw [List.all_eq_true] at h
  have := h J hJ
  cases hci : containerInfo? env J.name with
  | none => rw [hci] at this; exact nomatch this
  | some ci' =>
    rw [hci] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨ci', rfl, this.1, this.2⟩

/-- The containers' facts at every pin (K.14/K.15), read: the pin's
container recovers a group whose facts hold. -/
theorem nestedContainersOk_inv' {env : Env} {pins : List NestedPin}
    (h : nestedContainersOk env pins = true) :
    (pins.map (·.pin)).Nodup ∧
    ∀ q ∈ pins, ∃ ci : ContainerInfo, containerInfo? env q.container = some ci ∧
      containerGroupOk env ci = true := by
  unfold nestedContainersOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨of_decide_eq_true h.1, fun q hq => ?_⟩
  have := h.2 q hq
  cases hci : containerInfo? env q.container with
  | none => rw [hci] at this; exact nomatch this
  | some ci =>
    rw [hci] at this
    refine ⟨ci, rfl, ?_⟩
    unfold containerFactsOk at this
    rw [Bool.and_eq_true] at this
    exact this.1


/-! ## Closedness through the two walks -/

/-- **The walk's output is bvar-bounded as its input**: a fire's output
is the copy at the (closed) parameters and the input's own index
arguments. -/
theorem replaceAllNested_looseBVarsBounded {env : Env} {blvls : List Level} {params : List Expr}
    {pbs : List (Expr × BinderMeta)} (hparC : ∀ p ∈ params, p.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) {st st' : ElimState} {e' : Expr} {k : Nat},
      replaceAllNested env blvls params pbs st e = .ok (e', st') →
      e.looseBVarsBounded k = true → e'.looseBVarsBounded k = true
  | .app f a, st, st', e', k, h, he => by
    rcases replaceAllNested_app' h with ⟨rfl, -⟩ | hfire | ⟨-, f', a', st₁, hf, ha, rfl⟩
    · exact he
    · obtain ⟨I, lvls, ci, aux, -, -, -, hr, -⟩ := replaceIfNested_some hfire
      rw [hr]
      refine looseBVarsBounded_mkAppN (looseBVarsBounded_mkAppN rfl
        (fun x hx => looseBVarsBounded_mono (Nat.zero_le k) (hparC x hx))) ?_
      intro x hx
      exact (looseBVarsBounded_mkAppN_args (f := (Expr.app f a).getAppFn)
        (args := (Expr.app f a).getAppArgs) (by rw [Expr.mkAppN_getApp]; exact he)).2 x
        (List.mem_of_mem_drop hx)
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
      exact ⟨replaceAllNested_looseBVarsBounded hparC f hf he.1,
        replaceAllNested_looseBVarsBounded hparC a ha he.2⟩
  | .lam ty b bm, st, st', e', k, h, he => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_lam h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨replaceAllNested_looseBVarsBounded hparC ty hty he.1,
      replaceAllNested_looseBVarsBounded hparC b hb he.2⟩
  | .forallE ty b bm, st, st', e', k, h, he => by
    obtain ⟨ty', b', st₁, hty, hb, rfl⟩ := replaceAllNested_forallE h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨replaceAllNested_looseBVarsBounded hparC ty hty he.1,
      replaceAllNested_looseBVarsBounded hparC b hb he.2⟩
  | .letE ty v b, st, st', e', k, h, he => by
    obtain ⟨ty', v', b', st₁, st₂, hty, hv, hb, rfl⟩ := replaceAllNested_letE h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he ⊢
    exact ⟨⟨replaceAllNested_looseBVarsBounded hparC ty hty he.1.1,
      replaceAllNested_looseBVarsBounded hparC v hv he.1.2⟩,
      replaceAllNested_looseBVarsBounded hparC b hb he.2⟩
  | .proj s i x, st, st', e', k, h, he => by
    obtain ⟨x', hx, rfl⟩ := replaceAllNested_proj h
    simp only [Expr.looseBVarsBounded] at he ⊢
    exact replaceAllNested_looseBVarsBounded hparC x hx he
  | .bvar i, st, st', e', k, h, he => by
    rw [replaceAllNested_bvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .fvar i ty, st, st', e', k, h, he => by
    rw [replaceAllNested_fvar] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .sort u, st, st', e', k, h, he => by
    rw [replaceAllNested_sort] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .const c vs, st, st', e', k, h, he => by
    rw [replaceAllNested_const] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he
  | .lit l, st, st', e', k, h, he => by
    rw [replaceAllNested_lit] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
    exact he

/-- The raw restore's node step answers a closed term on a closed input. -/
theorem restoreNode_closed {R : RestoreTbl}
    (hpF : ∀ q ∈ R.pins, q.2.hasFvar = false) (hcF : ∀ q ∈ R.ctorPins, q.2.1.hasFvar = false)
    (hpB : ∀ q ∈ R.pins, q.2.looseBVarsBounded R.nP = true)
    (hcB : ∀ q ∈ R.ctorPins, q.2.1.looseBVarsBounded R.nP = true)
    {d : Nat} {e x : Expr} (h : restoreNode R d e = .ok (some x))
    (hF : e.hasFvar = false) (hB : e.looseBVarsBounded (R.nP + d) = true) :
    x.hasFvar = false ∧ x.looseBVarsBounded (R.nP + d) = true := by
  have hargsB : ∀ a ∈ e.getAppArgs, a.looseBVarsBounded (R.nP + d) = true :=
    (looseBVarsBounded_mkAppN_args (f := e.getAppFn) (args := e.getAppArgs)
      (by rw [Expr.mkAppN_getApp]; exact hB)).2
  rcases restoreNode_ok_inv h with ⟨n, us, n', rfl, -, hx⟩ | ⟨-, hh⟩
  · obtain rfl := Option.some.inj hx
    exact ⟨rfl, rfl⟩
  · rcases restoreHead_ok_inv hh with ⟨-, hx⟩ | ⟨n, us, -, hcase⟩
    · exact nomatch hx
    · rcases hcase with ⟨pin, hl, -, hx⟩ | ⟨-, q, hq, -, J, ilvls, -, hx⟩ | ⟨-, -, hx⟩
      · obtain rfl := Option.some.inj hx
        have hpin := List.mem_of_lookup_some hl
        refine ⟨hasFvar_mkAppN _ _ (by rw [hasFvar_liftLooseBVars]; exact hpF _ hpin)
          (fun a ha => hasFvar_getAppArgs hF a (List.mem_of_mem_drop ha)), ?_⟩
        exact looseBVarsBounded_mkAppN (Expr.looseBVarsBounded_liftLooseBVars d _ (hpB _ hpin))
          (fun a ha => hargsB a (List.mem_of_mem_drop ha))
      · obtain rfl := Option.some.inj hx
        have hqmem := List.mem_of_find?_eq_some hq
        have hnF : (q.2.1.liftLooseBVars d 0).hasFvar = false := by
          rw [hasFvar_liftLooseBVars]; exact hcF q hqmem
        have hnB : (q.2.1.liftLooseBVars d 0).looseBVarsBounded (R.nP + d) = true :=
          Expr.looseBVarsBounded_liftLooseBVars d _ (hcB q hqmem)
        refine ⟨hasFvar_mkAppN _ _ (hasFvar_mkAppN _ _ rfl (fun a ha => hasFvar_getAppArgs hnF a ha))
          (fun a ha => hasFvar_getAppArgs hF a (List.mem_of_mem_drop ha)), ?_⟩
        refine looseBVarsBounded_mkAppN (looseBVarsBounded_mkAppN rfl (fun a ha => ?_))
          (fun a ha => hargsB a (List.mem_of_mem_drop ha))
        exact (looseBVarsBounded_mkAppN_args (f := (q.2.1.liftLooseBVars d 0).getAppFn)
          (args := (q.2.1.liftLooseBVars d 0).getAppArgs)
          (by rw [Expr.mkAppN_getApp]; exact hnB)).2 a ha
      · exact nomatch hx

/-- **The raw restore keeps a closed term closed**: fvar-free and
bvar-bounded below the parameter count plus the depth. -/
theorem restoreWalk_closed {R : RestoreTbl}
    (hpF : ∀ q ∈ R.pins, q.2.hasFvar = false) (hcF : ∀ q ∈ R.ctorPins, q.2.1.hasFvar = false)
    (hpB : ∀ q ∈ R.pins, q.2.looseBVarsBounded R.nP = true)
    (hcB : ∀ q ∈ R.ctorPins, q.2.1.looseBVarsBounded R.nP = true) :
    ∀ (e : Expr) {d : Nat} {e' : Expr}, restoreWalk R d e = .ok e' →
      e.hasFvar = false → e.looseBVarsBounded (R.nP + d) = true →
      e'.hasFvar = false ∧ e'.looseBVarsBounded (R.nP + d) = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro d e' h hF hB
    unfold restoreWalk at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hF, hB⟩
    · split at h
      · exact nomatch h
      · next x hx =>
        obtain rfl := Except.ok.inj h
        exact restoreNode_closed hpF hcF hpB hcB hx hF hB
      · simp only at h
        split at h
        · exact nomatch h
        · next f' hf =>
          split at h
          · exact nomatch h
          · next a' ha =>
            obtain rfl := Except.ok.inj h
            simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hF
            simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hB ⊢
            obtain ⟨hf₁, hf₂⟩ := ihf hf hF.1 hB.1
            obtain ⟨ha₁, ha₂⟩ := iha ha hF.2 hB.2
            exact ⟨by simp [Expr.hasFvar, hf₁, ha₁], hf₂, ha₂⟩
  | lam ty b bm ihty ihb =>
    intro d e' h hF hB
    unfold restoreWalk at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hF, hB⟩
    · split at h
      · exact nomatch h
      · next x hx =>
        obtain rfl := Except.ok.inj h
        exact restoreNode_closed hpF hcF hpB hcB hx hF hB
      · simp only at h
        split at h
        · exact nomatch h
        · next ty' hty =>
          split at h
          · exact nomatch h
          · next b' hb =>
            obtain rfl := Except.ok.inj h
            simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hF
            simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hB ⊢
            obtain ⟨h₁, h₂⟩ := ihty hty hF.1 hB.1
            obtain ⟨h₃, h₄⟩ := ihb hb hF.2 (by rw [Nat.add_assoc] at hB; exact hB.2)
            exact ⟨by simp [Expr.hasFvar, h₁, h₃], h₂, by rw [Nat.add_assoc]; exact h₄⟩
  | forallE ty b bm ihty ihb =>
    intro d e' h hF hB
    unfold restoreWalk at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hF, hB⟩
    · split at h
      · exact nomatch h
      · next x hx =>
        obtain rfl := Except.ok.inj h
        exact restoreNode_closed hpF hcF hpB hcB hx hF hB
      · simp only at h
        split at h
        · exact nomatch h
        · next ty' hty =>
          split at h
          · exact nomatch h
          · next b' hb =>
            obtain rfl := Except.ok.inj h
            simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hF
            simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hB ⊢
            obtain ⟨h₁, h₂⟩ := ihty hty hF.1 hB.1
            obtain ⟨h₃, h₄⟩ := ihb hb hF.2 (by rw [Nat.add_assoc] at hB; exact hB.2)
            exact ⟨by simp [Expr.hasFvar, h₁, h₃], h₂, by rw [Nat.add_assoc]; exact h₄⟩
  | letE ty v b ihty ihv ihb =>
    intro d e' h hF hB
    unfold restoreWalk at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hF, hB⟩
    · split at h
      · exact nomatch h
      · next x hx =>
        obtain rfl := Except.ok.inj h
        exact restoreNode_closed hpF hcF hpB hcB hx hF hB
      · simp only at h
        split at h
        · exact nomatch h
        · next ty' hty =>
          split at h
          · exact nomatch h
          · next v' hv =>
            split at h
            · exact nomatch h
            · next b' hb =>
              obtain rfl := Except.ok.inj h
              simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hF
              simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hB ⊢
              obtain ⟨h₁, h₂⟩ := ihty hty hF.1.1 hB.1.1
              obtain ⟨h₃, h₄⟩ := ihv hv hF.1.2 hB.1.2
              obtain ⟨h₅, h₆⟩ := ihb hb hF.2 (by rw [Nat.add_assoc] at hB; exact hB.2)
              exact ⟨by simp [Expr.hasFvar, h₁, h₃, h₅], ⟨h₂, h₄⟩, by rw [Nat.add_assoc]; exact h₆⟩
  | proj s i x ih =>
    intro d e' h hF hB
    unfold restoreWalk at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hF, hB⟩
    · split at h
      · exact nomatch h
      · next y hy =>
        obtain rfl := Except.ok.inj h
        exact restoreNode_closed hpF hcF hpB hcB hy hF hB
      · simp only at h
        split at h
        · exact nomatch h
        · next x' hx =>
          obtain rfl := Except.ok.inj h
          simp only [Expr.hasFvar] at hF
          simp only [Expr.looseBVarsBounded] at hB ⊢
          obtain ⟨h₁, h₂⟩ := ih hx hF hB
          exact ⟨by simp [Expr.hasFvar, h₁], h₂⟩
  | _ =>
    intro d e' h hF hB
    unfold restoreWalk at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨hF, hB⟩
    · split at h
      · exact nomatch h
      · next x hx =>
        obtain rfl := Except.ok.inj h
        exact restoreNode_closed hpF hcF hpB hcB hx hF hB
      · simp only at h
        obtain rfl := Except.ok.inj h
        exact ⟨hF, hB⟩

/-- The bounds of a telescope's pieces from the whole's. -/
theorem looseBVarsBounded_stripPis :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr} {k : Nat},
      e.stripPis n = some (bs, body) → e.looseBVarsBounded k = true →
      (∀ (j : Nat) (b : Expr × BinderMeta), bs[j]? = some b → b.1.looseBVarsBounded (k + j) = true) ∧
      body.looseBVarsBounded (k + n) = true
  | 0, e, bs, body, k, h, he => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun j b hb => (nomatch hb), he⟩
  | n + 1, .forallE dom b bm, bs, body, k, h, he => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs⟩ := h
    simp only [Prod.mk.injEq] at hbs
    obtain ⟨rfl, rfl⟩ := hbs
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at he
    obtain ⟨hall, hbody⟩ := looseBVarsBounded_stripPis n (k := k + 1) h₀ he.2
    refine ⟨fun j bb hb => ?_, by rw [show k + (n + 1) = k + 1 + n by omega]; exact hbody⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      exact he.1
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb
      rw [show k + (j + 1) = k + 1 + j by omega]
      exact hall j bb hb
  | n + 1, .bvar _, _, _, _, h, _ | n + 1, .fvar _ _, _, _, _, h, _ | n + 1, .sort _, _, _, _, h, _
  | n + 1, .const _ _, _, _, _, h, _ | n + 1, .app _ _, _, _, _, h, _
  | n + 1, .lam _ _ _, _, _, _, h, _ | n + 1, .letE _ _ _, _, _, _, h, _
  | n + 1, .lit _, _, _, _, h, _ | n + 1, .proj _ _ _, _, _, _, h, _ => by
    simp [Expr.stripPis] at h

/-- A telescope of fvar-free pieces is fvar-free. -/
theorem hasFvar_of_stripPis :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) → (∀ b ∈ bs, b.1.hasFvar = false) →
      body.hasFvar = false → e.hasFvar = false
  | 0, e, bs, body, h, _, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hb
  | n + 1, .forallE dom b bm, bs, body, h, hbs, hb => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs'⟩ := h
    simp only [Prod.mk.injEq] at hbs'
    obtain ⟨rfl, rfl⟩ := hbs'
    simp only [Expr.hasFvar, Bool.or_eq_false_iff]
    exact ⟨hbs _ List.mem_cons_self,
      hasFvar_of_stripPis n h₀ (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb')) hb⟩
  | n + 1, .bvar _, _, _, h, _, _ | n + 1, .fvar _ _, _, _, h, _, _ | n + 1, .sort _, _, _, h, _, _
  | n + 1, .const _ _, _, _, h, _, _ | n + 1, .app _ _, _, _, h, _, _
  | n + 1, .lam _ _ _, _, _, h, _, _ | n + 1, .letE _ _ _, _, _, h, _, _
  | n + 1, .lit _, _, _, h, _, _ | n + 1, .proj _ _ _, _, _, h, _, _ => by
    simp [Expr.stripPis] at h

/-- A telescope of bounded pieces is bounded. -/
theorem looseBVarsBounded_of_stripPis :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr} {k : Nat},
      e.stripPis n = some (bs, body) →
      (∀ (j : Nat) (b : Expr × BinderMeta), bs[j]? = some b → b.1.looseBVarsBounded (k + j) = true) →
      body.looseBVarsBounded (k + n) = true → e.looseBVarsBounded k = true
  | 0, e, bs, body, k, h, _, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hb
  | n + 1, .forallE dom b bm, bs, body, k, h, hbs, hb => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs₀, body₀⟩, h₀, hbs'⟩ := h
    simp only [Prod.mk.injEq] at hbs'
    obtain ⟨rfl, rfl⟩ := hbs'
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨by have := hbs 0 (dom, bm) rfl; simpa using this, ?_⟩
    refine looseBVarsBounded_of_stripPis n (k := k + 1) h₀ (fun j bb hbb => ?_) ?_
    · have := hbs (j + 1) bb (by simpa using hbb)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    · rwa [show k + (n + 1) = k + 1 + n by omega] at hb
  | n + 1, .bvar _, _, _, _, h, _, _ | n + 1, .fvar _ _, _, _, _, h, _, _
  | n + 1, .sort _, _, _, _, h, _, _ | n + 1, .const _ _, _, _, _, h, _, _
  | n + 1, .app _ _, _, _, _, h, _, _ | n + 1, .lam _ _ _, _, _, _, h, _, _
  | n + 1, .letE _ _ _, _, _, _, h, _, _ | n + 1, .lit _, _, _, _, h, _, _
  | n + 1, .proj _ _ _, _, _, _, h, _, _ => by
    simp [Expr.stripPis] at h

/-- **The restored constant is closed**: `restoreNested` of a closed
constant with closed pins is fvar-free and bvar-closed (the leading
binders come back, the body walked at depth `0` under them). -/
theorem restoreNested_closed {R : RestoreTbl}
    (hpF : ∀ q ∈ R.pins, q.2.hasFvar = false) (hcF : ∀ q ∈ R.ctorPins, q.2.1.hasFvar = false)
    (hpB : ∀ q ∈ R.pins, q.2.looseBVarsBounded R.nP = true)
    (hcB : ∀ q ∈ R.ctorPins, q.2.1.looseBVarsBounded R.nP = true)
    {e e' : Expr} (h : restoreNested R e = .ok e') {bs : List (Expr × BinderMeta)} {body : Expr}
    (hs : e.stripPis R.nP = some (bs, body)) (hF : e.hasFvar = false)
    (hB : e.looseBVarsBounded 0 = true) :
    e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true := by
  obtain ⟨body', hw, hs'⟩ := restoreNested_stripPis h hs
  obtain ⟨hbsF, hbodyF⟩ := stripPis_not_hasFvar R.nP hs hF
  have hbodyB : body.looseBVarsBounded R.nP = true := by
    have := (looseBVarsBounded_stripPis R.nP hs hB).2
    rwa [Nat.zero_add] at this
  obtain ⟨hF', hB'⟩ := restoreWalk_closed hpF hcF hpB hcB body hw hbodyF
    (by rw [Nat.add_zero]; exact hbodyB)
  rw [Nat.add_zero] at hB'
  refine ⟨hasFvar_of_stripPis R.nP hs' hbsF hF', looseBVarsBounded_of_stripPis R.nP hs'
    (looseBVarsBounded_stripPis R.nP hs hB).1 ?_⟩
  rw [Nat.zero_add]
  exact hB'

end ConLeche
