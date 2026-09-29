module

public import ConLeche.Model.Inductives.TargetRecRead
public import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Verify.Abstract
import ConLeche.Verify.InstList

public section

/-!
# A field's normal form: a Π-tower over its leaf

The positivity walk returns, for a field, its NORMAL FORM: the whnf'd
Π-binders the `pi` rule passed (each domain hole-free), closed back over
the leaf the last rule met (`posD_field_leaf`).  The leaf is one of the
field kinds the calls land at: a member hole at the block's parameters,
a frame's hole at its key, a container instance (its node), or — no
member and no hole — a constant type (`FieldLeaf`).  The tower is a
syntactic `Expr.mkPisOf`, and its body opened at the variables the walk
opened it at is the leaf, up to erasure.
-/

namespace ConLeche.Model
open ConLeche (Env Expr Name Level NestCtx NestHole NestKey BinderMeta PosD PosJ NestFieldKind PosTree
  CheckerOps CheckM nestArity nestContainer)

/-! ## Towers, closed and opened -/

/-- Closing a tower's variable closes its domains and body, each below
the binders passed. -/
@[expose] def absTele (d : Nat) : Nat → List (Expr × BinderMeta) → List (Expr × BinderMeta)
  | _, [] => []
  | k, (t, bm) :: r => (t.abstract1 d k, bm) :: absTele d (k + 1) r

theorem absTele_length (d : Nat) : ∀ (k : Nat) (tele : List (Expr × BinderMeta)),
    (absTele d k tele).length = tele.length
  | _, [] => rfl
  | k, (_, _) :: r => by simp [absTele, absTele_length d (k + 1) r]

theorem mkPisOf_abstract1 (d : Nat) :
    ∀ (tele : List (Expr × BinderMeta)) (X : Expr) (k : Nat),
      (Expr.mkPisOf tele X).abstract1 d k
        = Expr.mkPisOf (absTele d k tele) (X.abstract1 d (k + tele.length))
  | [], X, k => by simp [Expr.mkPisOf, absTele]
  | (t, bm) :: r, X, k => by
    simp only [Expr.mkPisOf, Expr.abstract1, absTele, mkPisOf_abstract1 d r X (k + 1),
      List.length_cons]
    rw [show k + 1 + r.length = k + (r.length + 1) from by omega]

theorem looseBVarsBounded_mkPisOf_body :
    ∀ (tele : List (Expr × BinderMeta)) (X : Expr) (k : Nat),
      (Expr.mkPisOf tele X).looseBVarsBounded k = true → X.looseBVarsBounded (k + tele.length) = true
  | [], X, k, h => by simpa [Expr.mkPisOf] using h
  | (t, bm) :: r, X, k, h => by
    simp only [Expr.mkPisOf, Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have := looseBVarsBounded_mkPisOf_body r X (k + 1) h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem erasedEq_instantiateList : ∀ (vs : List Expr) {e e' : Expr} (d : Nat),
    Expr.ErasedEq e e' → Expr.ErasedEq (e.instantiateList vs d) (e'.instantiateList vs d)
  | [], e, e', d, h => by rw [Expr.instantiateList_nil, Expr.instantiateList_nil]; exact h
  | v :: vs, e, e', d, h => by
    rw [Expr.instantiateList_cons, Expr.instantiateList_cons]
    exact Expr.ErasedEq.instantiate1 (erasedEq_instantiateList vs (d + 1) h) (Expr.ErasedEq.rfl v)

/-- **Opening a closed binder at its own variable** gives the term back,
up to erasure: the last opener is the variable `abstract1` closed. -/
theorem abstract1_instantiateList_erasedEq {d n : Nat} {X : Expr} (hX : X.looseBVarsBounded n = true)
    {os : List Expr} (hos : os.length = n) (ty : Expr) :
    Expr.ErasedEq ((X.abstract1 d n).instantiateList (os ++ [.fvar d ty]) 0) (X.instantiateList os 0) := by
  rw [Expr.instantiateList_append_one, Nat.zero_add, hos]
  exact erasedEq_instantiateList os 0 (erasedEq_abstract1_instantiate1 X n hX)

/-! ## The leaf -/

section Leaf

variable (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)

/-- **A field's leaf** `w` at the frames `prog`: the last rule of its
derivation — a member hole at the block's parameters (hole-free indices,
full arity), a frame's hole at its key (hole-free indices, full arity), a
container instance whose node `u` (keyed by it) is among `ts`, or a term
naming no member and no hole. -/
@[expose] def FieldLeaf (prog : List NestHole) (w : Expr) (ts : List PosTree) : Prop :=
  (∃ i ty, w.getAppFn = .fvar i ty ∧ ctx.nP ≤ i ∧ i < ctx.hiAt 0 ∧
    w.getAppArgs.length = ctx.nP + ctx.nIdxs.getD (i - ctx.nP) 0 ∧
    w.getAppArgs.take ctx.nP = ctx.params ∧
    ∀ x ∈ w.getAppArgs, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∨
  (∃ i ty h, w.getAppFn = .fvar i ty ∧ ctx.hiAt 0 ≤ i ∧ i < ctx.hiAt prog.length ∧
    prog.reverse[i - ctx.hiAt 0]? = some h ∧ h.key.ds.length ≤ w.getAppArgs.length ∧
    w.getAppArgs.take h.key.ds.length = h.key.ds ∧
    (∀ x ∈ w.getAppArgs.drop h.key.ds.length,
      x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
    w.getAppArgs.length = nestArity ctx h.key.cname) ∨
  (∃ n us nPc L u, w.getAppFn = .const n us ∧ ctx.names.contains n = false ∧
    nestContainer ctx n = some (nPc, L) ∧ nPc ≤ w.getAppArgs.length ∧
    (∀ x ∈ w.getAppArgs.drop nPc, x.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
    (∀ x ∈ w.getAppArgs.take nPc, x.bvarB = 0 ∧ x.fvarB ≤ ctx.hiAt prog.length) ∧
    u ∈ ts ∧ u.occ = prog ∧ u.key = ⟨n, us, w.getAppArgs.take nPc⟩) ∨
  w.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false

variable {ops env ctx}

/-- **A field's normal form is a Π-tower over its leaf**: hole-free
domains, the body opened at the walk's variables the leaf (up to
erasure) at the depth the spine reaches, the leaf one of `FieldLeaf`'s. -/
theorem posD_field_leaf
    (hwb : ∀ d e w, ops.whnf env d e = .ok w → e.looseBVarsBounded 0 = true →
      w.looseBVarsBounded 0 = true) :
    ∀ {J : PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
      | .field prog dep _ e _ nd => ctx.hiAt prog.length ≤ dep → e.looseBVarsBounded 0 = true →
        nd.looseBVarsBounded 0 = true ∧
        ∃ (tele : List (Expr × BinderMeta)) (leafC w : Expr), nd = Expr.mkPisOf tele leafC ∧
          (∀ x ∈ tele, x.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
          (∀ os, LocList dep tele.length os → Expr.ErasedEq (leafC.instantiateList os 0) w) ∧
          FieldLeaf ctx prog w ts
      | _ => True := by
  intro J ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    intro _ he
    have hwB := hwb _ _ _ hw he
    refine ⟨by split <;> assumption, [],
      (if e.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) then w else e),
      (if e.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) then w else e), rfl, (by intro x hx; exact nomatch hx), fun os hos => ?_,
      Or.inr (Or.inr (Or.inr ?_))⟩
    · obtain rfl : os = [] := List.length_eq_zero_iff.mp hos.1
      rw [Expr.instantiateList_nil]; exact Expr.ErasedEq.rfl _
    · split
      · exact hocc
      · rename_i h; simpa using h
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ihb =>
    intro hhi he
    have hwB := hwb _ _ _ hw he
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwB
    have hbI : (b.instantiate1 (.fvar dep a)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 b 0 hwB.2
    obtain ⟨hnbB, tele, leafC, w, rfl, htele, hopen, hleaf⟩ := ihb (by omega) hbI
    refine ⟨?_, (a, bm) :: absTele dep 0 tele, leafC.abstract1 dep tele.length, w, ?_, ?_, ?_,
      hleaf⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hwB.1, looseBVarsBounded_abstract1 _ 0 hnbB⟩
    · rw [mkPisOf_abstract1, Nat.zero_add]; rfl
    · have hdep : ¬ (ctx.nP ≤ dep ∧ dep < ctx.hiAt prog.length) := by omega
      have key : ∀ (k : Nat) (tl : List (Expr × BinderMeta)),
          (∀ x ∈ tl, x.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) →
          ∀ x ∈ absTele dep k tl, x.1.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false := by
        intro k tl
        induction tl generalizing k with
        | nil => intro _ x hx; exact nomatch hx
        | cons y r ih =>
          intro hr x hx
          obtain ⟨t, bm'⟩ := y
          simp only [absTele, List.mem_cons] at hx
          rcases hx with rfl | hx
          · rw [nestOcc_abstract1 hdep]; exact hr _ List.mem_cons_self
          · exact ih (k + 1) (fun z hz => hr z (List.mem_cons_of_mem _ hz)) x hx
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact key 0 tele htele x hx
    · intro os hos
      have hlen : os.length = tele.length + 1 := by
        have := hos.1; simpa [absTele_length] using this
      obtain ⟨ty, hty⟩ := hos.2 tele.length (by simp [absTele_length])
      have hsplit : os = os.take tele.length ++ [.fvar dep ty] := by
        conv => lhs; rw [← List.take_append_drop tele.length os]
        congr 1
        rw [show dep + (List.length ((a, bm) :: absTele dep 0 tele)) - 1 - tele.length = dep by
          simp [absTele_length]] at hty
        apply List.ext_getElem (by simp [hlen])
        intro n h1 h2
        have hn : n = 0 := by simp at h2; omega
        subst hn
        simp only [List.getElem_drop, Nat.add_zero, List.getElem_singleton]
        exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hty)
      have htk : LocList (dep + 1) tele.length (os.take tele.length) := by
        have := hos.take (m := tele.length) (by simp [absTele_length])
        simpa [absTele_length, Nat.add_comm 1] using this
      have hbd : leafC.looseBVarsBounded tele.length = true := by
        have := looseBVarsBounded_mkPisOf_body tele leafC 0 hnbB
        simpa using this
      rw [hsplit]
      exact (abstract1_instantiateList_erasedEq hbd (by simp; omega) ty).trans (hopen _ htk)
  | @hole prog dep kb e w i ty hw hocc hfn hlo hhi' hlen hpar hfree =>
    intro _ he
    refine ⟨hwb _ _ _ hw he, [], w, w, rfl, (by intro x hx; exact nomatch hx), fun os hos => ?_,
      Or.inl ⟨i, ty, hfn, hlo, hhi', hlen, hpar, hfree⟩⟩
    obtain rfl : os = [] := List.length_eq_zero_iff.mp hos.1
    rw [Expr.instantiateList_nil]; exact Expr.ErasedEq.rfl _
  | @frameHole prog dep kb e w i ty h hw hocc hfn hlo hhi' hk hle hpar hfree har =>
    intro _ he
    refine ⟨hwb _ _ _ hw he, [], w, w, rfl, (by intro x hx; exact nomatch hx), fun os hos => ?_,
      Or.inr (Or.inl ⟨i, ty, h, hfn, hlo, hhi', hk, hle, hpar, hfree, har⟩)⟩
    obtain rfl : os = [] := List.length_eq_zero_iff.mp hos.1
    rw [Expr.instantiateList_nil]; exact Expr.ErasedEq.rfl _
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hdsw
      hnI hhead hsc hfrD ihf =>
    intro _ he
    refine ⟨hwb _ _ _ hw he, [], w, w, rfl, (by intro x hx; exact nomatch hx), fun os hos => ?_,
      Or.inr (Or.inr (Or.inl ⟨n, us, nPc, L, _, hfn, hnm, hq, by omega, hidx, hds,
        List.mem_singleton_self _, rfl, rfl⟩))⟩
    obtain rfl : os = [] := List.length_eq_zero_iff.mp hos.1
    rw [Expr.instantiateList_nil]; exact Expr.ErasedEq.rfl _
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hdsw
      hnI hmem hfrD ihf =>
    intro _ he
    refine ⟨hwb _ _ _ hw he, [], w, w, rfl, (by intro x hx; exact nomatch hx), fun os hos => ?_,
      Or.inr (Or.inr (Or.inl ⟨n, us, nPc, L, _, hfn, hnm, hq, by omega, hidx,
        fun x hx => ⟨(hds x hx).1, Nat.le_trans (hds x hx).2 (by simp [NestCtx.hiAt])⟩,
        List.mem_singleton_self _, rfl, rfl⟩))⟩
    obtain rfl : os = [] := List.length_eq_zero_iff.mp hos.1
    rw [Expr.instantiateList_nil]; exact Expr.ErasedEq.rfl _
  | _ => trivial

/-- **A field's normal form is scoped where its input is** (the walk's
whnf keeps scoping; a Π's body is closed back over its variable). -/
theorem posD_field_scoped
    (hws : ∀ d e w, ops.whnf env d e = .ok w → Expr.WScoped d e → Expr.WScoped d w) :
    ∀ {J : PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
      | .field _ dep _ e _ nd => Expr.WScoped dep e → Expr.WScoped dep nd
      | _ => True := by
  intro J ts h
  induction h with
  | @const prog dep kb e w hw hocc =>
    intro he
    have := hws _ _ _ hw he
    split <;> assumption
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ihb =>
    intro he
    have hwW := hws _ _ _ hw he
    simp only [Expr.WScoped] at hwW
    have hnb := ihb (Expr.WScoped.instantiate1 hwW.1 0 hwW.2)
    simp only [Expr.WScoped]
    exact ⟨hwW.1, ConLeche.WScoped.abstract1 0 hnb⟩
  | hole hw => intro he; exact hws _ _ _ hw he
  | frameHole hw => intro he; exact hws _ _ _ hw he
  | contNew hw => intro he; exact hws _ _ _ hw he
  | contHit hw => intro he; exact hws _ _ _ hw he
  | _ => trivial

end Leaf

end ConLeche.Model
