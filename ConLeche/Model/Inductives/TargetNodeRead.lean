module

public import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.BlockCallCerts
import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Verify.InferLemmas

public section

/-!
# The call node's value: `TargetNodeVal` discharged

`interp_targetAbstract` (`TargetRecRead.lean`) reads the classification-
free abstraction with ONE premise, `TargetNodeVal`: at a recursive call
`c x⃗ e⃗ (f a⃗)` of the stored rule body, the stored node reads to its
`ih` variable's value folded along the call's telescope variables.
This file discharges it, with the `ih` values the kernel's own call
typing names: the `ih` term of a call is the READING of the λ the
check inferred (`targetCallOk`: `λ a⃗ : A⃗, c x⃗ e⃗ (f a⃗)` with the
callee a variable of its stored type after the frame), at the callee's
value.  Three facts meet:

* the λ's fold along a FITTING spine is its body at the spine
  (`mkLamsAV_fold`, at the family's nonzero elimination bit);
* the spine the residue applies the `ih` variable to — the call's own
  telescope variables — fits: the residue node was typed by the rule
  stage (`IhTyped`), in the walk's context (`WalkCtx`), against the
  `ih` variable's type `∀ a⃗ : A⃗, …`, whose domains are the λ's;
* the λ's body and the stored node apply the callee's value to the
  same arguments: the stored node's arguments read the same at every
  frame they are opened at (`interp_open_indep`).

The telescope `A⃗` is read by one function, `teleDoms`, from both the
`∀`-tower (the `ih` type) and the λ-tower (the call's term): their
binders open alike, so their domains are literally one list.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe uv

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

/-! ## A telescope's domains, read -/

/-- **A telescope's domains, read above depth `D`**, with `os` of its
binders opened so far — each binder opened by its own opened domain,
exactly as `denoteMeta`'s binder clauses open it, so the `∀`-tower and
the λ-tower over one telescope read one list. -/
@[expose] def teleDoms (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (D : Nat) : List Expr → List Expr → Option (List AnnotTerm)
  | _, [] => some []
  | os, ty :: tys => do
    let a ← denoteMeta acval env φ (D + os.length) (ty.instantiateList os 0)
    let r ← teleDoms acval env φ D (.fvar (D + os.length) (ty.instantiateList os 0) :: os) tys
    pure (a :: r)

/-- **The `∀`-tower over a telescope, read**: its binder data are the
telescope's domains (`teleDoms`) at the binders' own bits, and its body
is read with the binders opened. -/
theorem denoteMeta_mkPisOf {D : Nat} :
    ∀ (tele : List (Expr × ConLeche.BinderMeta)) (X : Expr) (q : Nat) (os : List Expr)
      (P : AnnotTerm),
      LocList D q os →
      denoteMeta acval env φ (D + q) ((Expr.mkPisOf tele X).instantiateList os 0) = some P →
      ∃ (ds : List (Nat × Nat × AnnotTerm)) (Xr : AnnotTerm) (os' : List Expr),
        P = mkPisAV ds Xr ∧
        teleDoms acval env φ D os (tele.map (·.1)) = some (ds.map (·.2.2)) ∧
        ds.map (·.2.1) = tele.map (fun b => pwBit φ b.2.pw) ∧
        LocList D (q + tele.length) os' ∧
        denoteMeta acval env φ (D + (q + tele.length)) (X.instantiateList os' 0) = some Xr
  | [], X, q, os, P, hos, hP => by
    refine ⟨[], P, os, rfl, ?_, rfl, by simpa using hos, by simpa [Expr.mkPisOf] using hP⟩
    simp [teleDoms]
  | (ty, bm) :: bs, X, q, os, P, hos, hP => by
    have hq : os.length = q := hos.1
    simp only [Expr.mkPisOf, Expr.instantiateList] at hP
    rw [denoteMeta_forallE] at hP
    obtain ⟨ta, hta, hP⟩ := Option.bind_eq_some_iff.mp hP
    obtain ⟨ba, hba, hP⟩ := Option.bind_eq_some_iff.mp hP
    obtain rfl : P = .pi 0 (pwBit φ bm.pw) ta ba := (Option.some.inj hP).symm
    rw [← Expr.instantiateList_cons, show D + q + 1 = D + (q + 1) from by omega] at hba
    obtain ⟨ds, Xr, os', rfl, hdoms, hbits, hos', hX⟩ :=
      denoteMeta_mkPisOf bs X (q + 1) _ ba (hos.cons _) hba
    refine ⟨(0, pwBit φ bm.pw, ta) :: ds, Xr, os', rfl, ?_, ?_,
      by simpa [Nat.add_assoc, Nat.add_comm 1] using hos',
      by simpa [Nat.add_assoc, Nat.add_comm 1] using hX⟩
    · show teleDoms acval env φ D os (ty :: bs.map (·.1)) = some (ta :: ds.map (·.2.2))
      rw [teleDoms, hq, hta, hdoms]
      rfl
    · simp [hbits]

/-- **The λ-tower over a telescope, read** — as
`denoteMeta_mkPisOf`: the same domains, the λ's own bits. -/
theorem denoteMeta_mkLamsOf {D : Nat} :
    ∀ (tele : List (Expr × ConLeche.BinderMeta)) (X : Expr) (q : Nat) (os : List Expr)
      (L : AnnotTerm),
      LocList D q os →
      denoteMeta acval env φ (D + q) ((Expr.mkLamsOf tele X).instantiateList os 0) = some L →
      ∃ (ds : List (Nat × AnnotTerm)) (Xr : AnnotTerm) (os' : List Expr),
        L = mkLamsAV ds Xr ∧
        teleDoms acval env φ D os (tele.map (·.1)) = some (ds.map (·.2)) ∧
        ds.map (·.1) = tele.map (fun b => pwBit φ b.2.pw) ∧
        LocList D (q + tele.length) os' ∧
        denoteMeta acval env φ (D + (q + tele.length)) (X.instantiateList os' 0) = some Xr
  | [], X, q, os, L, hos, hL => by
    refine ⟨[], L, os, rfl, ?_, rfl, by simpa using hos, by simpa [Expr.mkLamsOf] using hL⟩
    simp [teleDoms]
  | (ty, bm) :: bs, X, q, os, L, hos, hL => by
    have hq : os.length = q := hos.1
    simp only [Expr.mkLamsOf, Expr.instantiateList] at hL
    rw [denoteMeta_lam] at hL
    obtain ⟨ta, hta, hL⟩ := Option.bind_eq_some_iff.mp hL
    obtain ⟨ba, hba, hL⟩ := Option.bind_eq_some_iff.mp hL
    obtain rfl : L = .lam (pwBit φ bm.pw) ta ba := (Option.some.inj hL).symm
    rw [← Expr.instantiateList_cons, show D + q + 1 = D + (q + 1) from by omega] at hba
    obtain ⟨ds, Xr, os', rfl, hdoms, hbits, hos', hX⟩ :=
      denoteMeta_mkLamsOf bs X (q + 1) _ ba (hos.cons _) hba
    refine ⟨(pwBit φ bm.pw, ta) :: ds, Xr, os', rfl, ?_, ?_,
      by simpa [Nat.add_assoc, Nat.add_comm 1] using hos',
      by simpa [Nat.add_assoc, Nat.add_comm 1] using hX⟩
    · show teleDoms acval env φ D os (ty :: bs.map (·.1)) = some (ta :: ds.map (·.2))
      rw [teleDoms, hq, hta, hdoms]
      rfl
    · simp [hbits]

/-! ## The domains, read at two depths -/

/-- Entry `j` lifted by `n` at the cut `k + j` — a telescope's domains
read `n` binders deeper. -/
@[expose] def liftAt (n : Nat) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | k, t :: ts => t.liftN n k :: liftAt n (k + 1) ts

/-- **A frame-bounded telescope read `n` binders deeper** lifts its
domains, each at its own depth. -/
theorem teleDoms_deepen
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (n B : Nat) :
    ∀ (tys : List Expr) (q : Nat) (os1 os2 : List Expr),
      (∀ t ∈ tys, ∀ l ∈ t.fvarLeaves, l.1 < B) → LocList B q os1 → LocList (B + n) q os2 →
      teleDoms acval env φ (B + n) os2 tys = (teleDoms acval env φ B os1 tys).map (liftAt n q)
  | [], q, os1, os2, _, _, _ => by simp [teleDoms, liftAt]
  | ty :: tys, q, os1, os2, hl, h1, h2 => by
    have hq1 : os1.length = q := h1.1
    have hq2 : os2.length = q := h2.1
    have hd := denoteMeta_open_deepen (acval := acval) (env := env) (φ := φ) hacl n B ty q os1 os2
      (hl ty (by simp)) h1 h2
    simp only [teleDoms, hq1, hq2]
    rw [hd]
    cases hA : denoteMeta acval env φ (B + q) (ty.instantiateList os1 0) with
    | none => rfl
    | some A =>
      simp only [Option.map_some]
      have ih := teleDoms_deepen hacl n B tys (q + 1)
        (.fvar (B + q) (ty.instantiateList os1 0) :: os1)
        (.fvar (B + n + q) (ty.instantiateList os2 0) :: os2) (fun t ht => hl t (by simp [ht]))
        (h1.cons _) (h2.cons _)
      rw [ih]
      cases teleDoms acval env φ B (.fvar (B + q) (ty.instantiateList os1 0) :: os1) tys with
      | none => rfl
      | some r => rfl

section Fit

variable {V : Type uv} [SetTheory V]

/-- A fit of lifted domains is a fit at the shifted frame. -/
theorem spineFit_liftAt (n : Nat) :
    ∀ (ds : List AnnotTerm) (k : Nat) (σ : Nat → V) (as : List V),
      SpineFit σ (liftAt n k ds) as ↔ SpineFit (shiftE n k σ) ds as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ds, k, σ, a :: as => by
    simp only [liftAt, SpineFit, interp_liftN]
    rw [← shiftE_cons_succ']
    exact and_congr Iff.rfl (spineFit_liftAt n ds (k + 1) (cons a σ) as)

end Fit

/-! ## A frame-bounded term's value does not see where it is opened -/

/-- `m` fresh openers above the frame `B`. -/
@[expose] def locOpen (B m : Nat) : List Expr :=
  (List.range m).map fun j => .fvar (B + m - 1 - j) (.sort .zero)

theorem locOpen_locList (B m : Nat) : LocList B m (locOpen B m) := by
  refine ⟨by simp [locOpen], fun j hj => ⟨.sort .zero, ?_⟩⟩
  simp [locOpen, List.getElem?_range hj]

theorem LocList.take {B d m : Nat} {xs : List Expr} (h : LocList B d xs) (hm : m ≤ d) :
    LocList (B + (d - m)) m (xs.take m) := by
  refine ⟨by rw [List.length_take, h.1]; omega, fun j hj => ?_⟩
  obtain ⟨ty, hty⟩ := h.2 j (by omega)
  refine ⟨ty, ?_⟩
  rw [List.getElem?_take, if_pos hj, hty]
  congr 2
  omega

/-- Opening a term bounded by `k + m` loose indices uses only the first
`m` openers. -/
theorem instantiateList_take_bounded :
    ∀ (e : Expr) (xs : List Expr) (k m : Nat), e.looseBVarsBounded (k + m) = true →
      e.instantiateList xs k = e.instantiateList (xs.take m) k
  | .bvar j, xs, k, m, hb => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    rw [Expr.instantiateList, Expr.instantiateList]
    by_cases hjk : j < k
    · rw [if_pos hjk, if_pos hjk]
    rw [if_neg hjk, if_neg hjk]
    by_cases hin : j - k < xs.length
    · have hin' : j - k < (xs.take m).length := by rw [List.length_take]; omega
      rw [dif_pos hin, dif_pos hin', List.getElem_take, List.take_take,
        Nat.min_eq_left (by omega)]
    · have hin' : ¬ j - k < (xs.take m).length := by rw [List.length_take]; omega
      rw [dif_neg hin, dif_neg hin', List.length_take, Nat.min_eq_right (by omega)]
  | .fvar _ _, _, _, _, _ => by rw [Expr.instantiateList, Expr.instantiateList]
  | .sort _, _, _, _, _ => by rw [Expr.instantiateList, Expr.instantiateList]
  | .const _ _, _, _, _, _ => by rw [Expr.instantiateList, Expr.instantiateList]
  | .lit _, _, _, _, _ => by rw [Expr.instantiateList, Expr.instantiateList]
  | .app f a, xs, k, m, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList]
    rw [instantiateList_take_bounded f xs k m hb.1, instantiateList_take_bounded a xs k m hb.2]
  | .lam ty b bi, xs, k, m, hb | .forallE ty b bi, xs, k, m, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList]
    rw [instantiateList_take_bounded ty xs k m hb.1,
      instantiateList_take_bounded b xs (k + 1) m (by rw [show k + 1 + m = k + m + 1 by omega]; exact hb.2)]
  | .letE ty v b, xs, k, m, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList]
    rw [instantiateList_take_bounded ty xs k m hb.1.1, instantiateList_take_bounded v xs k m hb.1.2,
      instantiateList_take_bounded b xs (k + 1) m (by rw [show k + 1 + m = k + m + 1 by omega]; exact hb.2)]
  | .proj _ _ e, xs, k, m, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.instantiateList]
    rw [instantiateList_take_bounded e xs k m hb]

section Indep

variable {V : Type uv} [SetTheory V]

/-- **A frame-bounded term's value is independent of where it is
opened**: opened by `m` locals above the frame plus `n₁` (resp. `n₂`)
extra variables, and read at the matching valuation, it has one value. -/
theorem interp_open_indep
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {B m n1 n2 : Nat} {t : Expr} (hl : ∀ l ∈ t.fvarLeaves, l.1 < B)
    {os1 os2 : List Expr} (h1 : LocList (B + n1) m os1) (h2 : LocList (B + n2) m os2)
    {vals ex1 ex2 : List V} {ρ' : Nat → V}
    (hv : vals.length = m) (he1 : ex1.length = n1) (he2 : ex2.length = n2)
    {A1 A2 : AnnotTerm}
    (hA1 : denoteMeta acval env φ (B + n1 + m) (t.instantiateList os1 0) = some A1)
    (hA2 : denoteMeta acval env φ (B + n2 + m) (t.instantiateList os2 0) = some A2) :
    interp V (consList vals (consList ex1 ρ')) A1 = interp V (consList vals (consList ex2 ρ')) A2 := by
  have h0 := locOpen_locList B m
  have d1 := denoteMeta_open_deepen (acval := acval) (env := env) (φ := φ) hacl n1 B t m
    (locOpen B m) os1 hl h0 h1
  have d2 := denoteMeta_open_deepen (acval := acval) (env := env) (φ := φ) hacl n2 B t m
    (locOpen B m) os2 hl h0 h2
  rw [hA1] at d1
  rw [hA2] at d2
  cases hA0 : denoteMeta acval env φ (B + m) (t.instantiateList (locOpen B m) 0) with
  | none => rw [hA0] at d1; exact nomatch d1
  | some A0 =>
    rw [hA0, Option.map_some] at d1 d2
    rw [Option.some.inj d1, Option.some.inj d2, interp_liftN, interp_liftN,
      shiftE_consList_ih hv he1, shiftE_consList_ih hv he2]

end Indep

/-! ## The call node's value -/

section NodeVal

variable {V : Type uv} [SetTheory V]

/-- A frame variable is a subject of the walk's context. -/
theorem WalkCtx.memSubj {envT : Env} {mT : EnvModel V envT} {D : Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    {ρfull : Nat → V} {Δa : List AnnotTerm} {L : List Expr}
    (h2 : FvarList D L) (h : WalkCtx V mT φ D ρfull Δa L) {x : Expr} (hx : x ∈ L)
    (hxf : ∃ (i : Nat) (ty : Expr), x = .fvar i ty) :
    Rules.Frame D x ∧ CtxOk mT φ D Δa x := by
  obtain ⟨i, ty, rfl⟩ := hxf
  have hcl : ∀ l ∈ (Expr.fvar i ty).fvarLeaves, Expr.fvar l.1 l.2 ∈ L := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hx
    · exact h.2.2.2.2.2.2 _ hx l hl
  exact ⟨⟨wscoped_of_leaves_mem h2 _ hcl, rfl, fun l hl => h.2.2.2.2.1 _ (hcl l hl)⟩,
    h.ctxOk hacl h2 hcl⟩

/-- The call's telescope variables, opened: read as the telescope's own indices. -/
theorem denoteMetaSpine_teleVars {Bn d m : Nat} {as2 : List Expr} (h2 : LocList Bn d as2)
    (hm : m ≤ d) :
    DenoteMetaSpine acval env φ (Bn + d)
      ((ConLeche.structTeleVars m).map (·.instantiateList as2 0)) (teleVarsAV m) := by
  have key : ∀ (ks : List Nat), (∀ k ∈ ks, k < m) →
      DenoteMetaSpine acval env φ (Bn + d)
        ((ks.map fun k => Expr.bvar (m - 1 - k)).map (·.instantiateList as2 0))
        (ks.map fun k => AnnotTerm.bvar (m - 1 - k)) := by
    intro ks
    induction ks with
    | nil => intro _; exact .nil
    | cons k ks ih =>
      intro hks
      have hk := hks k (by simp)
      obtain ⟨tyk, htyk⟩ := h2.bvar_lt (j := m - 1 - k) (by omega)
      refine .cons ?_ (ih fun k' hk' => hks k' (by simp [hk']))
      show denoteMeta acval env φ (Bn + d) ((Expr.bvar (m - 1 - k)).instantiateList as2 0) = _
      rw [htyk, denoteMeta_fvar,
        show Bn + d - 1 - (Bn + d - 1 - (m - 1 - k)) = m - 1 - k from by omega]
  simpa [ConLeche.structTeleVars, teleVarsAV, List.map_map] using
    key (List.range m) (fun k hk => List.mem_range.mp hk)

/-- **The `ih` variable's spine fits its telescope**: the residue node
`ih_r a⃗` was typed by the rule stage, so its arguments — the call's
telescope variables, valued at the last `m` locals — fit the `ih`
type's domains, which are the telescope's, read at the rule's frame. -/
theorem ihCall_fit {envT : Env} {mT : EnvModel V envT}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {B n d m r : Nat} {T X : Expr} {tele : List (Expr × ConLeche.BinderMeta)}
    {as2 frameIh : List Expr} {locals ihvals : List V} {ρ' : Nat → V} {Δa : List AnnotTerm}
    (h2 : LocList (B + n) d as2) (hL : FvarList (B + n + d) (as2 ++ frameIh))
    (hW : WalkCtx V mT φ (B + n + d) (consList locals (consList ihvals ρ')) Δa (as2 ++ frameIh))
    (hloc : locals.length = d) (hihl : ihvals.length = n) (hmd : m ≤ d)
    (hmem : Expr.fvar (B + r) T ∈ frameIh)
    (hT : T = Expr.mkPisOf tele X) (htl : tele.length = m)
    (hleaves : ∀ t ∈ tele.map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < B)
    (hty : IhTyped envT (B + n + d)
      ((Expr.mkAppN (.fvar (B + r) T) (ConLeche.structTeleVars m)).instantiateList as2 0)) :
    ∃ ts, teleDoms acval env φ B [] (tele.map (·.1)) = some ts ∧
      SpineFit ρ' ts (locals.drop (d - m)) := by
  -- the spine, in `certs_of_infer_mkAppN`'s shape
  have hspine : (Expr.mkAppN (.fvar (B + r) T) (ConLeche.structTeleVars m)).instantiateList as2 0
      = Expr.mkAppN (.fvar (B + r) T)
          ((ConLeche.structTeleVars m).map (·.instantiateList as2 0)) := by
    rw [instantiateList_mkAppN, Expr.instantiateList]
  rw [hspine] at hty
  obtain ⟨tI, hInf⟩ := hty
  have hlenA : ((ConLeche.structTeleVars m).map (·.instantiateList as2 0)).length = m := by
    simp [ConLeche.structTeleVars]
  have hcerts := certs_of_infer_mkAppN _ hInf (fun _ ht' => IhTyped.fvarTy ht')
    (piSpine_of_stripPis _ (by
      rw [hlenA, hT]
      exact stripPis_isSome_mkPisOf tele X m (by omega)))
  -- the `ih` variable's type: a subject of the context, read
  have hmemL : Expr.fvar (B + r) T ∈ as2 ++ frameIh := List.mem_append_right _ hmem
  obtain ⟨hFrT, hCtxT, hGrT⟩ := WalkCtx.annotOk haclT hL hW hmemL
  have hleafV : ∀ l ∈ (Expr.fvar (B + r) T).fvarLeaves, Expr.fvar l.1 l.2 ∈ as2 ++ frameIh := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hmemL
    · exact hW.2.2.2.2.2.2 _ hmemL l hl
  obtain ⟨-, hleaf⟩ := hW.ctxOk haclT hL hleafV
  obtain ⟨-, -, Ta, -, hTa, -, -, -⟩ := hleaf (B + r, T) (by simp [Expr.fvarLeaves])
  -- the arguments: local variables of the context
  have hargsSubj : ∀ x ∈ (ConLeche.structTeleVars m).map (·.instantiateList as2 0),
      Rules.Frame (B + n + d) x ∧ CtxOk mT φ (B + n + d) Δa x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
    have hk' := List.mem_range.mp hk
    obtain ⟨ty', hty'⟩ := h2.2 (m - 1 - k) (by omega)
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hty'
    have hx' : (Expr.bvar (m - 1 - k)).instantiateList as2 0
        = .fvar (B + n + d - 1 - (m - 1 - k)) ty' := by
      rw [Expr.instantiateList, if_neg (by omega), dif_pos (by omega)]
      simp only [Nat.sub_zero]
      rw [show as2[m - 1 - k] = _ from hget, Expr.instantiateList]
    rw [hx']
    exact WalkCtx.memSubj haclT hL hW (List.mem_append_left _ (List.mem_of_getElem? hty'))
      ⟨_, _, rfl⟩
  -- `certs_sound` at the walk's context
  have hsp := denoteMetaSpine_teleVars (acval := mT.acval) (env := envT) (φ := φ) h2 hmd
  obtain ⟨resta, hfitPA, -⟩ := Rules.certs_sound hin hcerts (fa := .sort 0) hFrT hCtxT hTa (hGrT _ hTa)
    hargsSubj hsp
    (fun x hx => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      intro ρ _
      exact ⟨by simp, by simp⟩)
    (fun h => absurd h (by simp))
  have hfitρ := hfitPA _ hW.2.1
  -- the type, read at the consed environment, is the telescope's Π-tower
  have hcbT : ConstsBound envT T := by
    have := hW.2.2.2.2.2.1 _ hmemL
    rwa [constsBound_fvar] at this
  have hTaE := hmono _ _ _ hcbT hTa
  rw [hT, ← ConLeche.Expr.instantiateList_nil (Expr.mkPisOf tele X) 0,
    show B + n + d = B + n + d + 0 from rfl] at hTaE
  obtain ⟨ds, Xr, -, rfl, hdoms, hbits, -, -⟩ :=
    denoteMeta_mkPisOf (acval := acval) (env := env) (φ := φ) (D := B + n + d) tele X 0 []
      _ ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩ hTaE
  have hdslen : ds.length = m := by
    have := congrArg List.length hbits
    simpa [htl] using this
  have hSF := spineFit_of_teleFitPA (by rw [← hsp.length, hlenA, hdslen]) hfitρ
  -- the values: the last `m` locals
  have hvals : (teleVarsAV m).map (interp V (consList locals (consList ihvals ρ')))
      = locals.drop (d - m) := by
    rw [← consList_teleVars (σ := consList ihvals ρ') hloc hmd]
    simp [teleVarsAV, List.map_map]
  rw [hvals] at hSF
  -- the domains, at the rule's own frame
  have hdeep := teleDoms_deepen (acval := acval) (env := env) (φ := φ) hacl (n + d) B
    (tele.map (·.1)) 0 [] [] hleaves ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rw [show B + (n + d) = B + n + d from by omega, hdoms] at hdeep
  cases hts : teleDoms acval env φ B [] (tele.map (·.1)) with
  | none => rw [hts] at hdeep; exact nomatch hdeep
  | some ts =>
    rw [hts, Option.map_some] at hdeep
    refine ⟨ts, rfl, ?_⟩
    rw [Option.some.inj hdeep, spineFit_liftAt, shiftE_consList_two hloc hihl] at hSF
    exact hSF

theorem targetCall?_inv {fr : ConLeche.TargetFrame} {d : Nat} {e : Expr} {i c m : Nat} {idx : List Expr}
    (h : ConLeche.targetCall? fr d e = some (i, c, m, idx))
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0) :
    ∃ rn : Name, e = Expr.mkAppN (.const rn fr.rlvls)
        (fr.pref ++ idx ++ [Expr.mkAppN (fr.fields.getD i default) (ConLeche.structTeleVars m)]) ∧
      ConLeche.nameIdxOf? fr.recNames rn = some c ∧ fr.rPs.getD c 0 = fr.rP ∧
      m = (fr.teles.getD i []).length ∧ m ≤ d ∧ i < fr.fields.length ∧
      ∀ x ∈ idx, x.looseBVarsBounded m = true ∧ x.mentionsAnyConst fr.recNames = false := by
  unfold ConLeche.targetCall? at h
  split at h
  next r us hfn =>
    split at h
    · exact nomatch h
    next c0 hc0 =>
      split at h
      · exact nomatch h
      next hus =>
      split at h
      · exact nomatch h
      next hrp =>
      dsimp only at h
      split at h
      · exact nomatch h
      next hlen =>
      split at h
      · exact nomatch h
      next hpref =>
      split at h
      · exact nomatch h
      next maj hmaj =>
      split at h
      · exact nomatch h
      next i0 hi0 =>
      split at h
      · exact nomatch h
      next hmd =>
      split at h
      · exact nomatch h
      next hargs =>
      split at h
      · exact nomatch h
      next hidx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      subst h1; subst h2; subst h3; subst h4
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hus hrp hlen hpref hargs
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Decidable.not_not] at hmd
      subst hus
      obtain ⟨hi0lt, hi0eq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi0
      have hfi : fr.fields[i0] = maj.getAppFn := by simpa using hi0eq
      have hrPmI := hle c0
      rw [hrp] at hrPmI
      obtain ⟨hmlt, hmget⟩ := List.getElem?_eq_some_iff.mp hmaj
      refine ⟨r, ?_, hc0, hrp, rfl, hmd, hi0lt, ?_⟩
      · have hsplit : ∀ (l : List Expr) (a b : Nat), a ≤ b →
            l = l.take a ++ ((l.drop a).take (b - a) ++ l.drop b) := by
          intro l a b hab
          have h2 : l.drop b = (l.drop a).drop (b - a) := by
            rw [List.drop_drop]; congr 1; omega
          rw [h2, List.take_append_drop, List.take_append_drop]
        have hlast : e.getAppArgs.drop (fr.mIs.getD c0 0)
            = [Expr.mkAppN (fr.fields.getD i0 default)
                (structTeleVars (fr.teles.getD i0 []).length)] := by
          rw [List.drop_eq_getElem_cons hmlt, hmget,
            List.drop_eq_nil_of_le (by omega)]
          congr 1
          rw [← Expr.mkAppN_getApp maj, ← hfi, hargs]
          simp [List.getD_eq_getElem?_getD, hi0lt]
        have hae := hsplit e.getAppArgs fr.rP (fr.mIs.getD c0 0) hrPmI
        rw [hpref, hlast] at hae
        calc e = Expr.mkAppN e.getAppFn e.getAppArgs := (Expr.mkAppN_getApp e).symm
          _ = _ := by rw [hfn]; exact congrArg _ (hae.trans (List.append_assoc _ _ _).symm)
      · intro x hx
        have H := by simpa using hidx
        have := H x (by simpa using hx)
        simpa using this
  · exact nomatch h

/-- **The call's λ, as the check inferred it** (`targetCallOk`): the
call `c x⃗ e⃗ (f a⃗)` abstracted over the field's telescope, the callee
a variable of its stored type right after the frame `B`. -/
@[expose] def targetCallE (fr : ConLeche.TargetFrame) (B : Nat) (pw : ConLeche.PropWhen)
    (ih : ConLeche.TargetIh) : Expr :=
  Expr.mkLamsOf ((fr.teles.getD ih.field []).map fun b => (b.1, ⟨pw⟩))
    (Expr.mkAppN (.fvar B (fr.recTys.getD ih.callee (.sort .zero)))
      (fr.pref ++ ih.idx ++
        [Expr.mkAppN (fr.fields.getD ih.field default)
          (ConLeche.structTeleVars (fr.teles.getD ih.field []).length)]))

/-- A leaf of a spine's argument is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN_arg : ∀ (as : List Expr) (f : Expr) (a : Expr), a ∈ as →
    ∀ l ∈ a.fvarLeaves, l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, ha, _, _ => nomatch ha
  | b :: as, f, a, ha, l, hl => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Rules.mem_fvarLeaves_mkAppN as (.app f a) l (by simp [Expr.fvarLeaves, hl])
    · exact mem_fvarLeaves_mkAppN_arg as (.app f b) a ha l hl

/-- The arguments' values do not see where they are opened. -/
theorem spine_open_indep
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {B m n1 n2 : Nat} {os1 os2 : List Expr} (h1 : LocList (B + n1) m os1)
    (h2 : LocList (B + n2) m os2) {vals ex1 ex2 : List V} {ρ' : Nat → V}
    (hv : vals.length = m) (he1 : ex1.length = n1) (he2 : ex2.length = n2) :
    ∀ (ts : List Expr) (ws1 ws2 : List AnnotTerm), (∀ t ∈ ts, ∀ l ∈ t.fvarLeaves, l.1 < B) →
      DenoteMetaSpine acval env φ (B + n1 + m) (ts.map (·.instantiateList os1 0)) ws1 →
      DenoteMetaSpine acval env φ (B + n2 + m) (ts.map (·.instantiateList os2 0)) ws2 →
      ws1.map (interp V (consList vals (consList ex1 ρ')))
        = ws2.map (interp V (consList vals (consList ex2 ρ')))
  | [], _, _, _, .nil, .nil => rfl
  | t :: ts, _, _, hl, .cons ha1 hr1, .cons ha2 hr2 => by
    simp only [List.map_cons]
    rw [interp_open_indep hacl (hl t (by simp)) h1 h2 hv he1 he2 ha1 ha2,
      spine_open_indep hacl h1 h2 hv he1 he2 ts _ _ (fun t' ht' => hl t' (by simp [ht'])) hr1 hr2]

set_option maxHeartbeats 1600000 in
/-- **`TargetNodeVal`, discharged.**  The `ih` value of entry `r` is
the reading of the call's λ (`targetCallE`) at the callee's value
`R c`; the callee's stored constant reads to that value; the entry's
type is the `∀`-tower over the field's frame-bounded telescope and is
a variable of the walk's frame; and the family's elimination bit is
nonzero (the body equation is stated above `Prop`). -/
theorem targetNodeVal_of {envT : Env} {mT : EnvModel V envT}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {fr : ConLeche.TargetFrame} {B : Nat} {ihsF : Array ConLeche.TargetIh}
    {frameIh : List Expr} {ρ' : Nat → V} {ihvals : List V} {R : Nat → V}
    {pw : ConLeche.PropWhen} (hbit : pwBit φ pw ≠ 0)
    (hih : ihvals.length = ihsF.size)
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0)
    (hpref : ∀ x ∈ fr.pref, x.looseBVarsBounded 0 = true)
    (hfields : ∀ x ∈ fr.fields, x.looseBVarsBounded 0 = true)
    (hcallee : ∀ (nm : Name) (c : Nat), ConLeche.nameIdxOf? fr.recNames nm = some c →
      ∃ ci : ConstantInfo, env.find? nm = some ci ∧
        fr.rlvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ ρ : Nat → V,
          interp V ρ (acval nm (Level.substFn φ ci.toConstantVal.levelParams fr.rlvls)) = R c)
    (hents : ∀ (r : Nat) (ih : ConLeche.TargetIh), ihsF[r]? = some ih →
      Expr.fvar (B + r) ih.ty ∈ frameIh ∧
      (∃ X : Expr, ih.ty = Expr.mkPisOf
        ((fr.teles.getD ih.field []).map fun b => (b.1, (⟨fr.pw⟩ : ConLeche.BinderMeta))) X) ∧
      (∀ t ∈ (fr.teles.getD ih.field []).map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < B) ∧
      ∃ L : AnnotTerm, denoteMeta acval env φ (B + 1) (targetCallE fr B pw ih) = some L ∧
        ihvals.getD r pt = interp V (cons (R ih.callee) ρ') L) :
    TargetNodeVal V acval env φ mT fr B ihsF frameIh ρ' ihvals := by
  intro d locals e i c m idx r ih as1 as2 Δa A hc hget hfi hca hid hl h1 h2 hL hloc hlf hW hty hA
  obtain ⟨hmem, ⟨X, hT⟩, hleaves, L, hLr, hval⟩ := hents r ih hget
  obtain ⟨rn, rfl, hnm, -, hm, hmd, hi, hidx⟩ := targetCall?_inv hc hle
  subst hfi hca hid
  -- (1) the call's spine fits the telescope
  obtain ⟨ts, hts, hfit⟩ := ihCall_fit hacl haclT hin hmono h2 hL hW hloc hih hmd hmem hT
    (by simp [hm]) (by simpa using hleaves) hty
  rw [show ((fr.teles.getD ih.field []).map
      fun b => (b.1, (⟨fr.pw⟩ : ConLeche.BinderMeta))).map (·.1)
      = (fr.teles.getD ih.field []).map (·.1) by simp] at hts
  -- (2) the call's λ, folded along the spine
  unfold targetCallE at hLr
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkLamsOf _ _) 0,
    show B + 1 = B + 1 + 0 from rfl] at hLr
  obtain ⟨ds, Yr, os', rfl, hdoms, hbits, hos', hY⟩ :=
    denoteMeta_mkLamsOf (acval := acval) (env := env) (φ := φ) (D := B + 1) _ _ 0 []
      _ ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩ hLr
  have htys : ((fr.teles.getD ih.field []).map fun b => (b.1, (⟨pw⟩ : ConLeche.BinderMeta))).map
      (·.1) = (fr.teles.getD ih.field []).map (·.1) := by simp
  rw [htys] at hdoms
  have hdeep := teleDoms_deepen (acval := acval) (env := env) (φ := φ) hacl 1 B
    ((fr.teles.getD ih.field []).map (·.1)) 0 [] [] hleaves
    ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩ ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  rw [hdoms, hts, Option.map_some] at hdeep
  have hfitL : SpineFit (cons (R ih.callee) ρ') (ds.map (·.2)) (locals.drop (d - m)) := by
    rw [Option.some.inj hdeep, spineFit_liftAt]
    exact hfit
  have hnz : ∀ x ∈ ds, x.1 ≠ 0 := by
    intro x hx
    have hx1 : x.1 ∈ ds.map (·.1) := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbits] at hx1
    simp only [List.map_map, Function.comp_def, List.mem_map] at hx1
    obtain ⟨b, -, hb⟩ := hx1
    rw [← hb]
    exact hbit
  have hfold := mkLamsAV_fold (b := Yr) hnz hfitL
  -- (3) the λ's body: the callee's value applied to the call's arguments
  have hvl : (locals.drop (d - m)).length = m := by rw [List.length_drop]; omega
  have hlenT : (0 + ((fr.teles.getD ih.field []).map
      fun b => (b.1, (⟨pw⟩ : ConLeche.BinderMeta))).length) = m := by simp [hm]
  rw [hlenT] at hos' hY
  rw [instantiateList_mkAppN, Expr.instantiateList] at hY
  obtain ⟨fa, ws2, hfa, hws2, rfl⟩ := denoteMeta_mkAppN_inv hY
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa.symm
  -- (4) the stored node: the callee's constant applied to the same arguments
  rw [instantiateList_mkAppN, Expr.instantiateList] at hA
  obtain ⟨fa1, ws1, hfa1, hws1, rfl⟩ := denoteMeta_mkAppN_inv hA
  obtain ⟨ci, hfind, hlvl, hRc⟩ := hcallee rn ih.callee hnm
  rw [denoteMeta_const hfind (by rw [hlvl])] at hfa1
  obtain rfl := Option.some.inj hfa1.symm
  -- the arguments, one list
  obtain ⟨args, hargs⟩ : ∃ args, args = fr.pref ++ ih.idx ++
      [Expr.mkAppN (fr.fields.getD ih.field default) (ConLeche.structTeleVars m)] := ⟨_, rfl⟩
  rw [← hm] at hws2
  rw [← hargs] at hws1 hws2 hl
  have hlA : ∀ t ∈ args, ∀ l ∈ t.fvarLeaves, l.1 < B :=
    fun t ht l hlt => hl l (mem_fvarLeaves_mkAppN_arg args _ t ht l hlt)
  have hbA : ∀ t ∈ args, t.looseBVarsBounded (0 + m) = true := by
    intro t ht
    rw [Nat.zero_add]
    rw [hargs] at ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le m) (hpref t ht)
    · exact (hidx t ht).1
    · refine ConLeche.looseBVarsBounded_mkAppN
        (ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le m) (hfields _ ?_)) ?_
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
        exact List.getElem_mem hi
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
        simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
        have := List.mem_range.mp hk
        omega
  have htake : args.map (·.instantiateList as1 0) = args.map (·.instantiateList (as1.take m) 0) :=
    List.map_congr_left fun t ht => instantiateList_take_bounded t as1 0 m (hbA t ht)
  rw [htake, show B + d = B + (d - m) + m from by omega] at hws1
  have hsplit : consList locals ρ'
      = consList (locals.drop (d - m)) (consList (locals.take (d - m)) ρ') := by
    rw [← consList_append, List.take_append_drop]
  have hargsEq := spine_open_indep (vals := locals.drop (d - m)) (ρ' := ρ')
    (ex1 := locals.take (d - m)) (ex2 := [R ih.callee]) (n1 := d - m) (n2 := 1) hacl
    (h1.take hmd) hos' hvl (by rw [List.length_take]; omega) (rfl : [R ih.callee].length = 1)
    args ws1 ws2 hlA hws1 hws2
  simp only [consList_cons, consList_nil] at hargsEq
  rw [interp_mkAppN_foldl, hsplit, hargsEq, hRc, hval, hfold, interp_mkAppN_foldl]
  congr 1
  show R ih.callee = consList (locals.drop (d - m)) (cons (R ih.callee) ρ') (B + 1 + m - 1 - B)
  rw [show B + 1 + m - 1 - B = 0 + (locals.drop (d - m)).length from by rw [hvl]; omega,
    consList_apply_add]
  rfl

/-! ## The body equation at a rule's frame -/

/-- The walk's frame list: the rule's prefix and fields (`fvsFr`, in
order), then its `ih` variables, reversed into opening order. -/
@[expose] def targetFrameIh (fvsFr : List Expr) (ihs : Array ConLeche.TargetIh) : List Expr :=
  (fvsFr ++ ihs.toList.map (·.fv)).reverse

theorem FvarList.locList {E : Nat} {xs : List Expr} (h : FvarList E xs) : LocList 0 E xs :=
  ⟨h.1, fun j hj => by simpa using h.2.1 j hj⟩

set_option maxHeartbeats 1600000 in
/-- **The body equation of one rule, at its frame**: the stored rule's
body, read at the frame's values, is the residue read at the frame
extended by the `ih` values — `interp_targetAbstract` at the walk's
entry, its premise discharged by `targetNodeVal_of`.  What stays a
premise is the frame's own data: the `ih` values' identification with
the call's λ (`hihv`, the model's choice of `ih` terms), the callee's
value (`hcallee`), the walk's context at the entry (`hW`: the frame's
readings, grading and fit), and the residue's scoping and typing. -/
theorem targetRuleBodyEq {envT : Env} {mT : EnvModel V envT}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    (hproj : ∀ (sn : Name) (i : Nat), envT.findProj? sn i = env.findProj? sn i)
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {fr : ConLeche.TargetFrame} {B : Nat} {body bodyO : Expr} {ihs : Array ConLeche.TargetIh}
    {fvsFr : List Expr}
    (habs : ConLeche.targetAbstract fr B 0 (body.instantiateList fvsFr.reverse 0) #[]
      = some (bodyO, ihs))
    (hbf : body.hasFvar = false) (hFr : FvarList B fvsFr.reverse)
    {ρ' : Nat → V} {ihvals : List V} {R : Nat → V} {pw : ConLeche.PropWhen}
    (hbit : pwBit φ pw ≠ 0) (hih : ihvals.length = ihs.size)
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0)
    (hpref : ∀ x ∈ fr.pref, x.looseBVarsBounded 0 = true)
    (hfields : ∀ x ∈ fr.fields, x.looseBVarsBounded 0 = true)
    (hcallee : ∀ (nm : Name) (c : Nat), ConLeche.nameIdxOf? fr.recNames nm = some c →
      ∃ ci : ConstantInfo, env.find? nm = some ci ∧
        fr.rlvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ ρ : Nat → V,
          interp V ρ (acval nm (Level.substFn φ ci.toConstantVal.levelParams fr.rlvls)) = R c)
    (hteles : ∀ (r : Nat) (ih : ConLeche.TargetIh), ihs[r]? = some ih →
      ∀ t ∈ (fr.teles.getD ih.field []).map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < B)
    (hihv : ∀ (r : Nat) (ih : ConLeche.TargetIh), ihs[r]? = some ih →
      ∃ L : AnnotTerm, denoteMeta acval env φ (B + 1) (targetCallE fr B pw ih) = some L ∧
        ihvals.getD r pt = interp V (cons (R ih.callee) ρ') L)
    {Δa : List AnnotTerm}
    (hL : FvarList (B + ihs.size) (targetFrameIh fvsFr ihs))
    (hW : WalkCtx V mT φ (B + ihs.size) (consList ihvals ρ') Δa (targetFrameIh fvsFr ihs))
    (hlL : ∀ l ∈ bodyO.fvarLeaves, Expr.fvar l.1 l.2 ∈ targetFrameIh fvsFr ihs)
    (hbT : bodyO.looseBVarsBounded 0 = true) (hcbe : ConstsBound envT bodyO)
    (hty : IhTyped envT (B + ihs.size) bodyO)
    {as1 : List Expr} (h1 : LocList 0 B as1) {A Bv : AnnotTerm}
    (hA : denoteMeta acval env φ B (body.instantiateList as1 0) = some A)
    (hB : denoteMeta mT.acval envT φ (B + ihs.size) bodyO = some Bv) :
    interp V ρ' A = interp V (consList ihvals ρ') Bv := by
  -- the accumulator's entries: the frame's `ih` variables at their `ih` types
  obtain ⟨-, hwf⟩ := targetAbstract_acc (fr := fr) (B := B) 0 _ #[] bodyO ihs habs
  have hwfF : TargetIhWF fr B ihs := hwf (fun r hr => absurd hr (by simp))
  have hcall : TargetNodeVal V acval env φ mT fr B ihs (targetFrameIh fvsFr ihs) ρ' ihvals := by
    refine targetNodeVal_of hacl haclT hin hmono hbit hih hle hpref hfields hcallee ?_
    intro r ih hr
    obtain ⟨hrl, hrget⟩ := Array.getElem?_eq_some_iff.mp hr
    obtain ⟨hfv, hty'⟩ := hwfF r hrl
    rw [hrget] at hfv hty'
    refine ⟨?_, ?_, hteles r ih hr, hihv r ih hr⟩
    · rw [targetFrameIh, List.mem_reverse, ← hfv]
      refine List.mem_append_right _ (List.mem_map.mpr ⟨ih, ?_, rfl⟩)
      rw [← hrget]
      exact Array.getElem_mem_toList hrl
    · unfold ConLeche.targetIhTy at hty'
      obtain ⟨X, -, hX⟩ := Option.map_eq_some_iff.mp hty'
      exact ⟨X, hX.symm⟩
  -- the stored body's leaves are the frame's
  have hlF : ∀ l ∈ (body.instantiateList fvsFr.reverse 0).fvarLeaves, l.1 < B := by
    intro l hl
    obtain ⟨x, hx, hlx⟩ := fvarLeaves_instantiateList hFr body hbf 0 l hl
    exact ConLeche.Expr.fvarLeaves_lt_of_wscoped (hFr.2.2 x hx) l hlx
  -- the reading at the caller's openers is the reading at the frame's
  have hd := denoteMeta_open_deepen (acval := acval) (env := env) (φ := φ) hacl 0 0 body B as1
    fvsFr.reverse (by simp [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hbf]) h1
    (by simpa using hFr.locList)
  simp only [Nat.zero_add] at hd
  rw [hA] at hd
  cases hA' : denoteMeta acval env φ B (body.instantiateList fvsFr.reverse 0) with
  | none => rw [hA'] at hd; exact nomatch hd
  | some A' =>
    rw [hA', Option.map_some] at hd
    obtain rfl : A = A' := by
      rw [Option.some.inj hd, ConLeche.Semantics.AnnotTerm.liftN_zero]
    have := interp_targetAbstract hacl haclT hin hproj hmono hih hcall
      (body.instantiateList fvsFr.reverse 0) 0 #[] bodyO ihs [] [] [] Δa A Bv habs
      (List.prefix_refl _) (fun r hr => absurd hr (by simp)) hlF hlL hbT hcbe
      (LocList.nil B) (LocList.nil (B + ihs.size)) (by simpa using hL) rfl LocalsFit.nil
      (by simpa using hW)
      (by simpa [ConLeche.Expr.instantiateList_nil] using hty)
      (by simpa [ConLeche.Expr.instantiateList_nil] using hA')
      (by simpa [ConLeche.Expr.instantiateList_nil] using hB)
    simpa using this

end NodeVal

end ConLeche.Model
