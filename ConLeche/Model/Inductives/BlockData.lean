module

public import ConLeche.Model.Inductives.SumKit
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Kernel.Inductives.FieldTele
import ConLeche.Kernel.Inductives.BlockInstall
public section

/-!
# A block constructor's data (task #315 M3)

`FixData.lean` at `k` members: a constructor of a block member, read
at an environment holding ALL the block's formers.  The sum's data
(`CtorDataI`, the readings of the constructor's telescope) together
with its opening at the canonical variables (parameters at `0 ..< nP`,
fields at `nP ..< nP + nF`): every field's opened domain reads to its
entry (`domRead`), and the opened residual is the member at the
parameter variables and the index arguments (`resShape`).  No field is
classified: what a field reading a member looks like is the stored
field shape facts' (`StoredFieldShapes`, lane HOLE2).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The constructor's data -/

/-- The leading Π-entries of a Π-telescope's reading carry the reading's
bits: domain bit `0`, codomain bit a `pwBit` (so at most `1`). -/
theorem stripPisAV_denoteMeta_bits {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} :
    ∀ (n : Nat) {d : Nat} {e : Expr} {fvs : List Expr} {o : Expr} {ea : AnnotTerm}
      {pps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      openPisAtFvars n e d = some (fvs, o) → denoteMeta acval env φ d e = some ea →
      stripPisAV n ea = some (pps, b) → ∀ p ∈ pps, p.1 = 0 ∧ p.2.1 ≤ 1
  | 0, _, _, _, _, _, _, _, _, _, hst => by
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, -⟩ := hst
    exact fun _ h => nomatch h
  | n + 1, d, e, fvs, o, ea, pps, b, hop, hr, hst => by
    match e, hop with
    | .forallE ty bd mb, hop =>
      obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hr
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [stripPisAV] at hst
        cases hst' : stripPisAV n ba with
        | none => rw [hst'] at hst; exact nomatch hst
        | some q =>
          rw [hst'] at hst
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
          obtain ⟨rfl, -⟩ := hst
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · refine ⟨rfl, ?_⟩
            show pwBit φ mb.pw ≤ 1
            unfold pwBit; split <;> omega
          · exact stripPisAV_denoteMeta_bits n hop' hba hst' p hp
      · exact nomatch hop
    | .bvar _, hop => nomatch hop
    | .fvar _ _, hop => nomatch hop
    | .sort _, hop => nomatch hop
    | .const _ _, hop => nomatch hop
    | .app _ _, hop => nomatch hop
    | .lam _ _ _, hop => nomatch hop
    | .letE _ _ _, hop => nomatch hop
    | .proj _ _ _, hop => nomatch hop
    | .lit _, hop => nomatch hop

/-- **A block constructor's data** at a carrier storing ALL the
block's formers (see the module docstring). -/
structure BlockCtorDataI {env : Env} (m : EnvModel V env) (T : Name)
    (lps : List Name) (cvC : ConstantVal) (nP nF nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (idxArgs : List Expr)
    (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm)
    (srcs : List (Option Nat)) (fvsP xFvs : List Expr) (xrest : Expr) : Prop
    extends CtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs where
  opens : ∃ crest, openPisAtFvars nP cvC.type 0 = some (fvsP, crest) ∧
    openPisAtFvars nF crest nP = some (xFvs, xrest)
  xLen : xFvs.length = nF
  pLen : fvsP.length = nP
  xIdx : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty
  pIdx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty
  idxEq : idxArgs = xrest.getAppArgs.drop nP
  domRead : ∀ ψ i x, xFvs[i]? = some x →
    denoteMeta m.acval env ψ (nP + i) x.fvarTypeD = some ((ds ψ).getD (nP + i) default).2.2
  /-- the opened residual is the member at the parameter variables and the
  index arguments (lane HOLE2: the result the hole reading abstracts) -/
  resShape : xrest = Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)

end ConLeche.Model

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-- The parameter variables read to the parameter spine at depth `D`. -/
theorem denoteMetaSpine_params {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    (D : Nat) {fvsP : List Expr} {nP : Nat} (hlen : fvsP.length = nP)
    (hidx : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty) :
    DenoteMetaSpine acval env φ D fvsP (paramBvarsAt nP D) := by
  have := denoteMetaSpine_fvars (acval := acval) (env := env) (φ := φ) D fvsP 0
    (fun k x hx => by
      obtain ⟨ty, h⟩ := hidx k x hx
      exact ⟨ty, by rw [h, Nat.zero_add]⟩)
  rw [hlen] at this
  have he : ((List.range nP).map fun k => AnnotTerm.bvar (D - 1 - (0 + k))) = paramBvarsAt nP D := by
    unfold paramBvarsAt
    apply List.map_congr_left
    intro k _
    rw [Nat.zero_add]
  rwa [he] at this

/-- The Π-tower's closedness, inverted: the domains under the earlier
ones, the body under all. -/
theorem bvarsBelow_mkPisAV_inv {k : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}, Term.bvarsBelow k (mkPisAV ds b).erase →
      DomsBelow k ds ∧ Term.bvarsBelow (k + ds.length) b.erase
  | [], _, h => ⟨trivial, by simpa [mkPisAV] using h⟩
  | d :: ds, b, h => by
    simp only [mkPisAV, AnnotTerm.erase_pi] at h
    obtain ⟨hd, hb⟩ := h
    obtain ⟨h1, h2⟩ := bvarsBelow_mkPisAV_inv (k := k + 1) (ds := ds) hb
    exact ⟨⟨hd, h1⟩, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2⟩

omit [SetTheory V] in
/-- An opening's variables (their types) and residual resolve when the
opened term does. -/
theorem openPisAtFvars_constsResolve {env₀ : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      e.constsResolve env₀ = true → openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, x.constsResolve env₀ = true) ∧ o.constsResolve env₀ = true
  | 0, e, d, fvs, o, he, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, he, hop => by
    match e, he, hop with
    | .forallE dom bd mb, he, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        simp only [Expr.constsResolve, Bool.and_eq_true] at he
        obtain ⟨hfvs, ho⟩ := openPisAtFvars_constsResolve n
          (Expr.constsResolve_instantiate1 he.1 0 he.2) h₁
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · simpa [Expr.constsResolve] using he.1
        · exact hfvs x hx
      · exact nomatch hop

omit [SetTheory V] in
/-- An argument of a resolving application resolves. -/
theorem Expr.constsResolve_of_mem_getAppArgs {env₀ : Env} :
    ∀ (e a : Expr), e.constsResolve env₀ = true → a ∈ e.getAppArgs →
      a.constsResolve env₀ = true
  | .app f a', a, h, ha => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    rcases ha with ha | rfl
    · exact Expr.constsResolve_of_mem_getAppArgs f a h.1 ha
    · exact h.2
  | .bvar _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .fvar _ _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .sort _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .const _ _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .lam _ _ _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .forallE _ _ _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .letE _ _ _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .proj _ _ _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])
  | .lit _, _, _, ha => absurd ha (by simp [Expr.getAppArgs])

/-- **The result's index arguments resolve where the stored type does**:
they are arguments of the opened residual. -/
theorem BlockCtorDataI.idxArgs_resolve {env : Env} {m : EnvModel V env} {T : Name}
    {lps : List Name} {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {fvsP xFvs : List Expr} {xrest : Expr}
    (h : BlockCtorDataI m T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs fvsP xFvs
      xrest) {env₀ : Env} (hres : cvC.type.constsResolve env₀ = true) :
    ∀ e ∈ idxArgs, e.constsResolve env₀ = true := by
  intro e he
  obtain ⟨crest, hopP, hopX⟩ := h.opens
  have hopAll : openPisAtFvars (nP + nF) cvC.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  obtain ⟨-, hxr⟩ := openPisAtFvars_constsResolve (nP + nF) hres hopAll
  rw [h.idxEq] at he
  exact Expr.constsResolve_of_mem_getAppArgs xrest e hxr (List.mem_of_mem_drop he)

/-- **A block constructor's data**, from its stage run at the
environment holding ALL the block's formers. -/
theorem blockCtorData_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name}
    {lps : List Name} {nP nF nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {cvC cvTa cvCa : ConstantVal} {env₁ : Env} {caps : IndCaps}
    {bs : List (Expr × BinderMeta)} {sorts : List Level} {sT : Level}
    (hCtor : ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx resSort
      isProp large cvC nF cvTa = .ok (cvCa, sorts))
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hsT : ∀ ψ : Name → Nat, sT.eval ψ = resSort.eval ψ)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort sT)) :
    ∃ (idxArgs : List Expr) (ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (Es : (Name → Nat) → List AnnotTerm) (srcs : List (Option Nat))
      (fvsP xFvs : List Expr) (xrest : Expr),
      BlockCtorDataI mp.base2 T lps cvCa nP nF nIdx resSort isProp large
        idxArgs ds Es srcs fvsP xFvs xrest := by
  obtain ⟨idxArgs, ds, Es, srcs, -, ⟨fvsP, crest, xFvs, xrest, hopP, hopX, hidxEq⟩, hCD⟩ :=
    sumCtorData_of hμ mp hCtor hfT hlpsT hsT hstripT
  obtain ⟨hcf, -, -, hcb⟩ := ConLeche.direct_sum_ctor_typeWF hCtor
  obtain ⟨hlenP, hidxP, -⟩ := opening_vars_at hopP
  obtain ⟨hlenX, hidxX, -⟩ := opening_vars_at hopX
  obtain ⟨-, -, fvsP₂, crest₂, tfvs, trest, xFvs₂, idxArgs₂, hopC, -, -, hopX₂, -, -, -, -⟩ :=
    ConLeche.checkSumCtor_shape hCtor
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hopP.symm.trans hopC))
  obtain ⟨rfl, hxr⟩ := Prod.mk.inj (Option.some.inj (hopX.symm.trans hopX₂))
  have hidxX' : ∀ k x, xFvs[k]? = some x → ∃ ty, x = Expr.fvar (nP + k) ty := hidxX
  have hidxP' : ∀ k x, fvsP[k]? = some x → ∃ ty, x = Expr.fvar k ty := fun k x hx => by
    obtain ⟨ty, h⟩ := hidxP k x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩
  have hopAll : openPisAtFvars (nP + nF) cvCa.type 0 = some (fvsP ++ xFvs, xrest) :=
    openPisAtFvars_add nP hopP (by rw [Nat.zero_add]; exact hopX)
  -- every field's opened domain reads to its entry
  have hdomRead : ∀ ψ i x, xFvs[i]? = some x →
      denoteMeta mp.base2.acval env ψ (nP + i) x.fvarTypeD
        = some ((ds ψ).getD (nP + i) default).2.2 := by
    intro ψ i x hx
    have hO := opened_of_peel hopAll hcf hcb (hCD.read ψ) (hCD.len ψ) (hCD.okTy ψ)
    have hxA : (fvsP ++ xFvs)[nP + i]? = some x := by
      rw [List.getElem?_append_right (by omega), hlenP, Nat.add_sub_cancel_left]
      exact hx
    have hi : i < nF := by rw [← hlenX]; exact (List.getElem?_eq_some_iff.mp hx).1
    have hd := hO.doms (nP + i) x hxA
    have hget : (ds ψ)[nP + i]? = some ((ds ψ).getD (nP + i) default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hCD.len ψ]; omega)]
      rfl
    rw [getD_reverse_of_peel (hCD.len ψ) (by omega) hget] at hd
    exact hd
  refine ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, ⟨hCD, ⟨crest, hopP, hopX⟩, hlenX, hlenP,
    hidxX', hidxP', hidxEq, hdomRead, ?_⟩⟩
  rw [hidxEq, hxr, Expr.getAppArgs_mkAppN]
  simp only [Expr.getAppArgs, List.nil_append]
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
    List.nil_append]

end ConLeche.Model
