module

public import ConLeche.Model.Inductives.NestedCopyIdx
import ConLeche.Model.Levels
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Steps.TowerKit
import ConLeche.Verify.Inductives.NestedCopyTele
import ConLeche.Verify.InstLevels
import ConLeche.Semantics.Tower.FixWire
-- The `inst` kit's two still-unconsumed modules (DESIGN §U.23 (e)):
-- hung here until the assembly `nestedPinsInst_of` reads them.
import ConLeche.Model.Inductives.NestedCopyFound
public section

/-!
# The copy's constructor, read (task #315 L-B, DESIGN §U.23 (e))

`NestedCopyIdx.lean` read a copy's FORMER (a Π-tower ending in a sort).
The `inst` half of `NestedPinsIdent` reads a copy's CONSTRUCTOR — the
container's constructor at the pin, `instPis (instantiateLevelParams
J.lps lvls cc.type) Ds` — whose conclusion is not a sort.  This module
generalises the peel to an arbitrary conclusion (`peelPis_mkPisAV`: the
tower over the data past the components instantiated from cut `0`, the
conclusion instantiated at the remaining data's depth) and states the
reading of the instantiated telescope at depth `nP` from the source's
reading (`instPisILP_read`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The peel at an arbitrary conclusion -/

theorem AnnotTerm.instAll_sort : ∀ (ds : List AnnotTerm) (k s : Nat),
    AnnotTerm.instAll ds k (.sort s) = .sort s
  | [], _, _ => rfl
  | d :: ds, k, s => by simp only [AnnotTerm.instAll, AnnotTerm.inst_sort, instAll_sort ds]

/-- **The peel of a Π-tower along a spine of the parameters' length**:
the tower over the remaining data instantiated from cut `0`, the
conclusion instantiated at the remaining data's depth. -/
theorem peelPis_mkPisAV :
    ∀ (ps I : List (Nat × Nat × AnnotTerm)) (vs : List AnnotTerm) (C : AnnotTerm),
      vs.length = ps.length →
      AnnotTerm.peelPis (mkPisAV (ps ++ I) C) vs
        = some (mkPisAV (instTeleP vs 0 I) (AnnotTerm.instAll vs I.length C))
  | [], I, [], C, _ => by
    simp only [List.nil_append, AnnotTerm.peelPis, instTeleP_nil, AnnotTerm.instAll]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | p :: ps, I, v :: vs, C, h => by
    simp only [List.cons_append, mkPisAV, AnnotTerm.peelPis]
    rw [inst_mkPisAV, instDomsAt_append]
    have hl : vs.length = ps.length := by simpa using h
    have hlen : vs.length = (instDomsAt v 0 ps).length := by rw [instDomsAt_length, hl]
    rw [peelPis_mkPisAV _ _ vs _ hlen, Nat.zero_add, instDomsAt_length, ← hl,
      ← Nat.zero_add vs.length, instTeleP_instDomsAt]
    simp only [AnnotTerm.instAll, List.length_append, Nat.zero_add]
    rw [show ps.length + I.length = I.length + vs.length from by omega]

/-- The sort case is `peelPis_mkPisAV_sort`. -/
theorem peelPis_mkPisAV_sort' (ps I : List (Nat × Nat × AnnotTerm)) (vs : List AnnotTerm) (s : Nat)
    (h : vs.length = ps.length) :
    AnnotTerm.peelPis (mkPisAV (ps ++ I) (.sort s)) vs
      = some (mkPisAV (instTeleP vs 0 I) (.sort s)) := by
  rw [peelPis_mkPisAV _ _ _ _ h, AnnotTerm.instAll_sort]

/-! ## The instantiated telescope, read at depth `nP` -/

/-- **The reading of a closed telescope instantiated at scoped
arguments**: `T` (closed, bounded) reading at `ψJ = substFn ψ ks us` as
`mkPisAV ppsJ C` (bounded), the arguments `Ds` (scoped at `nP`,
bounded) reading as `vs` at depth `nP`; then `instPis
(instantiateLevelParams ks us T) Ds` reads at depth `nP` as the tower
over `ppsJ` past the arguments, instantiated from cut `0`, with `C`
instantiated at the remaining depth. -/
theorem instPisILP_read (m : EnvModel V env) {ψ ψJ : Name → Nat} {nP : Nat}
    {T : Expr} (hTcl : T.hasFvar = false)
    {ks : List Name} {us : List Level} (hψJ : ψJ = Level.substFn ψ ks us)
    {ppsJ : List (Nat × Nat × AnnotTerm)} {C : AnnotTerm}
    (hread : denoteMeta m.acval env ψJ 0 T = some (mkPisAV ppsJ C))
    (hbelow : DomsBelow 0 ppsJ) (hC : Term.bvarsBelow ppsJ.length C.erase)
    {Ds : List Expr} {vs : List AnnotTerm} (hvl : vs.length ≤ ppsJ.length)
    (hDs : ∀ a ∈ Ds, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true)
    (hspine : DenoteMetaSpine m.acval env ψ nP Ds vs)
    {tyI : Expr} (hinst : Expr.instPis (Expr.instantiateLevelParams ks us T) Ds = some tyI) :
    denoteMeta m.acval env ψ nP tyI
      = some (mkPisAV (instTeleP vs 0 (ppsJ.drop vs.length))
          (AnnotTerm.instAll vs (ppsJ.length - vs.length) C)) := by
  have hTa : denoteMeta m.acval env ψ nP (Expr.instantiateLevelParams ks us T)
      = some (mkPisAV ppsJ C) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core m) ψ nP T, ← hψJ,
      denoteMeta_lift m.acval_closed (Expr.WScoped.of_not_hasFvar (d := 0) hTcl) nP (Nat.zero_le _),
      hread]
    simp only [Option.map_some, Nat.sub_zero]
    rw [liftN_eq_self_of_closed (mkPisAV_below_of hbelow (by simpa using hC)) 0 nP]
  obtain ⟨ds, hpr⟩ := ConLeche.instPis_instPisAt Ds _ tyI hinst
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAt_peel m.acval_closed (acval_inst_self m) Ds hpr
    (Expr.WScoped.of_not_hasFvar (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hTcl))
    hDs hTa hspine
  rw [← List.take_append_drop vs.length ppsJ,
    peelPis_mkPisAV _ _ vs C (by rw [List.length_take, Nat.min_eq_left hvl]),
    List.length_drop] at hpeel
  rw [hrest, ← Option.some.inj hpeel]

/-! ## The opened body of a Π-tower, read (task #315 L-B, DESIGN §U.38)

`denoteMeta` on a `∀` ALREADY reads its body OPENED at the binder's own
variable, one depth up (`denoteMeta_forallE`), which is exactly what
`openPisAtFvars` does — so a tower's opened body reads as the tower
reading's own body, with no substitution lemma in between.  This is the
bridge the copies' index readings cross: `instPisILP_read` gives the
reading of the whole instantiated constructor type, and the arms read
its RESIDUAL. -/

/-- The instantiated telescope has the original's length (off
`instTeleP_map`, since the walk's body is not exposed here). -/
theorem instTeleP_length (ds : List AnnotTerm) (c : Nat)
    (pps : List (Nat × Nat × AnnotTerm)) : (instTeleP ds c pps).length = pps.length := by
  have h := congrArg List.length (instTeleP_map ds c pps)
  simp only [List.length_map, instTele_length] at h
  simpa using h

/-- Parameter instantiation distributes over an application node. -/
theorem AnnotTerm.instAll_app : ∀ (ds : List AnnotTerm) (k : Nat) (f a : AnnotTerm),
    AnnotTerm.instAll ds k (.app f a)
      = .app (AnnotTerm.instAll ds k f) (AnnotTerm.instAll ds k a)
  | [], _, _, _ => rfl
  | d :: ds, k, f, a => by
    show AnnotTerm.instAll ds k ((AnnotTerm.app f a).inst d (k + ds.length)) = _
    rw [ConLeche.Semantics.AnnotTerm.inst_app, instAll_app ds k]
    rfl

/-- Parameter instantiation distributes over an application spine. -/
theorem AnnotTerm.instAll_mkAppN (ds : List AnnotTerm) (k : Nat) :
    ∀ (f : AnnotTerm) (args : List AnnotTerm),
      AnnotTerm.instAll ds k (AnnotTerm.mkAppN f args)
        = AnnotTerm.mkAppN (AnnotTerm.instAll ds k f) (args.map (AnnotTerm.instAll ds k))
  | _, [] => rfl
  | f, a :: args => by
    rw [ConLeche.Semantics.AnnotTerm.mkAppN_cons, AnnotTerm.instAll_mkAppN ds k _ args,
      AnnotTerm.instAll_app]
    rfl

/-- A term no substitution touches is untouched by a whole parameter
list — the shape a constant's value has (`EnvModel.acval_inst_self`). -/
theorem AnnotTerm.instAll_eq_self {e : AnnotTerm}
    (h : ∀ (y : AnnotTerm) (k : Nat), e.inst y k = e) :
    ∀ (ds : List AnnotTerm) (k : Nat), AnnotTerm.instAll ds k e = e
  | [], _ => rfl
  | d :: ds, k => by
    show AnnotTerm.instAll ds k (e.inst d (k + ds.length)) = e
    rw [h, AnnotTerm.instAll_eq_self h ds]

/-- **The tower's opened body reads as the tower reading's body.** -/
theorem denoteMeta_openPisAtFvars {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat} :
    ∀ (k : Nat) {d : Nat} {e o : Expr} {fvs : List Expr} {ea : AnnotTerm}
      {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm},
      ConLeche.openPisAtFvars k e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      stripPisAV k ea = some (pds, R) →
      denoteMeta acval env φ (d + k) o = some R := by
  intro k
  induction k with
  | zero =>
    intro d e o fvs ea pds R hop hea hst
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    simp only [stripPisAV, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨-, rfl⟩ := hop
    obtain ⟨-, rfl⟩ := hst
    rw [Nat.add_zero]
    exact hea
  | succ k ih =>
    intro d e o fvs ea pds R hop hea hst
    match e, hop with
    | .forallE ty rest mb, hop =>
      simp only [ConLeche.openPisAtFvars] at hop
      cases hop' : ConLeche.openPisAtFvars k (rest.instantiate1 (.fvar d ty)) (d + 1) with
      | none => rw [hop'] at hop; exact nomatch hop
      | some q =>
        rw [hop'] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨-, rfl⟩ := hop
        obtain ⟨ta, ba, -, hba, rfl⟩ := denoteMeta_forallE_inv hea
        simp only [stripPisAV, Option.map_eq_some_iff] at hst
        obtain ⟨⟨pds', R'⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨-, rfl⟩ := heq
        rw [show d + (k + 1) = d + 1 + k from by omega]
        exact ih hop' hba hst'

/-- **The tower's opened DOMAINS read as the tower reading's domains**
(task #315 L-B): `denoteMeta_openPisAtFvars`' twin at the binders.
`openPisAtFvars` plants `.fvar d dom` carrying the binder's own domain,
and `denoteMeta` on a `∀` reads that domain at the binder's depth — so
opener `l` reads as the tower's `l`-th binder datum, one depth per
binder. -/
theorem denoteMeta_openPisAtFvars_dom {acval : Name → (Name → Nat) → AnnotTerm}
    {φ : Name → Nat} :
    ∀ (k : Nat) {d : Nat} {e o : Expr} {fvs : List Expr} {ea : AnnotTerm}
      {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm},
      ConLeche.openPisAtFvars k e d = some (fvs, o) →
      denoteMeta acval env φ d e = some ea →
      stripPisAV k ea = some (pds, R) →
      ∀ (l : Nat) (x : Expr), fvs[l]? = some x →
        denoteMeta acval env φ (d + l) x.fvarTypeD = some ((pds.getD l default).2.2) := by
  intro k
  induction k with
  | zero =>
    intro d e o fvs ea pds R hop _ _ l x hx
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    simp at hx
  | succ k ih =>
    intro d e o fvs ea pds R hop hea hst l x hx
    match e, hop with
    | .forallE ty rest mb, hop =>
      simp only [ConLeche.openPisAtFvars] at hop
      cases hop' : ConLeche.openPisAtFvars k (rest.instantiate1 (.fvar d ty)) (d + 1) with
      | none => rw [hop'] at hop; exact nomatch hop
      | some q =>
        rw [hop'] at hop
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hea
        simp only [stripPisAV, Option.map_eq_some_iff] at hst
        obtain ⟨⟨pds', R'⟩, hst', heq⟩ := hst
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        cases l with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          rw [Nat.add_zero]
          exact hta
        | succ l =>
          simp only [List.getElem?_cons_succ] at hx
          rw [show d + (l + 1) = d + 1 + l from by omega, List.getD_cons_succ]
          exact ih hop' hba hst' l x hx

/-! ## A read spine, up to erasure (task #315 L-B, DESIGN §U.38 (e) step 4)

The copies' arms compare ONE residual read through two different
openings.  What an interpretation reads of a spine is its head and its
arguments one by one (`ErasedEq.getApp`), and erasure-equal
expressions read equally (`denoteMeta_erasedEq`), so a read spine may
be transported along a pointwise erasure equality. -/

/-- A dropped suffix, positionally (the twin of `NestedPinLaws`'
`getD_drop`, which this module does not see). -/
theorem getD_dropD {α : Type _} [Inhabited α] (as : List α) (n l : Nat) :
    (as.drop n).getD l default = as.getD (n + l) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **A read spine transports along a pointwise erasure equality.** -/
theorem DenoteMetaSpine.erasedEq {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat}
    {d : Nat} :
    ∀ {as bs : List Expr} {vs : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs → as.length = bs.length →
      (∀ l, l < as.length → Expr.ErasedEq (as.getD l default) (bs.getD l default)) →
      DenoteMetaSpine acval env φ d bs vs := by
  intro as bs vs h
  induction h generalizing bs with
  | nil =>
    intro hlen _
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact .nil
  | @cons a v as vs ha _ ih =>
    intro hlen hall
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      have h0 : Expr.ErasedEq a b := by
        have := hall 0 (by simp)
        simpa using this
      refine .cons ?_ (ih (by simpa using hlen) fun l hl => ?_)
      · rw [← denoteMeta_erasedEq h0 d]; exact ha
      · exact hall (l + 1) (by simpa using hl)

end ConLeche.Model
