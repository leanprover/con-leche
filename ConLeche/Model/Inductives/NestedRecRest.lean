module

import ConLeche.Verify.Cached.PushChain
import Std.Data.String.ToNat
public import ConLeche.Model.Inductives.BlockDeclRun

public section

/-!
# The nested recursors' stage: the facts beside the class induction

The facts the recursors' stage (`nestedRecStage`, `DeclBlockStep.lean`)
reads beside the class induction, one producer each, at the target
check's run (`TargetRecRun`).
-/

namespace ConLeche

/-! ## `hnd`: the family's names are distinct

The member-major records carry the names `{T_m.rec}` as a set (the
name-set check), the others `{T_0.rec_1 … T_0.rec_n}` as a set
(`targetRecPins`' auxiliary check, `RecPinsF.auxNames`).  Each set is
pinned at its own length, and the generated names are distinct
(`Nat.repr` is injective), so each half is `Nodup` by the pigeonhole;
the halves are disjoint because `"rec" ≠ "rec_" ++ n`. -/

/-- The generated auxiliary names' last components are distinct. -/
theorem auxRecStr_inj {i j : Nat} (h : s!"rec_{i + 1}" = s!"rec_{j + 1}") : i = j := by
  have h2 : toString (i + 1) = toString (j + 1) := by simpa using h
  have := Nat.repr_injective h2
  omega

/-- A member's recursor name is never an auxiliary one's last component. -/
theorem rec_ne_auxRecStr (i : Nat) : "rec" ≠ s!"rec_{i + 1}" := by
  intro h
  have := congrArg String.length h
  simp only [String.length_append] at this
  have h3 : "rec".length = 3 := by decide
  have h4 : (toString "rec_").length = 4 := by decide
  simp only [h3, h4] at this
  omega

/-- The generated auxiliary names are distinct. -/
theorem recAuxWant_nodup (q : BlockShape) : (recAuxWant q).Nodup := by
  unfold recAuxWant
  exact List.Pairwise.map _ (fun i j hij h => hij (auxRecStr_inj (Name.str.inj h).2))
    List.nodup_range

/-- **The target check's pins make the family's names distinct**, given
the members' own. -/
theorem RecPinsF.nodup {q : BlockShape} (h : RecPinsF q)
    (hndM : q.memberNames.Nodup) : (q.recs.map (·.cvR.name)).Nodup := by
  -- the member-major half
  have hown : ((q.recs.filter fun rc => decide (rc.tgt < q.k)).map (·.cvR.name)).Nodup :=
    Cached.blockRecNameSetOk_nodup (p := { q with recs := q.recs.filter fun rc => rc.tgt < q.k })
      h.nameSet hndM
  -- the auxiliary half
  have hA := h.auxNames
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hA
  obtain ⟨⟨hlenA, hwant⟩, hgot⟩ := hA
  have haux : (recAuxGot q).Nodup :=
    Cached.nodup_of_covering (recAuxWant_nodup q) hwant (Nat.le_of_eq hlenA)
  -- the halves are disjoint
  have hdisj : ∀ a ∈ (q.recs.filter fun rc => decide (rc.tgt < q.k)).map (·.cvR.name),
      a ∉ recAuxGot q := by
    intro a ha hb
    have hsetO := h.nameSet
    unfold blockRecNameSetOk at hsetO
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hsetO
    obtain ⟨ms, -, hms⟩ := List.mem_map.mp (hsetO.2 a ha)
    obtain ⟨i, -, hi⟩ := List.mem_map.mp (hgot a hb)
    rw [← hms] at hi
    exact rec_ne_auxRecStr i (Name.str.inj hi).2.symm
  have hperm : ((q.recs.filter fun rc => decide (rc.tgt < q.k)).map (·.cvR.name) ++
      recAuxGot q).Perm (q.recs.map (·.cvR.name)) := by
    unfold recAuxGot
    rw [← List.map_append]
    exact (List.filter_append_perm _ q.recs).map _
  exact hperm.nodup_iff.mp (List.nodup_append.mpr ⟨hown, haux, fun a ha b hb hab =>
    hdisj a ha (hab ▸ hb)⟩)

/-- **`hnd` at any majors**: the stored family's names are distinct —
positionally the records' (`recStageG_recNames`), which the pins make
distinct (`RecPinsF.nodup`). -/
theorem recStageG_nodup {mode : CheckMode} {F : Nat} {env : Env} {p : BlockShape}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : RecStageG mode F env p rs)
    (hndM : p.memberNames.Nodup) : (rs.map (·.1.name)).Nodup := by
  obtain ⟨hpins, hlenR, hall⟩ := recStageG_recNames h
  have hmap : rs.map (·.1.name) = p.recs.map (·.cvR.name) := by
    refine List.ext_getElem? (fun i => ?_)
    by_cases hi : i < p.recs.length
    · obtain ⟨rc, r, hrc, hr, hname, -, -, -⟩ := hall i hi
      simp only [List.getElem?_map, hrc, hr, Option.map_some]
      rw [hname]
    · rw [List.getElem?_eq_none (by simp only [List.length_map, hlenR]; omega),
        List.getElem?_eq_none (by simp only [List.length_map]; omega)]
  rw [hmap]
  exact hpins.nodup hndM

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockShape TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `ctorsIn`, `ctor`: the carried constructors are stored at the major's parameter count

At a member major, the constructors' core record (`BlockCtorsCore`); at
an outside major, the carrier's coverage of the container's block
(`tgtOutCls_of`: the recorded constructors ARE the ones the target
check read off the environment). -/

section Ctors

variable {F : Nat} {envC : Env} {pp : BlockShape}
  {memberCtors : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List Term} {isRec : Bool}
  {A : Nat → (Name → Nat) → Term}

/-- **`ctor` from the constructors' storage**: carried constructors
stored at the major's parameter count have their types bound (the
environment's well-formedness) and read (`EnvModelM.type_reads`).  Any
recursor stage whose carried constructors are stored has `ctor`. -/
theorem tgtRecCtor_seam_of_find {envC : Env} {mpC : EnvModelM V envC}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hfind0 : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
          = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT)) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT) ∧
        ConstsBound envC ctor.1.type ∧
        ∀ ψ : Name → Nat,
          denote mpC.base2.acval envC ψ 0 ctor.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) := by
  intro j r hr i ctor hctor
  obtain ⟨iT, hfind⟩ := hfind0 j r hr i ctor hctor
  have hmem := List.mem_of_find?_eq_some hfind
  have hwfC := mpC.base2.wf.consts _ hmem
  have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = ctor := by
    rw [hrd, List.getD_eq_getElem?_getD, hctor]; rfl
  refine ⟨iT, hfind, constsBound_of_constsResolve _ hwfC.2.2.1, fun ψ => ?_⟩
  obtain ⟨ta, hta⟩ := mpC.type_reads _ hmem ψ
  change denote mpC.base2.acval envC ψ 0 ctor.1.type = some ta at hta
  rw [blockRecCtorTy, hsel, hta]
  rfl

end Ctors


/-! ## The target field domains' length -/

/-! ## `eqP`: the target rule data read alike at valuations agreeing on the recursor's parameters

At ANY major, by the reading's level footprint (`lpDefF`,
`denote_params_extF`): the major's levels and parameters are read
off the recursor type's major domain (the checked type names only the
recursor's level parameters), the fired constructor's type names only
its own (a member's are the block's, a container's are instantiated at
the major's levels, as many as the container's own), and opening at
fvars keeps the footprint. -/

section Params

omit [SetTheory V] in
/-- Opening a telescope at fvars keeps the footprint, in the openers'
types and in the body. -/
theorem lpDefF_openPisAtFvars {ps : List Name} :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      ConLeche.openPisAtFvars n e i = some (fvs, body) → lpDefF ps e = true →
      (∀ x ∈ fvs, lpDefF ps x.fvarTypeD = true) ∧ lpDefF ps body = true
  | 0, e, i, fvs, body, h, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun x hx => (nomatch hx), he⟩
  | n + 1, e, i, fvs, body, h, he => by
    cases e with
    | forallE dom b =>
      simp only [ConLeche.openPisAtFvars] at h
      split at h
      · next fvs' e' hrec =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [lpDefF, Bool.and_eq_true] at he
        obtain ⟨h1, h2⟩ := lpDefF_openPisAtFvars n _ (i + 1) hrec
          (lpDefF_instantiate1 (v := .fvar i dom) rfl _ _ he.2)
        refine ⟨fun x hx => ?_, h2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact he.1
        · exact h1 x hx
      · exact nomatch h
    | _ => simp [ConLeche.openPisAtFvars] at h

/-- The opened domains read alike at valuations agreeing on their
footprint. -/
theorem readOpenedDoms_params {env : Env} (m : EnvModel V env) {ps : List Name}
    {ψ₁ ψ₂ : Name → Nat} (hq : ∀ q ∈ ps, ψ₁ q = ψ₂ q) :
    ∀ (d : Nat) (fvs : List Expr), (∀ x ∈ fvs, lpDefF ps x.fvarTypeD = true) →
      readOpenedDoms m.acval env ψ₁ d fvs = readOpenedDoms m.acval env ψ₂ d fvs
  | _, [], _ => rfl
  | d, x :: xs, h => by
    simp only [readOpenedDoms]
    rw [denote_params_extF m hq _ _ (h x List.mem_cons_self),
      readOpenedDoms_params m hq (d + 1) xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

variable {F : Nat} {envC : Env} {pp : BlockShape} {formers : List ConstantVal}
  {memberCtors : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

end Params

end ConLeche.Model
