module

-- `RedSoundKit` is the SHARED kit: `DenoteSpine`'s list algebra,
-- `denote_mkAppN(_inv)`, `frame_spine`,
-- `mkAppN_of_fitA`, `PiChain`/`peelPis_of_piChain` and the tower
-- entry's reading live there, not here.
public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Verify.Denote.Inst
import ConLeche.Verify.Denote.Depth
import ConLeche.Verify.Denote.OpenRevDenote
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.Closed
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Denote.Shift

public section

/-!
# The ι kit (task #305)

The spine, frame and fit lemmas the ι rule and the three stuck-major
rescues need, stated over `Verify/Denote/Lemmas.lean`'s
`DenoteSpine` and the `Frame`/`Graded`/`LeavesSub` abbreviations
of `Motive.lean`:

* the `DenoteSpine` residue only the ι rules use
  (`exists_of_all`); the rest of the spine API is
  `Verify/Denote/Lemmas.lean`'s, shared;
* `interp_mkAppN_congrK`, `constTy_pkg`, `denote_const_arityK`;
* the `take`/`drop`/`getD` list algebra over readings.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The `DenoteSpine` API

`mem` and `getD` are `Verify/Denote/Lemmas.lean`'s; what is left here
is the residue only the ι rules use. -/

namespace DenoteSpine

variable {acval : Name → (Name → Nat) → Term} {d : Nat}

/-- Every list of readable expressions has a reading spine. -/
theorem exists_of_all :
    ∀ (as : List Expr), (∀ x ∈ as, ∃ v, denote acval env φ d x = some v) →
      ∃ vs, DenoteSpine acval env φ d as vs := by
  intro as
  induction as with
  | nil => intro _; exact ⟨[], .nil⟩
  | cons a as ih =>
    intro h
    obtain ⟨v, hv⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := ih (fun y hy => h y (List.mem_cons_of_mem a hy))
    exact ⟨v :: vs, .cons hv hvs⟩

end DenoteSpine

/-- **The spine congruence at `interp`.** -/
theorem interp_mkAppN_congrK {ρ : Nat → V} :
    ∀ (asa bsa : List Term) {fa fb : Term},
      interp V ρ fa = interp V ρ fb →
      asa.map (interp V ρ) = bsa.map (interp V ρ) →
      interp V ρ (Term.mkAppN fa asa)
        = interp V ρ (Term.mkAppN fb bsa) := by
  intro asa
  induction asa with
  | nil =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => exact hf
    | cons _ _ => simp at hall
  | cons a as ih =>
    intro bsa fa fb hf hall
    cases bsa with
    | nil => simp at hall
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hall
      exact ih bs (by simp only [interp_app, hf, hall.1]) hall.2

/-- The frame of an application built over framed parts. -/
theorem frame_mkAppN {d : Nat} {f : Expr} {as : List Expr}
    (hf : Frame d f) (has : ∀ x ∈ as, Frame d x) :
    Frame d (Expr.mkAppN f as) := by
  refine ⟨ConLeche.Expr.WScoped.mkAppN hf.1 (fun y hy => (has y hy).1),
    ConLeche.looseBVarsBounded_mkAppN hf.2.1 (fun y hy => (has y hy).2.1),
    fun l hl => ?_⟩
  rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
  · exact hf.2.2 l hl'
  · exact (has y hy).2.2 l hly

/-- The leaves of an application are its parts' (`fvarLeaves_mkAppN`,
packaged at `Motive.lean`'s `LeavesSub`). -/
theorem leavesSub_mkAppN {f e : Expr} {as : List Expr}
    (hf : LeavesSub f e) (has : ∀ x ∈ as, LeavesSub x e) :
    LeavesSub (Expr.mkAppN f as) e := by
  intro l hl
  rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
  · exact hf l hl'
  · exact has y hy l hly

/-- A closed expression has no leaves at all. -/
theorem leavesSub_of_not_hasFvar {f e : Expr} (h : f.hasFvar = false) :
    LeavesSub f e := by
  intro l hl
  rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  exact nomatch hl

/-! ## The stored data -/

/-- A stored declaration's instantiated type: read at every depth,
graded, inhabited, and closed. -/
theorem constTy_pkg {m : EnvModel V env} (hct : ConstType m φ)
    {n : Name} {ci : ConLeche.ConstantInfo} (hf : env.find? n = some ci) {us : List Level}
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    ∃ ta : Term,
      (∀ d : Nat, denote m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta) ∧
      (∀ ρ : Nat → V, WellDenoted V ρ ta) ∧
      (∀ ρ : Nat → V,
        interp V ρ (m.acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) ∈ˢ interp V ρ ta) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).hasFvar = false ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
  obtain ⟨ta, hta, hok, hmem⟩ := hct 0 n ci us hf hlen
  have hwf := m.wf.consts _ (ConLeche.Env.find?_mem hf)
  have hnf : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hbd : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
    exact hwf.2.2.2.1
  exact ⟨ta, denote_depth_of_closed m.acval_closed hnf
      (fun k => denote_liftN_eq_self m.cval_closed hnf hbd hta 1 k)
      hta,
    fun ρ => (hok ρ).1, hmem, hnf, hbd⟩

/-- A closed stored type is framed and in context at every depth. -/
theorem frame_of_not_hasFvar {m : EnvModel V env} {d : Nat}
    {Δa : List Term} {e : Expr} (hnf : e.hasFvar = false)
    (hbd : e.looseBVarsBounded 0 = true) (hlen : Δa.length = d) :
    Frame d e ∧ CtxOkS m φ d Δa e :=
  ⟨⟨ConLeche.Expr.WScoped.of_not_hasFvar hnf, hbd,
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hnf⟩,
    ⟨hlen, fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl
      exact nomatch hl⟩⟩

/-- A `.const` that reads was applied at the stored arity, and its
reading is the leaf. -/
theorem denote_const_arityK {acval : Name → (Name → Nat) → Term}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    {ea : Term} (hf : env.find? n = some ci)
    (h : denote acval env φ d (.const n us) = some ea) :
    us.length = ci.toConstantVal.levelParams.length ∧
      ea = acval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  rw [denote, hf] at h
  dsimp only at h
  split at h
  · next hlen => exact ⟨hlen, (Option.some.inj h).symm⟩
  · exact nomatch h

/-! ## The list algebra over readings -/

/-- `getD` through `take`, below the cut. -/
theorem getD_takeAK {as : List Term} {k i : Nat} (hi : i < k) :
    (as.take k).getD i default = as.getD i default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, ite_eq_left hi]

/-- `getD` through `drop`. -/
theorem getD_dropAK (as : List Term) (k i : Nat) :
    (as.drop k).getD i default = as.getD (k + i) default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_drop]

/-- A list of length `k + 1` splits as its prefix plus its last element. -/
theorem take_getD_splitAK {as : List Term} {k : Nat}
    (h : as.length = k + 1) :
    as = as.take k ++ [as.getD k default] := by
  have hlen : (as.drop k).length = 1 := by
    rw [List.length_drop, h]; omega
  obtain ⟨a, ha⟩ : ∃ a, as.drop k = [a] := by
    match hd : as.drop k with
    | [a] => exact ⟨a, rfl⟩
    | [] => rw [hd] at hlen; simp at hlen
    | a :: b :: t => rw [hd] at hlen; simp at hlen
  have hget : a = as.getD k default := by
    have h0 : (as.drop k).getD 0 default = a := by rw [ha]; rfl
    rw [getD_dropAK, Nat.add_zero] at h0
    exact h0.symm
  calc as = as.take k ++ as.drop k := (List.take_append_drop k as).symm
    _ = as.take k ++ [as.getD k default] := by rw [ha, hget]

/-! ## The redex's own slots

The subject's grading is about the ORIGINAL major slot and the arity-checked
walk is handed the prepared one, so the last argument is exchanged
along the reduction's own `interp` equation. -/

/-! ## The fired rule's right-hand side and the telescope residual -/

/-- The fired rule's right-hand side reads at every depth. -/
theorem recRhs_depthK {m : EnvModel V env}
    {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hf : env.find? n = some (.recInfo cv mI rP isK rules))
    {rl : RecRule} (hmem : rl ∈ rules) {us : List Level} {Ra : Term}
    (hRa0 : denote m.acval env φ 0
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
      = some Ra) :
    (∀ d : Nat, denote m.acval env φ d
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra) ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).hasFvar = false ∧
      ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
        us).looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    m.wf.consts _ (ConLeche.Env.find?_mem hf)
  obtain ⟨hRnf, -, -, hRbd, -⟩ := hrec' cv mI rP isK rules rfl rl hmem
  have hnf : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hRnf
  have hbd : ((RecRule.rhs rl).instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hRbd
  exact ⟨denote_depth_of_closed m.acval_closed hnf
      (fun k => denote_liftN_eq_self m.cval_closed hnf hbd hRa0 1 k)
      hRa0,
    hnf, hbd⟩

/-- The frame of a `∀`-telescope's residual (at `Motive.lean`'s
`Frame`). -/
theorem piResidual_frameK {m : EnvModel V env} {d : Nat}
    {Δa : List Term} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr},
      ConLeche.piResidual T args = some rest →
      Frame d T → CtxOkS m φ d Δa T →
      (∀ x ∈ args, Frame d x ∧ CtxOkS m φ d Δa x) →
      Frame d rest ∧ CtxOkS m φ d Δa rest := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest h hfr hCt _
    obtain rfl : rest = T := (Option.some.inj h).symm
    exact ⟨hfr, hCt⟩
  | cons a as ih =>
    intro rest h hfr hCt hfrA
    obtain ⟨hw, hb, hL⟩ := hfr
    match T, h with
    | .bvar _, h => exact nomatch h
    | .fvar _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _, h => exact nomatch h
    | .letE _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h
    | .forallE ty body, h =>
    obtain ⟨⟨hwa, hba, hLa⟩, hCa⟩ := hfrA a (by simp)
    simp only [Expr.WScoped] at hw
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    refine ih h ⟨Expr.WScoped.instantiate1_gen hwa 0 hw.2,
        Expr.looseBVarsBounded_instantiate1_gen hba hb.2, fun l hl => ?_⟩
      ⟨hCt.1, fun l hl => ?_⟩ (fun x hx => hfrA x (by simp [hx])) <;>
    · rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · first
        | exact hL l (by simp [Expr.fvarLeaves, h2])
        | exact hCt.2 l (by simp [Expr.fvarLeaves, h2])
      · first
        | exact hLa l h2
        | exact hCa.2 l h2

/-- The leaves of a `∀`-telescope's residual are the telescope's and the
arguments'; graded where those are. -/
theorem piResidual_leavesGrK {m : EnvModel V env} {d : Nat} {ρ : Nat → V} :
    ∀ {T : Expr} {args : List Expr} {rest : Expr},
      ConLeche.piResidual T args = some rest →
      LeavesGr m φ d T ρ → (∀ x ∈ args, LeavesGr m φ d x ρ) →
      LeavesGr m φ d rest ρ := by
  intro T args
  induction args generalizing T with
  | nil =>
    intro rest h hT _
    obtain rfl : rest = T := (Option.some.inj h).symm
    exact hT
  | cons a as ih =>
    intro rest h hT hA
    match T, h with
    | .bvar _, h => exact nomatch h
    | .fvar _ _, h => exact nomatch h
    | .sort _, h => exact nomatch h
    | .const _ _, h => exact nomatch h
    | .app _ _, h => exact nomatch h
    | .lam _ _, h => exact nomatch h
    | .letE _ _ _, h => exact nomatch h
    | .lit _, h => exact nomatch h
    | .proj _ _ _, h => exact nomatch h
    | .forallE ty body, h =>
    refine ih h (fun l hl => ?_) (fun x hx => hA x (by simp [hx]))
    rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
    · exact hT l (by simp [Expr.fvarLeaves, h2])
    · exact hA a (by simp) l h2

/-- **A `TeleFitPA` fit's residual is the reading of the checker's own
`piResidual`**. -/
theorem teleFitPA_residualK {acval : Name → (Name → Nat) → Term}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {ρ : Nat → V} {d : Nat} :
    ∀ (args : List Expr) {ty rest : Expr} {Ta restA : Term}
      {vs : List Term},
      ConLeche.piResidual ty args = some rest →
      Expr.WScoped d ty →
      (∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      denote acval env φ d ty = some Ta →
      DenoteSpine acval env φ d args vs →
      TeleFitPA V ρ Ta vs restA →
      denote acval env φ d rest = some restA := by
  intro args
  induction args with
  | nil =>
    intro ty rest Ta restA vs hpr _ _ hty hsp hfit
    obtain rfl : rest = ty := (Option.some.inj hpr).symm
    cases hsp
    cases hfit
    exact hty
  | cons a as ih =>
    intro ty rest Ta restA vs hpr hwty hargs hty hsp hfit
    match ty, hpr, hwty, hty with
    | .bvar _, hpr, _, _ => exact nomatch hpr
    | .fvar _ _, hpr, _, _ => exact nomatch hpr
    | .sort _, hpr, _, _ => exact nomatch hpr
    | .const _ _, hpr, _, _ => exact nomatch hpr
    | .app _ _, hpr, _, _ => exact nomatch hpr
    | .lam _ _, hpr, _, _ => exact nomatch hpr
    | .letE _ _ _, hpr, _, _ => exact nomatch hpr
    | .lit _, hpr, _, _ => exact nomatch hpr
    | .proj _ _ _, hpr, _, _ => exact nomatch hpr
    | .forallE dom body, hpr, hwty, hty => ?_
    cases hsp with | @cons _ va _ vs' ha hsp' => ?_
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denote_forallE_inv hty
    have hbody' : denote acval env φ d (body.instantiate1 a)
        = some (bodya.inst va) := by
      rw [denote_beta hacl hainst (ty := dom)
        hbodyw.fvarsBelow hwa hba ha 0, hbodya]
      rfl
    cases hfit with
    | cons _ hfit' =>
      exact ih hpr (Expr.WScoped.instantiate1_gen hwa 0 hbodyw)
        (fun x hx => hargs x (List.mem_cons_of_mem a hx)) hbody' hsp' hfit'

/-! ## The reverse opening, read

`denote_openRev_base` and `denote_openRev` — the ONE copy,
which `Model/IndOpenRev.lean` reads from here: the `.nested`
fire's comparands are stored pins instantiated at the recursor's
parameter prefix, and this is what turns the law's OPEN reading at
depth `rP` into the instantiated comparand's reading at the ambient
depth. -/

/-- **The base-independence of the opened reading**: a
constant-frame subject's reverse opening reads to the same term at every base.  The lift the
induction has to absorb is killed by `Term.liftN_eq_self` at the
reading's bvar bound — `denote_closed`'s route, one depth up. -/
theorem denote_openRev_base {acval : Name → (Name → Nat) → Term}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hcl : ∀ n ψ, Term.Closed (acval n ψ))
    {e : Expr} (hnf : e.hasFvar = false) {n : Nat}
    (hb : e.looseBVarsBounded n = true) :
    ∀ d : Nat, denote acval env φ (d + n) (openRev d n e)
      = denote acval env φ n (openRev 0 n e) := by
  intro d
  induction d with
  | zero => rw [Nat.zero_add]
  | succ d ih =>
    have h1 : openRev (d + 1) n e = (openRev d n e).shiftFrom 0 :=
      (openRev_shiftFrom hnf d n).symm
    rw [show d + 1 + n = (d + n) + 1 from by omega, h1,
      denote_shiftFrom (p := 0) hacl (openRev d n e) (d + n)
        (Nat.zero_le _)
        (openRev_WScoped (Expr.WScoped.of_not_hasFvar hnf) n),
      ih]
    cases hden : denote acval env φ n (openRev 0 n e) with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Nat.sub_zero]
      refine Term.liftN_eq_self ?_ 1
      have hws : Expr.WScoped n (openRev 0 n e) := by
        have h2 := openRev_WScoped (d := 0)
          (Expr.WScoped.of_not_hasFvar hnf) n
        rwa [Nat.zero_add] at h2
      have hbv := denote_bvarsBelow (cval := acval) (env := env) (φ := φ)
        hcl n (openRev 0 n e) hws
        (openRev_bounded n 0 (by simpa using hb))
        hden
      exact hbv.mono (by omega)

/-- **Real-argument instantiation, read through the reverse opening.** -/
theorem denote_openRev {acval : Name → (Name → Nat) → Term}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (acval n ψ).inst y k = acval n ψ) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List Term}, DenoteSpine acval env φ d as vs →
      denote acval env φ d (Expr.instSeq as (as.length - 1) e)
        = (denote acval env φ (d + as.length)
            (openRev d as.length e)).map (Term.instRevChain vs) := by
  intro as
  induction as with
  | nil =>
    intro e d _ _ _ vs hsp
    cases hsp
    show denote acval env φ d e = (denote acval env φ (d + 0) e).map _
    cases denote acval env φ d e <;> rfl
  | cons a as ih =>
    intro e d hargs hfb hb vs hsp
    cases hsp with
    | @cons _ va _ vs' ha hsp' => ?_
    have hargs' : ∀ x ∈ as, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true :=
      fun x hx => hargs x (List.mem_cons_of_mem _ hx)
    obtain ⟨hwa, hba⟩ := hargs a List.mem_cons_self
    show denote acval env φ d
      (Expr.instSeq as ((a :: as).length - 1 - 1)
        (e.instantiate1 a ((a :: as).length - 1))) = _
    rw [show (a :: as).length - 1 - 1 = as.length - 1 from by simp,
      show (a :: as).length - 1 = as.length from by simp]
    rw [ih (e := e.instantiate1 a as.length) hargs'
      (Expr.fvarsBelow_instantiate1_gen hwa.fvarsBelow _ hfb)
      (Expr.looseBVarsBounded_instantiate1_gen hba (by simpa using hb))
      hsp']
    -- the opened side: commute the argument out, then β at the top
    rw [openRev_instantiate1_top hba d as.length e]
    have ha' : denote acval env φ (d + as.length) a
        = some (va.liftN as.length) := by
      rw [denote_lift hacl hwa (d + as.length) (by omega), ha,
        show d + as.length - d = as.length from by omega]
      rfl
    rw [denote_beta (ty := .sort .zero) hacl hainst
      (openRev_fvarsBelow hfb as.length) (hwa.mono (by omega)) hba ha' 0]
    show ((denote acval env φ (d + as.length + 1)
      (openRev d (as.length + 1) e)).map
        (Term.inst · (va.liftN as.length) 0)).map
        (Term.instRevChain vs') = _
    rw [Option.map_map,
      show d + as.length + 1 = d + (a :: as).length from by
        simp only [List.length_cons]
        omega,
      show (a :: as).length = as.length + 1 from rfl]
    cases denote acval env φ (d + (as.length + 1))
        (openRev d (as.length + 1) e) with
    | none => rfl
    | some X =>
      simp only [Option.map_some, Option.some.injEq, Function.comp_apply]
      show Term.instRevChain vs' (X.inst (va.liftN as.length) 0) = _
      rw [show Term.instRevChain (va :: vs') X
        = Term.instRevChain vs' (X.inst (va.liftN vs'.length) 0) from rfl,
        hsp'.length]

/-- **Real-argument instantiation, read through the reverse opening**,
`denote_openRev` above at `m.acval`. -/
theorem denote_openRevK {m : EnvModel V env}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : Term) (k : Nat),
      (m.acval n ψ).inst y k = m.acval n ψ) :
    ∀ (as : List Expr) {e : Expr} {d : Nat},
      (∀ a ∈ as, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true) →
      Expr.fvarsBelow d e → e.looseBVarsBounded as.length = true →
      ∀ {vs : List Term}, DenoteSpine m.acval env φ d as vs →
      denote m.acval env φ d (Expr.instSeq as (as.length - 1) e)
        = (denote m.acval env φ (d + as.length)
            (openRev d as.length e)).map (Term.instRevChain vs) :=
  denote_openRev hacl hainst

/-- A list member is the value at one of its indices (the shape the
`∀ x ∈ bsa` grading premises need when the fact is indexed). -/
theorem mem_getD_index {α : Type _} [Inhabited α] {l : List α} {x : α}
    (h : x ∈ l) : ∃ j, j < l.length ∧ l.getD j default = x := by
  obtain ⟨j, hj, hx⟩ := List.getElem_of_mem h
  exact ⟨j, hj, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hx]; rfl⟩

/-! ## The ι case split's kit (task #342 L10) -/

section IotaCase

variable {V : Type w} [SetTheory V]

/-- A fit's last argument may be exchanged for an interpretation-equal
one: the fit reads the argument only through its interpretation's
membership, and the residual after it is the next binder's body at it. -/
theorem teleFitPA_snoc_congr {ρ : Nat → V} :
    ∀ (xs : List Term) {T rest a b : Term},
      TeleFitPA V ρ T (xs ++ [a]) rest → interp V ρ a = interp V ρ b →
      ∃ rest', TeleFitPA V ρ T (xs ++ [b]) rest'
  | [], T, rest, a, b, h, heq => by
    cases h with
    | cons hmem hnil =>
      exact ⟨_, .cons (heq ▸ hmem) .nil⟩
  | x :: xs, T, rest, a, b, h, heq => by
    cases h with
    | cons hmem htail =>
      obtain ⟨rest', h'⟩ := teleFitPA_snoc_congr xs htail heq
      exact ⟨rest', .cons hmem h'⟩

/-- A conditional pointwise comparison of two mapped spines, by index. -/
theorem zip_cond_getD {f : Term → V} :
    ∀ {as bs : List Term}, as.length = bs.length →
      (∀ p ∈ (as.map f).zip (bs.map f), p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) →
      ∀ i, i < as.length → f (as.getD i default) ≠ pt → f (bs.getD i default) ≠ pt →
        f (as.getD i default) = f (bs.getD i default)
  | [], _, _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], hl, _, _, _, _, _ => by simp at hl
  | a :: as, b :: bs, hl, h, i, hi, ha, hb => by
    cases i with
    | zero => exact h (f a, f b) (by simp) ha hb
    | succ i =>
      exact zip_cond_getD (by simpa using hl)
        (fun p hp => h p (by simp only [List.map_cons, List.zip_cons_cons]; exact
          List.mem_cons_of_mem _ hp)) i (by simpa using hi) ha hb

end IotaCase

end ConLeche.Model.Rules
