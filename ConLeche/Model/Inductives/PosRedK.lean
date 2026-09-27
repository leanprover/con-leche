module

public import ConLeche.Model.Inductives.NestPosRed
public import ConLeche.Verify.Inductives.PosDerivK
public import ConLeche.Verify.EnvWF
import ConLeche.Model.Inductives.PosDerivShape
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Semantics.Inductives.FieldsEqOn
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
import ConLeche.Semantics.Frame
import ConLeche.Verify.Leaves
import ConLeche.Verify.Abstract
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The key-named derivation's normal form reads like its input, and its shape (PRIMREC / NESTKN-M5)

The install reads two facts of a member constructor's positivity derivation
besides its monotonicity and accessibility: the normal form READS like the
declared crest (`memberCtorD_red`, `NestPosRed.lean`) and the normal form,
opened, has one output per field, erasure-equal to its domain, hole-free at
an ordinary kind and never `inProgress` (`memberCtorD_open`,
`PosDerivShape.lean`).  Their key-named twins, by induction on `PosDKH` (at
ANY hook — neither reads the use rule):

* `posDK_red` / `memberCtorDK_red` — `posD_red`'s motive at a layout's depth
  `L.hi` (every field case is a `whnf` step, `red_whnf`; `pi`/`teleCons` as
  today);
* `posDK_field_out` / `posDK_tele_open` / `memberCtorDK_open` — at the ROOT
  layout no family and no own hole exists, so no field is `inProgress`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx BinderMeta closeTelescope fueledOps PosDKH PosJK
  PosKind UseHookK LayoutK MemberCtorDKH rootLayoutK openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

variable {env : Env} {m : EnvModel V env} {φ : Name → Nat}

section Motive

variable (m φ)

/-- **What a key-named derivation proves of its outputs**: `RedJ` at a
layout's depth. -/
@[expose] def RedJK : PosJK → Prop
  | .field _ _ dep _ e _ nd =>
    Frame dep e → ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
      CtxOkP m φ dep Δa e → denoteMeta m.acval env φ dep e = some ea → Graded V Δa ea →
      Frame dep nd ∧ LeavesSub nd e ∧ ∃ nda, denoteMeta m.acval env φ dep nd = some nda ∧
        Graded V Δa nda ∧ ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ nda
  | .tele L _ n j cur _ nds res =>
    Frame (L.hi + j) cur → ∀ {Δa : List AnnotTerm} {ca : AnnotTerm},
      CtxOkP m φ (L.hi + j) Δa cur → denoteMeta m.acval env φ (L.hi + j) cur = some ca →
      Graded V Δa ca →
      ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ca = mkPisAV abD B ∧
        denoteMeta m.acval env φ (L.hi + j) (closeTelescope nds (L.hi + j) res)
          = some (mkPisAV abN B) ∧
        abD.length = n ∧ abN.length = n ∧
        abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
        FieldsEqOn V Δa (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
        Graded V Δa (mkPisAV abN B) ∧
        Frame (L.hi + j) (closeTelescope nds (L.hi + j) res) ∧
        LeavesSub (closeTelescope nds (L.hi + j) res) cur
  | _ => True

end Motive

/-- **The key-named derivation's outputs read like its inputs** (`posD_red`'s
twin), by induction on the derivation, at any hook. -/
theorem posDK_red (hin : RulesInputs V m φ) {ctx : NestCtx} {F : Nat} {hk : UseHookK} :
    ∀ {J : PosJK}, PosDKH (fueledOps .verified F) env ctx hk J → RedJK m φ J := by
  intro J h
  induction h with
  | @const L met dep kb e w hw hocc =>
    intro hfr Δa ea hC hea hgr
    split
    · exact red_whnf hin hw hfr hC hea hgr
    · exact ⟨hfr, fun _ h => h, ea, hea, hgr, fun _ _ => rfl⟩
  | @pi L met dep kb e a b mb k nb hw hocc ha hb ihb =>
    intro hfr Δa ea hC hea hgr
    obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ := red_whnf hin hw hfr hC hea hgr
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCw : CtxOkP m φ dep Δa (.forallE a b mb) := hC.of_subset hsub
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    obtain ⟨hfrn, hsubn, nba, hnba, hgn, heqn⟩ :=
      ihb (frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd) hCop hba hgB
    obtain ⟨hwsn, hbn, hLn⟩ := hfrn
    have hbnd : nb.looseBVarsBounded 0 = true := hbn
    refine ⟨⟨?_, ?_, ?_⟩, ?_, .pi 0 (pwBit φ mb.pw) ta nba, ?_, ?_, ?_⟩
    · simp only [Expr.WScoped]
      exact ⟨hws.1, WScoped.abstract1 0 hwsn⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 nb 0 hbnd⟩
    · intro l hl
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hLa l hl
      · exact hLn l (Expr.fvarLeaves_abstract1_lt nb 0 hwsn l hl).1
    · intro l hl
      simp only [Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hsub l (by simp [Expr.fvarLeaves, hl])
      · obtain ⟨hl₁, hl₂⟩ := Expr.fvarLeaves_abstract1_lt nb 0 hwsn l hl
        rcases Expr.fvarLeaves_instantiate1 b 0 (hsubn l hl₁) with h3 | h3
        · exact hsub l (by simp [Expr.fvarLeaves, h3])
        · simp only [Expr.fvarLeaves, List.mem_cons] at h3
          rcases h3 with rfl | h3
          · exact absurd hl₂ (by simp)
          · exact hsub l (by simp [Expr.fvarLeaves, h3])
    · rw [denoteMeta_forallE, hta]
      simp only [bind, Option.bind]
      rw [denoteMeta_erasedEq (erasedEq_abstract1_instantiate1 nb 0 hbnd), hnba]
    · refine graded_pi_intro hgA hgn fun hv0 ρ hρ x hx => ?_
      rw [← heqn _ (Sat_cons V hρ hx)]
      have hgw' := hgw ρ hρ
      have hval := ((AnnotValid_pi V ρ 0 (pwBit φ mb.pw) ta ba) ▸ hgw'.2).2.2 hv0 x hx
      exact hval
    · intro ρ hρ
      rw [heq ρ hρ]
      simp only [interp_pi]
      exact piR_congr fun x hx => heqn _ (Sat_cons V hρ hx)
  | hole hw => intro hfr _ _ hC hea hgr; exact red_whnf hin hw hfr hC hea hgr
  | famHole hw => intro hfr _ _ hC hea hgr; exact red_whnf hin hw hfr hC hea hgr
  | ownHole hw => intro hfr _ _ hC hea hgr; exact red_whnf hin hw hfr hC hea hgr
  | cont hw => intro hfr _ _ hC hea hgr; exact red_whnf hin hw hfr hC hea hgr
  | teleNil =>
    intro hfr Δa ca hC hca hgr
    exact ⟨[], [], ca, rfl, by simpa [closeTelescope, mkPisAV] using hca, rfl, rfl, rfl, trivial,
      by simpa [mkPisAV] using hgr, by simpa [closeTelescope] using hfr,
      fun l hl => by simpa [closeTelescope] using hl⟩
  | @teleCons L met n j a b bm k nd ks nds res _ _ _ iha _ ihb =>
    intro hfr Δa ca hC hca hgr
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    -- the field
    obtain ⟨hfrn, hsubn, nda, hnda, hgn, heqn⟩ := iha ⟨hws.1, hb.1, hLa⟩ hC.forallE_ty hta hgA
    -- the rest, one binder down
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hb.1 hws.2 hb.2 hLa hLbd
    rw [show L.hi + j + 1 = L.hi + (j + 1) by omega] at hCop hfr' hba
    obtain ⟨abD, abN, B, hbaE, hrd, hlD, hlN, hbits, hEq, hgN, hfrc, hsubc⟩ :=
      ihb hfr' hCop hba hgB
    subst hbaE
    rw [show L.hi + (j + 1) = L.hi + j + 1 by omega] at hrd hfrc hsubc
    obtain ⟨hwsc, hbc, hLc⟩ := hfrc
    have hbnd : (closeTelescope nds (L.hi + j + 1) res).looseBVarsBounded 0 = true := hbc
    obtain ⟨hwsn, hbn, hLn⟩ := hfrn
    refine ⟨(0, pwBit φ bm.pw, ta) :: abD, (0, pwBit φ bm.pw, nda) :: abN, B, rfl, ?_,
      by simp [hlD], by simp [hlN], by simp [hbits], ⟨heqn, hEq⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [closeTelescope]
      rw [denoteMeta_forallE, hnda]
      simp only [bind, Option.bind]
      rw [denoteMeta_erasedEq (erasedEq_abstract1_instantiate1 _ 0 hbnd), hrd]
      rfl
    · refine graded_pi_intro hgn (graded_cons_congr heqn hgN) fun hv0 ρ hρ x hx => ?_
      have hx' : x ∈ˢ interp V ρ ta := (heqn ρ hρ).symm ▸ hx
      rw [← interp_mkPisAV_congr abD abN B hbits hEq _ (Sat_cons V hρ hx')]
      have hval := ((AnnotValid_pi V ρ 0 (pwBit φ bm.pw) ta (mkPisAV abD B)) ▸
        (hgr ρ hρ).2).2.2 hv0 x hx'
      exact hval
    · simp only [closeTelescope, Expr.WScoped]
      exact ⟨hwsn, WScoped.abstract1 0 hwsc⟩
    · simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbn, looseBVarsBounded_abstract1 _ 0 hbnd⟩
    · intro l hl
      simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact hLn l hl
      · exact hLc l (Expr.fvarLeaves_abstract1_lt _ 0 hwsc l hl).1
    · intro l hl
      simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact (by simp [Expr.fvarLeaves, hsubn l hl] : l ∈ (Expr.forallE a b bm).fvarLeaves)
      · obtain ⟨hl₁, hl₂⟩ := Expr.fvarLeaves_abstract1_lt _ 0 hwsc l hl
        rcases Expr.fvarLeaves_instantiate1 b 0 (hsubc l hl₁) with h3 | h3
        · simp [Expr.fvarLeaves, h3]
        · simp only [Expr.fvarLeaves, List.mem_cons] at h3
          rcases h3 with rfl | h3
          · exact absurd hl₂ (by simp)
          · simp [Expr.fvarLeaves, h3]
  | _ => trivial

/-- **A key-named member constructor's normal form reads like it**
(`memberCtorD_red`'s twin). -/
theorem memberCtorDK_red (hin : RulesInputs V m φ) {ctx : NestCtx} {F : Nat} {hk : UseHookK}
    {nF : Nat} {crest : Expr} {ks : List PosKind} {tyN : Expr}
    (hd : MemberCtorDKH (fueledOps .verified F) env ctx hk nF crest ks tyN)
    (hfr : Frame (ctx.hiAt 0) crest) {Δa : List AnnotTerm} {ca : AnnotTerm}
    (hC : CtxOkP m φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta m.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca) :
    ∃ (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      ca = mkPisAV abD B ∧ denoteMeta m.acval env φ (ctx.hiAt 0) tyN = some (mkPisAV abN B) ∧
      abD.length = nF ∧ abN.length = nF ∧
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) ∧
      FieldsEqOn V Δa (abD.map (·.2.2)) (abN.map (·.2.2)) ∧
      Graded V Δa (mkPisAV abN B) ∧ Frame (ctx.hiAt 0) tyN ∧ LeavesSub tyN crest := by
  obtain ⟨met, nds, cur, htele, htyN, -⟩ := hd
  subst htyN
  have := posDK_red hin htele (by simpa [rootLayoutK] using hfr) (by simpa [rootLayoutK] using hC)
    (by simpa [rootLayoutK] using hca) hgr
  simpa [rootLayoutK] using this

/-! ## The shape -/

/-- **A key-named field's output**: bvar-closed (for a bvar-closed input),
hole-free at an ordinary kind, and — at a layout with no family and no own
hole (the root) — never `inProgress`. -/
theorem posDK_field_out (henv : ConLeche.EnvWF env) {F : Nat} {ctx : NestCtx} {hk : UseHookK} :
    ∀ {J : PosJK}, PosDKH (fueledOps .verified F) env ctx hk J → match J with
      | .field L _ dep _ e k nf => e.looseBVarsBounded 0 = true → L.hi ≤ dep →
          nf.looseBVarsBounded 0 = true ∧
          (k = .ordinary → nf.nestOcc ctx.names ctx.nP L.hi = false) ∧
          (L.nF = 0 → L.grp = [] → k ≠ .inProgress)
      | _ => True := by
  intro J h
  have hwb : ∀ {dep : Nat} {e w : Expr}, (fueledOps .verified F).whnf env dep e = .ok w →
      e.looseBVarsBounded 0 = true → w.looseBVarsBounded 0 = true :=
    fun hw hcl => ConLeche.whnf_looseBVars henv F (show ConLeche.whnf .verified env F _ _ = _ from hw)
      hcl
  induction h with
  | @const L met dep kb e w hw hocc =>
    intro hcl _
    refine ⟨?_, fun _ => ?_, fun _ _ => nofun⟩
    · split
      · exact hwb hw hcl
      · exact hcl
    · split
      · exact hocc
      · rename_i h; simpa using h
  | @pi L met dep kb e a b bm k nb hw hocc ha hb ihb =>
    intro hcl hhi
    have hwcl := hwb hw hcl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwcl
    obtain ⟨h1, h2, h3⟩ := ihb (ConLeche.looseBVarsBounded_instantiate1 (d := dep) (ty := a) b 0
      hwcl.2) (by omega)
    refine ⟨?_, fun ho => ?_, h3⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hwcl.1, ConLeche.looseBVarsBounded_abstract1 nb 0 h1⟩
    · simp only [Expr.nestOcc, ha, Bool.false_or]
      rw [nestOcc_abstract1 (by omega) nb 0]
      exact h2 ho
  | @hole L met dep kb e w i ty hw =>
    intro hcl _
    refine ⟨hwb hw hcl, fun hk => ?_, fun _ _ hk => ?_⟩ <;> split at hk <;> exact nomatch hk
  | @famHole L met dep kb e w i ty key nI hw hocc hfn hlo hhi' hj =>
    intro hcl _
    refine ⟨hwb hw hcl, (fun hk => nomatch hk), fun hnF _ => ?_⟩
    omega
  | @ownHole L met dep kb e w i ty g hw hocc hfn hlo hhi' hj hg =>
    intro hcl _
    refine ⟨hwb hw hcl, (fun hk => nomatch hk), fun _ hgrp => ?_⟩
    rw [hgrp] at hg
    simp at hg
  | cont hw => intro hcl _; exact ⟨hwb hw hcl, nofun, fun _ _ => nofun⟩
  | _ => trivial

/-- **A key-named telescope, opened**: its fields, their outputs and
derivations (`posD_tele_open`'s twin). -/
theorem posDK_tele_open {ops : ConLeche.CheckerOps ConLeche.CheckM} {ctx : NestCtx}
    {hk : UseHookK} :
    ∀ {J : PosJK}, PosDKH ops env ctx hk J → match J with
    | .tele L met nF j cur ks nds res =>
      ks.length = nF ∧ nds.length = nF ∧ ∃ xs, openPisAtFvars nF cur (L.hi + j) = some (xs, res) ∧
        ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
          nds[i]?.map (·.1) = some nd ∧
          PosDKH ops env ctx hk (.field L met (L.hi + j + i) 0 x.fvarTypeD k nd)
    | _ => True := by
  intro J h
  induction h with
  | teleNil => exact ⟨rfl, rfl, [], by simp [openPisAtFvars], fun _ _ hx => nomatch hx⟩
  | @teleCons L met nF j a b bm k nd ks nds res ha _ _ _ _ ihb =>
    obtain ⟨hkl, hnl, xs, hop, hall⟩ := ihb
    refine ⟨by simp [hkl], by simp [hnl], .fvar (L.hi + j) a :: xs, ?_, fun i x hx => ?_⟩
    · simp only [openPisAtFvars]
      rw [show L.hi + j + 1 = L.hi + (j + 1) by omega, hop]
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨k, nd, rfl, rfl, by simpa [Expr.fvarTypeD] using ha⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨k', nd', h1, h2, h3⟩ := hall i x hx
        refine ⟨k', nd', by simpa using h1, by simpa using h2, ?_⟩
        rw [show L.hi + j + (i + 1) = L.hi + (j + 1) + i by omega]
        exact h3
  | _ => trivial

/-- **A key-named member constructor's normal form, opened**
(`memberCtorD_open`'s twin). -/
theorem memberCtorDK_open (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    {hk : UseHookK} {nF : Nat} {crest tyN cur : Expr} {ks : List PosKind}
    {nds : List (Expr × BinderMeta)} {met : List Nat} (hcl : crest.looseBVarsBounded 0 = true)
    (htele : PosDKH (fueledOps .verified F) env ctx hk
      (.tele (rootLayoutK ctx) met nF 0 crest ks nds cur))
    (htyN : tyN = closeTelescope nds (ctx.hiAt 0) cur) :
    ∃ (xs : List Expr) (rest : Expr),
      openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest) ∧ ks.length = nF ∧
      nds.length = nF ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd ∧
        (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
        k ≠ .inProgress := by
  obtain ⟨hkl, hnl, xs₀, hop₀, hall⟩ := posDK_tele_open htele
  simp only [rootLayoutK, Nat.add_zero] at hop₀ hall
  obtain ⟨hcurcl, hxcl⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop₀ hcl
  have hxl₀ : xs₀.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop₀
  have hfield : ∀ (i : Nat) (x : Expr), xs₀[i]? = some x → ∃ k nd,
      ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧ nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
      k ≠ .inProgress := by
    intro i x hx
    obtain ⟨k, nd, hk, hnd, hd⟩ := hall i x hx
    obtain ⟨h1, h2, h3⟩ := posDK_field_out henv hd (hxcl x (List.mem_of_getElem? hx))
      (by simp)
    exact ⟨k, nd, hk, hnd, h1, by simpa [rootLayoutK] using h2, h3 rfl rfl⟩
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
    have hil : i < xs₀.length := by
      rw [hxl₀, ← hnl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨k, nd, -, hnd, hcl', -, -⟩ := hfield i _ (List.getElem?_eq_getElem hil)
    rw [hi, Option.map_some, Option.some.injEq] at hnd
    rw [hnd]; exact hcl'
  subst htyN
  obtain ⟨xs, rest, hop, hdoms⟩ := fields_open hcurcl hnl hndcl
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  refine ⟨xs, rest, hop, hkl, hnl, fun i x hx => ?_⟩
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, xs₀[i]? = some x₀ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨k, nd, hk, hnd, -, hord, hnip⟩ := hfield i x₀ hx₀
  obtain ⟨nd', hnd', hE⟩ := hdoms i x hx
  rw [hnd] at hnd'
  obtain rfl := Option.some.inj hnd'
  exact ⟨k, nd, hk, hnd, hE, hord, hnip⟩

end ConLeche.Model
