module

public import ConLeche.Verify.Inductives.PosDeriv
public import ConLeche.Model.Inductives.NestPosOut
public import ConLeche.Verify.EnvWF
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InferLeaves

public section

/-!
# The positivity derivation's SHAPE (lane POSDERIV)

Syntactic facts read off the derivation `PosD` by induction, never off
the run:

* `posD_tele_open`: a derived telescope opens (`openPisAtFvars`) at its
  base depth onto its result, one kind and one output per field, each
  opened domain derived as a field;
* `posD_field_out`: a derived field's output is bvar-closed, hole-free at
  an ordinary kind, and — at no frames — never `inProgress`;
* `fields_open`: a closed normal form opens onto its outputs;
* `memberCtorD_open`: a member constructor's normal form, opened, each
  domain erasure-equal to its field's output.
-/

namespace ConLeche.Model

open ConLeche (Env Expr Name NestCtx NestHole BinderMeta PosD PosJ PosKind PosTree closeTelescope
  fueledOps openPisAtFvars)

/-- **A derived telescope, opened**: one kind and one output per field,
the telescope opening onto its result at its base depth, and each opened
domain derived as a field at its depth. -/
theorem posD_tele_open {ops : ConLeche.CheckerOps ConLeche.CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {J : PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
      | .tele prog base nF j cur ks nds res =>
        ks.length = nF ∧ nds.length = nF ∧ ∃ xs, openPisAtFvars nF cur (base + j) = some (xs, res) ∧
          ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd ts', ks[i]? = some k ∧
            nds[i]?.map (·.1) = some nd ∧
            PosD ops env ctx (.field prog (base + j + i) 0 x.fvarTypeD k nd) ts'
      | _ => True := by
  intro J ts h
  induction h with
  | teleNil => exact ⟨rfl, rfl, [], by simp [openPisAtFvars], fun _ _ hx => nomatch hx⟩
  | @teleCons prog base nF j a b bm k nd ks nds res ts ts' ha _ _ ihb =>
    obtain ⟨hkl, hnl, xs, hop, hall⟩ := ihb
    refine ⟨by simp [hkl], by simp [hnl], .fvar (base + j) a :: xs, ?_, fun i x hx => ?_⟩
    · simp only [openPisAtFvars]
      rw [show base + j + 1 = base + (j + 1) by omega, hop]
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨k, nd, ts, rfl, rfl, by simpa [Expr.fvarTypeD] using ha⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨k', nd', ts'', h1, h2, h3⟩ := hall i x hx
        refine ⟨k', nd', ts'', by simpa using h1, by simpa using h2, ?_⟩
        rw [show base + j + (i + 1) = base + (j + 1) + i by omega]
        exact h3
  | _ => trivial

/-- **A derived field's output**: bvar-closed (for a bvar-closed input),
hole-free at an ordinary kind, and — at no frames — never `inProgress`
(a frame's hole needs a frame). -/
theorem posD_field_out {env : Env} (henv : ConLeche.EnvWF env) {F : Nat} {ctx : NestCtx} :
    ∀ {J : PosJ} {ts : List PosTree}, PosD (fueledOps .verified F) env ctx J ts → match J with
      | .field prog dep _ e k nf => e.looseBVarsBounded 0 = true → ctx.hiAt prog.length ≤ dep →
          nf.looseBVarsBounded 0 = true ∧
          (k = .ordinary → nf.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false) ∧
          (prog = [] → k ≠ .inProgress)
      | _ => True := by
  intro J ts h
  have hwb : ∀ {dep : Nat} {e w : Expr}, (fueledOps .verified F).whnf env dep e = .ok w →
      e.looseBVarsBounded 0 = true → w.looseBVarsBounded 0 = true :=
    fun hw hcl => ConLeche.whnf_looseBVars henv F (show ConLeche.whnf .verified env F _ _ = _ from hw)
      hcl
  induction h with
  | @const prog dep kb e w hw hocc =>
    intro hcl _
    refine ⟨?_, fun _ => ?_, fun _ => nofun⟩
    · split
      · exact hwb hw hcl
      · exact hcl
    · split
      · exact hocc
      · rename_i h; simpa using h
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ihb =>
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
  | @hole prog dep kb e w i ty hw =>
    intro hcl _
    refine ⟨hwb hw hcl, fun hk => ?_, fun _ hk => ?_⟩ <;> split at hk <;> exact nomatch hk
  | @frameHole prog dep kb e w i ty h hw hocc hfn hlo hhi' =>
    intro hcl _
    refine ⟨hwb hw hcl, (fun hk => nomatch hk), fun hp => ?_⟩
    subst hp
    simp only [List.length_nil] at hhi'
    omega
  | contNew hw => intro hcl _; exact ⟨hwb hw hcl, nofun, fun _ => nofun⟩
  | contHit hw => intro hcl _; exact ⟨hwb hw hcl, nofun, fun _ => nofun⟩
  | _ => trivial

/-- **A walked telescope's normal form, opened** (any frames, any base
depth): the closed normal form opens at the base; every opened domain is
erasure-equal to its field's output. -/
theorem fields_open {base nF : Nat} {res : Expr} {nds : List (Expr × BinderMeta)}
    (hrescl : res.looseBVarsBounded 0 = true) (hnl : nds.length = nF)
    (hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) :
    ∃ (xs : List Expr) (rest : Expr),
      openPisAtFvars nF (closeTelescope nds base res) base = some (xs, rest) ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ nd,
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd := by
  obtain ⟨xs, rest, hop, -, hdoms⟩ := open_of_erasedEq_closeTelescope nds base res
    (closeTelescope nds base res) hndcl hrescl (Expr.ErasedEq.rfl _)
  rw [hnl] at hop
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  refine ⟨xs, rest, hop, fun i x hx => ?_⟩
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨p, hp⟩ : ∃ p, nds[i]? = some p := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  exact ⟨p.1, by rw [hp]; rfl, hdoms i x p.1 hx (by rw [hp]; rfl)⟩

/-- **A member constructor's normal form, opened** (its derivation's
telescope): it opens at the block's depth; every opened domain is
erasure-equal to its field's output, hole-free at an ordinary kind, and no
kind is `inProgress`. -/
theorem memberCtorD_open {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    {nF : Nat} {crest tyN cur : Expr} {ks : List PosKind} {nds : List (Expr × BinderMeta)}
    {ts : List PosTree} (hcl : crest.looseBVarsBounded 0 = true)
    (htele : PosD (fueledOps .verified F) env ctx (.tele [] (ctx.hiAt 0) nF 0 crest ks nds cur) ts)
    (htyN : tyN = closeTelescope nds (ctx.hiAt 0) cur) :
    ∃ (xs : List Expr) (rest : Expr),
      openPisAtFvars nF tyN (ctx.hiAt 0) = some (xs, rest) ∧ ks.length = nF ∧
      nds.length = nF ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd ∧
        (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
        k ≠ .inProgress := by
  obtain ⟨hkl, hnl, xs₀, hop₀, hall⟩ := posD_tele_open htele
  rw [Nat.add_zero] at hop₀
  obtain ⟨hcurcl, hxcl⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop₀ hcl
  have hxl₀ : xs₀.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop₀
  -- every field's output, read off its derivation
  have hfield : ∀ (i : Nat) (x : Expr), xs₀[i]? = some x → ∃ k nd,
      ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧ nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP (ctx.hiAt 0) = false) ∧
      k ≠ .inProgress := by
    intro i x hx
    obtain ⟨k, nd, ts', hk, hnd, hd⟩ := hall i x hx
    obtain ⟨h1, h2, h3⟩ := posD_field_out henv hd (hxcl x (List.mem_of_getElem? hx))
      (by simp only [List.length_nil]; omega)
    exact ⟨k, nd, hk, hnd, h1, h2, h3 rfl⟩
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
