module

public import ConLeche.Verify.Inductives.ClassInv
import ConLeche.Verify.EnvWF
public import ConLeche.Model.Inductives.StoredShapes
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Inductives.ErasureKit
import ConLeche.Verify.Subst
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The class check's derivation, its SHAPE (P2d, DESIGN CLASSCHECK / P2D4)

Syntactic facts read off the flat derivation `FieldD` by induction (the
class ports of the old walk's `posD_field_out`/`posD_tele_open`/
`fields_open`, whose modules go at the flip):

* `fieldD_field_out`: a derived field's output is bvar-closed, and
  hole-free at an ordinary kind;
* `fieldD_tele_open`: a derived telescope opens onto its result at its
  base depth, every opened domain derived as a field;
* `classCtorWalk_open`: a class constructor's normal form, opened, each
  domain erasure-equal to its field's output, hole-free at an ordinary
  kind.
-/

namespace ConLeche.Model
open ConLeche.Semantics

universe w

open ConLeche (Env Expr Name NestCtx BinderMeta ClassInfo ClassJ ClassField FieldD closeTelescope
  fueledOps openPisAtFvars)

variable {env : Env} {F : Nat} {ctx : NestCtx} {cls : List ClassInfo} {hi : Nat}

/-- **A derived field's output**: bvar-closed for a bvar-closed input,
hole-free at an ordinary kind. -/
theorem fieldD_field_out (henv : ConLeche.EnvWF env) :
    ∀ {J : ClassJ}, FieldD (fueledOps .verified F) env ctx cls hi J → match J with
      | .field dep _ e k nf => e.looseBVarsBounded 0 = true → hi ≤ dep →
          nf.looseBVarsBounded 0 = true ∧
          (k = .ordinary → nf.nestOcc ctx.names ctx.nP hi = false)
      | _ => True := by
  intro J h
  have hwb : ∀ {dep : Nat} {e w : Expr}, (fueledOps .verified F).whnf env dep e = .ok w →
      e.looseBVarsBounded 0 = true → w.looseBVarsBounded 0 = true :=
    fun hw hcl => ConLeche.whnf_looseBVars henv F (show ConLeche.whnf .verified env F _ _ = _ from hw)
      hcl
  induction h with
  | @const dep kb e w hw hocc =>
    intro hcl _
    refine ⟨?_, fun _ => ?_⟩
    · split
      · exact hwb hw hcl
      · exact hcl
    · split
      · exact hocc
      · rename_i h; simpa using h
  | @pi dep kb e a b bm k nb hw hocc ha hb ihb =>
    intro hcl hhi
    have hwcl := hwb hw hcl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hwcl
    obtain ⟨h1, h2⟩ := ihb (ConLeche.looseBVarsBounded_instantiate1 (d := dep) (ty := a) b 0
      hwcl.2) (by omega)
    refine ⟨?_, fun ho => ?_⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hwcl.1, ConLeche.looseBVarsBounded_abstract1 nb 0 h1⟩
    · simp only [Expr.nestOcc, ha, Bool.false_or]
      rw [nestOcc_abstract1 (by omega) nb 0]
      exact h2 ho
  | memberHole hw =>
    intro hcl _
    exact ⟨hwb hw hcl, fun hk => nomatch hk⟩
  | classHole hw =>
    intro hcl _
    exact ⟨hwb hw hcl, fun hk => nomatch hk⟩
  | _ => trivial

/-- **A derived telescope, opened**: one kind and one output per field,
the telescope opening onto its result at its base depth, each opened
domain derived as a field at its depth. -/
theorem fieldD_tele_open :
    ∀ {J : ClassJ}, FieldD (fueledOps .verified F) env ctx cls hi J → match J with
    | .tele base nF j cur ks nds res =>
      ks.length = nF ∧ nds.length = nF ∧ ∃ xs, openPisAtFvars nF cur (base + j) = some (xs, res) ∧
        ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
          nds[i]?.map (·.1) = some nd ∧
          FieldD (fueledOps .verified F) env ctx cls hi (.field (base + j + i) 0 x.fvarTypeD k nd)
    | _ => True := by
  intro J h
  induction h with
  | teleNil => exact ⟨rfl, rfl, [], by simp [openPisAtFvars], fun _ _ hx => nomatch hx⟩
  | @teleCons base nF j a b bm k nd ks nds res ha _ _ ihb =>
    obtain ⟨hkl, hnl, xs, hop, hall⟩ := ihb
    refine ⟨by simp [hkl], by simp [hnl], .fvar (base + j) a :: xs, ?_, fun i x hx => ?_⟩
    · simp only [openPisAtFvars]
      rw [show base + j + 1 = base + (j + 1) by omega, hop]
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        exact ⟨k, nd, rfl, rfl, by simpa [Expr.fvarTypeD] using ha⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        obtain ⟨k', nd', h1, h2, h3⟩ := hall i x hx
        refine ⟨k', nd', by simpa using h1, by simpa using h2, ?_⟩
        rw [show base + j + (i + 1) = base + (j + 1) + i by omega]
        exact h3
  | _ => trivial

/-- **A walked telescope's normal form, opened** (any base depth): the
closed normal form opens at the base; every opened domain is
erasure-equal to its field's output. -/
theorem fields_openC {base nF : Nat} {res : Expr} {nds : List (Expr × BinderMeta)}
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

/-- **A class constructor's normal form, opened** (its walk's telescope):
it opens at the holes' depth; every opened domain is erasure-equal to its
field's output, hole-free at an ordinary kind. -/
theorem classWalk_open (henv : ConLeche.EnvWF env) {nF : Nat} {crest cur : Expr}
    {ks : List ClassField} {nds : List (Expr × BinderMeta)}
    (hcl : crest.looseBVarsBounded 0 = true)
    (htele : FieldD (fueledOps .verified F) env ctx cls hi (.tele hi nF 0 crest ks nds cur)) :
    ∃ (xs : List Expr) (rest : Expr),
      openPisAtFvars nF (closeTelescope nds hi cur) hi = some (xs, rest) ∧ ks.length = nF ∧
      nds.length = nF ∧
      ∀ (i : Nat) (x : Expr), xs[i]? = some x → ∃ k nd, ks[i]? = some k ∧
        nds[i]?.map (·.1) = some nd ∧ Expr.ErasedEq x.fvarTypeD nd ∧
        (k = .ordinary → nd.nestOcc ctx.names ctx.nP hi = false) := by
  obtain ⟨hkl, hnl, xs₀, hop₀, hall⟩ := fieldD_tele_open htele
  rw [Nat.add_zero] at hop₀
  obtain ⟨hcurcl, hxcl⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop₀ hcl
  have hxl₀ : xs₀.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop₀
  have hfield : ∀ (i : Nat) (x : Expr), xs₀[i]? = some x → ∃ k nd,
      ks[i]? = some k ∧ nds[i]?.map (·.1) = some nd ∧ nd.looseBVarsBounded 0 = true ∧
      (k = .ordinary → nd.nestOcc ctx.names ctx.nP hi = false) := by
    intro i x hx
    obtain ⟨k, nd, hk, hnd, hd⟩ := hall i x hx
    obtain ⟨h1, h2⟩ := fieldD_field_out henv hd (hxcl x (List.mem_of_getElem? hx)) (by omega)
    exact ⟨k, nd, hk, hnd, h1, h2⟩
  have hndcl : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true := by
    intro p hp
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
    have hil : i < xs₀.length := by
      rw [hxl₀, ← hnl]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨k, nd, -, hnd, hcl', -⟩ := hfield i _ (List.getElem?_eq_getElem hil)
    rw [hi, Option.map_some, Option.some.injEq] at hnd
    rw [hnd]; exact hcl'
  obtain ⟨xs, rest, hop, hdoms⟩ := fields_openC hcurcl hnl hndcl
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length nF hop
  refine ⟨xs, rest, hop, hkl, hnl, fun i x hx => ?_⟩
  have hi : i < nF := by rw [← hxl]; exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, xs₀[i]? = some x₀ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨k, nd, hk, hnd, -, hord⟩ := hfield i x₀ hx₀
  obtain ⟨nd', hnd', hE⟩ := hdoms i x hx
  rw [hnd] at hnd'
  obtain rfl := Option.some.inj hnd'
  exact ⟨k, nd, hk, hnd, hE, hord⟩

/-! ## Erasure and U4, re-homed -/

/-- The occurrence test ignores what erasure ignores. -/
theorem erasedEq_nestOcc {names : List Name} {lo hi : Nat} :
    ∀ (a b : Expr), Expr.ErasedEq a b → a.nestOcc names lo hi = b.nestOcc names lo hi := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | fvar i ty _ => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | const n us => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.nestOcc]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ihf _ h.1, iha _ h.2]
  | lam ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | forallE ty bd mm iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.2.1, ihb _ h.2.2]
  | letE ty v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, iht _ h.1, ihv _ h.2.1, ihb _ h.2.2]
  | proj s i e ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq] at h
    simp only [Expr.nestOcc, ih _ h.2.2]


section Producer

variable {V : Type w} [SetTheory V] {m : EnvModel V env} {ψ : Name → Nat}

/-- **U4, read**: a field whose variable no later binder and not the result
uses is read by no later field — at any base depth (a container frame's
telescope). -/
theorem u4_fieldSlotAt {b nF l l' : Nat} {crest rest : Expr} {xs : List Expr}
    {x : Expr} {ea : AnnotTerm}
    (hop : openPisAtFvars nF crest (b) = some (xs, rest))
    (hW : Expr.WScoped (b) crest) (hU : structUsedLater crest 0 l = false)
    (hl : l < nF) (hll : l < l') (hx : xs[l']? = some x)
    (hr : denoteMeta m.acval env ψ (b + l') x.fvarTypeD = some ea) :
    NoBVar (LfpDatum.fieldSlot l l') ea := by
  obtain ⟨⟨bs, r⟩, hst⟩ := Option.isSome_iff_exists.mp
    (stripPis_of_openPis nF hop (l + 1) (by omega))
  have hfree : r.hasLooseBVar 0 = false := by
    unfold structUsedLater at hU
    rw [Nat.zero_add, hst] at hU
    simpa [Expr.hasLooseBVarB_eq] using hU
  obtain ⟨h1, -⟩ := openPisAtFvars_leaf_free nF l hop hl hst hfree fun z hz => by
    have := Expr.fvarLeaves_lt_of_wscoped hW z hz
    omega
  have hxfree : ∀ z ∈ x.fvarTypeD.fvarLeaves, z.1 ≠ b + l := by
    intro z hz
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF crest (b) hop l' x hx
    exact h1 l' hll _ hx z (by simp only [Expr.fvarTypeD] at hz; simp [Expr.fvarLeaves, hz])
  have hwx := openPisAtFvars_typeWScoped nF hop hW l' x hx
  obtain ⟨X, rfl⟩ := denoteMeta_liftN_of_leaf_free m _ _ hwx (q := b + l) (by omega)
    hxfree hr
  refine NoBVar.mono (fun i hi => ?_) (noBVar_liftN_one X _)
  simp only [LfpDatum.fieldSlot] at hi
  omega

end Producer

end ConLeche.Model
