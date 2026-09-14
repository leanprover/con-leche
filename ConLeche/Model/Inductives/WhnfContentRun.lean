module

public import ConLeche.Model.Inductives.CopyCtorWalkRun
public import ConLeche.Model.Inductives.NestedFormers
public import ConLeche.Model.Inductives.RestoreRead
public import ConLeche.Model.Annot.BitExtendDown
import ConLeche.Model.Inductives.StructRows
import ConLeche.Verify.Inductives.NestedCopyStored
import ConLeche.Verify.Inductives.NestedWalk
import ConLeche.Verify.Leaves

public section

/-!
# The `whnf` arm's content, from the formers' model (task #279 M-D′ D2, DESIGN §M.47)

`CopyCtorWalkRun.lean` names `WhnfContent`: at a container-ORDINARY
field the positivity normalisation `whnf`'d (`WhnfField`), the reading
of the container's instantiated field agrees with `restoreAV`'s arm of
the copy's stored field, at every frame the record's clauses use.  The
content is the `whnf` claim of the model of `env₁ =
consNestedFormers (stored.take p.k) env` (`nestedFormersModel`), and
this module assembles it.  Three kits precede the assembly:

* **the blank** — `Expr.blank` erases every `fvar` annotation.
  `denoteMeta` is blind to annotations (`denoteMeta_erasedEq`), so a
  reading transfers DOWN from the scratch environment to `env₁`
  (`denoteMeta_envExtend_down`, task #306) through the blank, whose
  `ConstsBound`/`NoProjAt` obligations are those of the term's
  NON-annotation nodes alone (`denoteMeta_down_blind`);
* **`CtxOk` at erased leaves** — `ctxOk_of_leaves_erased`: the context
  correlation `WhnfClaim` needs, from readings of the container-side
  openers, when the subject's leaves are those openers UP TO ERASURE
  (`WhnfField`'s leaf clause);
* **the frame** — `sat_of_frame`: the record's frame (`Sat` of the
  block's parameters, `SpineFit` of the container's instantiated
  earlier domains) satisfies the context of the instantiated entries.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The blank: annotation-blind currency -/

namespace Expr

/-- Every `fvar` annotation replaced by `Sort 0`. -/
@[expose] def blank : ConLeche.Expr → ConLeche.Expr
  | .fvar i _ => .fvar i (.sort .zero)
  | .app f a => .app (blank f) (blank a)
  | .lam ty b m => .lam (blank ty) (blank b) m
  | .forallE ty b m => .forallE (blank ty) (blank b) m
  | .letE t v b => .letE (blank t) (blank v) (blank b)
  | .proj s j e => .proj s j (blank e)
  | e => e

theorem erasedEq_blank : ∀ e : ConLeche.Expr, ConLeche.Expr.ErasedEq e (blank e)
  | .bvar _ => by simp [blank, ConLeche.Expr.ErasedEq]
  | .fvar _ _ => by simp [blank, ConLeche.Expr.ErasedEq]
  | .sort _ => by simp [blank, ConLeche.Expr.ErasedEq]
  | .const _ _ => by simp [blank, ConLeche.Expr.ErasedEq]
  | .lit _ => by simp [blank, ConLeche.Expr.ErasedEq]
  | .app f a => by
    simp only [blank, ConLeche.Expr.ErasedEq]
    exact ⟨erasedEq_blank f, erasedEq_blank a⟩
  | .lam ty b _ => by
    simp only [blank, ConLeche.Expr.ErasedEq]
    exact ⟨trivial, erasedEq_blank ty, erasedEq_blank b⟩
  | .forallE ty b _ => by
    simp only [blank, ConLeche.Expr.ErasedEq]
    exact ⟨trivial, erasedEq_blank ty, erasedEq_blank b⟩
  | .letE t v b => by
    simp only [blank, ConLeche.Expr.ErasedEq]
    exact ⟨erasedEq_blank t, erasedEq_blank v, erasedEq_blank b⟩
  | .proj _ _ e => by
    simp only [blank, ConLeche.Expr.ErasedEq]
    exact ⟨trivial, trivial, erasedEq_blank e⟩

/-- The blank's constants are the term's blind mentions. -/
theorem constsBound_blank {env : Env} :
    ∀ e : ConLeche.Expr, (∀ T, e.mentionsConstE T = true → (env.find? T).isSome = true) →
      ConstsBound env (blank e)
  | .bvar _, _ => by simp [blank]
  | .fvar _ _, _ => by simp [blank]
  | .sort _, _ => by simp [blank]
  | .lit _, _ => by simp [blank]
  | .const n _, h => by
    simp only [blank, constsBound_const]
    exact h n (by simp [ConLeche.Expr.mentionsConstE])
  | .app f a, h => by
    simp only [blank, constsBound_app]
    exact ⟨constsBound_blank f fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT]),
      constsBound_blank a fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT])⟩
  | .lam ty b _, h => by
    simp only [blank, constsBound_lam]
    exact ⟨constsBound_blank ty fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT]),
      constsBound_blank b fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT])⟩
  | .forallE ty b _, h => by
    simp only [blank, constsBound_forallE]
    exact ⟨constsBound_blank ty fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT]),
      constsBound_blank b fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT])⟩
  | .letE t v b, h => by
    simp only [blank, constsBound_letE]
    exact ⟨constsBound_blank t fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT]),
      constsBound_blank v fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT]),
      constsBound_blank b fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT])⟩
  | .proj _ _ e, h => by
    simp only [blank, constsBound_proj]
    exact constsBound_blank e fun T hT => h T (by simp [ConLeche.Expr.mentionsConstE, hT])

/-- A name the term does not mention blindly heads none of the blank's
projection nodes. -/
theorem noProjAt_blank_of_not_mentionsConstE {T : Name} {i : Nat} :
    ∀ e : ConLeche.Expr, e.mentionsConstE T = false → ConLeche.Expr.NoProjAt T i (blank e)
  | .bvar _, _ => by simp [blank]
  | .fvar _ _, _ => by simp [blank]
  | .sort _, _ => by simp [blank]
  | .lit _, _ => by simp [blank]
  | .const _ _, _ => by simp [blank]
  | .app f a, h => by
    simp only [ConLeche.Expr.mentionsConstE, Bool.or_eq_false_iff] at h
    simp only [blank, ConLeche.Expr.noProjAt_app]
    exact ⟨noProjAt_blank_of_not_mentionsConstE f h.1, noProjAt_blank_of_not_mentionsConstE a h.2⟩
  | .lam ty b _, h => by
    simp only [ConLeche.Expr.mentionsConstE, Bool.or_eq_false_iff] at h
    simp only [blank, ConLeche.Expr.noProjAt_lam]
    exact ⟨noProjAt_blank_of_not_mentionsConstE ty h.1, noProjAt_blank_of_not_mentionsConstE b h.2⟩
  | .forallE ty b _, h => by
    simp only [ConLeche.Expr.mentionsConstE, Bool.or_eq_false_iff] at h
    simp only [blank, ConLeche.Expr.noProjAt_forallE]
    exact ⟨noProjAt_blank_of_not_mentionsConstE ty h.1, noProjAt_blank_of_not_mentionsConstE b h.2⟩
  | .letE t v b, h => by
    simp only [ConLeche.Expr.mentionsConstE, Bool.or_eq_false_iff] at h
    simp only [blank, ConLeche.Expr.noProjAt_letE]
    exact ⟨noProjAt_blank_of_not_mentionsConstE t h.1.1, noProjAt_blank_of_not_mentionsConstE v h.1.2,
      noProjAt_blank_of_not_mentionsConstE b h.2⟩
  | .proj s _ e, h => by
    simp only [ConLeche.Expr.mentionsConstE, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
    simp only [blank, ConLeche.Expr.noProjAt_proj]
    exact ⟨fun hc => h.1 hc.1, noProjAt_blank_of_not_mentionsConstE e h.2⟩

/-- The blank keeps the absence of a slot's node. -/
theorem noProjAt_blank {T : Name} {i : Nat} :
    ∀ e : ConLeche.Expr, ConLeche.Expr.NoProjAt T i e → ConLeche.Expr.NoProjAt T i (blank e)
  | .bvar _, _ => by simp [blank]
  | .fvar _ _, _ => by simp [blank]
  | .sort _, _ => by simp [blank]
  | .lit _, _ => by simp [blank]
  | .const _ _, _ => by simp [blank]
  | .app f a, h => by
    simp only [ConLeche.Expr.noProjAt_app] at h
    simp only [blank, ConLeche.Expr.noProjAt_app]
    exact ⟨noProjAt_blank f h.1, noProjAt_blank a h.2⟩
  | .lam ty b _, h => by
    simp only [ConLeche.Expr.noProjAt_lam] at h
    simp only [blank, ConLeche.Expr.noProjAt_lam]
    exact ⟨noProjAt_blank ty h.1, noProjAt_blank b h.2⟩
  | .forallE ty b _, h => by
    simp only [ConLeche.Expr.noProjAt_forallE] at h
    simp only [blank, ConLeche.Expr.noProjAt_forallE]
    exact ⟨noProjAt_blank ty h.1, noProjAt_blank b h.2⟩
  | .letE t v b, h => by
    simp only [ConLeche.Expr.noProjAt_letE] at h
    simp only [blank, ConLeche.Expr.noProjAt_letE]
    exact ⟨noProjAt_blank t h.1, noProjAt_blank v h.2.1, noProjAt_blank b h.2.2⟩
  | .proj _ _ e, h => by
    simp only [ConLeche.Expr.noProjAt_proj] at h
    simp only [blank, ConLeche.Expr.noProjAt_proj]
    exact ⟨h.1, noProjAt_blank e h.2⟩

end Expr

/-- **The downward reading transfer, blind**: a reading at the larger
environment is a reading at the smaller one, when the term's BLIND
mentions are stored below and no projection node of the term's blank
sits at a slot tabled above but not below.  The annotations play no
part: `denoteMeta` reads the blank alike. -/
theorem denoteMeta_down_blind {env₁ envAux : Env}
    (hF : FindPreserved env₁ envAux) (hG : LitGuardsMono envAux env₁)
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat} (d : Nat) (e : Expr)
    (hcb : ∀ T, e.mentionsConstE T = true → (env₁.find? T).isSome = true)
    (hnp : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → Expr.NoProjAt sn i (Expr.blank e))
    {ea : AnnotTerm} (h : denoteMeta acval envAux φ d e = some ea) :
    denoteMeta acval env₁ φ d e = some ea := by
  rw [denoteMeta_erasedEq (Expr.erasedEq_blank e)] at h ⊢
  exact denoteMeta_envExtend_down hF hG d _ (Expr.constsBound_blank e hcb) hnp h

/-! ## `CtxOk` at erased leaves -/

/-- **`CtxOk` from openers up to erasure** (`ctxOk_of_openers`'s
transpose at `WhnfField`'s leaf clause): every leaf of the subject is
an opener of the list up to the annotation, the openers' annotations
read at their own depth to the entries `Aa`, and the context holds those
entries at the leaf positions.  The subject's own annotations are never
read — a leaf's reading is its opener's (`denoteMeta_erasedEq`). -/
theorem ctxOk_of_leaves_erased {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {k : Nat} {fvs : List Expr} {Aa : Nat → AnnotTerm} {Δa : List AnnotTerm}
    (hΔlen : Δa.length = k)
    (hdoms : ∀ (i : Nat) (x : Expr), i < k → fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Aa i))
    {e : Expr}
    (hws : Expr.WScoped k e)
    (hleaf : ∀ l ∈ e.fvarLeaves, ∃ tyC, fvs[l.1]? = some (.fvar l.1 tyC) ∧ Expr.ErasedEq l.2 tyC)
    (hent : ∀ i, i < k → Δa[k - 1 - i]? = some (Aa i))
    (hokA : ∀ i, i < k → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i)) :
    CtxOk m φ k Δa e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  obtain ⟨tyC, hx, hE⟩ := hleaf l hl
  obtain ⟨hlt, hwty⟩ := ConLeche.Expr.WScoped_leaves e hws l hl
  refine ⟨hlt, hwty.fvarsBelow, (Aa l.1).liftN (k - l.1) 0, Aa l.1, ?_, hent l.1 hlt, ?_, ?_⟩
  · have hd1 := hdoms l.1 _ hlt hx
    rw [show Expr.fvarTypeD (Expr.fvar l.1 tyC) = tyC from rfl] at hd1
    rw [denoteMeta_lift m.acval_closed hwty k (by omega), denoteMeta_erasedEq hE, hd1]
    rfl
  · intro ρ _
    rw [interp_liftN]
    congr 1
    funext j
    show (if j < 0 then ρ j else ρ (j + (k - l.1))) = ρ (j + (k - 1 - l.1) + 1)
    rw [if_neg (Nat.not_lt_zero j)]
    congr 1
    omega
  · intro ρ hρ
    refine (WellDenotedV_liftN V (k - l.1) (Aa l.1) 0 ρ).mpr ?_
    have h := hokA l.1 hlt ρ hρ
    have henv : shiftE (k - l.1) 0 ρ = fun j => ρ (j + (k - 1 - l.1) + 1) := by
      funext j
      show (if j < 0 then ρ j else ρ (j + (k - l.1))) = _
      rw [if_neg (Nat.not_lt_zero j)]
      congr 1
      omega
    rw [henv]
    exact h


/-! ## The frame: the record's `Sat`/`SpineFit` pair as a context -/

/-- The context of `i` container-instantiated entries over the block's
parameter entries, innermost first (the shape `Sat` reads at
`consList ws σ`). -/
@[expose] def entryCtx (ps : List AnnotTerm) (Cs : Nat → AnnotTerm) (i : Nat) : List AnnotTerm :=
  ((List.range i).map Cs).reverse ++ ps.reverse

omit [SetTheory V] in
theorem entryCtx_length (ps : List AnnotTerm) (Cs : Nat → AnnotTerm) (i : Nat) :
    (entryCtx ps Cs i).length = i + ps.length := by
  simp [entryCtx]

omit [SetTheory V] in
/-- The context's entry at a parameter position. -/
theorem entryCtx_getElem?_param (ps : List AnnotTerm) (Cs : Nat → AnnotTerm) (i : Nat) {l : Nat}
    (hl : l < ps.length) :
    (entryCtx ps Cs i)[i + ps.length - 1 - l]? = ps[l]? := by
  unfold entryCtx
  rw [List.getElem?_append_right (by simp; omega), List.length_reverse, List.length_map,
    List.length_range, List.getElem?_reverse (by omega)]
  congr 1
  omega

omit [SetTheory V] in
/-- The context's entry at a field position. -/
theorem entryCtx_getElem?_field (ps : List AnnotTerm) (Cs : Nat → AnnotTerm) (i : Nat) {k : Nat}
    (hk : k < i) :
    (entryCtx ps Cs i)[i - 1 - k]? = some (Cs k) := by
  unfold entryCtx
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_reverse (by simp; omega),
    List.length_map, List.length_range, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some]
  congr 2
  omega

omit [SetTheory V] in
/-- Dropping the later entries keeps the context of the earlier ones. -/
theorem entryCtx_drop (ps : List AnnotTerm) (Cs : Nat → AnnotTerm) {i k : Nat} (hk : k ≤ i) :
    (entryCtx ps Cs i).drop (i - k) = entryCtx ps Cs k := by
  unfold entryCtx
  rw [List.drop_append_of_le_length
      (by rw [List.length_reverse, List.length_map, List.length_range]; omega),
    List.drop_reverse, List.length_map, List.length_range, show i - (i - k) = k by omega,
    ← List.map_take, List.take_range, Nat.min_eq_left hk]

omit [SetTheory V] in
/-- The instantiated entries, listed by position. -/
theorem instSeqDoms_map_range (DsA : List AnnotTerm) (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)) :
    (instSeqDoms DsA t Γ).map (·.2.2)
      = (List.range Γ.length).map fun k => ((instSeqDoms DsA t Γ).getD k default).2.2 := by
  refine List.ext_getElem? fun k => ?_
  rw [List.getElem?_map, List.getElem?_map]
  by_cases hk : k < Γ.length
  · rw [List.getElem?_range hk]
    simp only [Option.map_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [instSeqDoms_length]; exact hk)]
    rfl
  · have h1 : (instSeqDoms DsA t Γ)[k]? = none := by
      rw [List.getElem?_eq_none_iff, instSeqDoms_length]; omega
    have h2 : (List.range Γ.length)[k]? = none := by
      rw [List.getElem?_eq_none_iff, List.length_range]; omega
    rw [h1, h2]
    rfl

/-- **The record's frame satisfies the context**: `Sat` of the block's
parameters at `σ` and a spine fitting the container's entries
instantiated at the pin's readings give `Sat` of the instantiated
entries' context at `consList ws σ`. -/
theorem sat_of_frame {σ : Nat → V} {ps DsA : List AnnotTerm} {t : Nat}
    {Γ : List (Nat × Nat × AnnotTerm)} {ws : List V}
    (hlen : DsA ≠ [] → DsA.length = t + 1)
    (hσ : Sat V ps.reverse σ)
    (hfit : SpineFit (consList (DsA.map (interp V σ)) σ) (Γ.map (·.2.2)) ws) :
    Sat V (entryCtx ps (fun k => ((instSeqDoms DsA t Γ).getD k default).2.2) Γ.length)
      (consList ws σ) := by
  have hfit' : SpineFit σ ((instSeqDoms DsA t Γ).map (·.2.2)) ws := by
    have h := (spineFit_instSeqDoms_iff (σ := σ) (ws := DsA) [] t Γ ws
      (fun hne => by rw [List.length_nil, Nat.add_zero]; exact hlen hne)).mpr
    simp only [consList_nil] at h
    exact h hfit
  have h := sat_of_spineFit hσ hfit'
  rw [instSeqDoms_map_range] at h
  exact h

/-- The converse: a valuation satisfying the context is the record's
frame — the first `i` values over the rest. -/
theorem frame_of_sat {ps DsA : List AnnotTerm} {t : Nat} {Γ : List (Nat × Nat × AnnotTerm)}
    {ρ : Nat → V} (hlen : DsA ≠ [] → DsA.length = t + 1)
    (h : Sat V (entryCtx ps (fun k => ((instSeqDoms DsA t Γ).getD k default).2.2) Γ.length) ρ) :
    ∃ (σ : Nat → V) (ws : List V), ws.length = Γ.length ∧ ρ = consList ws σ ∧
      Sat V ps.reverse σ ∧
      SpineFit (consList (DsA.map (interp V σ)) σ) (Γ.map (·.2.2)) ws := by
  refine ⟨fun j => ρ (j + Γ.length), (List.range Γ.length).reverse.map ρ, by simp, ?_, ?_, ?_⟩
  · rw [consList_range_reverse]
  · have hd := Sat_drop h (Γ.length - 0)
    rw [entryCtx_drop ps _ (Nat.zero_le _)] at hd
    simp only [entryCtx, List.range_zero, List.map_nil, List.reverse_nil, List.nil_append,
      Nat.sub_zero] at hd
    exact hd
  · have h' : Sat V (((instSeqDoms DsA t Γ).map (·.2.2)).reverse ++ ps.reverse) ρ := by
      rw [instSeqDoms_map_range]; exact h
    have hsp := spineFit_of_sat h'
    rw [List.length_map, instSeqDoms_length] at hsp
    have := (spineFit_instSeqDoms_iff (σ := fun j => ρ (j + Γ.length)) (ws := DsA) [] t Γ
      ((List.range Γ.length).reverse.map ρ)
      (fun hne => by rw [List.length_nil, Nat.add_zero]; exact hlen hne)).mp
    simp only [consList_nil] at this
    exact this hsp

/-! ## The `whnf` claim at a `WhnfField` -/

/-- **The `whnf` arm's reading** (task #279 M-D′ D2): at a field the
positivity normalisation `whnf`'d, the reading of the container's
instantiated field `eC` (the entry `Cs i`) is the reading of the copy's
restored stored field, at every valuation satisfying the entries'
context — `WhnfClaim` of the model of `env₁`, its context correlation
built from the container-side openers' readings through `WhnfField`'s
leaf clause. -/
theorem whnfField_reading {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat} {env₁ : Env}
    (mp₁ : EnvModelM V μ env₁) {ψ : Name → Nat} {R : ConLeche.RestoreTbl}
    {fvsP params xFvsC : List Expr} {nP i : Nat} {eA eC : Expr}
    (hparLen : params.length = nP)
    {ps : List AnnotTerm} (hpsLen : ps.length = nP) {Cs : Nat → AnnotTerm}
    -- the container-side openers' readings, at their own depths
    (hreadP : ∀ (k : Nat) (x : Expr), params[k]? = some x →
      denoteMeta mp₁.base2.acval env₁ ψ k x.fvarTypeD = some (ps.getD k default))
    (hreadC : ∀ (k : Nat) (xC : Expr), k ≤ i → xFvsC[k]? = some xC →
      denoteMeta mp₁.base2.acval env₁ ψ (nP + k) xC.fvarTypeD = some (Cs k))
    (hreadEC : denoteMeta mp₁.base2.acval env₁ ψ (nP + i) eC = some (Cs i))
    -- the entries are graded at their frames
    (hokP : ∀ (k : Nat), k < nP → ∀ ρ : Nat → V, Sat V ps.reverse ρ →
      WellDenotedV V (fun j => ρ (j + (nP - 1 - k) + 1)) (ps.getD k default))
    (hokC : ∀ (k : Nat), k ≤ i → ∀ ρ : Nat → V, Sat V (entryCtx ps Cs k) ρ →
      WellDenotedV V ρ (Cs k))
    -- the field
    (hW : WhnfField μ F env₁ R fvsP (params ++ xFvsC) (nP + i) eA eC)
    -- the restored field's reading (blind to erasure)
    {dsRa : AnnotTerm}
    (hdsR : ∀ dsR : Expr, Expr.ErasedEq dsR (ConLeche.restoreI (R.instAt fvsP) eA) →
      denoteMeta mp₁.base2.acval env₁ ψ (nP + i) dsR = some dsRa) :
    ∀ ρ : Nat → V, Sat V (entryCtx ps Cs i) ρ →
      interp V ρ (Cs i) = interp V ρ dsRa ∧ WellDenotedV V ρ dsRa := by
  obtain ⟨dm, dsR, hdmE, hwhnf, hdsRE, hws, hb, hL, hleaves⟩ := hW
  have hΔlen : (entryCtx ps Cs i).length = nP + i := by rw [entryCtx_length, hpsLen]; omega
  -- the entries by position
  let Aa : Nat → AnnotTerm := fun l => if l < nP then ps.getD l default else Cs (l - nP)
  have hdoms : ∀ (l : Nat) (x : Expr), l < nP + i → (params ++ xFvsC)[l]? = some x →
      denoteMeta mp₁.base2.acval env₁ ψ l x.fvarTypeD = some (Aa l) := by
    intro l x hl hx
    by_cases hl : l < nP
    · rw [List.getElem?_append_left (by omega)] at hx
      simp only [Aa, if_pos hl]
      exact hreadP l x hx
    · rw [List.getElem?_append_right (by omega), hparLen] at hx
      simp only [Aa, if_neg hl]
      have hk : l - nP ≤ i := by omega
      have := hreadC (l - nP) x hk hx
      rw [show nP + (l - nP) = l by omega] at this
      exact this
  have hent : ∀ l, l < nP + i → (entryCtx ps Cs i)[nP + i - 1 - l]? = some (Aa l) := by
    intro l hl
    by_cases hlP : l < nP
    · simp only [Aa, if_pos hlP]
      rw [show nP + i - 1 - l = i + ps.length - 1 - l by omega,
        entryCtx_getElem?_param ps Cs i (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    · simp only [Aa, if_neg hlP]
      rw [show nP + i - 1 - l = i - 1 - (l - nP) by omega]
      exact entryCtx_getElem?_field ps Cs i (by omega)
  have hokA : ∀ l, l < nP + i → ∀ ρ : Nat → V, Sat V (entryCtx ps Cs i) ρ →
      WellDenotedV V (fun j => ρ (j + (nP + i - 1 - l) + 1)) (Aa l) := by
    intro l hl ρ hρ
    by_cases hlP : l < nP
    · simp only [Aa, if_pos hlP]
      have hd := Sat_drop hρ (i - 0)
      rw [entryCtx_drop ps Cs (Nat.zero_le i)] at hd
      simp only [entryCtx, List.range_zero, List.map_nil, List.reverse_nil, List.nil_append,
        Nat.sub_zero] at hd
      have := hokP l hlP _ hd
      have hE : (fun j => ρ (j + (nP + i - 1 - l) + 1))
          = fun j => ρ (j + (nP - 1 - l) + 1 + i) := by
        funext j; congr 1; omega
      rw [hE]
      exact this
    · simp only [Aa, if_neg hlP]
      have hk : l - nP ≤ i := by omega
      have hd := Sat_drop hρ (i - (l - nP))
      rw [entryCtx_drop ps Cs hk] at hd
      have := hokC (l - nP) hk _ hd
      have hE : (fun j => ρ (j + (nP + i - 1 - l) + 1)) = fun j => ρ (j + (i - (l - nP))) := by
        funext j; congr 1; omega
      rw [hE]
      exact this
  have hctx : CtxOk mp₁.base2 ψ (nP + i) (entryCtx ps Cs i) dm :=
    ctxOk_of_leaves_erased hΔlen hdoms hws hleaves hent hokA
  have hdm : denoteMeta mp₁.base2.acval env₁ ψ (nP + i) dm = some (Cs i) := by
    rw [denoteMeta_erasedEq hdmE]; exact hreadEC
  have hdsR' := hdsR dsR hdsRE
  have hclaim := (claimsAt_of hμ mp₁ ψ F).whnf hwhnf hws hb hL hctx hdm hdsR'
    (fun ρ hρ => hokC i (Nat.le_refl i) ρ hρ)
  intro ρ hρ
  exact ⟨hclaim.2 ρ hρ, hclaim.1 ρ hρ⟩


omit [SetTheory V] in
/-- The context depends on the entries below the cut only. -/
theorem entryCtx_congr {ps : List AnnotTerm} {Cs Cs' : Nat → AnnotTerm} {i : Nat}
    (h : ∀ k, k < i → Cs k = Cs' k) : entryCtx ps Cs i = entryCtx ps Cs' i := by
  unfold entryCtx
  congr 2
  exact List.map_congr_left fun k hk => h k (List.mem_range.mp hk)

/-! ## The parameters, graded at their frames -/

/-- **A former's parameter entries are graded at their own frames**: at
a valuation satisfying the parameter context, entry `k` is graded at the
frame below it (`FormerData.okTy` peeled by `wellDenoted_mkPisAV_dom`). -/
theorem params_graded_of_formerData {env : Env} {m : EnvModel V env} {cvT : ConstantVal}
    {n : Nat} {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {lvls : (Name → Nat) → List Nat} (hFD : FormerData m cvT n resSort pps lvls)
    {ψ : Name → Nat} {nP : Nat} (hnP : nP ≤ n) :
    ∀ (k : Nat), k < nP → ∀ ρ : Nat → V, Sat V (((pps ψ).take nP).map (·.2.2)).reverse ρ →
      WellDenotedV V (fun j => ρ (j + (nP - 1 - k) + 1))
        ((((pps ψ).take nP).map (·.2.2)).getD k default) := by
  intro k hk ρ hρ
  have hlenP : (pps ψ).length = n := hFD.len ψ
  have hlen : (((pps ψ).take nP).map (·.2.2)).length = nP := by
    rw [List.length_map, List.length_take]; omega
  -- the first `k` entries, satisfied at the frame below them
  have hd := Sat_drop hρ (nP - k)
  rw [List.drop_reverse, hlen, show nP - (nP - k) = k by omega] at hd
  have hd' : Sat V (((((pps ψ).take nP).map (·.2.2)).take k).reverse ++ [])
      (fun j => ρ (j + (nP - k))) := by
    rw [List.append_nil]; exact hd
  have hsp := spineFit_of_sat hd'
  rw [List.length_take, hlen, Nat.min_eq_left (Nat.le_of_lt hk)] at hsp
  have htake : (((pps ψ).take nP).map (·.2.2)).take k = ((pps ψ).take k).map (·.2.2) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [htake] at hsp
  obtain ⟨dd, hdd⟩ : ∃ dd, (pps ψ)[k]? = some dd :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenP]; omega)⟩
  have hok := hFD.okTy ψ (fun j => (fun j => ρ (j + (nP - k))) (j + k))
  have h1 := wellDenoted_mkPisAV_dom hok.1 _ k dd hdd hsp
  have h2 := annotValid_mkPisAV_dom hok.2 _ k dd hdd hsp
  rw [consList_range_reverse] at h1 h2
  have hE : (fun j => ρ (j + (nP - 1 - k) + 1)) = fun j => ρ (j + (nP - k)) := by
    funext j; congr 1; omega
  have hget : (((pps ψ).take nP).map (·.2.2)).getD k default = dd.2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hk, hdd]
    rfl
  rw [hE, hget]
  exact ⟨h1, h2⟩

/-! ## The restored stored field, read at the formers' model -/

/-- **The unfired arms**: a copy field the restore leaves alone (copy-
ordinary, or recursive into a REAL member — no auxiliary name in it)
reads at the formers' model as the copy's own entry, `restoreAV`'s
second arm: the datum's reading at the scratch model transferred DOWN
(`denoteMeta_down_blind`) and moved to the formers' carrier
(`denoteMeta_acval_congr`). -/
theorem restoredField_read_self {μ : CheckMode} {env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    (hF : FindPreserved env₁ envAux) (hG : LitGuardsMono envAux env₁)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → mp₁.base2.acval n = mpAux.base2.acval n)
    {ψ : Name → Nat} {d : IndRepData V} {k₀ Ja i : Nat}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    {R : ConLeche.RestoreTbl} {fvsP : List Expr} {x : Expr}
    (hself : ConLeche.restoreI (R.instAt fvsP) x.fvarTypeD = x.fvarTypeD)
    (hnotArm : ¬ (i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i))
    (hread : denoteMeta mpAux.base2.acval envAux ψ (d.nP + i) x.fvarTypeD
      = some ((d.dsF Ja ψ).getD (d.nP + i) default).2.2)
    (hmention : ∀ T, x.fvarTypeD.mentionsConstE T = true → (env₁.find? T).isSome = true)
    (hproj : ∀ (sn : Name) (i' : Nat), env₁.findProj? sn i' = none →
      (envAux.findProj? sn i').isSome = true → Expr.NoProjAt sn i' (Expr.blank x.fvarTypeD)) :
    denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i) (ConLeche.restoreI (R.instAt fvsP) x.fvarTypeD)
      = some (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i) := by
  unfold IndRepData.restoreAV
  rw [if_neg hnotArm, hself, denoteMeta_acval_congr hag]
  exact denoteMeta_down_blind hF hG _ _ hmention hproj hread

/-- **The fired arm**: a copy field recursive into a COPY restores to a
field opening at the same variables to the target pin at the index
arguments (`restoreI_copyField`), which reads (`restoredCopyField_read`)
as `restoreAV`'s first arm — the target container's leaf at the pin's
readings lifted over the telescope, at the index readings, under the
telescope.  The telescope's bits are the datum's entries' bits: the
copy's own field reads as `mkPisAV tss _` at the scratch model, whose
Π-entries carry the binder data (`denoteMeta_openPis'`). -/
theorem restoredField_read_copy {μ : CheckMode} {env₁ envAux : Env}
    (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    {ψ : Name → Nat} {d : IndRepData V} {k₀ Ja i : Nat}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    {R : ConLeche.RestoreTbl} {fvsP : List Expr} (hRS : (R.instAt fvsP).Named)
    (hlenP : fvsP.length = R.nP)
    {x : Expr} {n : Nat} {afvs idx : List Expr} {blvls : List Level}
    (hop : ConLeche.openPisAtFvars n x.fvarTypeD (d.nP + i) = some (afvs,
      Expr.mkAppN (.const (d.memberName (d.tgtsR Ja i)) blvls) (fvsP ++ idx)))
    (hdoms : ∀ a ∈ afvs, ∀ m ∈ R.auxNames, a.fvarTypeD.mentionsConst m = false)
    {pin' : Expr}
    (hlook : (R.instAt fvsP).pins.lookup (d.memberName (d.tgtsR Ja i)) = some pin')
    (hpinC : pin'.looseBVarsBounded 0 = true)
    (hrec : (R.instAt fvsP).recMap.lookup (d.memberName (d.tgtsR Ja i)) = none)
    {J'' : Name} {lvls'' : List Level} {Ds'' : List Expr}
    (hpinE : Expr.ErasedEq pin' (Expr.mkAppN (.const J'' lvls'') Ds''))
    (harm : i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i)
    (hcont : tgtCont (d.tgtsR Ja i - k₀) = J'')
    {ci : ConstantInfo} (hJ : env₁.find? J'' = some ci)
    (hlvls : lvls''.length = ci.toConstantVal.levelParams.length)
    (hacv : mp₁.base2.acval J'' (Level.substFn ψ ci.toConstantVal.levelParams lvls'')
      = mpAux.base2.acval J'' (tgtLps (d.tgtsR Ja i - k₀)))
    (htss : ((d.tssR Ja ψ).getD i []).length = n)
    {B : AnnotTerm}
    (hreadA : denoteMeta mpAux.base2.acval envAux ψ (d.nP + i) x.fvarTypeD
      = some (mkPisAV ((d.tssR Ja ψ).getD i []) B))
    (hdomsRead : ∀ (k : Nat) (a : Expr), afvs[k]? = some a →
      denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i + k) a.fvarTypeD
        = some (((d.tssR Ja ψ).getD i []).getD k default).2.2)
    (hDs : DenoteMetaSpine mp₁.base2.acval env₁ ψ (d.nP + i + n) Ds''
      ((tgtDsA (d.tgtsR Ja i - k₀)).map (·.liftN (i + n) 0)))
    (hidx : DenoteMetaSpine mp₁.base2.acval env₁ ψ (d.nP + i + n) idx ((d.eissR Ja ψ).getD i [])) :
    denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i) (ConLeche.restoreI (R.instAt fvsP) x.fvarTypeD)
      = some (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i) := by
  -- the restore, opened
  obtain ⟨o, hopR, hoE⟩ := ConLeche.restoreI_copyField hRS hop hdoms hlook hpinC hlenP hrec
  have hoE' : Expr.ErasedEq o (Expr.mkAppN (Expr.mkAppN (.const J'' lvls'') Ds'') idx) :=
    hoE.trans (Expr.ErasedEq.mkAppN idx idx hpinE rfl (fun k a₁ a₂ h₁ h₂ => by
      rw [h₁] at h₂; obtain rfl := Option.some.inj h₂; exact Expr.ErasedEq.rfl _))
  -- the binders, kept by the restore
  obtain ⟨bs, r, hs, hlenA, hshA, -⟩ := Verify.openPisAtFvars_stripPis n hop
  have hsR := ConLeche.restoreI_stripPis hRS n hs
  -- the bits, off the copy's own reading
  obtain ⟨pps, b, heq, -, hlenpps, hbind⟩ := denoteMeta_openPis' n hop hs hreadA
  obtain ⟨hpps, -⟩ := mkPisAV_inj (by rw [hlenpps, htss]) heq
  have hbits : ∀ (k : Nat) (p : Nat × Nat × AnnotTerm) (bm : Expr × ConLeche.BinderMeta),
      ((d.tssR Ja ψ).getD i [])[k]? = some p →
      (bs.map fun b => (ConLeche.restoreI (R.instAt fvsP) b.1, b.2))[k]? = some bm →
      p.1 = 0 ∧ p.2.1 = pwBit ψ bm.2.pw := by
    intro k p bm hp hbm
    have hk : k < n := by rw [← htss]; exact (List.getElem?_eq_some_iff.mp hp).1
    obtain ⟨ty, hty⟩ := hshA k hk
    obtain ⟨p', hp', h1, ⟨bm', hbm', h2⟩, -⟩ := hbind k _ hty
    rw [hpps] at hp
    obtain rfl := Option.some.inj (hp'.symm.trans hp)
    rw [List.getElem?_map, hbm'] at hbm
    simp only [Option.map_some, Option.some.injEq] at hbm
    subst hbm
    exact ⟨h1, h2⟩
  have hmain := restoredCopyField_read hopR hsR hoE' hJ hlvls htss hbits
    (fun k a p ha hp => by rw [hdomsRead k a ha, List.getD_eq_getElem?_getD, hp]; rfl) hDs hidx
  rw [hmain]
  unfold IndRepData.restoreAV
  rw [if_pos harm, hcont, htss, hacv]

/-! ## The content at one field -/

/-- **`WhnfContent`'s reading conjunct at one field** (task #279 M-D′
D2): from the container-side readings at the formers' model, the
container's entries' grading, the field's `WhnfField` and the restored
stored field's reading as `restoreAV`'s arm, the interpretation of the
container's instantiated field agrees with `restoreAV`'s at every frame
of the record, where the latter is graded. -/
theorem whnfContent_field {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env₁ envAux : Env} (mp₁ : EnvModelM V μ env₁) (mpAux : EnvModelM V μ envAux)
    {ψ ψ' : Name → Nat} {d dJ : IndRepData V} {k₀ Ja Jc i : Nat} {cAJ : ConstantVal × Nat}
    {tgtCont : Nat → Name} {tgtLps : Nat → Name → Nat} {tgtDsA : Nat → List AnnotTerm}
    {R : ConLeche.RestoreTbl} {params xFvsC : List Expr} {DsA : List AnnotTerm}
    {x xC : Expr}
    (hi : i < cAJ.2) (hlenDs : (dJ.dsF Jc ψ').length = dJ.nP + cAJ.2)
    (hlenD : DsA.length = dJ.nP) (hparLen : params.length = d.nP)
    (hpsLen : (d.params ψ).length = d.nP)
    -- the container-side openers' readings at the formers' model
    (hreadP : ∀ (k : Nat) (y : Expr), params[k]? = some y →
      denoteMeta mp₁.base2.acval env₁ ψ k y.fvarTypeD = some ((d.params ψ).getD k default))
    (hreadC : ∀ (k : Nat) (yC : Expr), k ≤ i → xFvsC[k]? = some yC →
      denoteMeta mp₁.base2.acval env₁ ψ (d.nP + k) yC.fvarTypeD
        = some (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + k)
            ((dJ.dsF Jc ψ').getD (dJ.nP + k) default).2.2))
    (hxC : xFvsC[i]? = some xC)
    -- the entries' grading
    (hokP : ∀ (k : Nat), k < d.nP → ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ →
      WellDenotedV V (fun j => ρ (j + (d.nP - 1 - k) + 1)) ((d.params ψ).getD k default))
    (hgradeC : ∀ (k : Nat), k < cAJ.2 → ∀ (σ : Nat → V) (ws : List V), ws.length = k →
      Sat V (d.params ψ).reverse σ →
      SpineFit (consList (DsA.map (interp V σ)) σ)
        ((((dJ.dsF Jc ψ').drop dJ.nP).take k).map (·.2.2)) ws →
      WellDenotedV V (consList ws σ) (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + k - 1)
        ((dJ.dsF Jc ψ').getD (dJ.nP + k) default).2.2))
    -- the field
    (hW : WhnfField μ F env₁ R (d.fvsPF Ja) (params ++ xFvsC) (d.nP + i) x.fvarTypeD xC.fvarTypeD)
    (hrest : denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i)
        (ConLeche.restoreI (R.instAt (d.fvsPF Ja)) x.fvarTypeD)
      = some (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i)) :
    ∀ (σ : Nat → V) (ws : List V), ws.length = i → Sat V (d.params ψ).reverse σ →
      SpineFit (consList (DsA.map (interp V σ)) σ)
        ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws →
      interp V (consList ws σ) (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
          ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2)
        = interp V (consList ws σ) (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i) ∧
      WellDenotedV V (consList ws σ) (d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i) := by
  intro σ ws hws hσ hfit
  -- the entries by position, and the instantiated-domain spelling
  let Cs : Nat → AnnotTerm := fun k => ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + k)
    ((dJ.dsF Jc ψ').getD (dJ.nP + k) default).2.2
  have hlenT : DsA ≠ [] → DsA.length = dJ.nP - 1 + 1 := by
    intro hne
    have : DsA.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
    omega
  have hCsEq : ∀ (Γ : List (Nat × Nat × AnnotTerm)), Γ = ((dJ.dsF Jc ψ').drop dJ.nP).take i →
      ∀ k, k < Γ.length →
      ((instSeqDoms DsA (dJ.nP - 1) Γ).getD k default).2.2 = Cs k := by
    intro Γ hΓ k hk
    subst hΓ
    rw [List.getD_eq_getElem?_getD, instSeqDoms_getElem?]
    have hk' : k < i := by
      have := hk; rw [List.length_take, List.length_drop] at this; omega
    rw [List.getElem?_take_of_lt hk', List.getElem?_drop,
      List.getElem?_eq_getElem (by rw [hlenDs]; omega)]
    simp only [Option.map_some, Option.getD_some, Cs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenDs]; omega)]
    rfl
  have hΓlen : (((dJ.dsF Jc ψ').drop dJ.nP).take i).length = i := by
    rw [List.length_take, List.length_drop, hlenDs]; omega
  -- the frame satisfies the entries' context
  have hsat : Sat V (entryCtx (d.params ψ) Cs i) (consList ws σ) := by
    have h := sat_of_frame (ps := d.params ψ) (Γ := ((dJ.dsF Jc ψ').drop dJ.nP).take i)
      hlenT hσ hfit
    rw [hΓlen] at h
    rw [entryCtx_congr (Cs' := Cs) (fun k hk => hCsEq _ rfl k (by rw [hΓlen]; exact hk))] at h
    exact h
  -- the entries are graded at any satisfying valuation
  have hokC : ∀ (k : Nat), k ≤ i → ∀ ρ : Nat → V, Sat V (entryCtx (d.params ψ) Cs k) ρ →
      WellDenotedV V ρ (Cs k) := by
    intro k hk ρ hρ
    have hΓk : (((dJ.dsF Jc ψ').drop dJ.nP).take k).length = k := by
      rw [List.length_take, List.length_drop, hlenDs]; omega
    have hρ' : Sat V (entryCtx (d.params ψ)
        (fun k' => ((instSeqDoms DsA (dJ.nP - 1) (((dJ.dsF Jc ψ').drop dJ.nP).take k)).getD k'
          default).2.2) (((dJ.dsF Jc ψ').drop dJ.nP).take k).length) ρ := by
      rw [hΓk, entryCtx_congr (Cs' := Cs) (fun k' hk' => by
        have hk'' : k' < i := by omega
        rw [List.getD_eq_getElem?_getD, instSeqDoms_getElem?, List.getElem?_take_of_lt (by omega),
          List.getElem?_drop, List.getElem?_eq_getElem (by rw [hlenDs]; omega)]
        simp only [Option.map_some, Option.getD_some, Cs]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenDs]; omega)]
        rfl)]
      exact hρ
    obtain ⟨σ', ws', hws', rfl, hσ', hfit'⟩ := frame_of_sat hlenT hρ'
    rw [hΓk] at hws'
    have := hgradeC k (by omega) σ' ws' hws' hσ' hfit'
    simp only [Cs]
    rw [instSeq_cut_congr hlenD]
    exact this
  have hreadEC : denoteMeta mp₁.base2.acval env₁ ψ (d.nP + i) xC.fvarTypeD = some (Cs i) :=
    hreadC i xC (Nat.le_refl i) hxC
  have hmain := whnfField_reading hμ mp₁ hparLen hpsLen hreadP hreadC hreadEC hokP hokC hW
    (dsRa := d.restoreAV mpAux.base2 ψ k₀ Ja tgtCont tgtLps tgtDsA i)
    (fun dsR hE => by rw [denoteMeta_erasedEq hE]; exact hrest) _ hsat
  rw [← instSeq_cut_congr hlenD]
  exact hmain


/-! ## Glue for the run-level assembly (DESIGN §M.47) -/

/-- A read spine at one carrier is a read spine at a carrier agreeing
on the stored names. -/
theorem DenoteMetaSpine.acval_congr {env : Env} {φ : Name → Nat} {d : Nat}
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    (hag : ∀ n, (env.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval₁ env φ d as vs →
      DenoteMetaSpine acval₂ env φ d as vs
  | _, _, .nil => .nil
  | _, _, .cons ha hrest =>
    .cons (by rw [← denoteMeta_acval_congr hag]; exact ha) (DenoteMetaSpine.acval_congr hag hrest)

/-- A read spine at the larger environment is one at the smaller,
component by component (`denoteMeta_down_blind`). -/
theorem DenoteMetaSpine.down_blind {env₁ envAux : Env}
    (hF : FindPreserved env₁ envAux) (hG : LitGuardsMono envAux env₁)
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm},
      (∀ a ∈ as, ∀ T, a.mentionsConstE T = true → (env₁.find? T).isSome = true) →
      (∀ a ∈ as, ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
        (envAux.findProj? sn i).isSome = true → Expr.NoProjAt sn i (Expr.blank a)) →
      DenoteMetaSpine acval envAux φ d as vs → DenoteMetaSpine acval env₁ φ d as vs
  | _, _, _, _, .nil => .nil
  | a :: _, _, hcb, hnp, .cons ha hrest =>
    .cons (denoteMeta_down_blind hF hG d a (hcb a List.mem_cons_self) (hnp a List.mem_cons_self) ha)
      (DenoteMetaSpine.down_blind hF hG (fun a' ha' => hcb a' (List.mem_cons_of_mem _ ha'))
        (fun a' ha' => hnp a' (List.mem_cons_of_mem _ ha')) hrest)

namespace Expr

/-- A blind mention of an instantiation is one of the body or of the
substituted term. -/
theorem mentionsConstE_instantiate1 {T : Name} {v : Expr} :
    ∀ (e : Expr) (k : Nat), (e.instantiate1 v k).mentionsConstE T = true →
      e.mentionsConstE T = true ∨ v.mentionsConstE T = true
  | .bvar i, k, h => by
    simp only [ConLeche.Expr.instantiate1] at h
    split at h
    · exact Or.inr h
    · split at h <;> simp [ConLeche.Expr.mentionsConstE] at h
  | .fvar _ _, _, h => by simp [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE] at h
  | .sort _, _, h => by simp [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE] at h
  | .lit _, _, h => by simp [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE] at h
  | .const _ _, _, h => by
    simp only [ConLeche.Expr.instantiate1] at h
    exact Or.inl h
  | .app f a, k, h => by
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases mentionsConstE_instantiate1 f k h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases mentionsConstE_instantiate1 a k h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .lam ty b _, k, h => by
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases mentionsConstE_instantiate1 ty k h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases mentionsConstE_instantiate1 b (k + 1) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .forallE ty b _, k, h => by
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases mentionsConstE_instantiate1 ty k h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases mentionsConstE_instantiate1 b (k + 1) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .letE t v' b, k, h => by
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · rcases mentionsConstE_instantiate1 t k h with h' | h'
      · exact Or.inl (Or.inl (Or.inl h'))
      · exact Or.inr h'
    · rcases mentionsConstE_instantiate1 v' k h with h' | h'
      · exact Or.inl (Or.inl (Or.inr h'))
      · exact Or.inr h'
    · rcases mentionsConstE_instantiate1 b (k + 1) h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .proj _ _ e, k, h => by
    simp only [ConLeche.Expr.instantiate1, ConLeche.Expr.mentionsConstE, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases mentionsConstE_instantiate1 e k h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

/-- A blind mention of `instPis` is one of the telescope or of an
argument. -/
theorem mentionsConstE_instPis {T : Name} :
    ∀ (Ds : List Expr) (e e' : Expr), ConLeche.Expr.instPis e Ds = some e' →
      e'.mentionsConstE T = true →
      e.mentionsConstE T = true ∨ ∃ D ∈ Ds, D.mentionsConstE T = true
  | [], e, e', h, hm => by
    simp only [ConLeche.Expr.instPis, Option.some.injEq] at h
    subst h
    exact Or.inl hm
  | D :: Ds, e, e', h, hm => by
    match e, h with
    | .forallE ty body bm, h =>
      simp only [ConLeche.Expr.instPis] at h
      rcases mentionsConstE_instPis Ds _ e' h hm with h' | ⟨D', hD', hm'⟩
      · rcases mentionsConstE_instantiate1 body 0 h' with h'' | h''
        · exact Or.inl (by simp [ConLeche.Expr.mentionsConstE, h''])
        · exact Or.inr ⟨D, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨D', List.mem_cons_of_mem _ hD', hm'⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
    | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [ConLeche.Expr.instPis] at h

/-- `instPis` keeps the absence of a slot's node. -/
theorem NoProjAt.instPis {T : Name} {i : Nat} :
    ∀ (Ds : List Expr) (e e' : Expr), ConLeche.Expr.instPis e Ds = some e' →
      ConLeche.Expr.NoProjAt T i e → (∀ D ∈ Ds, ConLeche.Expr.NoProjAt T i D) →
      ConLeche.Expr.NoProjAt T i e'
  | [], e, e', h, he, _ => by
    simp only [ConLeche.Expr.instPis, Option.some.injEq] at h
    subst h
    exact he
  | D :: Ds, e, e', h, he, hDs => by
    match e, h with
    | .forallE ty body bm, h =>
      simp only [ConLeche.Expr.instPis] at h
      simp only [ConLeche.Expr.noProjAt_forallE] at he
      exact NoProjAt.instPis Ds _ e' h
        (ConLeche.Expr.NoProjAt.instantiate1 (hDs D List.mem_cons_self) _ _ he.2)
        (fun D' hD' => hDs D' (List.mem_cons_of_mem _ hD'))
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
    | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [ConLeche.Expr.instPis] at h

end Expr

/-- Consing formers changes no projection lookup (a former's name is
not proj-table-shaped). -/
theorem findProj?_consMutualFormers {T : Name} {i : Nat} :
    ∀ {fms : List ConLeche.MutualFormerA} {env : Env},
      (∀ f ∈ fms, f.cvTa.name.isProjFnShape = false) →
      (ConLeche.consMutualFormers fms env).findProj? T i = env.findProj? T i
  | [], _, _ => rfl
  | f :: fms, env, h => by
    show (ConLeche.consMutualFormers fms ⟨.indInfo f.cvTa {} :: env.consts⟩).findProj? T i = _
    rw [findProj?_consMutualFormers (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    refine ConLeche.Env.findProj?_cons_ne (fun hn => ?_) i
    have h1 := h f List.mem_cons_self
    have h2 := projTableName_isProjFnShape T
    rw [show (ConstantInfo.indInfo f.cvTa {}).name = f.cvTa.name from rfl] at hn
    rw [hn, h2] at h1
    exact nomatch h1

end ConLeche.Model
