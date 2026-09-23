module

public import ConLeche.Model.Inductives.StructRecKit2
public import ConLeche.Verify.Inductives.StructRec
import ConLeche.Model.Annot.BitInst
public section

/-!
# The generated recursor, read (task #175 S2)

The direct install stores the recursor it generates
(`structRecTy`/`structRecRhs`), so its reading is **syntactic**: the
generated type reads to the Π-tower

    mkPisAV (params (bit ℓ) ++ [motive, minor, major]) (motive t)

whose three special entries are spelled out (`motiveAV`, `minorAV`,
`majorAV`) over the type former's and the constructor's readings, and
the generated rule reads to the λ-tower over the same data
(`denoteP_structRecRhs`).  No frame pin is consumed: the recursor's
data (`recData_of`) comes from these readings, the fabricated type's
own inference run (its grading, `inferRow`) and the elimination datum
the generator wrote (its bits, `zeronessOf_sound`).

The two generic pieces are the readings of the binder walks
(`denoteMeta_replacePisPw`, `denoteMeta_pisToLamsPw`): a walk over an
opened telescope reads to the tower over the telescope's own domain
readings, bits reset, over the body instantiated at the opening's
variables.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## Bits reset -/

/-- Binder data with every codomain bit reset to `b`. -/
@[expose] def rebit (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  ds.map fun d => (d.1, b, d.2.2)

@[simp] theorem rebit_length (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).length = ds.length := by simp [rebit]

@[simp] theorem rebit_map_dom (b : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    (rebit b ds).map (·.2.2) = ds.map (·.2.2) := by simp [rebit]

theorem mem_rebit {b : Nat} {ds : List (Nat × Nat × AnnotTerm)} {d : Nat × Nat × AnnotTerm}
    (h : d ∈ rebit b ds) : d.2.1 = b := by
  obtain ⟨d', -, rfl⟩ := List.mem_map.mp h
  rfl

/-! ## Syntactic bookkeeping -/

/-- An instantiation sequence's index is immaterial at the empty
sequence. -/
theorem instSeq_idx_congr {sp : List Expr} {t t' : Nat} (e : Expr)
    (h : sp = [] ∨ t = t') : Expr.instSeq sp t e = Expr.instSeq sp t' e := by
  rcases h with rfl | rfl <;> rfl

/-- The variables of an opening at depth `0` are closed and indexed by
position, scoped one above their index. -/
theorem opening_vars {n : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e 0 = some (fvs, o)) (hcl : e.hasFvar = false) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar k ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) ∧
    (∀ (i : Nat) (a : Expr), fvs[i]? = some a → Expr.WScoped (0 + i + 1) a) := by
  have hidx := openPisAtFvars_index n e 0 hop
  refine ⟨openPisAtFvars_length n hop, fun k x hx => by
    obtain ⟨ty, h⟩ := hidx k x hx
    exact ⟨ty, by rw [h, Nat.zero_add]⟩, ?_, ?_⟩
  · intro a ha
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := hidx q a hq
    rfl
  · intro i a ha
    obtain ⟨ty, rfl⟩ := hidx i a ha
    have hw := openPisAtFvars_typeWScoped n hop (Expr.WScoped.of_not_hasFvar hcl) i _ ha
    simp only [Expr.fvarTypeD, Nat.zero_add] at hw
    simp only [Expr.WScoped, Nat.zero_add]
    exact ⟨Nat.lt_succ_self i, hw⟩

/-- The variables of an opening at any depth: one per binder, indexed
by position from the depth, closed. -/
theorem opening_vars_at {n d : Nat} {e : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e d = some (fvs, o)) :
    fvs.length = n ∧
    (∀ (k : Nat) (x : Expr), fvs[k]? = some x → ∃ ty, x = Expr.fvar (d + k) ty) ∧
    (∀ a ∈ fvs, a.looseBVarsBounded 0 = true) :=
  ⟨openPisAtFvars_length n hop, openPisAtFvars_index n e d hop, fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e d hop q a hq
    rfl⟩

/-! ## The constructor telescope's residual -/

/-- The reading of the constructor's residual, one under (the motive):
the field data lifted once. -/
theorem ctorResidual_read_lift {m : EnvModel V env} {ψ : Name → Nat} {nP nF : Nat}
    {crest : Expr} {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    (hread : denoteMeta m.acval env ψ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hw : Expr.WScoped nP crest) (hlenD : ds.length = nP + nF) (e : Nat) :
    denoteMeta m.acval env ψ (nP + e) crest
      = some (mkPisAV (liftDoms e 0 (ds.drop nP)) (bodyC.liftN e nF)) := by
  rw [denoteMeta_lift m.acval_closed hw (nP + e) (by omega), hread, Option.map_some,
    show nP + e - nP = e from by omega, liftN_mkPisAV, Nat.zero_add]
  congr 3
  simp [hlenD]

end ConLeche.Model
