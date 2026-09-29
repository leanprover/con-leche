module

public import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Subst
import ConLeche.Verify.InstLevels

public section

/-!
# An outside rule's conclusion, syntactically and read

The target check reads an outside rule's index expressions off the
instantiated constructor's conclusion, `cbody.getAppArgs.drop M.nPc`
(`tgtEsAV`).  The recursor model's index values at an outside class are
the recorded result indices substituted at the instantiation
(`tgtOutEs`, `instCtor_decode`'s).  They agree once the conclusion's
spine arity is known — which no reading gives (a leaf may be an
application), and which the carrier records (`LfpOwn.ctorConcl`: a
recorded constructor concludes in its member at
its own levels, applied to `nPc + |ids|` arguments):

* `PiConcl` — "past `n` syntactic binders, the constant `I` at `us`
  applied to `m` arguments", kept by instantiation (`instantiate1`,
  levels, `instPisWith`) and by opening (`openPisAtFvars`);
* `AnnotTerm.mkAppN_inj_head` — two applications of the same head are
  equal only at equal argument lists;
* **`tgtEsAV_outside`** — at an outside class the target check's index
  expressions read as the class's (`tgtEsAV = tgtOutEs`), so the rule
  data are the target check's at every class.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The conclusion's shape, syntactically -/

/-- Past `n` syntactic binders, the constant `I` at the levels `us`
applied to `m` arguments. -/
@[expose] def PiConcl (I : Name) (us : List Level) (m : Nat) : Nat → Expr → Prop
  | 0, e => ∃ args, e = Expr.mkAppN (.const I us) args ∧ args.length = m
  | n + 1, .forallE _ b _ => PiConcl I us m n b
  | _ + 1, _ => False

theorem piConcl_of_stripPis {I : Name} {us : List Level} {m : Nat} :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {args : List Expr},
      e.stripPis n = some (bs, Expr.mkAppN (.const I us) args) → args.length = m →
      PiConcl I us m n e
  | 0, e, bs, args, h, hl => by
    simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨args, h.2, hl⟩
  | n + 1, .forallE t b mb, bs, args, h, hl => by
    simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', b'⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact piConcl_of_stripPis n hs hl
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _ _, _, _, h, _ | _ + 1, .sort _, _, _, h, _
  | _ + 1, .const _ _, _, _, h, _ | _ + 1, .app _ _, _, _, h, _
  | _ + 1, .lam _ _ _, _, _, h, _ | _ + 1, .letE _ _ _, _, _, h, _ | _ + 1, .lit _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, h, _ => by simp [ConLeche.Expr.stripPis] at h

theorem piConcl_instantiate1 {I : Name} {us : List Level} {m : Nat} (v : Expr) :
    ∀ (n : Nat) (e : Expr) (k : Nat), PiConcl I us m n e → PiConcl I us m n (e.instantiate1 v k)
  | 0, e, k, ⟨args, he, hl⟩ => by
    subst he
    refine ⟨args.map (·.instantiate1 v k), ?_, by rw [List.length_map, hl]⟩
    rw [Expr.mkAppN_instantiate1]; rfl
  | n + 1, .forallE t b mb, k, h => piConcl_instantiate1 v n b (k + 1) h
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .lam _ _ _, _, h
  | _ + 1, .letE _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => h.elim

theorem piConcl_instantiateLevelParams {I : Name} {us : List Level} {m : Nat}
    (ks : List Name) (vs : List Level) :
    ∀ (n : Nat) (e : Expr), PiConcl I us m n e →
      PiConcl I (us.map (Level.subst ks vs)) m n (e.instantiateLevelParams ks vs)
  | 0, e, ⟨args, he, hl⟩ => by
    subst he
    refine ⟨args.map (·.instantiateLevelParams ks vs), ?_, by rw [List.length_map, hl]⟩
    rw [instantiateLevelParams_mkAppN]; rfl
  | n + 1, .forallE t b mb, h => piConcl_instantiateLevelParams ks vs n b h
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h
  | _ + 1, .const _ _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h
  | _ + 1, .letE _ _ _, h | _ + 1, .lit _, h | _ + 1, .proj _ _ _, h => h.elim

theorem piConcl_instPisWith {I : Name} {us : List Level} {m n : Nat} :
    ∀ (ds : List Expr) {e e' : Expr}, PiConcl I us m (ds.length + n) e →
      ConLeche.instPisWith ds e = some e' → PiConcl I us m n e'
  | [], e, e', h, hi => by
    simp only [ConLeche.instPisWith, Option.some.injEq] at hi
    subst hi; simpa using h
  | a :: ds, .forallE t b mb, e', h, hi => by
    have hi' : ConLeche.instPisWith ds (b.instantiate1 a) = some e' := hi
    have hb : PiConcl I us m (ds.length + n) b := by
      simp only [List.length_cons, show ds.length + 1 + n = (ds.length + n) + 1 by omega] at h
      exact h
    exact piConcl_instPisWith ds (piConcl_instantiate1 a _ b 0 hb) hi'
  | _ :: _, .bvar _, _, _, hi | _ :: _, .fvar _ _, _, _, hi | _ :: _, .sort _, _, _, hi
  | _ :: _, .const _ _, _, _, hi | _ :: _, .app _ _, _, _, hi | _ :: _, .lam _ _ _, _, _, hi
  | _ :: _, .letE _ _ _, _, _, hi | _ :: _, .lit _, _, _, hi
  | _ :: _, .proj _ _ _, _, _, hi => by simp [ConLeche.instPisWith] at hi

theorem piConcl_open {I : Name} {us : List Level} {m : Nat} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {cb : Expr}, PiConcl I us m n e →
      ConLeche.openPisAtFvars n e d = some (fvs, cb) → PiConcl I us m 0 cb
  | 0, e, d, fvs, cb, h, ho => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨-, rfl⟩ := ho
    exact h
  | n + 1, .forallE t b mb, d, fvs, cb, h, ho => by
    simp only [ConLeche.openPisAtFvars] at ho
    split at ho
    · next fvs' cb' hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨-, rfl⟩ := ho
      exact piConcl_open n (piConcl_instantiate1 _ n b 0 h) hrec
    · exact nomatch ho
  | _ + 1, .bvar _, _, _, _, _, ho | _ + 1, .fvar _ _, _, _, _, _, ho
  | _ + 1, .sort _, _, _, _, _, ho | _ + 1, .const _ _, _, _, _, _, ho
  | _ + 1, .app _ _, _, _, _, _, ho | _ + 1, .lam _ _ _, _, _, _, _, ho
  | _ + 1, .letE _ _ _, _, _, _, _, ho | _ + 1, .lit _, _, _, _, _, ho
  | _ + 1, .proj _ _ _, _, _, _, _, ho => by simp [ConLeche.openPisAtFvars] at ho

/-! ## Applications of one head -/

omit [SetTheory V] in
theorem sizeOf_le_mkAppN : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    sizeOf f ≤ sizeOf (AnnotTerm.mkAppN f as)
  | [], _ => Nat.le_refl _
  | a :: as, f => by
    rw [AnnotTerm.mkAppN_cons]
    refine Nat.le_trans ?_ (sizeOf_le_mkAppN as (.app f a))
    show sizeOf f ≤ 1 + sizeOf f + sizeOf a
    omega

omit [SetTheory V] in
/-- **Two applications of the same head are equal only at equal
argument lists.** -/
theorem AnnotTerm.mkAppN_inj_head {f : AnnotTerm} :
    ∀ {as bs : List AnnotTerm}, AnnotTerm.mkAppN f as = AnnotTerm.mkAppN f bs → as = bs := by
  intro as bs h
  rcases Nat.lt_trichotomy as.length bs.length with hlt | heq | hgt
  · exfalso
    obtain ⟨b₁, b₂, rfl, hl⟩ : ∃ b₁ b₂, bs = b₁ ++ b₂ ∧ b₂.length = as.length :=
      ⟨bs.take (bs.length - as.length), bs.drop (bs.length - as.length), by simp,
        by rw [List.length_drop]; omega⟩
    rw [annotMkAppN_append] at h
    obtain ⟨hf, -⟩ := AnnotTerm.mkAppN_inj h hl.symm
    have hne : b₁ ≠ [] := by
      intro h0; subst h0; rw [List.nil_append] at hlt; omega
    obtain ⟨b, b₁', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := sizeOf_le_mkAppN b₁' (.app f b)
    rw [← AnnotTerm.mkAppN_cons, ← hf] at this
    have h2 : sizeOf f < sizeOf (AnnotTerm.app f b) := by
      show sizeOf f < 1 + sizeOf f + sizeOf b; omega
    omega
  · exact (AnnotTerm.mkAppN_inj h heq).2
  · exfalso
    obtain ⟨a₁, a₂, rfl, hl⟩ : ∃ a₁ a₂, as = a₁ ++ a₂ ∧ a₂.length = bs.length :=
      ⟨as.take (as.length - bs.length), as.drop (as.length - bs.length), by simp,
        by rw [List.length_drop]; omega⟩
    rw [annotMkAppN_append] at h
    obtain ⟨hf, -⟩ := AnnotTerm.mkAppN_inj h hl
    have hne : a₁ ≠ [] := by
      intro h0; subst h0; rw [List.nil_append] at hgt; omega
    obtain ⟨a, a₁', rfl⟩ := List.exists_cons_of_ne_nil hne
    have := sizeOf_le_mkAppN a₁' (.app f a)
    rw [← AnnotTerm.mkAppN_cons, hf] at this
    have h2 : sizeOf f < sizeOf (AnnotTerm.app f a) := by
      show sizeOf f < 1 + sizeOf f + sizeOf a; omega
    omega

/-! ## The outside rule's conclusion -/

section Concl

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

end Concl

end ConLeche.Model
