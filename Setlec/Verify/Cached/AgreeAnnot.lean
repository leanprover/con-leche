import Setlec.Cached.ParsedT

/-!
# T2a / T2b — `annotate`'s config identity and the `pw` writes
(task #172, batch B7)

Census part 4 §3's second and third obligations, at the **cached** tier
(the user's drop-the-interned ruling).

At this tier the trusted core's `annotate` **is** the certified body at
`cfgT` (task #172 B3: the trusted core's *config*, the mode
accessor's successor) — `Cached/CoreT.lean` ties
`annotate := memoEIT … (fun d e => annotateBodyI cfgT prev.get fe d e)`
— so the two obligations are a *config collapse on one function*, stated
in the T1 shape: a **shared** `r`, one unfolding of the body.

* **T2a** (`annotateBodyI_cfg_eq`): at a shared `r` the two configs'
  `annotateBodyI` are the *same action* at every node that is not a
  binder — and B3's templating **strengthened** it: the statement now
  quantifies over every `CoreCfg`, not only the three a mode maps to.  A freeze-time finding, recorded because it narrows T2c: the
  `.proj` clause is **config-free**, so it is inside T2a, not carried to
  T2c.  What is left in T2c is entirely the two cores' `r` differing
  (class 2) — nothing about `annotateBody` itself.
* **T2b** (`annotateBindersOutI_erasePwC` and the two leaf clauses):
  at the two binder telescopes the configs differ *only* by the datum
  written into the rebuilt binder's `BinderMeta.pw`, which is exactly
  what `erasePw` forgets.

The cached representation is **pure** — `viewI = pure ∘ view`,
`internI = pure ∘ ofView`, `abstractRangeM`/`instListRevM` pure — so no
state relation is needed anywhere below.  That is why the "one expr
type everywhere" ruling makes this batch cheap.
-/

namespace Setlec.Cached

open Setlec

/-! ## T2a — the clause-level config identity -/

/-- The two binder nodes: the only clauses of `annotateBodyI` in which
the config occurs at all. -/
def ExprC.isBinderNode : ExprC → Bool
  | .lam .. | .forallE .. => true
  | _ => false

set_option maxRecDepth 10000 in
/-- **T2a.**  At a shared `r`, `annotateBodyI` does not depend on the
config at any non-binder node — *including* `.proj`, `.letE` and the two
literal clauses.  `rfl`-grade, clause by clause. -/
theorem annotateBodyI_cfg_eq (cfg : CoreCfg) (r : CoreFnsI) (fe : FEnv)
    (d : Nat) (e : ExprC) (h : ExprC.isBinderNode e = false) :
    annotateBodyI cfgT r fe d e = annotateBodyI cfg r fe d e := by
  cases e with
  | bvar _ => simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | fvar _ _ _ => simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | sort _ => simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | const _ _ => simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | app _ _ => simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | letE _ _ _ _ =>
    simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | lit l =>
    cases l <;> simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | proj _ _ _ => simp only [annotateBodyI, viewI, ExprC.view, pure_bind]
  | lam _ _ _ _ => exact absurd h (by simp [ExprC.isBinderNode])
  | forallE _ _ _ _ => exact absurd h (by simp [ExprC.isBinderNode])

/-! ## T2b — the `pw`-erasure at the cached representation -/

/-- `Expr.erasePw` at the cached representation: the binder data is
rebuilt with the `pw` field cleared, every other node structurally. -/
def ExprC.erasePwC : ExprC → ExprC
  | .bvar i => ExprC.mkBVar i
  | .fvar idx n ty => ExprC.mkFVar idx n (erasePwC ty)
  | .sort u => ExprC.mkSort u
  | .const n us => ExprC.mkConst n us
  | .app f a => ExprC.mkApp (erasePwC f) (erasePwC a)
  | .lam n ty b m =>
    ExprC.mkLam n (erasePwC ty) (erasePwC b) ⟨m.bi, .never⟩
  | .forallE n ty b m =>
    ExprC.mkForallE n (erasePwC ty) (erasePwC b) ⟨m.bi, .never⟩
  | .letE n ty v b =>
    ExprC.mkLetE n (erasePwC ty) (erasePwC v) (erasePwC b)
  | .lit l => ExprC.mkLit l
  | .proj s i e => ExprC.mkProj s i (erasePwC e)

/-- The cached erasure is the plain one: `erasePwC` computes
`Expr.erasePw` under `eraseC`.  Unconditional — the smart
constructors' equations are `rfl`. -/
theorem ExprC.eraseC_erasePwC (e : ExprC) :
    (ExprC.erasePwC e) = e.erasePw := by
  induction e <;>
    simp [ExprC.erasePwC, ExprC, Expr.erasePw, *]

/-- The write touches the `pw` field and nothing else. -/
theorem annotBinderMetaI_bi (pw? : Option PropWhen) (mb : BinderMeta) :
    (annotBinderMetaI pw? mb).bi = mb.bi := by
  cases pw? with
  | none => rfl
  | some p => by_cases h : pwWritten mb.pw <;> simp [annotBinderMetaI, h]

/-- At `cfgT` the telescope loops write nothing — the gate is the
config's `verified` field and nothing else, and it is a literal
`false` there (task #172 B3: the mode accessor became a config
field; the collapse is still `rfl`). -/
@[simp] theorem annotatePisPwI_cfgT (r : CoreFnsI) (fe : FEnv) (d k : Nat)
    (leaf' : ExprC) :
    annotatePisPwI cfgT r fe d k leaf' = pure none := rfl

@[simp] theorem annotateLamsPwI_cfgT (r : CoreFnsI) (fe : FEnv) (d k : Nat)
    (leaf' : ExprC) :
    annotateLamsPwI cfgT r fe d k leaf' = pure none := rfl

/-- **T2b, the rebuild loop.**  `annotateBindersOutI`'s output does not
depend on the datum written: two runs whose inputs agree modulo
`erasePwC` agree modulo `erasePwC`, whatever `pw?` each carries.

The hypothesis on `mk` is discharged for the two instantiations the
annotation pass uses (`.forallE` and `.lam`) by
`ofView_forallE_erasePwC` / `ofView_lam_erasePwC` below. -/
theorem annotateBindersOutI_erasePwC
    (mk : Name → ExprC → ExprC → BinderMeta → ExprView ExprC)
    (hmk : ∀ n ty b₁ b₂ m₁ m₂, ExprC.erasePwC b₁ = ExprC.erasePwC b₂ →
      m₁.bi = m₂.bi →
      ExprC.erasePwC (ExprC.ofView (mk n ty b₁ m₁))
        = ExprC.erasePwC (ExprC.ofView (mk n ty b₂ m₂)))
    (d : Nat) :
    ∀ (stk : List AnnotBinderEntry) (pw? pw?' : Option PropWhen) (j : Nat)
      (cur cur' : ExprC) (s s' : CState),
      ExprC.erasePwC cur = ExprC.erasePwC cur' →
      (annotateBindersOutI mk d pw? stk j cur s).map (fun p => ExprC.erasePwC p.1)
        = (annotateBindersOutI mk d pw?' stk j cur' s').map
            (fun p => ExprC.erasePwC p.1)
  | [], _, _, _, cur, cur', _, _, hcur => by
      show Except.ok (ExprC.erasePwC cur) = Except.ok (ExprC.erasePwC cur')
      rw [hcur]
  | (n, ty', mb) :: rest, pw?, pw?', j, cur, cur', s, s', hcur => by
      show (annotateBindersOutI mk d _ rest (j - 1) _ s).map _
        = (annotateBindersOutI mk d _ rest (j - 1) _ s').map _
      exact annotateBindersOutI_erasePwC mk hmk d rest _ _ (j - 1) _ _ s s'
        (hmk n _ cur cur' _ _ hcur
          ((annotBinderMetaI_bi pw? mb).trans (annotBinderMetaI_bi pw?' mb).symm))

theorem ofView_forallE_erasePwC (n : Name) (ty b₁ b₂ : ExprC)
    (m₁ m₂ : BinderMeta) (hb : ExprC.erasePwC b₁ = ExprC.erasePwC b₂)
    (hm : m₁.bi = m₂.bi) :
    ExprC.erasePwC (ExprC.ofView (.forallE n ty b₁ m₁))
      = ExprC.erasePwC (ExprC.ofView (.forallE n ty b₂ m₂)) := by
  show ExprC.mkForallE n _ (ExprC.erasePwC b₁) ⟨m₁.bi, .never⟩
    = ExprC.mkForallE n _ (ExprC.erasePwC b₂) ⟨m₂.bi, .never⟩
  rw [hb, hm]

theorem ofView_lam_erasePwC (n : Name) (ty b₁ b₂ : ExprC)
    (m₁ m₂ : BinderMeta) (hb : ExprC.erasePwC b₁ = ExprC.erasePwC b₂)
    (hm : m₁.bi = m₂.bi) :
    ExprC.erasePwC (ExprC.ofView (.lam n ty b₁ m₁))
      = ExprC.erasePwC (ExprC.ofView (.lam n ty b₂ m₂)) := by
  show ExprC.mkLam n _ (ExprC.erasePwC b₁) ⟨m₁.bi, .never⟩
    = ExprC.mkLam n _ (ExprC.erasePwC b₂) ⟨m₂.bi, .never⟩
  rw [hb, hm]

/-! ### T2b at the two gated clauses

The two telescope leaves are the *only* places the annotation pass
consults the config.  Both runs start from the same state and call the
same `r`, so they reach the rebuild loop with the same leaf; from there
the datum is all that differs, and `erasePwC` forgets it.

Scoped to *accept*, as everywhere in B7: the verified run's datum
computation calls `r.infer`, which may fail where the trusted run does
not (a class-1, acceptance-only divergence). -/

theorem annotatePisLeafI_erasePwC (cfg : CoreCfg) (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (t : ExprC) (k : Nat) (fvs : Array ExprC) (stk : List AnnotBinderEntry)
    {s : CState} {a₁ a₂ : ExprC} {s₁ s₂ : CState}
    (h₁ : annotatePisLeafI cfgT r fe d t k fvs stk s = .ok (a₁, s₁))
    (h₂ : annotatePisLeafI cfg r fe d t k fvs stk s = .ok (a₂, s₂)) :
    ExprC.erasePwC a₁ = ExprC.erasePwC a₂ := by
  have e₁ : annotatePisLeafI cfgT r fe d t k fvs stk s
      = (r.annotate (d + k) (ExprC.instantiateRev t fvs 0) s).bind
          (fun p => annotateBindersOutI
            (fun n ty b mb => ExprView.forallE n ty b mb) d none stk (k - 1)
            (ExprC.abstractRange p.1 d k) p.2) := rfl
  have e₂ : annotatePisLeafI cfg r fe d t k fvs stk s
      = (r.annotate (d + k) (ExprC.instantiateRev t fvs 0) s).bind
          (fun p => (annotatePisPwI cfg r fe d k p.1 p.2).bind
            (fun q => annotateBindersOutI
              (fun n ty b mb => ExprView.forallE n ty b mb) d q.1 stk (k - 1)
              (ExprC.abstractRange p.1 d k) q.2)) := rfl
  rw [e₁] at h₁; rw [e₂] at h₂
  cases hA : r.annotate (d + k) (ExprC.instantiateRev t fvs 0) s with
  | error e => rw [hA] at h₁; cases h₁
  | ok p =>
    rw [hA] at h₁ h₂
    simp only [Except.bind] at h₁ h₂
    cases hB : annotatePisPwI cfg r fe d k p.1 p.2 with
    | error e => rw [hB] at h₂; cases h₂
    | ok q =>
      rw [hB] at h₂
      simp only at h₂
      have hh := annotateBindersOutI_erasePwC
        (fun n ty b mb => ExprView.forallE n ty b mb)
        (fun n ty b₁ b₂ m₁ m₂ hb hm =>
          ofView_forallE_erasePwC n ty b₁ b₂ m₁ m₂ hb hm)
        d stk none q.1 (k - 1) (ExprC.abstractRange p.1 d k)
        (ExprC.abstractRange p.1 d k) p.2 q.2 rfl
      rw [h₁, h₂] at hh
      simp only [Except.map] at hh
      exact Except.ok.inj hh

theorem annotateLamsLeafI_erasePwC (cfg : CoreCfg) (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (t : ExprC) (k : Nat) (fvs : Array ExprC) (stk : List AnnotBinderEntry)
    {s : CState} {a₁ a₂ : ExprC} {s₁ s₂ : CState}
    (h₁ : annotateLamsLeafI cfgT r fe d t k fvs stk s = .ok (a₁, s₁))
    (h₂ : annotateLamsLeafI cfg r fe d t k fvs stk s = .ok (a₂, s₂)) :
    ExprC.erasePwC a₁ = ExprC.erasePwC a₂ := by
  have e₁ : annotateLamsLeafI cfgT r fe d t k fvs stk s
      = (r.annotate (d + k) (ExprC.instantiateRev t fvs 0) s).bind
          (fun p => annotateBindersOutI
            (fun n ty b mb => ExprView.lam n ty b mb) d none stk (k - 1)
            (ExprC.abstractRange p.1 d k) p.2) := rfl
  have e₂ : annotateLamsLeafI cfg r fe d t k fvs stk s
      = (r.annotate (d + k) (ExprC.instantiateRev t fvs 0) s).bind
          (fun p => (annotateLamsPwI cfg r fe d k p.1 p.2).bind
            (fun q => annotateBindersOutI
              (fun n ty b mb => ExprView.lam n ty b mb) d q.1 stk (k - 1)
              (ExprC.abstractRange p.1 d k) q.2)) := rfl
  rw [e₁] at h₁; rw [e₂] at h₂
  cases hA : r.annotate (d + k) (ExprC.instantiateRev t fvs 0) s with
  | error e => rw [hA] at h₁; cases h₁
  | ok p =>
    rw [hA] at h₁ h₂
    simp only [Except.bind] at h₁ h₂
    cases hB : annotateLamsPwI cfg r fe d k p.1 p.2 with
    | error e => rw [hB] at h₂; cases h₂
    | ok q =>
      rw [hB] at h₂
      simp only at h₂
      have hh := annotateBindersOutI_erasePwC
        (fun n ty b mb => ExprView.lam n ty b mb)
        (fun n ty b₁ b₂ m₁ m₂ hb hm =>
          ofView_lam_erasePwC n ty b₁ b₂ m₁ m₂ hb hm)
        d stk none q.1 (k - 1) (ExprC.abstractRange p.1 d k)
        (ExprC.abstractRange p.1 d k) p.2 q.2 rfl
      rw [h₁, h₂] at hh
      simp only [Except.map] at hh
      exact Except.ok.inj hh

end Setlec.Cached
