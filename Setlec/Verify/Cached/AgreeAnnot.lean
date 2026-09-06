import Setlec.Cached.ParsedC

/-!
# T2a / T2b — `annotate`'s config identity and the `pw` writes
(task #172, batch B7)

Census part 4 §3's second and third obligations, at the **cached** tier
(the user's drop-the-interned ruling).

At this tier the trusted core's `annotate` **is** the verified body —
since the twin's retirement (2026-09-06) the trusted core is the one
knot `coreKnotI` at `cfgT`, whose `annotate` slot is `annotateBodyI`,
a body that takes no config at all.

**T2a and T2b are discharged by the SIGNATURE since 2026-09-06.**  The
mode rename's second half ungated the `pw` writers (DESIGN.md, "MODE
RENAME"): writing the datum is part of the real checker's algorithm, so
the trusted mode annotates exactly as the verified mode does.  With the
gates gone the annotation pass reads no configuration at any node —
`annotateBodyI`, `annotatePisI`/`annotateLamsI` and their leaves take no
`CoreCfg` parameter at all — so the "config collapse on one function"
obligation is not a theorem any more: there is one function.  The
statements that compared the two configs' runs (`annotateBodyI_cfg_eq`
and the two `…PwI_cfgT` collapses) had the trusted config's `pw?` at
`none`; they were deleted with the gate rather than restated, a row
whose subject no longer exists.

What survives is the *content* the obligations rested on, still used to
say what the pass may and may not change:

* `annotateBindersOutI_erasePwC` — the rebuild loop's output does not
  depend on the datum written, whatever `pw?` it carries;
* the two leaf clauses (`annotatePisLeafI_erasePwC`,
  `annotateLamsLeafI_erasePwC`) — the leaf's output is determined
  modulo `erasePwC`, which is exactly the `pw` field.

The cached representation is **pure** — `viewI = pure ∘ view`,
`internI = pure ∘ ofView`, `abstractRangeM`/`instListRevM` pure — so no
state relation is needed anywhere below.  That is why the "one expr
type everywhere" ruling makes this batch cheap.
-/

namespace Setlec.Cached

open Setlec

/-! ## T2a — the clause-level config identity -/

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

/-! ### T2b at the two telescope leaves

The two leaves used to be the only places the annotation pass consulted
the config; since the writers were ungated they consult none, so what is
left to say is that the leaf determines its output modulo the `pw`
field. -/

theorem annotatePisLeafI_erasePwC (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (t : ExprC) (k : Nat) (fvs : Array ExprC) (stk : List AnnotBinderEntry)
    {s : CState} {a₁ a₂ : ExprC} {s₁ s₂ : CState}
    (h₁ : annotatePisLeafI r fe d t k fvs stk s = .ok (a₁, s₁))
    (h₂ : annotatePisLeafI r fe d t k fvs stk s = .ok (a₂, s₂)) :
    ExprC.erasePwC a₁ = ExprC.erasePwC a₂ := by
  have ha : a₁ = a₂ := congrArg Prod.fst (Except.ok.inj (h₁.symm.trans h₂))
  rw [ha]

theorem annotateLamsLeafI_erasePwC (r : CoreFnsI) (fe : FEnv) (d : Nat)
    (t : ExprC) (k : Nat) (fvs : Array ExprC) (stk : List AnnotBinderEntry)
    {s : CState} {a₁ a₂ : ExprC} {s₁ s₂ : CState}
    (h₁ : annotateLamsLeafI r fe d t k fvs stk s = .ok (a₁, s₁))
    (h₂ : annotateLamsLeafI r fe d t k fvs stk s = .ok (a₂, s₂)) :
    ExprC.erasePwC a₁ = ExprC.erasePwC a₂ := by
  have ha : a₁ = a₂ := congrArg Prod.fst (Except.ok.inj (h₁.symm.trans h₂))
  rw [ha]

end Setlec.Cached
