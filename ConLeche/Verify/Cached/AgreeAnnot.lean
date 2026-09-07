import ConLeche.Cached.ParsedC

/-!
# T2a / T2b — `annotate`'s config identity and the `pw` writes
(task #172, batch B7)

Census part 4 §3's second and third obligations, at the **cached** tier
(the user's drop-the-interned ruling).

At this tier the trusted core's `annotate` **is** the verified body —
since the twin's retirement (2026-09-06) the trusted core is the one
knot `coreKnotI` at `.trusted`, whose `annotate` slot is
`annotateBodyI`, a body that takes no mode at all.

**T2a and T2b are discharged by the SIGNATURE since 2026-09-06.**  The
mode rename's second half ungated the `pw` writers (DESIGN.md, "MODE
RENAME"): writing the datum is part of the real checker's algorithm, so
the trusted mode annotates exactly as the verified mode does.  With the
gates gone the annotation pass reads no configuration at any node —
`annotateBodyI`, `annotatePisI`/`annotateLamsI` and their leaves take no
`CheckMode` parameter at all — so the "mode collapse on one function"
obligation is not a theorem any more: there is one function.  The
statements that compared the two modes' runs (`annotateBodyI_cfg_eq`
and the two trusted-config `…PwI` collapses) had the trusted mode's `pw?` at
`none`; they were deleted with the gate rather than restated, a row
whose subject no longer exists.

What survives is the *content* the obligations rested on, still used to
say what the pass may and may not change:

* `annotateBindersOutI_erasePwC` — the rebuild loop's output does not
  depend on the datum written, whatever `pw?` it carries;
* the two leaf clauses (`annotatePisLeafI_erasePwC`,
  `annotateLamsLeafI_erasePwC`) — the leaf's output is determined
  modulo `erasePwC`, which is exactly the `pw` field.

The cached representation is **pure** — a node is destructured by
`match` and built by allocation, `abstractRangeM`/`instListRevM` are
`pure` — so no state relation is needed anywhere below.  That is why the
"one expr type everywhere" ruling makes this batch cheap.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## T2a — the clause-level config identity -/

/-! ## T2b — the `pw`-erasure at the cached representation -/

/-- `Expr.erasePw` at the cached representation: the binder data is
rebuilt with the `pw` field cleared, every other node structurally. -/
def ExprC.erasePwC : ExprC → ExprC
  | .bvar i => ExprC.mkBVar i
  | .fvar idx ty => ExprC.mkFVar idx (erasePwC ty)
  | .sort u => ExprC.mkSort u
  | .const n us => ExprC.mkConst n us
  | .app f a => ExprC.mkApp (erasePwC f) (erasePwC a)
  | .lam ty b _m =>
    ExprC.mkLam (erasePwC ty) (erasePwC b) ⟨.never⟩
  | .forallE ty b _m =>
    ExprC.mkForallE (erasePwC ty) (erasePwC b) ⟨.never⟩
  | .letE ty v b =>
    ExprC.mkLetE (erasePwC ty) (erasePwC v) (erasePwC b)
  | .lit l => ExprC.mkLit l
  | .proj s i e => ExprC.mkProj s i (erasePwC e)

/-- The cached erasure is the plain one: `erasePwC` computes
`Expr.erasePw` under `eraseC`.  Unconditional — the smart
constructors' equations are `rfl`. -/
theorem ExprC.eraseC_erasePwC (e : ExprC) :
    (ExprC.erasePwC e) = e.erasePw := by
  induction e <;>
    simp [ExprC.erasePwC, ExprC, Expr.erasePw, *]

/-- **T2b, the rebuild loop.**  `annotateBindersOutI`'s output does not
depend on the datum written: two runs whose inputs agree modulo
`erasePwC` agree modulo `erasePwC`, whatever `pw?` each carries.

The hypothesis on `mk` is discharged for the two instantiations the
annotation pass uses (`.forallE` and `.lam`) by
`forallE_erasePwC` / `lam_erasePwC` below. -/
theorem annotateBindersOutI_erasePwC
    (mk : ExprC → ExprC → BinderMeta → ExprC)
    (hmk : ∀ ty b₁ b₂ m₁ m₂, ExprC.erasePwC b₁ = ExprC.erasePwC b₂ →
      ExprC.erasePwC (mk ty b₁ m₁)
        = ExprC.erasePwC (mk ty b₂ m₂))
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
  | (ty', mb) :: rest, pw?, pw?', j, cur, cur', s, s', hcur => by
      show (annotateBindersOutI mk d _ rest (j - 1) _ s).map _
        = (annotateBindersOutI mk d _ rest (j - 1) _ s').map _
      exact annotateBindersOutI_erasePwC mk hmk d rest _ _ (j - 1) _ _ s s'
        (hmk _ cur cur' _ _ hcur)

theorem forallE_erasePwC (ty b₁ b₂ : ExprC)
    (m₁ m₂ : BinderMeta) (hb : ExprC.erasePwC b₁ = ExprC.erasePwC b₂) :
    ExprC.erasePwC (.forallE ty b₁ m₁)
      = ExprC.erasePwC (.forallE ty b₂ m₂) := by
  show ExprC.mkForallE _ (ExprC.erasePwC b₁) ⟨.never⟩
    = ExprC.mkForallE _ (ExprC.erasePwC b₂) ⟨.never⟩
  rw [hb]

theorem lam_erasePwC (ty b₁ b₂ : ExprC)
    (m₁ m₂ : BinderMeta) (hb : ExprC.erasePwC b₁ = ExprC.erasePwC b₂) :
    ExprC.erasePwC (.lam ty b₁ m₁)
      = ExprC.erasePwC (.lam ty b₂ m₂) := by
  show ExprC.mkLam _ (ExprC.erasePwC b₁) ⟨.never⟩
    = ExprC.mkLam _ (ExprC.erasePwC b₂) ⟨.never⟩
  rw [hb]

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

end ConLeche.Cached
