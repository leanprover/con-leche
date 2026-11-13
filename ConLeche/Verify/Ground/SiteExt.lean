module

public import ConLeche.Verify.EnvExt.Reads
import ConLeche.Kernel.Ground
import ConLeche.Verify.EnvExt.Whnf
import ConLeche.Verify.Ground.SimSite
import ConLeche.Verify.Ground.SimRun
public import ConLeche.Verify.Ground.SimBridge
import ConLeche.Verify.Ground.SimState
import ConLeche.Verify.Ground.Compile
import ConLeche.Verify.Ground.SimExt
import ConLeche.Verify.Ground.Site
import ConLeche.Verify.Ground.Keys
import ConLeche.Verify.Ground.SimStep1

public section

/-!
# The engine at an extension of the environment (task #423 soundness, layer (d), item 2(e))

`EnvExt.defeqBody_rel` needs the engine's whole answer, every stop and the
budget's decline included, to be one at `env₂ ⊇ env₁` and at `env₁`, at one
fuel, on a term resolving in `env₁`.  Both runs are on fresh programs, so
they compile the same bodies at the same steps: the simulation in lock-step
(`j = 0`), with `N` the names stored in `env₁`, on which the two
environments' lookups agree (`lookAgree_ext`).  Where `env₁` lacks the
`Nat`/`String` basis the flags may differ; no value reads them there, since a
literal and an accelerated operation bring their basis into `N`
(`StoredFacts.natTrio`, `natOps`, `boolCtors`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- The names stored in an environment. -/
def Stored (env : Env) (c : Name) : Prop := (env.find? c).isSome = true

/-- A resolved term has its names stored. -/
theorem namesIn_of_res {env : Env} : ∀ e : Expr, Res env e → NamesIn (Stored env) e
  | .bvar _, _ | .sort _, _ => trivial
  | .lit (.natVal _), h => by
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  | .lit (.strVal _), h => by
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩, h₉⟩, h₁₀⟩ := h
    exact ⟨⟨h₁, h₂, h₃⟩, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
  | .const _ _, h => h
  | .fvar _ ty, h => namesIn_of_res ty (res_fvar.mp h)
  | .app f a, h => ⟨namesIn_of_res f (res_app.mp h).1, namesIn_of_res a (res_app.mp h).2⟩
  | .lam t b, h => ⟨namesIn_of_res t (res_lam.mp h).1, namesIn_of_res b (res_lam.mp h).2⟩
  | .forallE t b, h => ⟨namesIn_of_res t (res_forall.mp h).1, namesIn_of_res b (res_forall.mp h).2⟩
  | .letE t v b, h => by
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨namesIn_of_res t h.1.1, namesIn_of_res v h.1.2, namesIn_of_res b h.2⟩
  | .proj _ _ e, h => by
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨h.1, namesIn_of_res e h.2⟩

theorem res_g4PiBody {env : Env} : ∀ {e : Expr}, Res env e → Res env (g4PiBody e)
  | .forallE _ b, h => res_g4PiBody (e := b) (res_forall.mp h).2
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _, h | .letE _ _ _, h
  | .lit _, h | .proj _ _ _, h => h

/-- A resolved head constant is stored. -/
theorem stored_head {env : Env} {e : Expr} (h : Res env e) {c : Name} {us : List Level}
    (hc : e.getAppFn = .const c us) : Stored env c := by
  have := res_getAppFn h
  rw [hc] at this
  exact res_const.mp this

section
variable {env₁ env₂ : Env}

/-- The erasure mask of a resolved type reads only stored constants. -/
theorem g4Mask_ext (hx : EnvExt env₁ env₂) (isRec : Bool) :
    ∀ (t : Expr) (acc : Array Bool), Res env₁ t → g4Mask env₂.find? isRec t acc = g4Mask env₁.find? isRec t acc
  | .forallE d b, acc, h => by
    obtain ⟨hd, hb⟩ := res_forall.mp h
    simp only [g4Mask]
    rw [g4Mask_ext hx isRec b _ hb]
    congr 3
    have hr := res_getAppFn (res_g4PiBody hd)
    generalize (g4PiBody d).getAppFn = g at hr ⊢
    cases g <;> try rfl
    rename_i c us
    dsimp only
    rw [hx.find_of_isSome (res_const.mp hr)]
  | .bvar _, _, _ | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .app _ _, _, _ | .lam _ _, _, _
  | .letE _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => by simp only [g4Mask]

/-- **The two environments' lookups agree on `env₁`'s names**, which are closed
under what a run reads. -/
theorem lookAgree_ext (hx : EnvExt env₁ env₂) :
    LookAgree (Stored env₁) env₁.find? env₁.findProj? env₂.find? env₂.findProj? where
  find c hc := hx.find_of_isSome hc
  proj sn i hs := hx.findProj hs i
  mask c hc := by
    unfold maskName
    rw [hx.find_of_isSome hc]
    cases hf : env₁.find? c with
    | none => rfl
    | some ci => exact g4Mask_ext hx _ _ _ (hx.facts.type hf)
  kfab c us hc := by
    unfold kfabKey
    rw [hx.find_of_isSome hc]
    split
    · rename_i cv mI rP rl hf
      obtain ⟨cvj, nP, nF, hj⟩ := hx.facts.recCtors _ _ _ _ _ _ hf rl (List.mem_singleton_self _)
      rw [hx.find_of_isSome (by rw [hj]; rfl : (env₁.find? rl.ctor).isSome = true)]
    · rfl
  defVal c cv v hs _ hf := namesIn_of_res v (hx.facts.value hf)
  rules c cv mI rP isK rules _ hf rl hrl := by
    obtain ⟨cvj, nP, nF, hj⟩ := hx.facts.recCtors _ _ _ _ _ _ hf rl hrl
    refine ⟨by show (env₁.find? rl.ctor).isSome = true; rw [hj]; rfl,
      namesIn_of_res _ (hx.facts.rhs hf hrl), fun cvj' nP' nF' hj' T ls hT => ?_⟩
    exact stored_head (res_piResult (hx.facts.type hj')) hT
  natTrio h := hx.facts.natTrio h
  natOp c hc hb := by
    have hop : natOpName c = true := by
      simp only [natBin14, Bool.and_eq_true] at hb
      simp only [natBin14Slow, Bool.or_eq_true, beq_iff_eq, or_assoc] at hb
      exact natOpName_of_bin hb.2
    have h := hx.facts.natOps c hop (hx.facts.opDefn c hop hc)
    simp only [natLitStored, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  boolOp c hc hcb := by
    have hop : natOpName c = true := by rcases hcb with rfl | rfl <;> decide
    have hd := hx.facts.opDefn c hop hc
    exact hx.facts.boolCtors (by rcases hcb with rfl | rfl; exact .inl hd; exact .inr hd)

/-- The `String` flag at an extension, the string basis stored. -/
theorem strLit_ext (hx : EnvExt env₁ env₂) (hs : StrNames (Stored env₁)) :
    strLitStored env₂ = strLitStored env₁ := by
  obtain ⟨⟨h₁, h₂, h₃⟩, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := hs
  unfold strLitStored natLitStored
  rw [hx.find_of_isSome h₁, hx.find_of_isSome h₂, hx.find_of_isSome h₃, hx.find_of_isSome h₄,
    hx.find_of_isSome h₅, hx.find_of_isSome h₆, hx.find_of_isSome h₇, hx.find_of_isSome h₈,
    hx.find_of_isSome h₉, hx.find_of_isSome h₁₀]

end

/-! ## Fresh programs have compiled nothing -/

/-- No body and no right-hand side compiled. -/
def NoCode (P : G4Prog) : Prop := (∀ κ, ¬ CodeK P κ) ∧ ∀ κ d, ¬ RuleK P κ d

theorem NoCode.ext {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P P' : G4Prog}
    (h : NoCode P) (hI : TabInv f p P) (hx : Ext P P') : NoCode P' :=
  ⟨fun κ hk => h.1 κ ((codeK_ext hx κ).1 hk), fun κ d hk => h.2 κ d ((ruleK_ext hI hx κ d).1 hk)⟩

theorem NoCode.same {PA PB : G4Prog} (hA : NoCode PA) (hB : NoCode PB) : CodeSame PA PB :=
  ⟨fun κ => ⟨fun h => absurd h (hB.1 κ), fun h => absurd h (hA.1 κ)⟩,
    fun κ d => ⟨fun h => absurd h (hB.2 κ d), fun h => absurd h (hA.2 κ d)⟩⟩

/-- **A fresh program with a term compiled** has compiled no body. -/
theorem noCode_fresh (f : Name → Option ConstantInfo) (p : Name → Nat → Option ProjEntry)
    (natOk strOk : Bool) (e : Expr) :
    NoCode (g4Comp f p (g4Setup f p natOk strOk {}) e).2 := by
  have h₀ := Inv.fresh (find? := f) (findProj? := p) natOk strOk
  have n₀ : NoCode ({ natOk := natOk, strOk := strOk } : G4Prog) :=
    ⟨fun _ ⟨_, _, hi, _⟩ => by simp at hi, fun _ _ ⟨_, _, _, _, _, _, _, _, _, _, hi, _⟩ => by simp at hi⟩
  have hs : NoCode (g4Setup f p natOk strOk {}) ∧ Inv f p (g4Setup f p natOk strOk {}) := by
    unfold g4Setup
    simp only [show (({} : G4Prog).kTag.size == 0) = true from rfl, ↓reduceIte]
    obtain ⟨hI₁, hx₁, -⟩ := g4Resolve_spec f p _ boolTrueName [] h₀
    generalize g4Resolve f p ({ natOk := natOk, strOk := strOk } : G4Prog)
      boolTrueName [] = q₁ at hI₁ hx₁ ⊢
    obtain ⟨kT, P₁⟩ := q₁
    obtain ⟨hI₂, hx₂, -⟩ := g4Resolve_spec f p P₁ boolFalseName [] hI₁
    generalize g4Resolve f p P₁ boolFalseName [] = q₂ at hI₂ hx₂ ⊢
    obtain ⟨kF, P₂⟩ := q₂
    obtain ⟨hI₃, hx₃, -⟩ := g4Resolve_spec f p P₂ natZeroName [] hI₂
    generalize g4Resolve f p P₂ natZeroName [] = q₃ at hI₃ hx₃ ⊢
    obtain ⟨kZ, P₃⟩ := q₃
    obtain ⟨hI₄, hx₄, -⟩ := g4Resolve_spec f p P₃ natSuccName [] hI₃
    generalize g4Resolve f p P₃ natSuccName [] = q₄ at hI₄ hx₄ ⊢
    obtain ⟨kS, P₄⟩ := q₄
    dsimp only at *
    have n₄ := (((n₀.ext h₀.toTabInv hx₁).ext hI₁.toTabInv hx₂).ext hI₂.toTabInv hx₃).ext hI₃.toTabInv hx₄
    exact ⟨n₄, hI₄.setSite kT kF kZ kS P₄.epBase P₄.slotA⟩
  obtain ⟨-, hx, -⟩ := g4Comp_spec f p _ e hs.2
  exact hs.1.ext hs.2.toTabInv hx

/-! ## The site at an extension -/

/-- **The engine at an extension** (item 2(e)): on fresh programs at one fuel,
a closed term resolving in `env₁` gets one answer at `env₂` and at `env₁`,
every stop and the budget's decline included. -/
theorem ground4_ext {env₁ env₂ : Env} (hx : EnvExt env₁ env₂) (mx : Option Nat) (F : Nat) {e : Expr}
    (he : e.looseBVarsBounded 0 = true) (hres : Res env₁ e) :
    (ground4BoolCoreF env₂.find? env₂.findProj? (natLitStored env₂) (strLitStored env₂) mx F {} e).1.1 =
      (ground4BoolCoreF env₁.find? env₁.findProj? (natLitStored env₁) (strLitStored env₁) mx F {} e).1.1 := by
  have hKA := setup_kept (env := env₁) (P₀ := {}) rfl rfl (.inl rfl)
  have hKB := setup_kept (env := env₂) (P₀ := {}) rfl rfl (.inl rfl)
  have hfA := setup_flags env₁.find? env₁.findProj? (P₀ := {}) (natOk := natLitStored env₁)
    (strOk := strLitStored env₁) (.inl rfl)
  have hfB := setup_flags env₂.find? env₂.findProj? (P₀ := {}) (natOk := natLitStored env₂)
    (strOk := strLitStored env₂) (.inl rfl)
  have hcode := NoCode.same (noCode_fresh env₁.find? env₁.findProj? (natLitStored env₁) (strLitStored env₁)
    e) (noCode_fresh env₂.find? env₂.findProj? (natLitStored env₂) (strLitStored env₂) e)
  unfold ground4BoolCoreF
  generalize g4Setup env₁.find? env₁.findProj? (natLitStored env₁) (strLitStored env₁) {} = PA
    at hKA hfA hcode ⊢
  generalize g4Setup env₂.find? env₂.findProj? (natLitStored env₂) (strLitStored env₂) {} = PB
    at hKB hfB hcode ⊢
  simp only [G4Prog.flags, Prod.mk.injEq] at hfA hfB
  dsimp only
  have hr := siteMS_rel (j := 0) (N := Stored env₁) hKA hKB
    (fun hn => by rw [hfA.1, hfB.1]; exact natLit_ext hx (.inl hn.1))
    (fun hs => by rw [hfA.2, hfB.2]; exact strLit_ext hx hs) e
    (namesIn_of_res e hres) (fun _ => hcode)
  obtain ⟨h₂, hR₂⟩ := siteMS_minv hKA he
  have hsim := sim_run (mx := mx) hx.facts.wf (lookAgree_ext hx) (fun hs => by
      simp only [strLitStored, natLitStored, Bool.and_eq_true] at hs
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩, h₉⟩, h₁₀⟩ := hs
      exact ⟨⟨h₁, h₂, h₃⟩, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩) e F
    _ _ _ _ h₂ hR₂ hr F (.inl ⟨rfl, rfl⟩)
  generalize g4Comp env₁.find? env₁.findProj? PA e = rA at hsim ⊢
  generalize g4Comp env₂.find? env₂.findProj? PB e = rB at hsim ⊢
  obtain ⟨oA, QA⟩ := rA
  obtain ⟨oB, QB⟩ := rB
  unfold MS.run siteMS at hsim
  dsimp only at hsim ⊢
  generalize g4Run env₁.find? env₁.findProj? mx F { QA with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[] #[]
    QA.slotA #[] (Array.replicate 1024 0) 0 oA 0 0 0 = outA at hsim ⊢
  generalize g4Run env₂.find? env₂.findProj? mx F { QB with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0]
    #[] #[] #[] QB.slotA #[] (Array.replicate 1024 0) 0 oB 0 0 0 = outB at hsim ⊢
  rcases hsim with ⟨st, rfl, hb⟩ | ⟨g, st, rfl, rfl⟩ | ⟨sA, sB, lA, lB, hr', hm1, -, hv, rfl, rfl⟩
  · obtain ⟨st', rfl⟩ := hb rfl
    rfl
  · cases g <;> rfl
  · dsimp only
    have hg := hr'.regs
    simp only [RegRel, hm1] at hg
    obtain ⟨-, hx', -⟩ := hg
    rw [hx']
    have hcond : (sB.val[g4X4 sA.x]! == 1 && sB.val[g4X4 sA.x + 3]! == 0 &&
        sB.val[g4X4 sA.x + 1]! == sB.P.kTrue) =
        (sA.val[g4X4 sA.x]! == 1 && sA.val[g4X4 sA.x + 3]! == 0 && sA.val[g4X4 sA.x + 1]! == sA.P.kTrue) := by
      obtain ⟨w0, -, w3, hw⟩ := hr'.valW hv
      rw [w0, w3]
      by_cases h1 : sA.val[g4X4 sA.x]! = 1
      · rw [h1] at hw
        have hk : ERel (Stored env₁) sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! := hw
        rw [ent_beq hr'.invA.toCompInv hr'.invB.toCompInv hk hr'.kTrue.1]
      · have h1' : (sA.val[g4X4 sA.x]! == 1) = false := by simpa using h1
        simp only [h1', Bool.false_and]
    rw [hcond]
    split <;> rfl

/-- **The specification's engine call at an extension** (`groundSite`): on
two sides resolving in `env₁`, one answer at `env₂` and at `env₁`. -/
theorem groundSite_ext {env₁ env₂ : Env} (hx : EnvExt env₁ env₂) (eager : Bool) {a b : Expr}
    (ha : Res env₁ a) (hb : Res env₁ b) :
    groundSite eager env₂ a b = groundSite eager env₁ a b := by
  unfold groundSite
  rcases ht : groundTarget eager a b with _ | t
  · rfl
  · obtain ⟨hside, hcl⟩ := groundTarget_some ht
    have hres : Res env₁ t := by
      rcases hside with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ha
      · exact hb
    dsimp only
    rw [ground4_ext hx none (2 * groundFuel + 1) hcl hres]

end ConLeche.Verify.Ground
