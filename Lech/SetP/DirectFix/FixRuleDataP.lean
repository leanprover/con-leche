import Lech.SetP.DirectFix.FixRecDataP

/-!
# The recursive rules' readings at the recursor's cons (task #188)

A recursive rule's right-hand side mentions the recursor, so it reads
only at an environment holding it: the constructors' reading
premises cross the recursor's cons (`CtorReadsR.cross` — the
constructor types and their index expressions, instantiated at the
opening's variables, resolve at the pre-recursor environment), and
`denoteP_directRecRhsR` reads rule `j` there, with the recursor's leaf
the stored valuation.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta
  DirectFixParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Boundness through openings -/

omit [SetTheory V] in
/-- A bounded telescope's binder domains and body are bounded. -/
theorem constsBound_stripPis {env₀ : Env} :
    ∀ (n : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      ConstsBound env₀ e → e.stripPis n = some (bs, body) →
      (∀ b ∈ bs, ConstsBound env₀ b.2.1) ∧ ConstsBound env₀ body
  | 0, e, bs, body, he, hst => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨(fun b hb => nomatch hb), he⟩
  | n + 1, e, bs, body, he, hst => by
    match e, he, hst with
    | .forallE nm dom bd mb, he, hst =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs', body₀⟩, hst', heq⟩ := hst
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [constsBound_forallE] at he
      obtain ⟨hbs, hbody⟩ := constsBound_stripPis n he.2 hst'
      refine ⟨fun b hb => ?_, hbody⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact he.1
      · exact hbs b hb

omit [SetTheory V] in
/-- A bounded application's arguments are bounded. -/
theorem constsBound_getAppArgs {env₀ : Env} :
    ∀ (e : Expr), ConstsBound env₀ e → ∀ a ∈ e.getAppArgs, ConstsBound env₀ a
  | .app f a, he, x, hx => by
    rw [constsBound_app] at he
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact constsBound_getAppArgs f he.1 x hx
    · exact he.2
  | .bvar _, _, _, hx => nomatch hx
  | .fvar _ _ _, _, _, hx => nomatch hx
  | .sort _, _, _, hx => nomatch hx
  | .const _ _, _, _, hx => nomatch hx
  | .lam _ _ _ _, _, _, hx => nomatch hx
  | .forallE _ _ _ _, _, _, hx => nomatch hx
  | .letE _ _ _ _, _, _, hx => nomatch hx
  | .lit _, _, _, hx => nomatch hx
  | .proj _ _ _, _, _, hx => nomatch hx

omit [SetTheory V] in
/-- Instantiation at bounded terms preserves boundness. -/
theorem constsBound_instSeq {env₀ : Env} :
    ∀ (as : List Expr) (t : Nat) (e : Expr), (∀ a ∈ as, ConstsBound env₀ a) →
      ConstsBound env₀ e → ConstsBound env₀ (Expr.instSeq as t e)
  | [], _, _, _, he => he
  | a :: as, t, e, has, he =>
    constsBound_instSeq as (t - 1) _ (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))
      (ConstsBound.instantiate1 (has a List.mem_cons_self) e t he)

omit [SetTheory V] in
/-- An opening's variables (their types) and residual are bounded when
the opened term is. -/
theorem openPisAtFvars_constsBound {env₀ : Env} :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      ConstsBound env₀ e → openPisAtFvars n e d = some (fvs, o) →
      (∀ x ∈ fvs, ConstsBound env₀ x) ∧ ConstsBound env₀ o
  | 0, e, d, fvs, o, he, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    exact ⟨(fun x hx => nomatch hx), he⟩
  | n + 1, e, d, fvs, o, he, hop => by
    match e, he, hop with
    | .forallE nm dom bd mb, he, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs₁ e₁ h₁ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        rw [constsBound_forallE] at he
        have hfv : ConstsBound env₀ (Expr.fvar d nm dom) := by
          rw [constsBound_fvar]; exact he.1
        obtain ⟨hfvs, ho⟩ := openPisAtFvars_constsBound n
          (ConstsBound.instantiate1 hfv bd 0 he.2) h₁
        refine ⟨fun x hx => ?_, ho⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hfv
        · exact hfvs x hx
      · exact nomatch hop

/-! ## The constructors' reading premises across the recursor's cons -/

/-- A recursive constructor's reading premise crosses a cons whose
head is not the block's former and is not mentioned by the
constructor's type. -/
theorem CtorReadR.cross {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {c : Name × Nat × Expr × List Nat} {cd : CtorDatumR}
    (h : CtorReadR m ψ T lps nP nIdx c cd)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e) (hcb : ConstsBound env c.2.2.1)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    CtorReadR m₂ ψ T lps nP nIdx c cd := by
  have hTac : m₂.acval T ψ = m.acval T ψ := by rw [hac, acvalWith_ne hT]
  obtain ⟨ci, hci, hlps⟩ := h.find
  refine ⟨h.name, h.nF, ⟨ci, Lech.Env.find?_cons_of_fresh hfresh hci, hlps⟩, h.hasFvar, h.bounded,
    h.resid, ?_, h.len, h.lenE, h.recIdx, h.recIdxBnd, h.recIdxSorted, h.eissLen, h.eisLen, ?_, ?_⟩
  · rw [hTac, hac]
    exact denoteP_cons_mono hfresh (hat _) ψ 0 hcb h.read
  · intro i hi fvs o hop
    rw [hac]
    refine DenoteSpineP.cons_mono hfresh hat ?_ (h.eisRead i hi fvs o hop)
    -- the instantiated index expressions are bounded
    obtain ⟨cbs, es, hst, -⟩ := h.resid
    obtain ⟨hbs, -⟩ := constsBound_stripPis (nP + c.2.1) hcb hst
    obtain ⟨hfvs, -⟩ := openPisAtFvars_constsBound (nP + c.2.1) hcb hop
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    refine constsBound_instSeq _ _ _ (fun x hx => hfvs x (List.mem_of_mem_take hx)) ?_
    unfold Lech.directFieldIdxOf at he
    rw [hst] at he
    have hlt : nP + i < cbs.length := by
      rw [Lech.Expr.stripPis_length _ hst]
      have := h.recIdxBnd i hi
      omega
    have hmem : cbs.getD (nP + i) default ∈ cbs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.getElem_mem hlt
    exact constsBound_getAppArgs _ (hbs _ hmem) e (List.mem_of_mem_drop he)
  · intro i hi
    rw [hTac]
    exact h.recEntry i hi

/-- The reading premises cross the recursor's cons. -/
theorem CtorReadsR.cross {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none) (hT : T ≠ c₀.name)
    (hat : ∀ e : Expr, ConsCrossAt c₀ e)
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    ∀ {ctors : List (Name × Nat × Expr × List Nat)} {cds : List CtorDatumR},
      CtorReadsR m ψ T lps nP nIdx ctors cds →
      (∀ c ∈ ctors, ConstsBound env c.2.2.1) →
      CtorReadsR m₂ ψ T lps nP nIdx ctors cds
  | _, _, .nil, _ => .nil
  | c :: _, _, .cons hr htl, hcb =>
    .cons (hr.cross hfresh hT hat (hcb c List.mem_cons_self) m₂ hac)
      (CtorReadsR.cross hfresh hT hat m₂ hac htl fun c' hc' => hcb c' (List.mem_cons_of_mem _ hc'))

/-! ## The rules, read at the recursor's cons -/

/-- **Rule `j`'s reading** at the recursor's cons: the rule's λ-data
over the rule's core with the stored recursor leaf. -/
theorem fixRuleData_of (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectFixParts} {cvTa cvRa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {rhss : List Expr} {caps : IndCaps}
    (hRec : Lech.checkDirectFixRec (Lech.fueledOps μ F) env p cvTa ctorsA = .ok (cvRa, rhss))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    {bsT : List (Name × Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest))
    {ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    {env₀ : Env} {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
    {eissF : Nat → (Name → Nat) → List (List AVExpr)}
    (hlenK : p.kinds.length = ctorsA.length)
    (hks : ∀ i, i < ctorsA.length → p.kinds[i]? = some (ksF i))
    (hcf : ∀ i cA, ctorsA[i]? = some cA →
      FixCtorFactsAt mp.base2 env₀ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF i cA)
    {mI rP : Nat} {rules : List Lech.RecRule}
    (hfresh : env.find? cvRa.name = none) (hT : p.cvT.name ≠ cvRa.name)
    {A : (Name → Nat) → AVExpr}
    (m₂ : EnvS2Core V ⟨.recInfo cvRa mI rP rules :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name A)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) :
    ∃ rhs : Expr, rhss[j]? = some rhs ∧
      rhs.constsResolve ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩ = true ∧
      rhs.hasFvar = false ∧ rhs.looseBVarsBounded 0 = true ∧
      ∀ ψ : Name → Nat, denoteP m₂.acval ⟨.recInfo cvRa mI rP rules :: env.consts⟩ ψ 0 rhs
        = some (mkLamsAV (fixRuleDataAV m₂ p.cvT.name ψ p.nP p.nIdx
            (Lech.directElimLevel p.elim p.large) ((ppsAll ψ).take p.nP) ((ppsAll ψ).drop p.nP)
            (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0) (dsF j ψ))
          (fixRuleCoreAV (A ψ) p.nP cA.2 ctorsA.length j (Lech.recIdxOf (ksF j)) (eissF j ψ))) := by
  obtain ⟨cvRi, recTy, sty, u, -, -, -, -, -, -, -, -, -, hrules, rfl⟩ :=
    Lech.checkDirectFixRec_shape hRec
  obtain ⟨hTf, -, -, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf
  have hjn : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, hall⟩ := Lech.checkDirectFixRules_inv hrules
  have hlen4 : (Lech.directFixCtors4 ctorsA p.kinds).length = ctorsA.length :=
    Lech.directFixCtors4_length hlenK.symm
  obtain ⟨rhs, hrhs, hgen, -, hres, hbr, hrf⟩ := hall j (by rw [hlen4]; exact hjn)
  rw [Nat.zero_add] at hgen
  -- the cons head and the crossing
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ mI rP rules) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hcbC : ∀ c ∈ Lech.directFixCtors4 ctorsA p.kinds, ConstsBound env c.2.2.1 := by
    intro c hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hc
    simp only [Lech.directFixCtors4, List.getElem?_zipWith] at hi
    cases hA : ctorsA[i]? with
    | none => rw [hA] at hi; exact nomatch hi
    | some cAi =>
      have hin : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hA).1
      rw [hA, hks i hin] at hi
      simp only [Option.some.injEq] at hi
      subst hi
      obtain ⟨hf, -, -⟩ := hcf i cAi hA
      obtain ⟨-, -, hCres, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hf)
      exact constsBound_of_constsResolve _ hCres
  have hcr₂ : ∀ ψ, CtorReadsR m₂ ψ p.cvT.name p.cvT.levelParams p.nP p.nIdx
      (Lech.directFixCtors4 ctorsA p.kinds) (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0) :=
    fun ψ => CtorReadsR.cross hfresh hT hcross m₂ hac (fixCtorReadsR_of ψ hlenK hks hcf) hcbC
  -- the former and the recursor at the cons
  have hcbT : ConstsBound env cvTa.type := by
    obtain ⟨-, -, hTres, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfT)
    exact constsBound_of_constsResolve _ hTres
  have hFD₂ := hFD.cross (c₀ := .recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ mI rP rules) hfresh
    (hcross _) hcbT m₂ hac
  have hfT₂ : (⟨.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ mI rP rules :: env.consts⟩ : Env).find?
      p.cvT.name = some (.indInfo cvTa caps) :=
    Lech.Env.find?_cons_of_fresh hfresh hfT
  have hfR₂ : (⟨.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ mI rP rules :: env.consts⟩ : Env).find?
      p.cvR.name = some (.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ mI rP rules) :=
    Lech.Env.find?_cons_self _ _
  have hjd : ∀ ψ, (fixCtorDataList dsF esF ksF eissF ψ ctorsA 0)[j]?
      = some (cA.1.name, cA.2, dsF j ψ, esF j ψ, Lech.recIdxOf (ksF j), eissF j ψ) := by
    intro ψ
    rw [fixCtorDataList_getElem?, hj, Nat.zero_add]
    rfl
  refine ⟨rhs, hrhs, hres, hrf, hbr, fun ψ => ?_⟩
  have := denoteP_directRecRhsR (m := m₂) hfT₂
    (show (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams = p.cvT.levelParams from hlpsT)
    (hcr₂ ψ) hfR₂ rfl hgen hTf (by rw [hstripT]; rfl) hopT (hFD₂.read ψ) (hFD₂.len ψ) (hjd ψ)
  rw [fixCtorDataList_length] at this
  rw [this, hac]
  show some (mkLamsAV _ (fixRuleCoreAV (acvalWith mp.base2.acval p.cvR.name A p.cvR.name ψ) _ _ _ _ _ _)) = _
  rw [acvalWith_self]

end Lech.SetP
