module

public import ConLeche.Model.Inductives.GenCallKit
public import ConLeche.Model.Inductives.GenNodeList

public section

/-!
# A generated call, decoded (lane GENREC-B2)

`genCall_data` — a generated call of recursor `c`'s `j`-th rule
(`genCallT` at `genIhdAV`) is, by construction, a recursive field `i` of
the class's constructor `x` (its run `ClassCtorRun`): the declared fields
opened at the rule's prefix, the datum's walked telescope instantiated at
them, the field's `ih` telescope opened, the callee the family's recursor
at the `ih`'s class; the target is the `ih`'s index readings and the field
applied.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead GenRecRun ClassMajorRun ClassCtorRun openPisAtFvars
  targetPiDomsWith fueledOps mkFEnv NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Decode

variable {F : Nat} {env₁ envC : Env} {p : BlockParts} {nestedBit : Bool}
  {pos : NestState} {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **A class's constructor, as the generated stage read it**: the
`j`-th constructor of recursor `c`'s class, its run, the rule generated
for it. -/
theorem genCtor_at
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {c : Nat} (hc : c < (ConLeche.tgtRs out).length) {j : Nat}
    (hj : j < (tgtMajor out c).ctors.length) :
    ∃ cls M₀ nfs cA x gen, R.rd.recCls[c]? = some cls ∧ cls < R.Ms.length ∧
      R.Ms₀[cls]? = some M₀ ∧ R.Ms[cls]? = some { M₀ with nfs := nfs } ∧
      tgtMajor out c = { M₀ with nfs := nfs } ∧
      Nonempty (ClassMajorRun μ F (mkFEnv envC) p.toBlockShape ctorsAs R.ctx.params
        (ConLeche.classKeyCanon R.ctx.params (R.rd.classes.getD cls default)) M₀) ∧
      ConLeche.targetMajorNfs (fueledOps μ F) envC p.toBlockShape (cvTas.map (·.type))
        M₀.pfvs M₀.lvls M₀.ds M₀.ctors R.st.ctorNfs.toList = .ok nfs ∧
      M₀.ctors[j]? = some cA ∧ (R.ctors.getD cls [])[j]? = some x ∧
      genCtorAt R.g R.rd c j = x ∧
      Nonempty (ClassCtorRun μ F envC p.toBlockShape (cvTas.map (·.type)) R.rd R.Ms cls cA x) ∧
      ConLeche.classGenRule R.g (ConLeche.classRecOf R.rd.recCls R.cvGs)
        ((out.getD c default).1.levelParams.map .param) cls x = some gen := by
  have hi' : c < out.length := by simpa [ConLeche.tgtRs] using hc
  obtain ⟨rc, cls, cvG, rhss, M₀, nfs, hrc, hcl, hlt, hM₀, hMs, ho, -, hMR, hnfs⟩ :=
    genOut_cls R hi'
  have hMeq : tgtMajor out c = { M₀ with nfs := nfs } := by
    simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
  rw [hMeq] at hj
  obtain ⟨c', cvG', rhss', hc', -, -, ho', hr, -⟩ := genRecRun_at R hrc
  rw [hcl] at hc'
  obtain rfl := Option.some.inj hc'
  rw [ho] at ho'
  obtain ⟨rfl, -, rfl⟩ : cvG = cvG' ∧ _ ∧ rhss = rhss' := by
    simp only [Option.some.injEq, Prod.mk.injEq] at ho'
    exact ⟨ho'.1, ho'.2.1, ho'.2.2⟩
  obtain ⟨-, hallR⟩ := ConLeche.classRulesOk_run hr
  obtain ⟨-, hallC⟩ := ConLeche.classesCtors_run R.hctors
  obtain ⟨xs', hxs', hco⟩ := hallC cls _ hMs
  obtain ⟨-, hallX⟩ := ConLeche.classCtorsOf_run hco
  obtain ⟨cA, hcA⟩ : ∃ cA, M₀.ctors[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨x, hx, hRc⟩ := hallX j cA hcA
  have hgd : R.ctors.getD cls [] = xs' := by rw [List.getD_eq_getElem?_getD, hxs', Option.getD_some]
  rw [← hgd] at hx
  obtain ⟨gen, -, -, hgen, -⟩ := hallR j x hx
  have hcvG : (out.getD c default).1 = cvG := by
    rw [List.getD_eq_getElem?_getD, ho, Option.getD_some]
  refine ⟨cls, M₀, nfs, cA, x, gen, hcl, hlt, hM₀, hMs, hMeq, hMR, hnfs, hcA, hx, ?_,
    by rw [Nat.zero_add] at hRc; exact hRc, by rw [hcvG]; exact hgen⟩
  unfold genCtorAt genClsOf
  show (R.ctors.getD (R.rd.recCls.getD c 0) []).getD j default = x
  rw [List.getD_eq_getElem?_getD (l := R.rd.recCls), hcl, Option.getD_some,
    List.getD_eq_getElem?_getD (l := R.ctors.getD cls []), hx, Option.getD_some]


/-- **A generated call, decoded** (see the module docstring). -/
theorem genCall_data
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {c : Nat} (hc : c < (ConLeche.tgtRs out).length) {j : Nat}
    (hj : j < (tgtMajor out c).ctors.length)
    (acval : Name → (Name → Nat) → AnnotTerm) (bit : Nat) (ψ : Name → Nat)
    (tup : Nat → List V → V) (ρ : Nat → V) {xs fs : List V} {v : V}
    (hcall : genCallT tup ρ (fun c j => genIhdAV acval envC R.g R.rd bit ψ c j) xs c j fs v) :
    ∃ (cls : Nat) (M₀ : TargetMajor) (nfs : List ConLeche.NestCtorNf) (cA : ConstantVal × Nat)
      (x : ClassCtor) (i tt tele : Nat) (fvsR : List Expr) (oR : Expr) (ws xsO : List Expr)
      (leafO : Expr) (bs : List V),
      R.rd.recCls[c]? = some cls ∧ cls < R.Ms.length ∧
      R.Ms₀[cls]? = some M₀ ∧ R.Ms[cls]? = some { M₀ with nfs := nfs } ∧
      tgtMajor out c = { M₀ with nfs := nfs } ∧
      Nonempty (ClassMajorRun μ F (mkFEnv envC) p.toBlockShape ctorsAs R.ctx.params
        (ConLeche.classKeyCanon R.ctx.params (R.rd.classes.getD cls default)) M₀) ∧
      ConLeche.targetMajorNfs (fueledOps μ F) envC p.toBlockShape (cvTas.map (·.type))
        M₀.pfvs M₀.lvls M₀.ds M₀.ctors R.st.ctorNfs.toList = .ok nfs ∧
      M₀.ctors[j]? = some cA ∧ (R.ctors.getD cls [])[j]? = some x ∧
      Nonempty (ClassCtorRun μ F envC p.toBlockShape (cvTas.map (·.type)) R.rd R.Ms cls cA x) ∧
      i < x.nF ∧ x.kinds.getD i .ordinary = .recursive tt tele ∧
      openPisAtFvars x.nF x.tyD R.pre.length = some (fvsR, oR) ∧
      targetPiDomsWith fvsR x.tyN = some ws ∧
      openPisAtFvars tele (ws.getD i default) (R.pre.length + x.nF) = some (xsO, leafO) ∧
      R.rd.recCls[genRecIdx R.rd tt]? = some tt ∧
      genRecIdx R.rd tt < (ConLeche.tgtRs out).length ∧
      SpineFit (consList (xs ++ fs) ρ) (readOpenedDoms acval envC ψ (R.pre.length + x.nF) xsO) bs ∧
      v = tagged (genRecIdx R.rd tt) (tup (genRecIdx R.rd tt)
          ((leafO.getAppArgs.drop (R.Ms.getD tt default).nPc).map fun e =>
            interp V (consList bs (consList (xs ++ fs) ρ))
              ((denoteMeta acval envC ψ (R.pre.length + x.nF + xsO.length) e).getD default)))
        (interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta acval envC ψ (R.pre.length + x.nF + xsO.length)
            (Expr.mkAppN (fvsR.getD i default) xsO)).getD default)) := by
  obtain ⟨cls, M₀, nfs, cA, x, gen, hcl, hlt, hM₀, hMs, hMeq, hMR, hnfs, hcA, hxj, hgx, hRc, hgen⟩ :=
    genCtor_at R hc hj
  obtain ⟨q, hq, bs, hbs, hv⟩ := hcall
  simp only [genIhdAV, hgx] at hq
  obtain ⟨⟨i, tt, tele⟩, hrec, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hi, hk⟩ := ConLeche.ClassGen.recs_mem (x := x) hrec
  obtain ⟨fvsR, oR, ws, xsO₀, idx, rn, hop, hws, hih, hrn⟩ := ConLeche.classGenRule_ih hgen hi hk
  have hpre : R.g.pre = R.pre := rfl
  rw [hpre] at hop hih
  have hih' := hih
  unfold ConLeche.ClassGen.ihParts at hih'
  obtain ⟨⟨xsO, leafO⟩, hopO, hih'⟩ := Option.bind_eq_some_iff.mp hih'
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hih'
  obtain ⟨rfl, rfl⟩ := hih'
  -- the callee
  have hlenG := (ConLeche.classRecTysOk_run R.hcvGs).1
  have hlenO := (ConLeche.classRecsRulesOk_run R.hrules).1
  have hle : R.cvGs.length ≤ R.rd.recCls.length := by
    obtain ⟨hlG, hallG⟩ := ConLeche.classRecTysOk_run R.hcvGs
    rw [hlG]
    rcases Nat.eq_zero_or_pos p.toBlockShape.recs.length with h0 | hpos
    · omega
    · obtain ⟨c0, -, hc0, -⟩ := hallG (p.toBlockShape.recs.length - 1) _
        (List.getElem?_eq_getElem (show p.toBlockShape.recs.length - 1 < p.toBlockShape.recs.length
          by omega))
      have := (List.getElem?_eq_some_iff.mp hc0).1
      omega
  obtain ⟨hrr, hrl⟩ := genRecIdx_spec hrn hle
  refine ⟨cls, M₀, nfs, cA, x, i, tt, tele, fvsR, oR, ws, xsO, leafO, bs, hcl, hlt, hM₀, hMs, hMeq,
    hMR, hnfs, hcA, hxj, hRc, hi, hk, hop, hws, hopO, hrr, ?_, ?_, ?_⟩
  · simp only [ConLeche.tgtRs, List.length_map]; omega
  · simp only [hop, hws, hpre, Option.map_some, Option.getD_some, hih] at hbs
    simpa [List.map_map, Function.comp_def] using hbs
  · simp only [hop, hws, hpre, Option.map_some, Option.getD_some, hih] at hv
    rw [hv, List.map_map]; rfl

end Decode

end ConLeche.Model
