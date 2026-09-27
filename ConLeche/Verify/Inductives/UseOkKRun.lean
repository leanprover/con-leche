module

public import ConLeche.Verify.Inductives.UseOkK
public import ConLeche.Verify.Inductives.PosDerivKInv
import ConLeche.Verify.Inductives.LayoutKSpec

public section

/-!
# The run discharges the use hook (PRIMREC / NESTKN-M3B)

`hookOkK_useOkK`: every use of a successful key-named positivity run
satisfies `UseOkK` — its (K) clauses from the kernel's checks (`useK`'s U0/U1,
`nestLayoutK`'s U3/U5 and joint typing, `matchK`'s `bindsOkK`), its (P)
clause from the kernel's own constructions (`useSynK_of_run`).  The one
hypothesis is the environment's: the context's stored types are closed
(`CtxTysClosed`, `EnvWF`'s `ConstWF` at the context's lookup).

The inversion (`posK_deriv`, generic in the hook since M3B) then yields the
derivation AT the hook: `nestBlockCtorsK_derivU` — every member
constructor, and every entry of the run's final node cache, derived at
`UseOkK`.  `nestBlockCtorsK_posPremise` / `nestBlockCtorsK_accPremise` are
the premises the install consumers read (`memberCtorDK_monoOk` for
`blockCtorPos_of_walk`, `memberCtorDK_accOk` for `blockCtorAcc_of_walk`).
-/

namespace ConLeche

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}

/-- **The use hook, discharged by the run.** -/
theorem hookOkK_useOkK (hcl : CtxTysClosed ctx) : HookOkK ops env ctx (UseOkK ops env ctx) := by
  intro L kc kn ps lo metc rs bs nd hu0 hu1 hrb hlay hgrp hlv hkds hlen hbs hinner hall hfT hfN
    hmet hbok
  obtain ⟨-, -, -, hlvl, -, -, -, -, -, ⟨T, hT⟩, -, hU3, hU5⟩ := nestLayoutK_spec hlay
  refine ⟨hu0, hu1, hrb, hU3, ⟨_, T, by rw [hlvl]; exact hT⟩, hU5, fun j hj => ?_,
    fun hs => useSynK_of_run hcl hs (hkds.symm.trans hrb) hlay hbs hinner⟩
  obtain ⟨b, hb, hbc, hty, har⟩ := bindsOkK_ok hbok j (List.mem_range.mpr hj)
  rw [hfT] at hty
  refine ⟨b, hb, hbc, hty, fun hjm key nI hk => ?_⟩
  rw [← hmet] at hjm
  have h := har hjm
  rw [hfN] at h
  have hnI : (lo.L.fams.map (·.2)).getD j 0 = nI := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hk]; rfl
  rwa [hnI] at h

/-- The context's stored types are closed, from the environment's
well-formedness, at a context reading the environment. -/
theorem ctxTysClosed_of_envWF (hwf : EnvWF env) (hfind : ctx.find? = env.find?) :
    CtxTysClosed ctx := by
  intro n ci hf
  rw [hfind] at hf
  have hc := hwf ci (List.mem_of_find?_eq_some hf)
  exact ⟨hc.1, hc.2.2.2.1⟩

/-- **`nestBlockCtorsK`, derived AT THE USE HOOK**: every member
constructor's crest derived at the root layout at `UseOkK`, with the run's
kinds and normal form, and the final state's invariant (every cached node's
derivation at `UseOkK`). -/
theorem nestBlockCtorsK_derivU (hcl : CtxTysClosed ctx) {holes : List Expr}
    {css : List (List (ConstantVal × Nat))} {ksss : List (List (List NestFieldKind))}
    {nsss : List (List Expr)} {base : NestState}
    (h : nestBlockCtorsK (m := CheckM) ops env ctx holes css = .ok (ksss, nsss, base)) :
    ∃ st : NestStK, st.base = base ∧ DerivCacheK ops env ctx (UseOkK ops env ctx) st ∧
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
        ∃ crest ks tyN, instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
          (ksss.getD c [])[j]? = some ks ∧ (nsss.getD c [])[j]? = some tyN ∧
          MemberCtorDKH ops env ctx (UseOkK ops env ctx) cA.2 crest (ks.map (·.erase)) tyN :=
  nestBlockCtorsK_deriv (hookOkK_useOkK hcl) h

/-- **The positivity consumer's premise** (`memberCtorDK_monoOk`'s `hd`, which
`blockCtorPos_of_walk` will read in place of the path route's `MemberCtorD`):
from the run of `nestBlockCtorsK`, every member constructor's crest,
kinds and normal form, derived at `UseOkK`. -/
theorem nestBlockCtorsK_posPremise (hcl : CtxTysClosed ctx) {holes : List Expr}
    {css : List (List (ConstantVal × Nat))} {ksss : List (List (List NestFieldKind))}
    {nsss : List (List Expr)} {base : NestState}
    (h : nestBlockCtorsK (m := CheckM) ops env ctx holes css = .ok (ksss, nsss, base))
    {c : Nat} {cs : List (ConstantVal × Nat)} (hc : css[c]? = some cs)
    {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    ∃ crest ks, instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
      (ksss.getD c [])[j]? = some ks ∧
      MemberCtorDKH ops env ctx (UseOkK ops env ctx) cA.2 crest (ks.map (·.erase))
        ((nsss.getD c []).getD j default) := by
  obtain ⟨-, -, -, hall⟩ := nestBlockCtorsK_derivU hcl h
  obtain ⟨crest, ks, tyN, hcr, hks, hnf, hd⟩ := hall c cs hc j cA hj
  refine ⟨crest, ks, hcr, hks, ?_⟩
  rw [List.getD_eq_getElem?_getD, hnf]
  exact hd

/-- **The accessibility consumer's premises** (`memberCtorDK_accOk`'s `htele`,
`hhead`, `hok`, which `blockCtorAcc_of_walk` will read): from the run of
`nestBlockCtorsK`, every member constructor's field telescope derived at the
root layout at `UseOkK`, its result headed by a member with hole-free
indices, its normal form the telescope closed. -/
theorem nestBlockCtorsK_accPremise (hcl : CtxTysClosed ctx) {holes : List Expr}
    {css : List (List (ConstantVal × Nat))} {ksss : List (List (List NestFieldKind))}
    {nsss : List (List Expr)} {base : NestState}
    (h : nestBlockCtorsK (m := CheckM) ops env ctx holes css = .ok (ksss, nsss, base))
    {c : Nat} {cs : List (ConstantVal × Nat)} (hc : css[c]? = some cs)
    {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    ∃ crest ks met nds cur, instPisWith ctx.params (nestAbstract ctx holes cA.1.type) = some crest ∧
      (ksss.getD c [])[j]? = some ks ∧
      PosDKH ops env ctx (UseOkK ops env ctx)
        (.tele (rootLayoutK ctx) met cA.2 0 crest (ks.map (·.erase)) nds cur) ∧
      nestResHead cur = true ∧
      (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true ∧
      (nsss.getD c []).getD j default = closeTelescope nds (ctx.hiAt 0) cur := by
  obtain ⟨crest, ks, hcr, hks, met, nds, cur, htele, htyN, -, hhead, hok, -⟩ :=
    nestBlockCtorsK_posPremise (ops := ops) (env := env) hcl h hc hj
  exact ⟨crest, ks, met, nds, cur, hcr, hks, htele, hhead, hok, htyN⟩

end ConLeche
