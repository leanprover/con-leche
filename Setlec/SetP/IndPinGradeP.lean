import Setlec.SetP.IndOpenRevP

/-!
# The nested-pin grading, produced (task #161, IND TIER part 7)

**The part-6 repair's producer.**  The probe refuted the old conjunct
by naming the wrong object; the ratified repair grades
`AVExpr.instRevChain zs vpa` — the term the equality half already
names — under the prefix telescope's own fit.  This file establishes
exactly that, from exactly the certificate the checker runs.

The route, in one line: the certificate is about `pinsP` at the public
frame, `pinCrossP` turns that object into this one **syntactically**,
and `annotOkP_instSeq` carries the grading across the substitution
because the fired prefix is graded (which the repaired conjunct, unlike
the interp-equality half, *does* hypothesise).

```
   checkTypedList … pinsP cdomsP          (Kernel/Modeled.lean:290)
     ⇒ TypedListOk.infer_of_mem           (Verify/IotaWalkInv.lean)
     ⇒ InferClaims2P                      ∀ σ, Sat2 V Δ σ → AnnotOkP V σ w0
     ⇒ at σ := chainP V ρ (zs ++ padA…)   Sat2 by the prefix fit
     ⇒ annotOkP_instSeq                   AnnotOkP V ρ (instSeq … w0)
     ⇒ pinCrossP                          AnnotOkP V ρ (instRevChain zs vpa)
```

Three things are worth naming, because each is a place the earlier
spelling could not have gone:

* **the grading crosses the substitution only because the arguments
  are graded.**  `AnnotOk2_inst`/`AnnotValidV_inst` charge for the
  substituted value at every cut, so `annotOkP_instSeq` needs
  `∀ w ∈ ws, AnnotOkP V ρ w`.  The repaired conjunct supplies it
  (`∀ z ∈ zs, AnnotOkP V ρ z`); the interp-equality half never could,
  which is precisely why part 4 routed the *equality* through the
  top-down descent instead;
* **the padding must be graded too**, and must inhabit its context
  slot.  v1's `dummyPropT` only had to do the second; here the spine's
  padding is charged a grading by `annotOkP_instSeq`.  `.prf` is the
  obvious candidate and it **fails**: `pt_not_mem_univZero`.  The
  padding that works is `padA := .eqE (.sort 0) (.sort 0) (.sort 0)` —
  its reading is `eqv (univ 0) (univ 0) ∈ˢ univ 0` (`eqv_mem_univ`) and
  its grading is `True ∧ True`;
* **the certificate's context is the public frame's, padded at the
  bottom.**  The pins mention only openers `0 … rP - 1` while the run
  is at depth `rP + cnF`, so the entries the conversion consults sit
  at indices `≥ cnF`; the `cnF` slots below them are the part-3/4
  padding trick's `.sort 0`s, satisfied by the spine's own padding.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The padding element

The spine's padding slots must **inhabit** their `.sort 0` context
entries *and* be **graded**.  `.prf` fails the first
(`pt_not_mem_univZero`); a reflexive equation does both. -/

/-- The reading tier's spine padding: a closed truth value. -/
def padA : AVExpr := .eqE (.sort 0) (.sort 0) (.sort 0)

@[simp] theorem interp2_padA (ρ : Nat → V) :
    interp2 V ρ padA = eqv (univ 0 : V) (univ 0) := by
  rw [padA, interp2_eqE, interp2_sort]

theorem annotOkP_padA (ρ : Nat → V) : AnnotOkP V ρ padA := by
  refine ⟨?_, ?_⟩
  · rw [padA, AnnotOk2_eqE]
    exact ⟨trivial, trivial⟩
  · rw [padA, AnnotValidV_eqE]
    exact ⟨trivial, trivial⟩

/-! ## The chain's ambient environment -/

/-- Shifting past a whole reading chain cancels it — the `chainP`
mirror of `shiftE_envChainP`. -/
theorem shiftE_chainP (ρ : Nat → V) (ws : List AVExpr) :
    shiftE ws.length 0 (chainP V ρ ws) = ρ := by
  funext i
  show (if i < 0 then _ else chainP V ρ ws (i + ws.length)) = ρ i
  rw [if_neg (Nat.not_lt_zero i), chainP_ge (by omega)]
  congr 1
  omega

/-! ## Grading across a fired substitution -/

/-- **The grading crosses `instSeq`**: a body graded at the chain
environment, substituted along a spine whose elements are graded at
the ambient one, is graded at the ambient one.

`chainP_cons_eq_instE` is the whole content — the chain's `cons` step
*is* the `instE` the substitution lemma produces — and
`shiftE_chainP` cancels the lift each argument carries. -/
theorem annotOkP_instSeq {ρ : Nat → V} :
    ∀ (ws : List AVExpr) {X : AVExpr},
      (∀ w ∈ ws, AnnotOkP V ρ w) →
      AnnotOkP V (chainP V ρ ws) X →
      AnnotOkP V ρ (Setlec.SetR.AVExpr.instSeq ws (ws.length - 1) X) := by
  intro ws
  induction ws with
  | nil => intro X _ hX; exact hX
  | cons w ws ih =>
    intro X hoks hX
    have hokw : AnnotOkP V ρ w := hoks w List.mem_cons_self
    have hstep : AnnotOkP V (chainP V ρ ws) (X.inst w ws.length) := by
      have hshift : shiftE ws.length 0 (chainP V ρ ws) = ρ :=
        shiftE_chainP ρ ws
      refine ⟨?_, ?_⟩
      · rw [AnnotOk2_inst V X w ws.length (chainP V ρ ws)
          (by rw [hshift]; exact hokw.1)]
        rw [hshift, ← chainP_cons_eq_instE]
        exact hX.1
      · rw [AnnotValidV_inst V X w ws.length (chainP V ρ ws)
          (by rw [hshift]; exact hokw.2)]
        rw [hshift, ← chainP_cons_eq_instE]
        exact hX.2
    have h := ih (fun x hx => hoks x (List.mem_cons_of_mem _ hx)) hstep
    show AnnotOkP V ρ (Setlec.SetR.AVExpr.instSeq ws
      ((w :: ws).length - 1 - 1) (X.inst w ((w :: ws).length - 1)))
    simpa using h

/-! ## The padded chain satisfies the public frame's context -/

/-- **The public frame's padded context, satisfied by the fired
prefix.**  The frame's run sits at depth `rP + cnF` while its openers
occupy `0 … rP - 1`, so the context is `cnF` padding slots below the
recursor tower's own `rP`.  The chain of `zs ++ replicate cnF padA`
satisfies it: above the padding it is the prefix chain (the fit's own
`Sat2`), and each padding slot holds a truth value. -/
theorem sat2_padded_chainP {rP cnF : Nat} {TVa RP : AVExpr}
    {ΓP : List AVExpr} (htowerP : PiTeleP rP TVa ΓP RP)
    {zs : List AVExpr} {ρ : Nat → V} {restR : AVExpr}
    (hzslen : zs.length = rP) (hfit : TeleFitPA V ρ TVa zs restR) :
    Sat2 V (List.replicate cnF (.sort 0) ++ ΓP)
      (chainP V ρ (zs ++ List.replicate cnF padA)) := by
  have hΓlen : ΓP.length = rP := htowerP.length
  have hZlen : (zs ++ List.replicate cnF padA).length = rP + cnF := by
    simp only [List.length_append, List.length_replicate, hzslen]
  -- the prefix's own satisfaction, from the fit
  have hsatP : Sat2 V ΓP (chainP V ρ zs) :=
    sat2_of_tower htowerP hzslen
      (teleFitPA_to_chain rP htowerP hzslen hfit)
  intro i Aa hi
  by_cases hic : i < cnF
  · -- a padding slot: the value is a truth value
    rw [List.getElem?_append_left (by simpa using hic),
      List.getElem?_replicate_of_lt hic] at hi
    obtain rfl := Option.some.inj hi
    have hval : chainP V ρ (zs ++ List.replicate cnF padA) i
        = eqv (univ 0 : V) (univ 0) := by
      rw [chainP_lt (by rw [hZlen]; omega), hZlen,
        show (zs ++ List.replicate cnF padA).getD
            (rP + cnF - 1 - i) default = padA from by
          rw [List.getD, List.getElem?_append_right (by omega),
            hzslen, List.getElem?_replicate_of_lt (by omega)]
          rfl]
      rw [interp2_padA]
    show _ ∈ˢ interp2 V _ (AVExpr.sort 0)
    rw [interp2_sort, hval]
    exact eqv_mem_univ _ _
  · -- a tower slot: the chain is the prefix chain, shifted
    rw [List.getElem?_append_right (by simpa using hic)] at hi
    simp only [List.length_replicate] at hi
    have hilt : i - cnF < rP := by
      rcases Nat.lt_or_ge (i - cnF) rP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [hΓlen]; omega)] at hi
        exact nomatch hi
    have hval : chainP V ρ (zs ++ List.replicate cnF padA) i
        = chainP V ρ zs (i - cnF) := by
      rw [chainP_lt (by rw [hZlen]; omega), chainP_lt (by omega), hZlen,
        hzslen,
        show (zs ++ List.replicate cnF padA).getD
            (rP + cnF - 1 - i) default
          = zs.getD (rP - 1 - (i - cnF)) default from by
          rw [List.getD, List.getD,
            List.getElem?_append_left (by rw [hzslen]; omega),
            show rP + cnF - 1 - i = rP - 1 - (i - cnF) from by omega]]
    have henv : (fun j =>
        chainP V ρ (zs ++ List.replicate cnF padA) (j + i + 1))
        = (fun j => chainP V ρ zs (j + (i - cnF) + 1)) := by
      funext j
      by_cases hj : j + i + 1 < rP + cnF
      · rw [chainP_lt (by rw [hZlen]; omega),
          chainP_lt (by rw [hzslen]; omega), hZlen, hzslen,
          List.getD, List.getD,
          List.getElem?_append_left (by rw [hzslen]; omega),
          show rP + cnF - 1 - (j + i + 1)
            = rP - 1 - (j + (i - cnF) + 1) from by omega]
      · rw [chainP_ge (by rw [hZlen]; omega),
          chainP_ge (by rw [hzslen]; omega), hZlen, hzslen]
        congr 1
        omega
    rw [hval, henv]
    exact hsatP (i - cnF) Aa hi

/-! ## The producer -/

set_option maxHeartbeats 1600000 in
/-- **THE PRODUCER: the repaired nested-pin conjunct's grading half,
established from the checker's own certificate.**

`hcert` is the claims-layer form of `checkTypedList ops envSelf depth
pinsP cdomsP` (`Kernel/Modeled.lean:290`) read through
`TypedListOk.infer_of_mem` and `InferClaims2P`: context-guarded, at the
public frame's padded context, on the *instantiated* pin `pinsP i` —
the object the part-6 probe showed the certificate is actually about.

The conclusion is `RecRuleLawP`'s repaired conjunct verbatim, at the
chain the equality half names. -/
theorem nestedPinGradeP {acval : Name → (Name → Nat) → AVExpr}
    {cval : TConstVal}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AVExpr) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {rP cnF : Nat} {os : List Expr} (hoslen : os.length = rP)
    (hshape : ∀ (i : Nat) (x : Expr), os[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwsOs : ∀ x ∈ os, Expr.WScoped (rP + cnF) x)
    (hbOs : ∀ x ∈ os, x.looseBVarsBounded 0 = true)
    {p : Expr} (hpw : p.hasFvar = false)
    (hpb : p.looseBVarsBounded rP = true)
    {vpa : AVExpr}
    (hvpden : denoteP acval env φ rP (openRev 0 rP p) = some vpa)
    -- the recursor's own tower, and the ambient context the
    -- certificate's conversion is guarded by
    {TVa RP : AVExpr} {ΓP : List AVExpr}
    (htowerP : PiTeleP rP TVa ΓP RP)
    -- the certificate, in claims-layer form, on the INSTANTIATED pin
    (hcert : ∀ w0 : AVExpr,
      denoteP acval env φ (rP + cnF)
        (Expr.instSpine os (rP - 1) p) = some w0 →
      ∀ σ : Nat → V,
        Sat2 V (List.replicate cnF (.sort 0) ++ ΓP) σ →
        AnnotOkP V σ w0)
    -- the repaired conjunct's own hypotheses
    {ρ : Nat → V} {zs : List AVExpr} {restR : AVExpr}
    (hzslen : zs.length = rP)
    (hzsOk : ∀ z ∈ zs, AnnotOkP V ρ z)
    (hfit : TeleFitPA V ρ TVa zs restR) :
    AnnotOkP V ρ (Setlec.SetR.AVExpr.instRevChain zs vpa) := by
  obtain ⟨w0, hw0, hcross⟩ := pinCrossP (acval := acval) (cval := cval)
    (env := env) (φ := φ) (cnF := cnF) hacl hainst hlink hcl padA hoslen
    hshape hwsOs hbOs hpw hpb hvpden hzslen (vals := zs) (n := rP)
    hzslen (Nat.le_refl _) (by omega)
    (List.take_of_length_le (Nat.le_of_eq hzslen))
  rw [show rP + cnF - rP = cnF from by omega] at hcross
  rw [← hcross]
  have hZlen : (zs ++ List.replicate cnF padA).length
      = rP + cnF := by
    simp only [List.length_append, List.length_replicate, hzslen]
  rw [show rP + cnF - 1
      = (zs ++ List.replicate cnF padA).length - 1 from by
    rw [hZlen]]
  refine annotOkP_instSeq _ ?_ ?_
  · intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hzsOk x hx'
    · obtain rfl := List.eq_of_mem_replicate hx'
      exact annotOkP_padA ρ
  · exact hcert w0 hw0 _
      (sat2_padded_chainP (cnF := cnF) htowerP hzslen hfit)

end Setlec.SetR.Interp2
