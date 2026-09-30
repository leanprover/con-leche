module

public import ConLeche.Kernel.ExprOps

public section

/-!
# A nested rule's syntactic reading, inverted

`Expr.nestedRuleSyn` reads a recursor rule's level and parameter
instantiations off the recursor type's major-premise domain.  Its
guards are `EnvWF`'s `.nested` clause verbatim; `nestedRuleSyn_inv`
turns a successful reading into that clause; the recursor check reads
it at an outside major (`tgtStoredRules`, `auxRuleFireR`).
-/

namespace ConLeche

/-- **The syntactic reading, inverted** into the facts `EnvWF` records
for a stored `.nested` rule: the prefix-major offset, the syntactic
well-formedness of the stored instantiations (lowered into the
rule-prefix context), and the recursor-type pin the instantiations
were read off — the major domain applies the family to the
instantiations' liftings past the index binders followed by the index
variables in order. -/
theorem nestedRuleSyn_inv {resolves : Expr → Bool} {lps : List Name} {tyA : Expr}
    {mI rP cnP : Nat} {lvls : List Level} {pins : List Expr}
    (h : Expr.nestedRuleSyn resolves lps tyA mI rP cnP = some (lvls, pins)) :
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined lps = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined lps = true ∧
      resolves pin = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre dom body bm D,
      tyA.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map
            (fun i => Expr.bvar (mI - rP - 1 - i)) ∧
      pins.length = cnP := by
  simp only [Expr.nestedRuleSyn] at h
  split at h
  case isFalse => exact nomatch h
  rename_i hcond1
  revert h
  match hstrip : tyA.stripPis mI with
  | none => intro h; exact nomatch h
  | some (pre, .bvar _) => intro h; exact nomatch h
  | some (pre, .fvar _ _) => intro h; exact nomatch h
  | some (pre, .sort _) => intro h; exact nomatch h
  | some (pre, .const _ _) => intro h; exact nomatch h
  | some (pre, .app _ _) => intro h; exact nomatch h
  | some (pre, .lam _ _ _) => intro h; exact nomatch h
  | some (pre, .letE _ _ _) => intro h; exact nomatch h
  | some (pre, .lit _) => intro h; exact nomatch h
  | some (pre, .proj _ _ _) => intro h; exact nomatch h
  | some (pre, .forallE dom body bm) => ?_
  intro h
  try dsimp only at h
  revert h
  match hfn : dom.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const D lvls' => ?_
  intro h
  try dsimp only at h
  split at h
  case isFalse => exact nomatch h
  rename_i hcond2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hlen, htake, hdrop, hpinsAll, hlvlsAll⟩ := hcond2
  have hplen : ((dom.getAppArgs.take cnP).map
      (Expr.lowerBVars (mI - rP) 0)).length = cnP := by
    rw [List.length_map, List.length_take, hlen]
    omega
  refine ⟨hcond1, ?_, ?_, pre, dom, body, bm, D, rfl, hfn,
    ?_, hplen⟩
  · intro l hl
    exact List.all_eq_true.mp hlvlsAll l hl
  · intro p hp
    have hall := List.all_eq_true.mp hpinsAll p hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hall
    exact ⟨hall.1.1.1, hall.2, hall.1.2, hall.1.1.2⟩
  · conv => lhs; rw [← List.take_append_drop cnP dom.getAppArgs]
    congr 1
    · exact eq_of_beq htake
    · exact eq_of_beq hdrop

end ConLeche
