module

public import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualWF

public section

/-!
# The restored recursors' store: environment well-formedness (task #315, M7-2)

`mutual_recs_wf`'s twin (`MutualWF.lean`) at the nested route's own two
conses.  The kernel conses the `k + nPins` RESTORED recursors twice:
RULE-LESS (`provisionNestedRecs`, the environment every restored rule
is scoped at) and then, at the SAME names in the SAME order, WITH
their restored rules (`storeNestedRecs`).  So a rule's right-hand side
resolves at the PROVISION and not at the prefix its own cons sits on —
which is no obstacle, because `EnvWF` asks `ConstWF` of every stored
constant *at the whole environment*, and the two conses find exactly
the same names (`provisionNestedRecs_store_le`).

Where the mutual pair takes the block and COMPUTES each entry's
arities and rules, the nested pair takes the entries as data: the
provision a list of triples, the store the same list of triples with
each entry's rules appended.  So the statement here is generic in one
quadruple list `l`, its projection `nestedProvOf l` being the
provision's, and the per-entry syntactic facts are the caller's —
`restoreRecTys_at` for a type, `restoreRules_at` for a rule
(`NestedRecDoor.lean`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The two conses, compared -/

/-- The provision list a store list projects to: the same entries
without their rules. -/
@[expose] def nestedProvOf (l : List (ConstantVal × Nat × Nat × List RecRule)) :
    List (ConstantVal × Nat × Nat) :=
  l.map fun x => (x.1, x.2.1, x.2.2.1)

/-- The store finds everything the environment it is built on finds. -/
theorem storeNestedRecs_le :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} (n : Name),
      (env.find? n).isSome = true → ((storeNestedRecs l env).find? n).isSome = true
  | [], _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, n, h => by
    simp only [storeNestedRecs]
    exact storeNestedRecs_le n (find?_isSome_cons h)

/-- **The provision and the store cons the same names**: the
rule-less recursors and the recursors with their rules are consed in
the same order onto lookup-comparable environments, so a rule scoped
at the provision resolves at the store. -/
theorem provisionNestedRecs_store_le :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env env' : Env},
      (∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) →
      ∀ n, ((provisionNestedRecs (nestedProvOf l) env).find? n).isSome = true →
        ((storeNestedRecs l env').find? n).isSome = true
  | [], _, _, hf, n, h => hf n h
  | (cvRa, mI, rP, rules) :: rest, env, env', hf, n, h => by
    simp only [nestedProvOf, List.map_cons, provisionNestedRecs] at h
    simp only [storeNestedRecs]
    refine provisionNestedRecs_store_le (l := rest)
      (env := ⟨.recInfo cvRa mI rP [] :: env.consts⟩)
      (env' := ⟨.recInfo cvRa mI rP rules :: env'.consts⟩) ?_ n h
    exact find?_isSome_cons_mono rfl hf

/-- The store's constants: the environment's own, or one of the stored
recursors. -/
theorem storeNestedRecs_mem :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {c : ConstantInfo},
      c ∈ (storeNestedRecs l env).consts →
      c ∈ env.consts ∨ ∃ x ∈ l, c = .recInfo x.1 x.2.1 x.2.2.1 x.2.2.2
  | [], _, _, h => Or.inl h
  | (cvRa, mI, rP, rules) :: rest, env, c, h => by
    simp only [storeNestedRecs] at h
    rcases storeNestedRecs_mem h with hm | ⟨x, hx, rfl⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact Or.inr ⟨(cvRa, mI, rP, rules), List.mem_cons_self, rfl⟩
      · exact Or.inl hm'
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, rfl⟩

/-! ## The stage -/

/-- **The restored recursors stored as a group keep the environment
well-formed** (`mutual_recs_wf`'s twin): a stored entry's TYPE carries
the four syntactic facts at the environment the store is built on, and
each of its RULES carries them at the PROVISION — which is the
environment `restoreRules` ran at — together with the `.nested` fire's
own shape.  Resolution crosses both ways by the two `_le` lemmas, so
the walk over the final environment is one `envWF_of_le`. -/
theorem nested_recs_wf {env : Env} (henv : EnvWF env)
    {l : List (ConstantVal × Nat × Nat × List RecRule)}
    (htys : ∀ x ∈ l, x.1.type.hasFvar = false ∧
      x.1.type.allLevelParamsDefined x.1.levelParams = true ∧
      x.1.type.constsResolve env = true ∧ x.1.type.looseBVarsBounded 0 = true)
    (hrules : ∀ x ∈ l, ∀ r ∈ x.2.2.2,
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined x.1.levelParams = true ∧
      (RecRule.rhs r).constsResolve (provisionNestedRecs (nestedProvOf l) env) = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        x.2.2.1 ≤ x.2.1 ∧
        (∀ u ∈ lvls, u.allParamsDefined x.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined x.1.levelParams = true ∧
          pin.constsResolve (provisionNestedRecs (nestedProvOf l) env) = true ∧
          pin.looseBVarsBounded x.2.2.1 = true) ∧
        ∃ pre dom body bm D,
          x.1.type.stripPis x.2.1 = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars (x.2.1 - x.2.2.1) 0) ++
              (List.range (x.2.1 - x.2.2.1)).map
                (fun i => Expr.bvar (x.2.1 - x.2.2.1 - 1 - i))) :
    EnvWF (storeNestedRecs l env) := by
  have hprov : ∀ n, ((provisionNestedRecs (nestedProvOf l) env).find? n).isSome = true →
      ((storeNestedRecs l env).find? n).isSome = true :=
    provisionNestedRecs_store_le (fun _ h => h)
  refine envWF_of_le henv (fun n => storeNestedRecs_le n) ?_
  intro c hc
  rcases storeNestedRecs_mem hc with hm | ⟨x, hx, rfl⟩
  · exact Or.inl hm
  right
  obtain ⟨hfv, hlp, hres, hbv⟩ := htys x hx
  refine structConstWF hfv hlp
    (Expr.constsResolve_le (fun n => storeNestedRecs_le n) hres) hbv
    (fun _ _ _ heq => nomatch heq) ?_
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e2
  subst e3
  subst e4
  obtain ⟨hrfv, hrlp, hrres, hrbv, hrn⟩ := hrules x hx r hr
  refine ⟨hrfv, hrlp, Expr.constsResolve_le hprov hrres, hrbv, ?_⟩
  intro lvls pins hf
  obtain ⟨hle, hlvls, hpins, hshape⟩ := hrn lvls pins hf
  exact ⟨hle, hlvls, fun pin hpin => by
      obtain ⟨p1, p2, p3, p4⟩ := hpins pin hpin
      exact ⟨p1, p2, Expr.constsResolve_le hprov p3, p4⟩,
    hshape⟩

end ConLeche
