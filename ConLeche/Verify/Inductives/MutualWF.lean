module

public import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.FixRec
import ConLeche.Verify.Inductives.StructRec

public section

/-!
# The mutual install: environment well-formedness (task #278)

`EnvWF` for the environments `checkMutual` walks through, read off the
stages' own guards as `SumWF.lean`/`FixWF.lean` read the fixpoint
route's: the formers' conses (each a checked constant with the block's
capability record `{}`), the constructors' conses
(`consMutualCtors`), the `k` recursors stored as a group with their
rules, and the structure-like members' projection tables.

The recursors' stage is the one novelty.  A mutual rule mentions the
SIBLING recursors, so its right-hand side is scoped at the environment
holding all `k` rule-less provisions (`provisionMutualRecs`) and not
at the prefix its own cons sits on — which is no obstacle, because
`EnvWF` asks `ConstWF` of every stored constant *at the whole
environment*: the provision and the store cons the same `k` names in
the same order onto the same environment, so they find exactly the
same names (`provisionMutualRecs_store_le`) and resolution carries
over.  The walk over the final environment is therefore one
`envWF_of_le` and not a chain of `EnvWF.cons`.
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The generated recursor type's syntactic telescope (moved from
`NestedRecDoor` so that this module's own recursor cons can read it) -/

/-- The motives' telescope's two steps, by `rfl`.  NOT `simp only
[mutualMotivesPis]`: unfolding through the equation lemmas realizes
`mutualMotivesPis.match_1.splitter` HERE, and this module sits below
every capstone in the import order, so the splitter's attribution moves
into it and the proof-term gate reads a door. -/
private theorem doorMotivesPis_nil {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {i : Nat} {body : Expr} : mutualMotivesPis lps nP ℓ pw [] i body = some body := rfl

private theorem doorMotivesPis_cons {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen}
    {f : MutualFormer} {fs : List MutualFormer} {i : Nat} {body : Expr} :
    mutualMotivesPis lps nP ℓ pw (f :: fs) i body
      = (mutualMotiveTy lps nP ℓ i f).bind fun mty =>
          (mutualMotivesPis lps nP ℓ pw fs (i + 1) body).map fun rest =>
            Expr.forallE mty rest ⟨pw⟩ := rfl

/-- The minors' telescope's two steps, by `rfl` (same reason). -/
private theorem doorMinorsPis_nil {lps : List Name} {nP : Nat} {pw : PropWhen} {o : Nat}
    {body : Expr} : mutualMinorsPis lps nP pw [] o body = some body := rfl

private theorem doorMinorsPis_cons {lps : List Name} {nP : Nat} {pw : PropWhen}
    {c : MutualCtor4} {cs : List MutualCtor4} {o : Nat} {body : Expr} :
    mutualMinorsPis lps nP pw (c :: cs) o body
      = (mutualMinorTy lps nP o pw c).bind fun mty =>
          (mutualMinorsPis lps nP pw cs (o + 1) body).map fun rest =>
            Expr.forallE mty rest ⟨pw⟩ := rfl

/-- The motives' telescope: one `∀` per former, meta `⟨pw⟩`, the body
under them. -/
theorem mutualMotivesPis_stripPis {lps : List Name} {nP : Nat} {ℓ : Level} {pw : PropWhen} :
    ∀ (fs : List MutualFormer) {i : Nat} {body mots : Expr},
      mutualMotivesPis lps nP ℓ pw fs i body = some mots →
      ∃ bs : List (Expr × BinderMeta), mots.stripPis fs.length = some (bs, body) ∧
        ∀ x ∈ bs, x.2 = (⟨pw⟩ : BinderMeta) := by
  intro fs
  induction fs with
  | nil =>
    intro i body mots h
    rw [doorMotivesPis_nil, Option.some.injEq] at h
    exact ⟨[], by rw [← h]; rfl, by simp⟩
  | cons f fs ih =>
    intro i body mots h
    rw [doorMotivesPis_cons] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, rest, hrest, rfl⟩ := h
    obtain ⟨bs, hbs, hmeta⟩ := ih hrest
    refine ⟨(mty, ⟨pw⟩) :: bs, ?_, ?_⟩
    · simp only [List.length_cons, Expr.stripPis, hbs, Option.map_some]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hmeta x hx

/-- The minors' telescope: one `∀` per constructor, meta `⟨pw⟩`, the
body under them. -/
theorem mutualMinorsPis_stripPis {lps : List Name} {nP : Nat} {pw : PropWhen} :
    ∀ (cs : List MutualCtor4) {o : Nat} {body mins : Expr},
      mutualMinorsPis lps nP pw cs o body = some mins →
      ∃ bs : List (Expr × BinderMeta), mins.stripPis cs.length = some (bs, body) ∧
        ∀ x ∈ bs, x.2 = (⟨pw⟩ : BinderMeta) := by
  intro cs
  induction cs with
  | nil =>
    intro o body mins h
    rw [doorMinorsPis_nil, Option.some.injEq] at h
    exact ⟨[], by rw [← h]; rfl, by simp⟩
  | cons c cs ih =>
    intro o body mins h
    rw [doorMinorsPis_cons] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨mty, -, rest, hrest, rfl⟩ := h
    obtain ⟨bs, hbs, hmeta⟩ := ih hrest
    refine ⟨(mty, ⟨pw⟩) :: bs, ?_, ?_⟩
    · simp only [List.length_cons, Expr.stripPis, hbs, Option.map_some]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact hmeta x hx

/-- A spine mentions a constant only through its head or an argument
(the Verify copy of the Model tier's `mentionsConst_mkAppN_false`). -/
private theorem doorMentionsConst_mkAppN_false {n : Name} :
    ∀ (as : List Expr) (f : Expr), f.mentionsConst n = false →
      (∀ a ∈ as, a.mentionsConst n = false) → (Expr.mkAppN f as).mentionsConst n = false
  | [], _, hf, _ => hf
  | a :: as, f, hf, has =>
    doorMentionsConst_mkAppN_false as (.app f a)
      (by simp only [Expr.mentionsConst, hf, has a List.mem_cons_self, Bool.or_self])
      (fun x hx => has x (List.mem_cons_of_mem _ hx))

/-- **THE MAJOR PREMISE'S DOMAIN IS AN APPLICATION OF A CONSTANT**
(task #315, the crossing's premise): the generated recursor type of
member `mm`, stripped at its MAJOR INDEX — one binder short of
`mutualRecTy_stripPis`' strip — exposes the major premise itself, and
its domain is the member's own family application, whose head is a
`const`.

This is the unconditional form: no rule, no fire, no `.nested` guard —
the shape holds of the type the route GENERATES, and the stream's
record is only required to be defeq to it, so what is STORED is this
term.  `structFamI` is the family at the parameter and index openers,
so the head is `.const f.name (lps.map .param)` by construction. -/
theorem mutualRecTy_majorDom {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f : MutualFormer) (bs : List (Expr × BinderMeta)) (dom body : Expr) (bm : BinderMeta),
      formers[mm]? = some f ∧
      recTy.stripPis (nP + formers.length + ctors.length + f.nIdx)
        = some (bs, .forallE dom body bm) ∧
      dom.getAppFn = .const f.name (lps.map .param) := by
  unfold mutualRecTy at h
  split at h
  · next f f₀ hf _hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis f.nIdx hmaj
    have h2 := replacePisPw_stripPis f.nIdx hmaj hbs1
    obtain ⟨bs2, hbs2, -⟩ := mutualMinorsPis_stripPis ctors hmin
    have h5 := stripPis_append ctors.length hbs2 h2
    obtain ⟨bs3, hbs3, -⟩ := mutualMotivesPis_stripPis formers hmot
    have h6 := stripPis_append formers.length hbs3 h5
    obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
    have h7 := replacePisPw_stripPis nP hr hbs0
    have h8 := stripPis_append nP h7 h6
    rw [show nP + (formers.length + (ctors.length + f.nIdx))
      = nP + formers.length + ctors.length + f.nIdx from by omega] at h8
    refine ⟨f, _, _, _, _, hf, h8, ?_⟩
    rw [structFamI, Expr.getAppFn_mkAppN]
    rfl
  · exact nomatch h

/-- **The generated recursor type of member `mm` is a syntactic
`∀`-telescope** of `nP + k + n + nIdx_m + 1` binders, every binder meta
the elimination datum, whose residual is the conclusion `motive_m ı⃗ t`
— an application of bound variables, mentioning no constant. -/
theorem mutualRecTy_stripPis {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f : MutualFormer) (cbs : List (Expr × BinderMeta)),
      formers[mm]? = some f ∧
      recTy.stripPis (nP + formers.length + ctors.length + f.nIdx + 1)
        = some (cbs, Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
            (structPsAt 1 f.nIdx ++ [.bvar 0])) ∧
      (∀ x ∈ cbs, x.2 = (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)) ∧
      ∀ n : Name, (Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
        (structPsAt 1 f.nIdx ++ [.bvar 0])).mentionsConst n = false := by
  unfold mutualRecTy at h
  split at h
  · next f f₀ hf _hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    -- the index telescope and the major, under the `f.nIdx + 1` binders
    obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis f.nIdx hmaj
    have h2 := replacePisPw_stripPis f.nIdx hmaj hbs1
    have h4 := stripPis_append f.nIdx h2 (m := 1) rfl
    -- the minors, then the motives
    obtain ⟨bs2, hbs2, hm2⟩ := mutualMinorsPis_stripPis ctors hmin
    have h5 := stripPis_append ctors.length hbs2 h4
    obtain ⟨bs3, hbs3, hm3⟩ := mutualMotivesPis_stripPis formers hmot
    have h6 := stripPis_append formers.length hbs3 h5
    -- the parameters
    obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
    have h7 := replacePisPw_stripPis nP hr hbs0
    have h8 := stripPis_append nP h7 h6
    rw [show nP + (formers.length + (ctors.length + (f.nIdx + 1)))
      = nP + formers.length + ctors.length + f.nIdx + 1 from by omega] at h8
    refine ⟨f, _, hf, h8, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; rfl
      rcases List.mem_append.mp hx with hx | hx
      · exact hm3 x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hm2 x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; rfl
      · rw [List.mem_singleton.mp hx]
    · intro n
      refine doorMentionsConst_mkAppN_false _ _ rfl ?_
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; rfl
      · rw [List.mem_singleton.mp ha]; rfl
  · exact nomatch h

/-- **THE GENERATED RECURSOR TYPE'S MAJOR BINDER, SYNTACTICALLY**
(task #315 M7-2): `mutualRecTy_stripPis` with the LAST binder named.

Relocated here at integration 3s: it consumes the telescope kit that
M8 session 6 moved out of `NestedRecDoor.lean` into this file, so it
follows the kit.  Its consumer, `Model/Inductives/NestedRecRule.lean`,
already reaches this module, so the move adds no import edge.
The telescope's binder `nP + k + n + nIdx_m` — the one the major
premise occupies — carries the domain `structFamI`, member `m`'s own
former applied to the block's parameters and the index binders, and
the elimination datum like every other.  The mimic recursors' fire
shape reads THIS binder through the restore, which is why it has to be
named. -/
theorem mutualRecTy_major {lps : List Name} {elim : Name} {large : Bool} {nP mm : Nat}
    {formers : List MutualFormer} {ctors : List MutualCtor4} {recTy : Expr}
    (h : mutualRecTy lps elim large nP formers ctors mm = some recTy) :
    ∃ (f : MutualFormer) (cbs₀ : List (Expr × BinderMeta)) (conc : Expr),
      formers[mm]? = some f ∧
      recTy.stripPis (nP + formers.length + ctors.length + f.nIdx + 1)
        = some (cbs₀ ++ [(structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0,
            (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))], conc) ∧
      cbs₀.length = nP + formers.length + ctors.length + f.nIdx := by
  unfold mutualRecTy at h
  split at h
  · next f f₀ hf _hf₀ =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨q, hq, major, hmaj, minors, hmin, motives, hmot, hr⟩ := h
    obtain ⟨bs1, body1, hbs1⟩ := replacePisPw_some_stripPis f.nIdx hmaj
    have h2 := replacePisPw_stripPis f.nIdx hmaj hbs1
    have h4 := stripPis_append f.nIdx h2 (m := 1) rfl
    obtain ⟨bs2, hbs2, -⟩ := mutualMinorsPis_stripPis ctors hmin
    have h5 := stripPis_append ctors.length hbs2 h4
    obtain ⟨bs3, hbs3, -⟩ := mutualMotivesPis_stripPis formers hmot
    have h6 := stripPis_append formers.length hbs3 h5
    obtain ⟨bs0, body0, hbs0⟩ := replacePisPw_some_stripPis nP hr
    have h7 := replacePisPw_stripPis nP hr hbs0
    have h8 := stripPis_append nP h7 h6
    rw [show nP + (formers.length + (ctors.length + (f.nIdx + 1)))
      = nP + formers.length + ctors.length + f.nIdx + 1 from by omega] at h8
    refine ⟨f, (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
        BinderMeta))) ++ (bs3 ++ (bs2 ++ (bs1.map fun x => (x.1,
          (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))))),
      Expr.mkAppN (.bvar (f.nIdx + ctors.length + formers.length - mm))
        (structPsAt 1 f.nIdx ++ [.bvar 0]), hf, ?_, ?_⟩
    · rw [show (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
          BinderMeta))) ++ (bs3 ++ (bs2 ++ (bs1.map fun x => (x.1,
            (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)))))
          ++ [(structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0,
            (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))]
        = (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
            BinderMeta))) ++ (bs3 ++ (bs2 ++ ((bs1.map fun x => (x.1,
              (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta)))
            ++ [(structFamI f.name lps nP f.nIdx (formers.length + ctors.length) 0,
              (⟨Level.zeronessOf (structElimLevel elim large)⟩ : BinderMeta))]))) from by
          simp only [List.append_assoc]]
      exact h8
    · have e0 : (bs0.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
          BinderMeta))).length = nP := by
        rw [List.length_map]
        exact Expr.stripPis_length _ hbs0
      have e1 : (bs1.map fun x => (x.1, (⟨Level.zeronessOf (structElimLevel elim large)⟩ :
          BinderMeta))).length = f.nIdx := by
        rw [List.length_map]
        exact Expr.stripPis_length _ hbs1
      have e2 : bs2.length = ctors.length := Expr.stripPis_length _ hbs2
      have e3 : bs3.length = formers.length := Expr.stripPis_length _ hbs3
      simp only [List.length_append, e0, e1, e2, e3]
      omega
  · exact nomatch h

/-! ## Monotone extension -/

/-- One constant's well-formedness is monotone under lookup-preserving
extension (`EnvWF.cons`'s tail half, at an arbitrary extension). -/
theorem ConstWF.le {envA envB : Env} {c : ConstantInfo}
    (hf : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true)
    (hc : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, hmaj, h6, h8, h9⟩ := hc
  refine ⟨h1, h2, Expr.constsResolve_le hf h3, h4, fun cv value hint heq =>
    let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
    ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩, hmaj, ?_,
    fun tbl heq =>
      let ⟨g0, g⟩ := h8 tbl heq
      ⟨g0, fun i bd hb =>
        let ⟨g1, g2, g3, g4⟩ := g i bd hb
        ⟨g1, g2, Expr.constsResolve_le hf g3, g4⟩⟩, h9⟩
  intro cv mI rP rules heq r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
  refine ⟨g1, g2, Expr.constsResolve_le hf g3, g4, ?_⟩
  intro lvls pins hfr
  obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
  exact ⟨n1, n2, fun pin hpin =>
    let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
    ⟨p1, p2, Expr.constsResolve_le hf p3, p4⟩, n4⟩

/-- **Well-formedness of a whole extension**: every constant of the
extended environment is either one of the old ones (carried over by
monotonicity) or well-formed at the extended environment itself.  The
mutual recursors' group store needs this shape: a rule mentions the
sibling recursors, so the group is well-formed together and not one
cons at a time. -/
theorem envWF_of_le {env envOut : Env} (henv : EnvWF env)
    (hle : ∀ n, (env.find? n).isSome = true → (envOut.find? n).isSome = true)
    (hsplit : ∀ c ∈ envOut.consts, c ∈ env.consts ∨ ConstWF envOut c) :
    EnvWF envOut := by
  intro c hc
  rcases hsplit c hc with hm | hw
  · exact ConstWF.le hle (henv c hm)
  · exact hw

/-- A cons finds everything its base finds. -/
theorem find?_isSome_cons {c : ConstantInfo} {env : Env} {n : Name}
    (h : (env.find? n).isSome = true) :
    (Env.find? ⟨c :: env.consts⟩ n).isSome = true := by
  rw [Env.find?_cons]
  split
  · rfl
  · exact h

/-- Two conses of the same name over lookup-comparable environments
stay lookup-comparable. -/
theorem find?_isSome_cons_mono {c c' : ConstantInfo} {env env' : Env}
    (hn : c.name = c'.name)
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ n, (Env.find? ⟨c :: env.consts⟩ n).isSome = true →
      (Env.find? ⟨c' :: env'.consts⟩ n).isSome = true := by
  intro n h
  rw [Env.find?_cons] at h
  rw [Env.find?_cons, ← hn]
  split
  · rfl
  · next hne =>
    rw [if_neg hne] at h
    exact hf n h

/-! ## Stage 1: the formers -/

/-- **The formers' fold is length-preserving** (task #315): needed
because the stored recursor's major index is
`b.rulePrefix + (fms.getD m default).nIdx` while `mutualRecTy` is called
at `formers4 = fms.map …`. -/
theorem mutualFormerChecks_length {nP F : Nat} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {fms : List MutualFormerA},
      mutualFormerChecks (fueledOps mode F) env nP false l = .ok fms →
      fms.length = l.length
  | [], _, _, h => by
    obtain rfl := mutualFormerChecks_nil_inv h
    rfl
  | (cv, nIdx) :: rest, env, fms, h => by
    obtain ⟨cvTa₀, cvTa, s, bs, fs, -, -, -, hrest, rfl⟩ := mutualFormerChecks_inv h
    simp only [List.length_cons]
    exact congrArg (· + 1) (mutualFormerChecks_length hrest)

/-- The type-slot `ConstWF` facts of every checked former, AT THE
PRE-BLOCK ENVIRONMENT (where the whole stage runs). -/
theorem mutualFormerChecks_typeWF {nP F : Nat} {l : List (ConstantVal × Nat)} {env : Env}
    {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP false l = .ok fms) :
    ∀ f ∈ fms, f.cvTa.type.hasFvar = false ∧
      f.cvTa.type.allLevelParamsDefined f.cvTa.levelParams = true ∧
      f.cvTa.type.constsResolve env = true ∧
      f.cvTa.type.looseBVarsBounded 0 = true := by
  intro f hf
  obtain ⟨cv', hccv'⟩ := mutualFormerChecks_checked h f hf
  exact checkConstantVal_typeWF hccv'

/-- The formers' conses keep well-formedness: every member's type
resolves at the pre-block environment, and resolution is monotone
along the conses (the members' names need not be compared — `EnvWF` is
about the constants' own data). -/
theorem envWF_consMutualFormers :
    ∀ {fms : List MutualFormerA} {env : Env},
      EnvWF env →
      (∀ f ∈ fms, f.cvTa.type.hasFvar = false ∧
        f.cvTa.type.allLevelParamsDefined f.cvTa.levelParams = true ∧
        f.cvTa.type.constsResolve env = true ∧
        f.cvTa.type.looseBVarsBounded 0 = true) →
      EnvWF (consMutualFormers fms env)
  | [], _, henv, _ => henv
  | f :: fs, env, henv, hall => by
    simp only [consMutualFormers]
    obtain ⟨htf, htp, htr, htb⟩ := hall f List.mem_cons_self
    refine envWF_consMutualFormers ?_ ?_
    · exact EnvWF.cons henv (structConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
        (by intro tbl hh; exact ConstantInfo.noConfusion hh)
        (IndCapsWF.of_caps (fun hu => absurd hu (by decide))
          (fun he => absurd he (by decide))))
    · intro f' hf'
      obtain ⟨h1, h2, h3, h4⟩ := hall f' (List.mem_cons_of_mem _ hf')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- The formers' stage keeps the environment well-formed: every member
is a checked constant, consed with the block's (empty) capability
record. -/
theorem envWF_mutualFormers {nP F : Nat} {l : List (ConstantVal × Nat)}
    {env env' : Env} {fms : List MutualFormerA}
    (henv : EnvWF env)
    (h : mutualFormers (fueledOps mode F) nP l env = .ok (env', fms)) :
    EnvWF env' := by
  obtain ⟨hchecks, rfl⟩ := mutualFormers_inv h
  exact envWF_consMutualFormers henv (mutualFormerChecks_typeWF hchecks)

/-! ## Stage 3: the constructors -/

/-- A name fresh above the constructors' conses is fresh below them. -/
theorem consMutualCtors_find?_none {nP : Nat} {n : Name} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (consMutualCtors nP ctorsA env).find? n = none → env.find? n = none
  | [], _, h => h
  | c :: cs, env, h => by
    simp only [consMutualCtors] at h
    have h' := consMutualCtors_find?_none h
    rw [Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The constructors' conses keep well-formedness: every consed
constructor's type resolves at the environment it is consed onto
(resolution is monotone along the conses). -/
theorem envWF_consMutualCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      EnvWF env →
      (∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      EnvWF (consMutualCtors nP ctorsA env)
  | [], _, henv, _ => henv
  | c :: cs, env, henv, hall => by
    simp only [consMutualCtors]
    obtain ⟨htf, htp, htr, htb⟩ := hall c List.mem_cons_self
    refine envWF_consMutualCtors ?_ ?_
    · exact EnvWF.cons henv (structConstWF htf htp (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq))
    · intro c' hc'
      obtain ⟨h1, h2, h3, h4⟩ := hall c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Expr.constsResolve_mono h3, h4⟩

/-- A constructor's run at the formers' environment: its type is
closed, level-defined, resolving and bounded. -/
theorem mutual_ctor_typeWF {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok (cvCa, sorts)) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨_, hccv⟩, -, -⟩ := checkMutualCtor_shape h
  exact checkConstantVal_typeWF hccv

/-- Every annotated constructor of the block carries the four type-slot
facts at the formers' environment. -/
theorem checkMutualCtors_typeWF {env : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {isProp : Bool} {F : Nat} {cs : List MutualCtor} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)}
    (h : checkMutualCtors (fueledOps mode F) env b fms isProp false cs = .ok (ctorsA, sortss)) :
    ∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true := by
  obtain ⟨hlen, -, hall⟩ := checkMutualCtors_inv h
  intro c hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hj' : j < cs.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  obtain ⟨-, _, -, hrun⟩ := hall j cs[j] c (List.getElem?_eq_getElem hj') hj
  exact mutual_ctor_typeWF hrun

/-! ## Stage 4: the recursors -/

/-- The stored rules carry the generated right-hand sides and are
never `.nested` (`sumRules_mem` at a mutual block). -/
theorem mutualRules_mem {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ mutualRules find? recName nP mI rP recTy l →
      (∃ cr ∈ l, r.rhs = cr.2) ∧ ∀ lvls pins, r.fire ≠ .nested lvls pins
  | [], r, h => by simp [mutualRules] at h
  | cr :: cs, r, h => by
    simp only [mutualRules, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨⟨cr, List.mem_cons_self, rfl⟩, fun lvls pins => ?_⟩
      show (if Expr.recRulePlain recTy mI rP nP then RecRuleFire.plain else .inert) ≠ _
      split <;> simp
    · obtain ⟨⟨cr', hm, he⟩, hf⟩ := mutualRules_mem h
      exact ⟨⟨cr', List.mem_cons_of_mem _ hm, he⟩, hf⟩

/-- Every stored rule of a mutual recursor carries the two rescue bits
its own install-time lookup computes. -/
theorem mutualRules_bits {find? : Name → Option ConstantInfo} {recName : Name}
    {nP mI rP : Nat} {recTy : Expr} :
    ∀ {l : List (MutualCtor × Expr)} {r : RecRule},
      r ∈ mutualRules find? recName nP mI rP recTy l →
      r.k = recRuleKOf find? r.ctor ∧ r.eta = recRuleEtaOf find? recName r.ctor
  | [], r, h => by simp [mutualRules] at h
  | _ :: cs, r, h => by
    simp only [mutualRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, rfl⟩
    · exact mutualRules_bits h

/-- One member's generated rules, by membership. -/
theorem checkMutualMemberRules_mem {envR : Env} {b : MutualBlock}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {mIdx : Nat}
    {streamRec : Option (ConstantVal × List RecRule)} {rules : List (MutualCtor × Expr)}
    (h : checkMutualMemberRules (m := CheckM) envR b formers4 ctors4 mIdx streamRec
      = .ok rules)
    {cr : MutualCtor × Expr} (hm : cr ∈ rules) :
    cr.2.hasFvar = false ∧ cr.2.allLevelParamsDefined b.rlps = true ∧
    cr.2.constsResolve envR = true ∧ cr.2.looseBVarsBounded 0 = true := by
  obtain ⟨-, hlen, hall⟩ := checkMutualMemberRules_inv h
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  have hi' : i < (b.ownCtors mIdx).length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨J, c, rhs, -, hget, -, hlp, hres, hbv, hfv⟩ := hall i hi'
  obtain rfl := Option.some.inj (hi.symm.trans hget)
  exact ⟨hfv, hlp, hres, hbv⟩

/-- The store finds everything the environment it is built on finds. -/
theorem storeMutualRecs_le {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((storeMutualRecs env₂ b fms rulesOf l env).find? n).isSome = true
  | [], _, _, h => h
  | (cvRa, mIdx) :: rest, env, n, h => by
    simp only [storeMutualRecs]
    exact storeMutualRecs_le n (find?_isSome_cons h)

/-- **The provision and the store cons the same names**: the `k`
rule-less recursors and the `k` recursors with their rules are consed
in the same order onto lookup-comparable environments, so a rule
scoped at the provision resolves at the store. -/
theorem provisionMutualRecs_store_le {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env env' : Env},
      (∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true) →
      ∀ n, ((provisionMutualRecs b fms l env).find? n).isSome = true →
        ((storeMutualRecs env₂ b fms rulesOf l env').find? n).isSome = true
  | [], _, _, hf, n, h => hf n h
  | (cvRa, mIdx) :: rest, env, env', hf, n, h => by
    simp only [provisionMutualRecs] at h
    simp only [storeMutualRecs]
    refine provisionMutualRecs_store_le (l := rest)
      (env := ⟨.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []
        :: env.consts⟩)
      (env' := ⟨.recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
        (mutualRules env₂.find? cvRa.name b.nP
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
          (rulesOf.getD mIdx [])) :: env'.consts⟩) ?_ n h
    exact find?_isSome_cons_mono rfl hf

/-- The store's constants: the environment's own, or one of the `k`
recursors. -/
theorem storeMutualRecs_mem {env₂ : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {rulesOf : List (List (MutualCtor × Expr))} :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {c : ConstantInfo},
      c ∈ (storeMutualRecs env₂ b fms rulesOf l env).consts →
      c ∈ env.consts ∨ ∃ cvRa mIdx, (cvRa, mIdx) ∈ l ∧
        c = .recInfo cvRa (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
          (mutualRules env₂.find? cvRa.name b.nP
            (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
            (rulesOf.getD mIdx []))
  | [], _, _, h => Or.inl h
  | (cvRa, mIdx) :: rest, env, c, h => by
    simp only [storeMutualRecs] at h
    rcases storeMutualRecs_mem h with hm | ⟨cvRa', mIdx', hmem, rfl⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact Or.inr ⟨cvRa, mIdx, List.mem_cons_self, rfl⟩
      · exact Or.inl hm'
    · exact Or.inr ⟨cvRa', mIdx', List.mem_cons_of_mem _ hmem, rfl⟩

/-- **The generated recursors' MAJOR-PREMISE HEADS** (task #315): each
member's stored recursor type is `mutualRecTy`'s output, and that
generator puts the member's own family application in the major
premise's domain — a `const` head.  The three arity facts line the
stored major index `b.rulePrefix + nIdx` up with the generator's
`b.nP + formers.length + ctors.length + f.nIdx`. -/
theorem checkMutualRecTys_majorHead {env₂ : Env} {b : MutualBlock}
    {fms : List MutualFormerA} {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {cvRas : List ConstantVal}
    {F : Nat}
    (hrectys : checkMutualRecTys (fueledOps mode F) env₂ b formers4 ctors4 streamRecs b.k
      = .ok cvRas)
    (hkf : b.k = formers4.length) (hnc : b.n = ctors4.length)
    (hnIdxs : ∀ m f, formers4[m]? = some f → (fms.getD m default).nIdx = f.nIdx) :
    ∀ (t : Nat) (cvRa : ConstantVal), t < b.k → cvRas[t]? = some cvRa →
      Expr.recMajorHeadOk cvRa.type (b.rulePrefix + (fms.getD t default).nIdx) = true := by
  intro t cvRa ht hget
  obtain ⟨-, hallR⟩ := checkMutualRecTys_inv hrectys
  obtain ⟨cvRa', hget', hrec⟩ := hallR t ht
  obtain rfl := Option.some.inj (hget.symm.trans hget')
  obtain ⟨recTy, sty, u, hgenM, -, -, -, -, -, -, -, rfl⟩ := checkMutualRecTy_shape hrec
  obtain ⟨f, bs0, dom0, body0, bm0, hf, hs, hd⟩ := mutualRecTy_majorDom hgenM
  have hmi : b.rulePrefix + (fms.getD t default).nIdx
      = b.nP + formers4.length + ctors4.length + f.nIdx := by
    rw [hnIdxs t f hf, MutualBlock.rulePrefix, hkf, hnc]
  show Expr.recMajorHeadOk recTy (b.rulePrefix + (fms.getD t default).nIdx) = true
  rw [hmi, Expr.recMajorHeadOk, hs]
  simp only [hd]

/-- **Stage 4 at the run level**: the `k` recursors stored as a group
with their rules keep the environment well-formed. -/
theorem mutual_recs_wf {env₂ : Env} (henv₂ : EnvWF env₂) {b : MutualBlock}
    {fms : List MutualFormerA} {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))} {F : Nat}
    (hrectys : checkMutualRecTys (fueledOps mode F) env₂ b formers4 ctors4 streamRecs b.k
      = .ok cvRas)
    (hrules : checkMutualAllRules (m := CheckM)
      (provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 streamRecs b.k
      = .ok rulesOf)
    -- **THE STAGE LISTS' LENGTHS AND THE MEMBERS' INDEX COUNTS** (task
    -- #315): the pass's own facts, needed because the stored recursor's
    -- MAJOR INDEX is `b.rulePrefix + (fms.getD mIdx default).nIdx =
    -- b.nP + b.k + b.n + nIdx` while `mutualRecTy` is called at
    -- `formers4`/`ctors4`
    (hkf : b.k = formers4.length) (hnc : b.n = ctors4.length)
    (hnIdxs : ∀ m f, formers4[m]? = some f →
      (fms.getD m default).nIdx = f.nIdx) :
    EnvWF (storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) := by
  obtain ⟨hlenR, hallR⟩ := checkMutualRecTys_inv hrectys
  obtain ⟨hlenU, hallU⟩ := checkMutualAllRules_inv hrules
  refine envWF_of_le henv₂ (fun n => storeMutualRecs_le n) ?_
  intro c hc
  rcases storeMutualRecs_mem hc with hm | ⟨cvRa, mIdx, hmem, rfl⟩
  · exact Or.inl hm
  right
  -- the member's index and its recursor's own stage
  have hget : cvRas[mIdx]? = some cvRa := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hlt : mIdx < b.k := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    omega
  obtain ⟨cvRa', hget', hrec⟩ := hallR mIdx hlt
  obtain rfl := Option.some.inj (hget.symm.trans hget')
  obtain ⟨recTy, sty, u, -, hlp, hres, hbv, hfv, -, -, -, rfl⟩ :=
    checkMutualRecTy_shape hrec
  -- the member's rules
  obtain ⟨rl, hrlget, hrl⟩ := hallU mIdx hlt
  have hrlD : rulesOf.getD mIdx [] = rl := by
    rw [List.getD_eq_getElem?_getD, hrlget]; rfl
  rw [hrlD]
  -- **THE MAJOR PREMISE'S HEAD** (task #315): this route STORES
  -- `mutualRecTy`'s output, so the clause is the generator's own shape
  refine structConstWF hfv hlp
    (Expr.constsResolve_le (fun n => storeMutualRecs_le n) hres) hbv
    (fun _ _ _ heq => nomatch heq) ?_ (hmaj := ?maj)
  case maj =>
    -- **THE MAJOR PREMISE'S HEAD** (task #315): this route STORES
    -- `mutualRecTy`'s output, so the clause is the generator's own shape
    intro cv mI rP rules heq
    obtain ⟨rfl, rfl, -, -⟩ := ConstantInfo.recInfo.inj heq
    exact checkMutualRecTys_majorHead hrectys hkf hnc hnIdxs mIdx _ hlt hget
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  obtain ⟨⟨cr, hcr, hrhs⟩, hfire⟩ := mutualRules_mem hr
  obtain ⟨hrfv, hrlp, hrres, hrbv⟩ := checkMutualMemberRules_mem hrl hcr
  refine ⟨by rw [hrhs]; exact hrfv, by rw [hrhs]; exact hrlp, ?_, by rw [hrhs]; exact hrbv, ?_⟩
  · rw [hrhs]
    exact Expr.constsResolve_le (provisionMutualRecs_store_le (fun _ h => h)) hrres
  · intro lvls pins hf
    exact absurd hf (hfire lvls pins)

/-! ## Stage 5: the projection tables -/

/-- One member's table stage keeps the environment well-formed. -/
theorem mutualMemberTable_wf {b : MutualBlock} {f : MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {mIdx : Nat}
    {env env' : Env} (henv : EnvWF env)
    (h : mutualMemberTable (m := CheckM) b f ctorsA sortss mIdx env = .ok env') :
    EnvWF env' := by
  rcases mutualMemberTable_inv h with rfl | ⟨J, c, -, -, htbl⟩
  · exact henv
  · exact direct_table_wf henv htbl

/-- Stage 5 at the run level. -/
theorem mutualTables_wf {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} :
    ∀ {l : List (MutualFormerA × Nat)} {env env' : Env},
      EnvWF env →
      mutualTables (m := CheckM) b ctorsA sortss l env = .ok env' →
      EnvWF env'
  | [], env, env', henv, h => by
    obtain rfl := mutualTables_nil_inv h
    exact henv
  | (f, mIdx) :: rest, env, env', henv, h => by
    obtain ⟨envI, hI, hrest⟩ := mutualTables_inv h
    exact mutualTables_wf (mutualMemberTable_wf henv hI) hrest

/-! ## The install -/

/-- **The mutual core keeps the environment well-formed.** -/
theorem checkMutualCore_wf {env envOut : Env} (henv : EnvWF env) {b : MutualBlock}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {F : Nat}
    (h : checkMutualCore (fueledOps mode F) env b streamRecs = .ok envOut) :
    EnvWF envOut := by
  obtain ⟨-, -, -, -, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, hformers, -, -, -, -, hctors, hkinds, -, hgd, hrectys, hrules, htbl, -⟩ :=
    checkMutualCore_inv h
  have henv₁ : EnvWF env₁ := envWF_mutualFormers henv hformers
  have henv₂ : EnvWF (consMutualCtors b.nP ctorsA env₁) :=
    envWF_consMutualCtors henv₁ (checkMutualCtors_typeWF hctors)
  -- the three arity facts come off `mutualGenData`'s equation, which the
  -- inversion carries: its first component is `fms.map fun f =>
  -- ⟨f.cvTa.name, f.nIdx, f.cvTa.type⟩`, so the former count is
  -- `fms.length` and the index counts are COPIED; the constructor count
  -- is the zip's
  obtain ⟨hf4, hc4⟩ := Prod.mk.inj hgd
  obtain ⟨hlenC, -, -⟩ := checkMutualCtors_inv hctors
  obtain ⟨-, -, -, hlenK⟩ := classifyMutualKinds_inv hkinds
  refine mutualTables_wf (mutual_recs_wf henv₂ hrectys hrules ?_ ?_ ?_) htbl
  · rw [← hf4, List.length_map,
      mutualFormerChecks_length (mutualFormers_inv hformers).1]
    rfl
  · rw [← hc4]
    simp only [List.length_zipWith, List.length_zip, hlenC, hlenK]
    simp only [MutualBlock.n]
    omega
  · intro m f hm
    rw [← hf4, List.getElem?_map] at hm
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hm
    rw [List.getD_eq_getElem?_getD, hg]
    rfl

/-- **The recognised mutual block's install keeps the environment
well-formed.** -/
theorem checkMutual_wf {env envOut : Env} (henv : EnvWF env) {p : MutualParts} {F : Nat}
    (h : checkMutual (fueledOps mode F) env p = .ok envOut) : EnvWF envOut :=
  checkMutualCore_wf henv (checkMutual_inv h).2


/-! ## The type-slot facts at a grade (task #315 M6 s6) -/

/-- A constructor's run at a grade: its type is closed, level-defined,
resolving and bounded (`mutual_ctor_typeWF`'s twin). -/
theorem mutual_ctorG_typeWF {env : Env} {memberNames : List Name} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvC cvTa cvCa : ConstantVal} {nF F : Nat} {g : Bool} {sorts : List Level}
    (h : checkMutualCtor (fueledOps mode F) env memberNames T lps nP nIdx resSort isProp large
      cvC nF cvTa g = .ok (cvCa, sorts)) :
    cvCa.type.hasFvar = false ∧ cvCa.type.allLevelParamsDefined cvCa.levelParams = true ∧
    cvCa.type.constsResolve env = true ∧ cvCa.type.looseBVarsBounded 0 = true := by
  obtain ⟨⟨_, hdoor⟩, -, -⟩ := checkMutualCtorG_shape h
  exact ⟨hdoor.noFvar, hdoor.lpsOk, hdoor.resolve, hdoor.bounded⟩

/-- Every constructor of the block carries the four type-slot facts at
the formers' environment, at a grade. -/
theorem checkMutualCtorsG_typeWF {env : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {isProp g : Bool} {F : Nat} {cs : List MutualCtor} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)}
    (h : checkMutualCtors (fueledOps mode F) env b fms isProp g cs = .ok (ctorsA, sortss)) :
    ∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true := by
  obtain ⟨hlen, -, hall⟩ := checkMutualCtors_inv h
  intro c hc
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hj' : j < cs.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  obtain ⟨-, _, -, hrun⟩ := hall j cs[j] c (List.getElem?_eq_getElem hj') hj
  exact mutual_ctorG_typeWF hrun

/-- The type-slot facts of every checked former at a grade. -/
theorem mutualFormerChecksG_typeWF {nP F : Nat} {g : Bool} {l : List (ConstantVal × Nat)}
    {env : Env} {fms : List MutualFormerA}
    (h : mutualFormerChecks (fueledOps mode F) env nP g l = .ok fms) :
    ∀ f ∈ fms, f.cvTa.type.hasFvar = false ∧
      f.cvTa.type.allLevelParamsDefined f.cvTa.levelParams = true ∧
      f.cvTa.type.constsResolve env = true ∧
      f.cvTa.type.looseBVarsBounded 0 = true := by
  intro f hf
  obtain ⟨cv', hdoor⟩ := mutualFormerChecksG_checked h f hf
  exact ⟨hdoor.noFvar, hdoor.lpsOk, hdoor.resolve, hdoor.bounded⟩

end ConLeche
