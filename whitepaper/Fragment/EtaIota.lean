module

public import Fragment.Sound

public section

/-!
# ι through the projections, with no certificate (task #350)

**The question** (maintainer, 2026-10-12).  After Lean's kernel logic
renovation (lean4#14977) a family that may be `Prop` eliminates into
every sort only when it has no constructor, has K, or has structure η:
a non-recursive, non-indexed, non-impredicative structure (`And`,
`PUnit.{u}`, a sort-polymorphic `PSigma'.{u,v} : Sort (max u v)`),
every field of which is a proof wherever the structure is a
proposition.  Can ι on such a structure go through its projections,

  `S.rec ps motive minor x  ⟶  minor (S.p₀ ps x) … (S.pₖ ps x)`,

instead of reading the fields off a constructor literal, and need no
certificate?  (#349's counterexample shows that plain ι on a literal,
at a valuation where the family is `Prop`, needs a full-grade
certificate on every field: the literal is the point, so its arguments
are unconstrained.)

**The answer: yes, provided the step takes the major as it stands —
not its reduct.**

* `Red.iotaEta_core_sem` / `Red.iotaEta_sound`: the step is sound under
  the conditional claims with no certificate, no comparison (levels,
  parameters, indices) and no reduction of the major, given the
  environment's plain ι law (`RecRuleLaw`, already an `EnvModel`
  field) and the structure-η law on values (`StructEtaLaw`, the
  installation's obligation: every member of the structure's fibre is
  the constructor at its projections, which are typed).  The redex is
  not the point, so the whole spine — the major included — fits the
  recursor's telescope (`teleFit_of_ne_pt`); the projections are then
  applied to a major in its own domain, and their values are fixed by
  the major's value alone.  At a valuation where the structure is a
  proposition that value is the point, the projections of the point
  are the point (`projPt_of_fieldSort`: a field's type is a proposition
  wherever the structure is — non-impredicativity), and the reduct is
  the minor at the point, which is the recursor's value there.
* `Red.projCtor_core_sem`: the projection of a constructor literal
  (`S.pᵢ qs maj ⟶ fᵢ` where `maj` reduces to `S.mk … fs`) is sound with
  no certificate — the step #347 already freed of `projCertAt`.
  Where the structure is a proposition the redex is the point (the
  same `projPt_of_fieldSort`) and nothing is claimed; where
  it is not, the major is not the point, so its reduction is claimed,
  and the literal fits the constructor's telescope.
* **The chain** (`Red.trans`, `Red.appFn`, the `DefEq` consumers).  The
  eta reduct holds `S.pᵢ ps (S.mk ps n b)` for a literal major; it
  denotes the point at a propositional valuation, and its reduct `n`
  may be anything there.  That reduct is never consumed at such a
  valuation: `Red` has no congruence in argument position; a `Red`
  claim is consumed only on a subject that is not the point
  (`trans`: the middle term has the first term's denotation;
  `appFn`: the head of an application that is not the point is not
  the point); `DefEq`'s claim is about two sides that are both
  well-denoted and not the point, and each side is a subterm of the
  conclusion or a reduct whose invariant a claim supplied; the
  projection's own reduction is claimed only when the projection is
  not the point, which forces the structure to be a type.  The one
  place a reduct of a point-denoting term was consumed is plain ι's
  major (#347's `major_eq`, case 3 of the certificate table), which
  this path does not use.
* **Eta on the reduct of the major is not covered**
  (`etaIota_reduced_major_witness`).  A major that denotes the point
  may reduce to a term that is not well-denoted (a β-redex whose
  argument lies outside its λ's domain: a λ that is the point
  constrains nothing), so `minor (S.p₀ ps maj')` is not well-denoted
  although the redex is, and the reduction's claim fails.  The checker
  must eta-expand the major as it finds it (as lean4#15371 does,
  before `whnf` of the major), and must not first reduce it to a
  literal.  Its value is still right (the projections of the point are
  the point); whether a verdict-level counterexample exists is not
  settled here, the claim is what fails.
* **The contrast with plain ι** (`plainIota_literal_witness`): #349's
  counterexample on values — at the same redex, the plain reduct
  `minor n` is not well-denoted, the eta reduct `minor (S.p₀ (S.mk n))`
  is and has the redex's value.
* **K and structure η** (`recRuleLawK_of_eta`, `iotaEta_noFields`): for
  a structure with no fields (`True`, `PUnit`) the eta reduct is the K
  reduct, syntactically, and the structure-η law with the plain law
  gives the K law (#349's `RecRuleLawK`): the two paths coincide.
  Since #342 F2 the K law is itself an environment law
  (`EnvModel.rec_rules_k`, proved by inversion of the least fixed
  point, `IndSpec.rec_rule_lawK`) and K a rule (`Red.iotaK`); the
  theorem here shows the eta route reaches the same law.

The fragment has no projections, so the projection functions are
stored constants read only through the laws, and the two steps are
theorems about the claims, not rules of `Red` (as #349 did for K,
which #342 F2 has since made the rule `Red.iotaK`): a
rule needs an `EnvModel` field for `StructEtaLaw`/`ProjLaw` and its
proof in the installer (the projections read the unique decoding of a
member of the fibre, `Uniq.lean`, which at a proposition has every
field the point when every field's sort is zero), threaded through
`transport`, `InstallDef` and `InstallNest`.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## The projections -/

/-- The projections `p ps x`, for each projection constant `p` at
levels `ls`. -/
def projApps (projs : List Name) (ls : List Level) (ps : List Expr) (x : Expr) : List Expr :=
  projs.map fun p => Expr.mkAppN (.const p ls) (ps ++ [x])

/-- The projections' values at parameter values `ps` and a major value
`x`. -/
def projVals (M : Name → List Nat → V) (ls : List Nat) (projs : List Name) (ps : List V)
    (x : V) : List V :=
  projs.map fun p => appList (M p ls) (ps ++ [x])

theorem interp_projApps (M : Name → List Nat → V) (ρ : Nat → V) (projs : List Name)
    (ls : List Level) (ps : List Expr) (x : Expr) :
    (projApps projs ls ps x).map (interp M φ ρ)
      = projVals M (ls.map (Level.eval φ)) projs (ps.map (interp M φ ρ)) (interp M φ ρ x) := by
  simp only [projApps, projVals, List.map_map]
  apply List.map_congr_left
  intro p _
  simp [interp_mkAppN_appList, List.map_append]

/-- **Structure η on values** (task #350; the installation's
obligation for a structure with projections `projs`).  For the
recursor stored as `ci`, with `numParams` parameters, no indices and
the major at `majorIdx`, and its one rule's constructor `mk` stored as
`cij` at the recursor's last levels (`us.drop d`, `d` the elimination
level in front): whenever values `xs` and a major `x` fit the
recursor's telescope, each projection applied to the parameters and
`x` is a well-formed application chain, the parameters and the
projections' values fit the constructor's telescope, and `x` is the
constructor at them.

In the inductive model the projections read the unique decoding of a
member of the fibre (`IndSpec.Mem`, `Uniq`), so this is the decoding's
existence.  Where the structure is a type, the member is the tagged
tuple of its fields.  Where it is a proposition, the member is the
point, every field's domain is a truth value (the renovation's
non-impredicativity: a field's sort is at most the structure's), so
every field of the decoding is the point, the projections of the
point are the point (`projPt_of_fieldSort`), and the constructor
applied to anything is the point. -/
def StructEtaLaw (M : Name → List Nat → V) (ci : ConstInfo) (numParams majorIdx d : Nat)
    (mk : Name) (cij : ConstInfo) (projs : List Name) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (us : List Level) (xs : List V) (x : V),
    us.length = ci.lparams.length → xs.length = majorIdx →
    TeleFitV M φ ρ (ci.type.instL ci.lparams us) (xs ++ [x]) →
    (∀ p ∈ projs, SpineOk (M p ((us.drop d).map (Level.eval φ))) (xs.take numParams ++ [x])) ∧
    TeleFitV M φ ρ (cij.type.instL cij.lparams (us.drop d))
      (xs.take numParams ++
        projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x) ∧
    x = appList (M mk ((us.drop d).map (Level.eval φ)))
      (xs.take numParams ++ projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x)

/-- A list of length `n + 1` is its first `n` elements and its last
(`List.take_append_getD` at any universe). -/
theorem List.take_append_getD' {α : Type _} (d : α) :
    ∀ (l : List α) (n : Nat), l.length = n + 1 → l = l.take n ++ [l.getD n d]
  | [], _, h => by simp at h
  | _ :: l, 0, h => by
    simp at h
    simp [h]
  | a :: l, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [← take_append_getD' d l n h]

/-- Every pair of a list zipped with itself is a pair of equals. -/
theorem List.eq_of_mem_zip_self {α : Type _} :
    ∀ {l : List α} {p : α × α}, p ∈ l.zip l → p.1 = p.2
  | [], _, h => by simp at h
  | a :: l, p, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact eq_of_mem_zip_self h

/-- **The ι law through the projections, on values**: the plain law
(`RecRuleLaw`) at the constructor's projections, which the structure-η
law supplies.  No field of any constructor application is read: the
values the minor receives are the projections of the major's value. -/
theorem etaLaw_vals {M : Name → List Nat → V} {c : Name} {ci : ConstInfo}
    {numParams numBefore d : Nat} {rl : RecRule} {cij : ConstInfo} {projs : List Name}
    (hlaw : RecRuleLaw M c ci numParams numBefore numBefore rl cij)
    (heta : StructEtaLaw M ci numParams numBefore d rl.ctor cij projs)
    (hnP : numParams ≤ numBefore) (hnf : projs.length = rl.nfields)
    (hd : d + cij.lparams.length = ci.lparams.length)
    (φ : Name → Nat) (ρ : Nat → V) (us : List Level) (xs : List V) (x : V)
    (hus : us.length = ci.lparams.length) (hxs : xs.length = numBefore)
    (hfit : TeleFitV M φ ρ (ci.type.instL ci.lparams us) (xs ++ [x]))
    (hn : appList (M c (us.map (Level.eval φ))) (xs ++ [x]) ≠ pt) :
    appList (M c (us.map (Level.eval φ))) (xs ++ [x])
        = appList (interp M φ ρ (rl.rhs.instL ci.lparams us))
            (xs ++ projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x) ∧
      WellDenoted M φ ρ (rl.rhs.instL ci.lparams us) ∧
      SpineOk (interp M φ ρ (rl.rhs.instL ci.lparams us))
        (xs ++ projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x) ∧
      (∀ p ∈ projs, SpineOk (M p ((us.drop d).map (Level.eval φ))) (xs.take numParams ++ [x])) := by
  obtain ⟨hsp, hfitj, hx⟩ := heta φ ρ us xs x hus hxs hfit
  have hps : (xs.take numParams).length = numParams := by simp [hxs]; omega
  have hpv : (projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x).length
      = rl.nfields := by simp [projVals, hnf]
  have hys1 : (xs.take numParams ++ projVals M ((us.drop d).map (Level.eval φ)) projs
      (xs.take numParams) x).take numParams = xs.take numParams := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  have hys2 : (xs.take numParams ++ projVals M ((us.drop d).map (Level.eval φ)) projs
      (xs.take numParams) x).drop numParams
        = projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x := by
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append]
  have hctor := hx
  have hlev : (us.drop d).map (Level.eval φ)
      = (us.drop (us.length - (us.drop d).length)).map (Level.eval φ) := by
    rw [List.length_drop, show us.length - (us.length - d) = d by omega]
  obtain ⟨heq, hwr, hspr⟩ := hlaw φ ρ us (us.drop d) xs
    (xs.take numParams ++ projVals M ((us.drop d).map (Level.eval φ)) projs (xs.take numParams) x)
    hus (by rw [List.length_drop]; omega) hxs (by rw [List.length_append, hps, hpv])
    (by rw [← hctor]; exact hfit) hfitj hlev
    (by
      rw [hys1]
      intro p hp _ _
      exact List.eq_of_mem_zip_self hp)
    (by
      intro _ _ _ _ _ _ _ _ _ p hp
      rw [List.drop_of_length_le (by omega), List.zip_nil_right] at hp
      simp at hp)
    (by rw [← hctor]; exact hn)
  rw [List.take_of_length_le (show xs.length ≤ numBefore by omega), hys2] at heq hspr
  rw [← hctor] at heq
  exact ⟨heq, hwr, hspr, hsp⟩

namespace Red

/-- **ι through the projections, the semantic core**: given
the plain ι law and the structure-η law, the redex
`rec ps motive minor x` reduces to `minor (p₀ ps x) … (pₖ ps x)` with
no certificate — no slot certificate on the major, no constructor
telescope, no level, parameter or index comparison, and no reduction
of the major.  The redex is not the point, so its whole spine fits
the recursor's telescope (`teleFit_of_ne_pt`); everything else is the
laws'. -/
theorem iotaEta_core_sem {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {args : List Expr} {numParams numBefore d : Nat} {rl : RecRule} {cij : ConstInfo}
    {projs : List Name}
    (hfind : env.find? c = some ci)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = numBefore + 1)
    (hpis : ci.type.hasPis (numBefore + 1) = true)
    (hlaw : RecRuleLaw m.M c ci numParams numBefore numBefore rl cij)
    (heta : StructEtaLaw m.M ci numParams numBefore d rl.ctor cij projs)
    (hnP : numParams ≤ numBefore) (hnf : projs.length = rl.nfields)
    (hd : d + cij.lparams.length = ci.lparams.length) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us)
        (args.take numBefore ++
          projApps projs (us.drop d) (args.take numParams) (args.getD numBefore (.bvar 0)))) := by
  intro ρ hs hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hT := m.type_ok c ci hfind φ ρ us hus
  have hp : (ci.type.instL ci.lparams us).hasPis args.length = true := by
    rw [Expr.hasPis_instL, hlen]; exact hpis
  have hfit := teleFitV_of_teleFit m.M φ ρ hp
    (teleFit_of_ne_pt hT.1 (by rw [interp_const]; exact hT.2.2) hp hw hn)
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwx : WellDenoted m.M φ ρ (args.getD numBefore (Expr.bvar 0)) :=
    hargs _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _)
  generalize args.getD numBefore (Expr.bvar 0) = x at hsplit hwx ⊢
  have hvs : args.map (interp m.M φ ρ)
      = (args.take numBefore).map (interp m.M φ ρ) ++ [interp m.M φ ρ x] := by
    conv => lhs; rw [hsplit]
    simp
  have hv : interp m.M φ ρ (Expr.mkAppN (Expr.const c us) args)
      = appList (m.M c (us.map (Level.eval φ)))
          ((args.take numBefore).map (interp m.M φ ρ) ++ [interp m.M φ ρ x]) := by
    rw [interp_mkAppN_appList, interp_const, hvs]
  rw [hvs] at hfit
  have hxs : ((args.take numBefore).map (interp m.M φ ρ)).length = numBefore := by
    simp [hlen]
  obtain ⟨heq, hwr, hspr, hsp⟩ := etaLaw_vals hlaw heta hnP hnf hd φ ρ us _ _ hus hxs hfit
    (hv ▸ hn)
  have hparams : ((args.take numBefore).map (interp m.M φ ρ)).take numParams
      = (args.take numParams).map (interp m.M φ ρ) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left hnP]
  rw [hparams] at heq hspr hsp
  have hvals : (args.take numBefore ++
        projApps projs (us.drop d) (args.take numParams) x).map (interp m.M φ ρ)
      = (args.take numBefore).map (interp m.M φ ρ) ++
        projVals m.M ((us.drop d).map (Level.eval φ)) projs
          ((args.take numParams).map (interp m.M φ ρ)) (interp m.M φ ρ x) := by
    rw [List.map_append, interp_projApps]
  have hwps : ∀ a ∈ args.take numParams, WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  refine ⟨WellDenoted_mkAppN_of_spineOk m.M φ ρ hwr ?_ (by rw [hvals]; exact hspr), ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hargs a (List.mem_of_mem_take ha)
    · simp only [projApps, List.mem_map] at ha
      obtain ⟨p, hp, rfl⟩ := ha
      refine WellDenoted_mkAppN_of_spineOk m.M φ ρ trivial ?_ ?_
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact hwps b hb
        · rw [List.mem_singleton] at hb; subst hb; exact hwx
      · simpa [List.map_append] using hsp p hp
  · rw [hv, interp_mkAppN_appList, hvals]
    exact heq

/-- **ι through the projections, as the checker would fire it**: a
stored recursor of a structure (no indices; one motive and one minor
in a non-mutual block, though the count is not used), whose rule's
constructor is stored, at a structure-η law for its projections.  The
plain law is the environment's (`EnvModel.rec_rules`); nothing is
certified. -/
theorem iotaEta_sound {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors : Nat} {rules : List RecRule}
    {args : List Expr} {rl : RecRule} {cij : ConstInfo} {d : Nat} {projs : List Name}
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors 0 rules)
    (hrl : rl ∈ rules) (hinst : rl.inst = none) (hcj : env.find? rl.ctor = some cij)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = numParams + numMotives + numMinors + 1)
    (hpis : ci.type.hasPis (numParams + numMotives + numMinors + 1) = true)
    (heta : StructEtaLaw m.M ci numParams (numParams + numMotives + numMinors) d rl.ctor cij projs)
    (hnf : projs.length = rl.nfields)
    (hd : d + cij.lparams.length = ci.lparams.length) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us)
        (args.take (numParams + numMotives + numMinors) ++
          projApps projs (us.drop d) (args.take numParams)
            (args.getD (numParams + numMotives + numMinors) (.bvar 0)))) := by
  have hlaw := m.rec_rules c ci numParams numMotives numMinors 0 rules hfind hkind rl hrl hinst
    cij hcj
  exact iotaEta_core_sem hfind hus hlen hpis hlaw heta (by omega) hnf hd

end Red

/-! ## K and structure η -/

/-- **A structure with no fields: the eta reduct is the K reduct**,
syntactically — the minor at the recursor's parameters, motives and
minors (`True`, `PUnit`). -/
theorem iotaEta_noFields (rhs : Expr) (args : List Expr) (numBefore numParams : Nat)
    (ls : List Level) (x : Expr) :
    Expr.mkAppN rhs (args.take numBefore ++ projApps [] ls (args.take numParams) x)
      = Expr.mkAppN rhs (args.take numBefore) := by
  simp [projApps]

/-- **…and the structure-η law gives the K law** (#349's
`RecRuleLawK`) for it: with no projections, "the major is the
constructor at the parameters" is the inversion K needs.  So a family
that is both K and a structure (`True`) fires either path with the
same reduct and the same justification, and neither certifies. -/
theorem recRuleLawK_of_eta {M : Name → List Nat → V} {c : Name} {ci : ConstInfo}
    {numParams numBefore d : Nat} {rl : RecRule} {cij : ConstInfo}
    (hlaw : RecRuleLaw M c ci numParams numBefore numBefore rl cij)
    (heta : StructEtaLaw M ci numParams numBefore d rl.ctor cij [])
    (hnP : numParams ≤ numBefore) (hnf : rl.nfields = 0)
    (hd : d + cij.lparams.length = ci.lparams.length) :
    RecRuleLawK M c ci numBefore numBefore rl := by
  intro φ ρ us vs hus hlen hfit hn
  have hsplit := List.take_append_getD' pt vs _ hlen
  rw [hsplit] at hfit hn ⊢
  have hxs : (vs.take numBefore).length = numBefore := by simp [hlen]
  obtain ⟨heq, hwr, hspr, -⟩ :=
    etaLaw_vals hlaw heta hnP (by simp [hnf]) hd φ ρ us _ _ hus hxs hfit hn
  have htk : (vs.take numBefore ++ [vs.getD numBefore pt]).take numBefore = vs.take numBefore := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  simp only [projVals, List.map_nil, List.append_nil] at heq hspr
  rw [htk]
  exact ⟨heq, hwr, hspr⟩

/-! ## The projection of a constructor literal -/

/-- **The projection law on values** (the installation's obligation for
a projection `p`, the `i`-th field of the structure whose constructor
is `mk`, stored as `pci` and `cij` over the same level parameters):
where the projection's argument is the point, so is the projection
(`projPt_of_fieldSort` derives it from the field's sort); where it is
the constructor applied to values fitting its telescope and not the
point, the projection is the field. -/
def ProjLaw (M : Name → List Nat → V) (p : Name) (pci : ConstInfo) (numParams i : Nat)
    (mk : Name) (cij : ConstInfo) : Prop :=
  ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level) (qs : List V) (x : V),
    ls.length = pci.lparams.length → qs.length = numParams →
    TeleFitV M φ ρ (pci.type.instL pci.lparams ls) (qs ++ [x]) →
    (x = pt → appList (M p (ls.map (Level.eval φ))) (qs ++ [x]) = pt) ∧
    (∀ (lsj : List Level) (ys : List V), lsj.length = cij.lparams.length →
      TeleFitV M φ ρ (cij.type.instL cij.lparams lsj) ys →
      x = appList (M mk (lsj.map (Level.eval φ))) ys → x ≠ pt →
      appList (M p (ls.map (Level.eval φ))) (qs ++ [x]) = ys.getD (numParams + i) pt)

/-- **The projection of the point is the point**, from the field's
sort: if the projection's type, walked along the parameters, is
`(x : D) → B` and `B` is a proposition at every member of `D` whenever
`D` holds the point — the field's sort is at most the structure's, so
it is `Prop` wherever the structure is (non-impredicativity) — then the
projection at the point is the point.  This is what fails for an
impredicative structure (a data field of a `Prop` structure), which
after the renovation has no projections. -/
theorem projPt_of_fieldSort {M : Name → List Nat → V} {T : Expr} {ρ : Nat → V} {f : V}
    {qs : List V} {x : V}
    (hf : f ∈ˢ interp M φ ρ T) (hfit : TeleFitV M φ ρ T (qs ++ [x]))
    (hfs : ∀ (D B : Expr) (ρ' : Nat → V), piBodyV ρ T qs = some (.pi D B, ρ') →
      pt ∈ˢ interp M φ ρ' D → ∀ y, y ∈ˢ interp M φ ρ' D → interp M φ (cons y ρ') B ∈ˢ univ 0)
    (hx : x = pt) :
    appList f (qs ++ [x]) = pt := by
  obtain ⟨D, B, ρ', hb, hfitq, hxD⟩ := teleFitV_snoc M φ hfit
  have hmem := mem_piBodyV M φ hf hfitq hb
  rw [interp_pi] at hmem
  have hpt : appList f qs = pt := by
    refine eq_pt_of_mem_piV (fun y hy z hz => ?_) hmem
    exact eq_pt_of_mem_univ_zero (hfs D B ρ' hb (hx ▸ hxD) y hy) hz
  rw [appList_append, hpt, appList_cons, app_pt, appList_nil]

namespace Red

/-- **The projection of a constructor literal, with no certificate**
(no certificate on the major's reduct): `p qs maj ⟶ fᵢ` where the
major reduces to `mk … fs`.  If the major is the point, so is the
redex, and nothing is claimed.  If not, the major's reduction is
claimed, the literal is not the point, so it fits the constructor's
telescope (`teleFit_of_ne_pt`), and the law gives the field.  No
parameter or level comparison: the field's position is all that is
read. -/
theorem projCtor_core_sem {Γ : List Expr} {p : Name} {pci : ConstInfo} {ls : List Level}
    {qs : List Expr} {s : Expr} {mk : Name} {cij : ConstInfo} {lsj : List Level}
    {margs : List Expr} {numParams i : Nat}
    (hfind : env.find? p = some pci) (hls : ls.length = pci.lparams.length)
    (hqs : qs.length = numParams)
    (hpis : pci.type.hasPis (numParams + 1) = true)
    (hred : RedSem m φ Γ s (Expr.mkAppN (Expr.const mk lsj) margs))
    (hcj : env.find? mk = some cij) (hlsj : lsj.length = cij.lparams.length)
    (hpis' : cij.type.hasPis margs.length = true)
    (hi : numParams + i < margs.length)
    (hlaw : ProjLaw m.M p pci numParams i mk cij) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const p ls) (qs ++ [s]))
      (margs.getD (numParams + i) (.bvar 0)) := by
  intro ρ hs hw hn
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN m.M φ hw
  have hT := m.type_ok p pci hfind φ ρ ls hls
  have hp : (pci.type.instL pci.lparams ls).hasPis (qs ++ [s]).length = true := by
    rw [Expr.hasPis_instL]; simpa [hqs] using hpis
  have hfit := teleFitV_of_teleFit m.M φ ρ hp
    (teleFit_of_ne_pt hT.1 (by rw [interp_const]; exact hT.2.2) hp hw hn)
  rw [List.map_append, List.map_singleton] at hfit
  have hv : interp m.M φ ρ (Expr.mkAppN (Expr.const p ls) (qs ++ [s]))
      = appList (m.M p (ls.map (Level.eval φ)))
          (qs.map (interp m.M φ ρ) ++ [interp m.M φ ρ s]) := by
    rw [interp_mkAppN_appList, interp_const, List.map_append, List.map_singleton]
  obtain ⟨hpt, hcomp⟩ := hlaw φ ρ ls _ _ hls (by simp [hqs]) hfit
  have hsn : interp m.M φ ρ s ≠ pt := fun h => hn (hv ▸ hpt h)
  have hws : WellDenoted m.M φ ρ s := hargs s (by simp)
  obtain ⟨hwmaj, hemaj⟩ := hred ρ hs hws hsn
  have hmajv : interp m.M φ ρ (Expr.mkAppN (Expr.const mk lsj) margs)
      = appList (m.M mk (lsj.map (Level.eval φ))) (margs.map (interp m.M φ ρ)) := by
    rw [interp_mkAppN_appList, interp_const]
  have hTj := m.type_ok mk cij hcj φ ρ lsj hlsj
  have hpj : (cij.type.instL cij.lparams lsj).hasPis margs.length = true := by
    rw [Expr.hasPis_instL]; exact hpis'
  have hfitj := teleFitV_of_teleFit m.M φ ρ hpj
    (teleFit_of_ne_pt hTj.1 (by rw [interp_const]; exact hTj.2.2) hpj hwmaj (hemaj ▸ hsn))
  have heq := hcomp lsj _ hlsj hfitj (hemaj.trans hmajv) hsn
  have hget : (margs.map (interp m.M φ ρ)).getD (numParams + i) pt
      = interp m.M φ ρ (margs.getD (numParams + i) (.bvar 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_map]
  refine ⟨(WellDenoted_mkAppN m.M φ hwmaj).2 _ ?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  · rw [hv, heq, hget]

end Red

/-! ## The witnesses

Closed terms over constants, at a model of the empty environment
(`EnvModel.empty`) that gives the constants the values of a valuation
where the structure is a proposition: the constructor `mk` and the
projection `p0` are the point (as they are there), the minor is a
graph over `{pt}` (`True → Nat`-like, the field's domain a truth
value), the recursor sends a minor `m` to `fun x => m x` (its value at
the point is the minor at the point), `n` and `a` denote `True` — a
value outside `{pt}`, ill-slotted as a field.  The terms are not typed
by a checker; the witnesses are about the reduction **claims** (as
`lam_congr_untyped_unsound` is), which the soundness proof needs of
every step it takes. -/

namespace EtaWit

/-- The constant `n` at no levels. -/
def cst (n : Name) : Expr := .const n []

/-- The literal `mk n`. -/
def mkn : Expr := .app (cst "mk") (cst "n")

/-- `rec minor (mk n)`. -/
def redex1 : Expr := .app (.app (cst "rec") (cst "minor")) mkn

/-- Plain ι's reduct: `minor n`. -/
def plain1 : Expr := .app (cst "minor") (cst "n")

/-- The eta reduct: `minor (p0 (mk n))`. -/
def eta1 : Expr := .app (cst "minor") (.app (cst "p0") mkn)

/-- `g (k x)` under one binder. -/
def body : Expr := .app (cst "g") (.app (cst "k") (.bvar 0))

/-- A major that denotes the point: `(fun x : A => g (k x)) a`, a λ
that is the point applied outside its domain. -/
def maj : Expr := .app (.lam (cst "A") body) (cst "a")

/-- Its β-reduct `g (k a)`, which is not well-denoted. -/
def maj' : Expr := .app (cst "g") (.app (cst "k") (cst "a"))

/-- `rec minor maj`. -/
def redex2 : Expr := .app (.app (cst "rec") (cst "minor")) maj

/-- The eta reduct on the major as it stands: `minor (p0 maj)`. -/
def eta2 : Expr := .app (cst "minor") (.app (cst "p0") maj)

/-- The eta reduct on the major's reduct: `minor (p0 maj')`. -/
def etaRed2 : Expr := .app (cst "minor") (.app (cst "p0") maj')

/-- The minor's (and `k`'s) value: the constant `True` over `{pt}`. -/
noncomputable def grOne : V := graph (fun _ => one) one

/-- The minor's domain. -/
noncomputable def dm : V := piSet one (fun _ => univ 0)

/-- The recursor's value: a minor `m` to `fun x : {pt} => m x`. -/
noncomputable def recV : V := graph (fun mv => graph (fun x => app mv x) one) (dm : V)

/-- The model. -/
noncomputable def witM : Name → List Nat → V := fun c _ =>
  if c = "minor" ∨ c = "k" then grOne
  else if c = "rec" then recV
  else if c = "n" ∨ c = "a" ∨ c = "A" then one
  else pt

variable (φ : Name → Nat) (ρ : Nat → V)

theorem v_minor : interp (witM (V := V)) φ ρ (cst "minor") = grOne := by simp [cst, witM]
theorem v_k : interp (witM (V := V)) φ ρ (cst "k") = grOne := by simp [cst, witM]
theorem v_rec : interp (witM (V := V)) φ ρ (cst "rec") = recV := by simp [cst, witM]
theorem v_n : interp (witM (V := V)) φ ρ (cst "n") = one := by simp [cst, witM]
theorem v_a : interp (witM (V := V)) φ ρ (cst "a") = one := by simp [cst, witM]
theorem v_A : interp (witM (V := V)) φ ρ (cst "A") = one := by simp [cst, witM]
theorem v_mk : interp (witM (V := V)) φ ρ (cst "mk") = pt := by simp [cst, witM]
theorem v_p0 : interp (witM (V := V)) φ ρ (cst "p0") = pt := by simp [cst, witM]
theorem v_g : interp (witM (V := V)) φ ρ (cst "g") = pt := by simp [cst, witM]

theorem one_ne_pt' : (one : V) ≠ pt := ne_pt_of_mem_univ_zero one_mem_univ_zero
theorem pt_mem_one : (pt : V) ∈ˢ one := mem_one.mpr rfl
theorem one_not_mem_one : ¬ (one : V) ∈ˢ one := fun h => one_ne_pt' (mem_one.mp h)
theorem IsTy_one' : IsTy (one : V) := Or.inl one_mem_univ_zero

theorem grOne_mem : (grOne : V) ∈ˢ dm := graph_mem_piSet fun _ _ => one_mem_univ_zero
theorem app_grOne {x : V} (hx : x ∈ˢ one) : app (grOne : V) x = one := app_graph hx

theorem recV_mem : (recV : V) ∈ˢ piSet dm (fun _ => dm) :=
  graph_mem_piSet fun _ hm => graph_mem_piSet fun _ hx => app_mem_piSet hm hx

theorem app_recV_grOne : app (recV : V) grOne = graph (fun x => app grOne x) one :=
  app_graph grOne_mem

/-- An application whose head is the point: well-denoted (the point
applies to anything). -/
theorem wd_pt_app {f a : Expr} (hf : WellDenoted (witM (V := V)) φ ρ f)
    (ha : WellDenoted witM φ ρ a) (hv : interp witM φ ρ f = pt) :
    WellDenoted witM φ ρ (.app f a) := by
  rw [WellDenoted_app]
  exact ⟨hf, ha, hv ▸ appliesTo_pt _⟩

/-- An application of a member of a function space to a member of its
domain: well-denoted. -/
theorem wd_graph_app {f a : Expr} {A : V} {B : V → V} (hf : WellDenoted (witM (V := V)) φ ρ f)
    (ha : WellDenoted witM φ ρ a) (hv : interp witM φ ρ f ∈ˢ piSet A B)
    (hA : interp witM φ ρ a ∈ˢ A) (hT : IsTy A) : WellDenoted witM φ ρ (.app f a) := by
  rw [WellDenoted_app]
  exact ⟨hf, ha, appliesTo_of_mem_piSet hv hT hA⟩

/-- A graph applied outside its domain: not well-denoted. -/
theorem not_wd_graph_app {f a : Expr} {A : V} {B : V → V}
    (hv : interp (witM (V := V)) φ ρ f ∈ˢ piSet A B) (hA : ¬ interp witM φ ρ a ∈ˢ A) :
    ¬ WellDenoted witM φ ρ (.app f a) := by
  rw [WellDenoted_app]
  rintro ⟨-, -, hap⟩
  exact hA (hap.mem hv)

theorem wd_mkn : WellDenoted (witM (V := V)) φ ρ mkn :=
  wd_pt_app φ ρ trivial trivial (v_mk φ ρ)

theorem v_mkn : interp (witM (V := V)) φ ρ mkn = pt := by
  simp only [mkn, interp_app, v_mk, app_pt]

theorem wd_recMinor : WellDenoted (witM (V := V)) φ ρ (.app (cst "rec") (cst "minor")) :=
  wd_graph_app φ ρ trivial trivial (by rw [v_rec]; exact recV_mem)
    (by rw [v_minor]; exact grOne_mem)
    (Or.inr strict_piSet)

theorem v_recMinor : interp (witM (V := V)) φ ρ (.app (cst "rec") (cst "minor"))
    = graph (fun x => app grOne x) one := by
  rw [interp_app, v_rec, v_minor, app_recV_grOne]

theorem recMinor_mem : interp (witM (V := V)) φ ρ (.app (cst "rec") (cst "minor"))
    ∈ˢ piSet one (fun _ => univ 0) := by
  rw [v_recMinor]
  exact graph_mem_piSet fun _ hx => by rw [app_grOne hx]; exact one_mem_univ_zero

/-- `rec minor t` for a well-denoted `t` denoting the point:
well-denoted, and `True`, not the point. -/
theorem redex_at_pt {t : Expr} (hw : WellDenoted (witM (V := V)) φ ρ t)
    (hv : interp witM φ ρ t = pt) :
    WellDenoted witM φ ρ (.app (.app (cst "rec") (cst "minor")) t) ∧
      interp witM φ ρ (.app (.app (cst "rec") (cst "minor")) t) = one := by
  refine ⟨wd_graph_app φ ρ (wd_recMinor φ ρ) hw (recMinor_mem φ ρ) (by rw [hv]; exact pt_mem_one)
    IsTy_one', ?_⟩
  rw [interp_app, v_recMinor, hv, app_graph pt_mem_one, app_grOne pt_mem_one]

/-- `minor (p0 t)` for a well-denoted `t`:
well-denoted, and `True`. -/
theorem eta_at_pt {t : Expr} (hw : WellDenoted (witM (V := V)) φ ρ t) :
    WellDenoted witM φ ρ (.app (cst "minor") (.app (cst "p0") t)) ∧
      interp witM φ ρ (.app (cst "minor") (.app (cst "p0") t)) = one := by
  have hp : WellDenoted (witM (V := V)) φ ρ (.app (cst "p0") t) :=
    wd_pt_app φ ρ trivial hw (v_p0 φ ρ)
  have hpv : interp (witM (V := V)) φ ρ (.app (cst "p0") t) = pt := by
    rw [interp_app, v_p0, app_pt]
  refine ⟨wd_graph_app φ ρ trivial hp (by rw [v_minor]; exact grOne_mem)
    (by rw [hpv]; exact pt_mem_one)
    IsTy_one', ?_⟩
  rw [interp_app, v_minor, hpv, app_grOne pt_mem_one]

theorem wd_maj : WellDenoted (witM (V := V)) φ ρ maj := by
  have hlam : WellDenoted (witM (V := V)) φ ρ (.lam (cst "A") body) := by
    rw [WellDenoted_lam, v_A]
    refine ⟨trivial, IsTy_one', fun y hy => ?_, fun _ => one, fun y _ => ?_, fun _ _ => IsTy_one'⟩
    · have hk : WellDenoted (witM (V := V)) φ (cons y ρ) (.app (cst "k") (.bvar 0)) :=
        wd_graph_app φ _ trivial trivial (by rw [v_k]; exact grOne_mem) (by simpa using hy)
          IsTy_one'
      exact wd_pt_app φ _ trivial hk (v_g φ _)
    · simp only [body, interp_app, v_g, app_pt]; exact pt_mem_one
  refine wd_pt_app φ ρ hlam trivial ?_
  rw [interp_lam]
  exact lamV_eq_pt fun _ _ => by simp only [body, interp_app, v_g, app_pt]

theorem v_maj : interp (witM (V := V)) φ ρ maj = pt := by
  have : interp (witM (V := V)) φ ρ (.lam (cst "A") body) = pt := by
    rw [interp_lam]
    exact lamV_eq_pt fun _ _ => by simp only [body, interp_app, v_g, app_pt]
  rw [maj, interp_app, this, app_pt]

theorem not_wd_maj' : ¬ WellDenoted (witM (V := V)) φ ρ maj' := by
  intro h
  rw [maj', WellDenoted_app] at h
  exact not_wd_graph_app φ ρ (by rw [v_k]; exact grOne_mem) (by rw [v_a]; exact one_not_mem_one)
    h.2.1

end EtaWit

open EtaWit in
/-- **The field counterexample, on values, and the eta path's answer to
it**.  At a valuation where the structure is a
proposition, the redex `rec minor (mk n)` with an ill-slotted field
`n` is well-denoted and not the point.  Plain ι's reduct `minor n` is
not well-denoted, so plain ι without a certificate on the field
breaks the reduction claim; the eta reduct `minor (p0 (mk n))` is
well-denoted and denotes what the redex does, so the step through the
projections satisfies it with no certificate. -/
theorem plainIota_literal_witness (φ : Name → Nat) :
    (∀ ρ : Nat → V, WellDenoted (witM (V := V)) φ ρ redex1 ∧ interp witM φ ρ redex1 ≠ pt) ∧
    ¬ RedSem (EnvModel.empty (witM (V := V))) φ [] redex1 plain1 ∧
    RedSem (EnvModel.empty (witM (V := V))) φ [] redex1 eta1 := by
  have hr := fun ρ => redex_at_pt (V := V) φ ρ (wd_mkn φ ρ) (v_mkn φ ρ)
  have hne : ∀ ρ : Nat → V, interp (witM (V := V)) φ ρ redex1 ≠ pt := fun ρ => by
    rw [redex1, (hr ρ).2]; exact one_ne_pt'
  refine ⟨fun ρ => ⟨(hr ρ).1, hne ρ⟩, ?_, ?_⟩
  · intro h
    have hρ := h (fun _ => pt) trivial (hr _).1 (hne _)
    exact not_wd_graph_app φ _ (by rw [v_minor]; exact grOne_mem)
      (by rw [v_n]; exact one_not_mem_one) hρ.1
  · intro ρ _ _ _
    have he := eta_at_pt (V := V) φ ρ (wd_mkn φ ρ)
    have hv : interp (witM (V := V)) φ ρ redex1 = interp witM φ ρ eta1 := by
      rw [redex1, (hr ρ).2]; exact he.2.symm
    exact ⟨he.1, hv⟩

open EtaWit in
/-- **Eta on the reduct of the major is outside the claims**.
The major `maj := (fun x : A => g (k x)) a` is well-denoted
and the point (a lambda that is the point constrains nothing, so `a` may
lie outside `A`), and it β-reduces to `maj' := g (k a)`, which is not
well-denoted (`k` is a graph over `A`).  The redex `rec minor maj` is
well-denoted and not the point.  Eta-expanding the major's reduct,
`minor (p0 maj')`, breaks the reduction claim; eta-expanding the major
as it stands, `minor (p0 maj)`, satisfies it.  So the checker's eta
path must not reduce the major first (lean4#15371 expands before the
major's `whnf`). -/
theorem etaIota_reduced_major_witness [LevelOracle] (φ : Name → Nat) (env : Env)
    (Γ : List Expr) :
    Red env Γ maj maj' ∧
    (∀ ρ : Nat → V, WellDenoted (witM (V := V)) φ ρ redex2 ∧ interp witM φ ρ redex2 ≠ pt ∧
      interp witM φ ρ maj = pt) ∧
    ¬ RedSem (EnvModel.empty (witM (V := V))) φ [] redex2 etaRed2 ∧
    RedSem (EnvModel.empty (witM (V := V))) φ [] redex2 eta2 := by
  have hr := fun ρ => redex_at_pt (V := V) φ ρ (wd_maj φ ρ) (v_maj φ ρ)
  have hne : ∀ ρ : Nat → V, interp (witM (V := V)) φ ρ redex2 ≠ pt := fun ρ => by
    rw [redex2, (hr ρ).2]; exact one_ne_pt'
  refine ⟨Red.beta, fun ρ => ⟨(hr ρ).1, hne ρ, v_maj φ ρ⟩, ?_, ?_⟩
  · intro h
    have hρ := h (fun _ => pt) trivial (hr _).1 (hne _)
    have h1 := hρ.1
    rw [etaRed2, WellDenoted_app] at h1
    have h2 := h1.2.1
    rw [WellDenoted_app] at h2
    exact not_wd_maj' φ _ h2.2.1
  · intro ρ _ _ _
    have he := eta_at_pt (V := V) φ ρ (wd_maj φ ρ)
    have hv : interp (witM (V := V)) φ ρ redex2 = interp witM φ ρ eta2 := by
      rw [redex2, (hr ρ).2]; exact he.2.symm
    exact ⟨he.1, hv⟩

end Fragment
