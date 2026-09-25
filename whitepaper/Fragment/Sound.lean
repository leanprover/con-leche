module

public import Fragment.Motive
public import Fragment.Tele

public section

/-!
# Soundness: derivation ⇒ claim

**One mutual structural induction over the three relations**
(`red_sound`/`defeq_sound`/`infer_sound` at the end of this file);
every case is one lemma about one rule, stated over the environment's
laws (`EnvModel`) and the library (`SetLib`), never over an
implementation.  This is the shape of `ConLeche/Model/Rules/Sound.lean`
and its per-rule lemma files, on the fragment.

The cases the paper dwells on, each its own lemma:

* `Red.betaGate_sound` — β with no certificate, sound in the graph
  regime from the invariant alone;
* `Red.beta_sound` — β with the argument certified, sound at any
  regime;
* `DefEq.eta_sound` — η, from the library's η law;
* `DefEq.proofIrrel_sound` — proof irrelevance for free: both sides
  denote the point, and the two types are never compared;
* `Infer.app_sound` — the application rule, where no Π-injectivity is
  needed.
-/

namespace Fragment
open SetLib

universe u

variable {V : Type u} [SetLib V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-! ## Small facts -/

/-- The oracle's `eq` is `eval`-equality at the valuation. -/
theorem eval_eq_of_oracle [LevelOracle] {u v : Level} (h : LevelOracle.eq u v = true) :
    Level.eval φ u = Level.eval φ v :=
  (LevelOracle.eq_iff u v).mp h φ

/-- A checked annotation reads `true` exactly where the sort is zero. -/
theorem holds_of_zeroness {v : Level} {pw : PropWhen} (h : Level.zeroness v = pw) :
    pw.holds φ = true ↔ Level.eval φ v = 0 := by
  subst h; exact Level.holds_zeroness φ v

/-- The invariant of a spine gives the invariant of its head and of
every argument. -/
theorem WellDenoted_mkAppN {ρ : Nat → V} :
    ∀ {f : Expr} {args : List Expr}, WellDenoted m.M φ ρ (Expr.mkAppN f args) →
      WellDenoted m.M φ ρ f ∧ ∀ a ∈ args, WellDenoted m.M φ ρ a
  | _, [], h => ⟨h, by simp⟩
  | f, a :: args, h => by
    rw [Expr.mkAppN_cons] at h
    obtain ⟨h1, h2⟩ := WellDenoted_mkAppN h
    rw [WellDenoted_app] at h1
    refine ⟨h1.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1.2.1
    · exact h2 b hb

/-- A list of length `n + 1` is its first `n` elements and its last. -/
theorem List.take_append_getD {α : Type} (d : α) :
    ∀ (l : List α) (n : Nat), l.length = n + 1 → l = l.take n ++ [l.getD n d]
  | [], _, h => by simp at h
  | _ :: l, 0, h => by
    simp at h
    simp [h]
  | a :: l, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.take_succ_cons, List.getD_cons_succ, List.cons_append]
    rw [← take_append_getD d l n h]

/-- **Certificates give fit**: a spine whose arguments are typed against
the telescope's domains (each argument's inferred type definitionally
equal to the binder domain it meets) fits the telescope semantically —
the folded `Certs` walk of `Red.iota`, made semantic. -/
theorem teleFit_of_certs {Γ : List Expr} {ρ : Nat → V} (hs : Sat m.M φ Γ ρ) :
    ∀ {T : Expr} {spine tys doms : List Expr},
      WellDenoted m.M φ ρ T → (∀ a ∈ spine, WellDenoted m.M φ ρ a) →
      Expr.piDomains T spine = some doms → tys.length = doms.length →
      (∀ p ∈ spine.zip tys, InferSem m φ Γ p.1 p.2) →
      (∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2) →
      TeleFit m.M φ ρ T spine
  | _, [], _, _, _, _, _, _, _, _ => trivial
  | .pi A _ B, a :: as, tys, _, hT, hsp, hdoms, hlen, hI, hD => by
    simp only [Expr.piDomains, Option.map_eq_some_iff] at hdoms
    obtain ⟨ds, hds, rfl⟩ := hdoms
    cases tys with
    | nil => simp at hlen
    | cons ta ts =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [WellDenoted_pi] at hT
      have hwa := hsp a List.mem_cons_self
      obtain ⟨-, hwta, hmem⟩ := hI (a, ta) (by simp) ρ hs
      rw [hD (ta, A) (by simp) ρ hs hwta hT.1] at hmem
      refine ⟨hmem, ?_⟩
      refine teleFit_of_certs hs ((WellDenoted_inst0 m.M φ hwa).mpr (hT.2.1 _ hmem))
        (fun b hb => hsp b (List.mem_cons_of_mem a hb)) hds hlen ?_ ?_
      · intro p hp
        exact hI p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
      · intro p hp
        exact hD p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
  | .bvar _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .sort _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .const _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .app _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h
  | .lam _ _ _, _ :: _, _, _, _, _, h, _, _, _ => by simp [Expr.piDomains] at h

/-- **The residual is well-denoted**: walking a well-denoted telescope
along a fitting spine of well-denoted arguments leaves a well-denoted
residual (the body's invariant transported along each substitution). -/
theorem WellDenoted_piResidual {ρ : Nat → V} :
    ∀ {T : Expr} {as : List Expr} {R : Expr},
      WellDenoted m.M φ ρ T → (∀ a ∈ as, WellDenoted m.M φ ρ a) →
      TeleFit m.M φ ρ T as → Expr.piResidual T as = some R → WellDenoted m.M φ ρ R
  | T, [], _, hT, _, _, h => by simp at h; subst h; exact hT
  | .pi A _ B, a :: as, R, hT, has, hfit, h => by
    rw [Expr.piResidual_pi_cons] at h
    obtain ⟨hmem, hfit'⟩ := hfit
    rw [WellDenoted_pi] at hT
    exact WellDenoted_piResidual
      ((WellDenoted_inst0 m.M φ (has a List.mem_cons_self)).mpr (hT.2.1 _ hmem))
      (fun b hb => has b (List.mem_cons_of_mem a hb)) hfit' h
  | .bvar _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .sort _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .const _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .app _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h
  | .lam _ _ _, _ :: _, _, _, _, _, h => by simp [Expr.piResidual] at h

/-! ## Reduction -/

namespace Red

theorem refl_sound {Γ : List Expr} {e : Expr} : RedSem m φ Γ e e :=
  fun _ _ h => ⟨h, rfl⟩

theorem trans_sound {Γ : List Expr} {e₁ e₂ e₃ : Expr}
    (h₁ : RedSem m φ Γ e₁ e₂) (h₂ : RedSem m φ Γ e₂ e₃) : RedSem m φ Γ e₁ e₃ := by
  intro ρ hs hw
  obtain ⟨hw₁, he₁⟩ := h₁ ρ hs hw
  obtain ⟨hw₂, he₂⟩ := h₂ ρ hs hw₁
  exact ⟨hw₂, he₁.trans he₂⟩

theorem appFn_sound {Γ : List Expr} {f f' a : Expr} (h : RedSem m φ Γ f f') :
    RedSem m φ Γ (Expr.app f a) (Expr.app f' a) := by
  intro ρ hs hw
  rw [WellDenoted_app] at hw
  obtain ⟨hf, ha, p, A, B, hslot, hmem, hB⟩ := hw
  obtain ⟨hf', he⟩ := h ρ hs hf
  refine ⟨?_, by simp [he]⟩
  rw [WellDenoted_app]
  exact ⟨hf', ha, p, A, B, he ▸ hslot, hmem, hB⟩

/-- **β at a `never` gate is sound with no certificate.**  The
application is well-denoted, so the λ's denotation is a member of some
product with the argument in its domain.  The λ is annotated `never`,
so it denotes a graph, never the point — hence that product is in the
graph regime, and a graph determines its domain: the slot's domain is
the λ's own, the argument is in it, and the graph's β fires
(`WellDenoted_beta_graph`).  No typing information about the argument
was ever consulted. -/
theorem betaGate_sound {Γ : List Expr} {A b a : Expr} :
    RedSem m φ Γ (Expr.app (Expr.lam A .never b) a) (b.inst a) := by
  intro ρ _ hw
  obtain ⟨he, hw'⟩ := WellDenoted_beta_graph m.M φ hw
  exact ⟨hw', he⟩

/-- **Certified β is sound at any regime.**  The argument's inferred
type is definitionally equal to the domain, so the argument's
denotation is in the domain's; at a proposition both sides are the
point, above it the graph's β fires (`WellDenoted_beta`).  This is
the check the checker runs wherever the body may be a proposition:
there the λ denotes the point, whose "domain" the model cannot
recover, so the invariant of the redex says nothing about the argument
— the certificate does. -/
theorem beta_sound {Γ : List Expr} {A b a ta : Expr} {pw : PropWhen}
    (hta : InferSem m φ Γ a ta) (hd : DefEqSem m φ Γ ta A) :
    RedSem m φ Γ (Expr.app (Expr.lam A pw b) a) (b.inst a) := by
  intro ρ hs hw
  have hA : WellDenoted m.M φ ρ A := by
    rw [WellDenoted_app, WellDenoted_lam] at hw
    exact hw.1.1
  obtain ⟨-, hwta, hmem⟩ := hta ρ hs
  rw [hd ρ hs hwta hA] at hmem
  obtain ⟨he, hw'⟩ := WellDenoted_beta m.M φ hw hmem
  exact ⟨hw', he⟩

/-- δ: the environment's `unfold` law. -/
theorem delta_sound {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo} {v : Expr}
    (hfind : env.find? c = some ci) (hv : ci.value? = some v)
    (hls : ls.length = ci.lparams.length) :
    RedSem m φ Γ (Expr.const c ls) (v.instL ci.lparams ls) := by
  intro ρ _ _
  obtain ⟨hw, he⟩ := m.unfold c ci v hfind hv φ ρ ls hls
  exact ⟨hw, by rw [interp_const, he]⟩

/-- ι: the two certificates give the two telescope fits, the three
comparisons give their semantic forms (the residual's index
expressions are well-denoted because the residual is,
`WellDenoted_piResidual`), the reduced major's denotation replaces the
argument's, and the environment's `RecRuleLaw` gives the equation and
the reduct's invariant. -/
theorem iota_sound [LevelOracle] {Γ : List Expr} {c : Name} {us : List Level} {ci : ConstInfo}
    {numParams numMotives numMinors numIndices : Nat} {rules : List RecRule}
    {args : List Expr} {major : Expr} {cj : Name} {usj : List Level}
    {cij : ConstInfo} {margs : List Expr} {rl : RecRule}
    {doms tys doms' tys' : List Expr} {numBefore majorIdx : Nat}
    {residual : Expr} {I : Name} {lsI : List Level} {rps ridx : List Expr}
    (hnB : numBefore = numParams + numMotives + numMinors)
    (hmI : majorIdx = numParams + numMotives + numMinors + numIndices)
    (hfind : env.find? c = some ci)
    (hkind : ci.kind = .recursor numParams numMotives numMinors numIndices rules)
    (hus : us.length = ci.lparams.length)
    (hlen : args.length = majorIdx + 1)
    (hpis : ci.type.hasPis (majorIdx + 1) = true)
    (hmaj : RedSem m φ Γ (args.getD majorIdx (Expr.bvar 0)) major)
    (hmeq : major = Expr.mkAppN (Expr.const cj usj) margs)
    (hrl : rl ∈ rules) (hctor : rl.ctor = cj)
    (hcij : env.find? cj = some cij)
    (husj : usj.length = cij.lparams.length)
    (hmlen : margs.length = numParams + rl.nfields)
    (hpis' : cij.type.hasPis (numParams + rl.nfields) = true)
    (hdoms : Expr.piDomains (ci.type.instL ci.lparams us) (args.take majorIdx ++ [major]) = some doms)
    (htys : tys.length = doms.length)
    (hI : ∀ p ∈ (args.take majorIdx ++ [major]).zip tys, InferSem m φ Γ p.1 p.2)
    (hD : ∀ p ∈ tys.zip doms, DefEqSem m φ Γ p.1 p.2)
    (hdoms' : Expr.piDomains (cij.type.instL cij.lparams usj) margs = some doms')
    (htys' : tys'.length = doms'.length)
    (hI' : ∀ p ∈ margs.zip tys', InferSem m φ Γ p.1 p.2)
    (hD' : ∀ p ∈ tys'.zip doms', DefEqSem m φ Γ p.1 p.2)
    (hlv : Level.eqList usj (us.drop (us.length - usj.length)) = true)
    (hP : ∀ p ∈ (margs.take numParams).zip (args.take numParams), DefEqSem m φ Γ p.1 p.2)
    (hres : Expr.piResidual (cij.type.instL cij.lparams usj) margs = some residual)
    (hshape : residual = Expr.mkAppN (Expr.const I lsI) (rps ++ ridx))
    (hrps : rps.length = numParams)
    (hX : ∀ p ∈ ridx.zip ((args.take majorIdx).drop numBefore), DefEqSem m φ Γ p.1 p.2) :
    RedSem m φ Γ (Expr.mkAppN (Expr.const c us) args)
      (Expr.mkAppN (rl.rhs.instL ci.lparams us) (args.take numBefore ++ margs.drop numParams)) := by
  intro ρ hs hw
  subst hnB hmI hmeq hctor
  -- every argument of the spine is well-denoted; the spine is `take ++ [major argument]`
  obtain ⟨-, hargs⟩ := WellDenoted_mkAppN hw
  have hsplit := List.take_append_getD (Expr.bvar 0) args _ hlen
  have hwmaj : WellDenoted m.M φ ρ
      (args.getD (numParams + numMotives + numMinors + numIndices) (Expr.bvar 0)) := by
    have hlt : numParams + numMotives + numMinors + numIndices < args.length := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact hargs _ (List.getElem_mem hlt)
  have hwxs : ∀ a ∈ args.take (numParams + numMotives + numMinors + numIndices),
      WellDenoted m.M φ ρ a :=
    fun a ha => hargs a (List.mem_of_mem_take ha)
  -- the reduced major: well-denoted, same denotation, a well-denoted constructor spine
  obtain ⟨hwmajor, hemaj⟩ := hmaj ρ hs hwmaj
  obtain ⟨-, hmargs⟩ := WellDenoted_mkAppN hwmajor
  -- the two telescope fits, from the certificates
  have hfit := teleFit_of_certs hs (m.type_ok c ci hfind φ ρ us hus).1
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact hwxs a ha
      · rw [List.mem_singleton.mp ha]; exact hwmajor)
    hdoms htys hI hD
  have hfit' := teleFit_of_certs hs (m.type_ok _ cij hcij φ ρ usj husj).1 hmargs
    hdoms' htys' hI' hD'
  -- the fits, on values
  have hmajv : interp m.M φ ρ (Expr.mkAppN (Expr.const rl.ctor usj) margs)
      = appList (m.M rl.ctor (usj.map (Level.eval φ))) (margs.map (interp m.M φ ρ)) := by
    rw [interp_mkAppN_appList, interp_const]
  have hfitV := teleFitV_of_teleFit m.M φ ρ
    (by
      rw [Expr.hasPis_instL]
      have : (args.take (numParams + numMotives + numMinors + numIndices)
          ++ [Expr.mkAppN (Expr.const rl.ctor usj) margs]).length
          = numParams + numMotives + numMinors + numIndices + 1 := by
        simp only [List.length_append, List.length_take, List.length_singleton, hlen]; omega
      rw [this]; exact hpis)
    hfit
  have hfitV' := teleFitV_of_teleFit m.M φ ρ
    (by rw [Expr.hasPis_instL, hmlen]; exact hpis') hfit'
  rw [List.map_append, List.map_singleton, hmajv] at hfitV
  -- the three comparisons, made semantic
  have hwres : WellDenoted m.M φ ρ residual :=
    WellDenoted_piResidual (m.type_ok _ cij hcij φ ρ usj husj).1 hmargs hfit' hres
  rw [hshape] at hwres
  obtain ⟨-, hwridx⟩ := WellDenoted_mkAppN hwres
  have hP' : (margs.map (interp m.M φ ρ)).take numParams
      = ((args.take (numParams + numMotives + numMinors + numIndices)).map
          (interp m.M φ ρ)).take numParams := by
    rw [← List.map_take, ← List.map_take, List.take_take, Nat.min_eq_left (by omega)]
    apply List.map_eq_of_zip
    · rw [List.length_take, List.length_take]; omega
    · intro p hp
      exact hP p hp ρ hs (hmargs _ (List.mem_of_mem_take (List.of_mem_zip hp).1))
        (hargs _ (List.mem_of_mem_take (List.of_mem_zip hp).2))
  have hXsem : ∀ p ∈ ridx.zip
      ((args.take (numParams + numMotives + numMinors + numIndices)).drop
        (numParams + numMotives + numMinors)),
      interp m.M φ ρ p.1 = interp m.M φ ρ p.2 := by
    intro p hp
    exact hX p hp ρ hs (hwridx _ (List.mem_append_right _ (List.of_mem_zip hp).1))
      (hwxs _ (List.mem_of_mem_drop (List.of_mem_zip hp).2))
  have hX' : ∀ (B : Expr) (ρ' : Nat → V) (I' : Name) (lsI' : List Level) (rps' ridx' : List Expr),
      piBodyV ρ (cij.type.instL cij.lparams usj) (margs.map (interp m.M φ ρ)) = some (B, ρ') →
      B = Expr.mkAppN (.const I' lsI') (rps' ++ ridx') → rps'.length = numParams →
      ∀ p ∈ (ridx'.map (interp m.M φ ρ')).zip
        (((args.take (numParams + numMotives + numMinors + numIndices)).map
          (interp m.M φ ρ)).drop (numParams + numMotives + numMinors)), p.1 = p.2 := by
    intro B ρ' I' lsI' rps' ridx' hB hBs hrps' p hp
    have hRB := piResidual_of_piBodyV m.M φ ρ hres hB
    rw [hshape, hBs, Expr.instChain_mkAppN, Expr.instChain_const] at hRB
    obtain ⟨-, -, hargs_eq⟩ := Expr.mkAppN_const_inj hRB
    rw [List.map_append] at hargs_eq
    have hridx : ridx = ridx'.map (Expr.instChain · margs) :=
      List.append_inj_right hargs_eq (by simp [hrps, hrps'])
    rw [piBodyV_env hB] at hp
    have hmap : ridx'.map (interp m.M φ (consList (margs.map (interp m.M φ ρ)).reverse ρ))
        = ridx.map (interp m.M φ ρ) := by
      rw [hridx, List.map_map]
      apply List.map_congr_left
      intro r _
      simp [Function.comp, interp_instChain]
    rw [hmap, ← List.map_drop, List.zip_map] at hp
    obtain ⟨⟨r, x⟩, hrx, rfl⟩ := List.mem_map.mp hp
    exact hXsem (r, x) hrx
  -- the environment's ι law
  obtain ⟨heq, hwrhs, hspine⟩ := m.rec_rules c ci numParams numMotives numMinors numIndices rules
    hfind hkind rl hrl cij hcij φ ρ us usj _ _ hus husj
    (by simp only [List.length_map, List.length_take, hlen]; omega) (by simp [hmlen])
    hfitV hfitV' ((Level.eqList_iff _ _).mp hlv φ) hP' hX'
  have hvals : (args.take (numParams + numMotives + numMinors) ++ margs.drop numParams).map
        (interp m.M φ ρ)
      = ((args.take (numParams + numMotives + numMinors + numIndices)).map
          (interp m.M φ ρ)).take (numParams + numMotives + numMinors)
        ++ (margs.map (interp m.M φ ρ)).drop numParams := by
    rw [List.map_append, ← List.map_take, ← List.map_drop, List.take_take,
      Nat.min_eq_left (by omega)]
  refine ⟨?_, ?_⟩
  · apply WellDenoted_mkAppN_of_spineOk m.M φ ρ hwrhs
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hargs a (List.mem_of_mem_take ha)
      · exact hmargs a (List.mem_of_mem_drop ha)
    · rw [hvals]; exact hspine
  · conv => lhs; rw [hsplit]
    rw [interp_mkAppN_appList, interp_mkAppN_appList, hvals, interp_const, List.map_append,
      List.map_singleton, hemaj, hmajv]
    exact heq

end Red

/-! ## Definitional equality -/

namespace DefEq

theorem refl_sound {Γ : List Expr} {a : Expr} : DefEqSem m φ Γ a a :=
  fun _ _ _ _ => rfl

theorem symm_sound {Γ : List Expr} {a b : Expr} (h : DefEqSem m φ Γ a b) :
    DefEqSem m φ Γ b a :=
  fun ρ hs hb ha => (h ρ hs ha hb).symm

/-- Reduce, then continue: the reduct is well-denoted with the same
denotation, so the continuation applies to it.  (This is exactly what
a `trans` rule could not do: its middle term's invariant has no
supplier.) -/
theorem redL_sound {Γ : List Expr} {a a' b : Expr}
    (hr : RedSem m φ Γ a a') (h : DefEqSem m φ Γ a' b) : DefEqSem m φ Γ a b := by
  intro ρ hs ha hb
  obtain ⟨ha', he⟩ := hr ρ hs ha
  exact he.trans (h ρ hs ha' hb)

theorem sort_sound [LevelOracle] {Γ : List Expr} {u v : Level} (h : LevelOracle.eq u v = true) :
    DefEqSem m φ Γ (Expr.sort u) (Expr.sort v) :=
  fun _ _ _ _ => by simp [eval_eq_of_oracle h]

theorem const_sound [LevelOracle] {Γ : List Expr} {c : Name} {ls ls' : List Level}
    (h : Level.eqList ls ls' = true) : DefEqSem m φ Γ (Expr.const c ls) (Expr.const c ls') :=
  fun _ _ _ _ => by simp [(Level.eqList_iff ls ls').mp h φ]

theorem pi_sound {Γ : List Expr} {A₁ B₁ A₂ B₂ : Expr} {pw : PropWhen}
    (hA : DefEqSem m φ Γ A₁ A₂) (hB : DefEqSem m φ (A₂ :: Γ) B₁ B₂) :
    DefEqSem m φ Γ (Expr.pi A₁ pw B₁) (Expr.pi A₂ pw B₂) := by
  intro ρ hs h₁ h₂
  rw [WellDenoted_pi] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1
  simp only [interp_pi]
  rw [heA]
  apply piR_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
  exact hB (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂.1, hx⟩) (h₁.2.1 x hx₁) (h₂.2.1 x hx)

theorem lam_sound {Γ : List Expr} {A₁ b₁ A₂ b₂ : Expr} {pw : PropWhen}
    (hA : DefEqSem m φ Γ A₁ A₂) (hb : DefEqSem m φ (A₂ :: Γ) b₁ b₂) :
    DefEqSem m φ Γ (Expr.lam A₁ pw b₁) (Expr.lam A₂ pw b₂) := by
  intro ρ hs h₁ h₂
  rw [WellDenoted_lam] at h₁ h₂
  have heA := hA ρ hs h₁.1 h₂.1
  simp only [interp_lam]
  rw [heA]
  apply lamR_congr
  intro x hx
  have hx₁ : x ∈ˢ interp m.M φ ρ A₁ := by rw [heA]; exact hx
  exact hb (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, h₂.1, hx⟩) (h₁.2.1 x hx₁) (h₂.2.1 x hx)

theorem app_sound {Γ : List Expr} {f₁ a₁ f₂ a₂ : Expr}
    (hf : DefEqSem m φ Γ f₁ f₂) (ha : DefEqSem m φ Γ a₁ a₂) :
    DefEqSem m φ Γ (Expr.app f₁ a₁) (Expr.app f₂ a₂) := by
  intro ρ hs h₁ h₂
  rw [WellDenoted_app] at h₁ h₂
  simp only [interp_app]
  rw [hf ρ hs h₁.1 h₂.1, ha ρ hs h₁.2.1 h₂.2.1]

/-- **η is sound.**  `b`'s type reduces to a `∀` over `A₂`, so `⟦b⟧`
is a member of the product `piR p ⟦A₂⟧ …` at the annotation's regime
`p`.  Under the binder, the λ's body denotes `app ⟦b⟧ x` for every
`x` in the domain (the `DefEq` premise, at a well-denoted
`app (lift b) (Expr.bvar 0)`), so the λ denotes `lamR p ⟦A₂⟧ (Expr.app ⟦b⟧ ·)`,
which is `⟦b⟧` by the library's η (`lamR_eta`) — at a proposition,
because both are the point. -/
theorem eta_sound {Γ : List Expr} {A₁ b₁ b tb A₂ B : Expr} {pw : PropWhen}
    (htb : InferSem m φ Γ b tb) (hr : RedSem m φ Γ tb (Expr.pi A₂ pw B))
    (hA : DefEqSem m φ Γ A₂ A₁)
    (hbody : DefEqSem m φ (A₁ :: Γ) b₁ (Expr.app (b.liftN 1) (Expr.bvar 0))) :
    DefEqSem m φ Γ (Expr.lam A₁ pw b₁) b := by
  intro ρ hs hlam hwb
  -- `⟦b⟧` is a member of the product its type reduces to
  obtain ⟨-, hwtb, hmemb⟩ := htb ρ hs
  obtain ⟨hwpi, hepi⟩ := hr ρ hs hwtb
  rw [hepi, interp_pi] at hmemb
  rw [WellDenoted_pi] at hwpi
  rw [WellDenoted_lam] at hlam
  have heA : interp m.M φ ρ A₂ = interp m.M φ ρ A₁ := hA ρ hs hwpi.1 hlam.1
  -- the lifted `b` under the binder is `b`
  have hsh : ∀ x, shiftE 1 0 (cons x ρ) = ρ := by
    intro x; funext i; simp [shiftE]
  have hlift : ∀ x, interp m.M φ (cons x ρ) (b.liftN 1) = interp m.M φ ρ b := by
    intro x
    rw [interp_liftN, hsh]
  -- the body, pointwise, is `b` applied
  have hpt : ∀ x, x ∈ˢ interp m.M φ ρ A₁ →
      interp m.M φ (cons x ρ) b₁ = SetLib.app (interp m.M φ ρ b) x := by
    intro x hx
    have hx₂ : x ∈ˢ interp m.M φ ρ A₂ := by rw [heA]; exact hx
    have happ : WellDenoted m.M φ (cons x ρ) (Expr.app (b.liftN 1) (Expr.bvar 0)) := by
      rw [WellDenoted_app]
      refine ⟨(WellDenoted_liftN m.M φ 1 b 0 (cons x ρ)).mpr ?_, trivial,
        pw.holds φ, interp m.M φ ρ A₂, fun y => interp m.M φ (cons y ρ) B, ?_, hx₂, hwpi.2.2⟩
      · rw [hsh]; exact hwb
      · rw [hlift]; exact hmemb
    have := hbody (cons x ρ) ((Sat_cons m.M φ).mpr ⟨hs, hlam.1, hx⟩) (hlam.2.1 x hx) happ
    rw [this, interp_app, interp_bvar, cons_zero, hlift]
  -- η in the model
  rw [interp_lam, lamR_congr hpt, ← heA]
  exact lamR_eta hmemb

/-- A term whose type has sort `Prop` denotes the point. -/
theorem eq_pt_of_prop [LevelOracle] {Γ : List Expr} {a ta tta : Expr} {u : Level}
    (hta : InferSem m φ Γ a ta) (htta : InferSem m φ Γ ta tta)
    (hu : RedSem m φ Γ tta (Expr.sort u)) (hu0 : LevelOracle.eq u .zero = true)
    (ρ : Nat → V) (hs : Sat m.M φ Γ ρ) : interp m.M φ ρ a = pt := by
  obtain ⟨-, hwta, hmem⟩ := hta ρ hs
  obtain ⟨-, hwtta, hmem₂⟩ := htta ρ hs
  obtain ⟨-, heq⟩ := hu ρ hs hwtta
  rw [heq, interp_sort, eval_eq_of_oracle hu0, Level.eval_zero] at hmem₂
  exact eq_pt_of_mem_univ_zero hmem₂ hmem

/-- **Proof irrelevance is sound, for free.**  Each side's type has
sort `Prop`, so each side's denotation is a member of a truth value,
hence the point; the two types are never compared, and need not be. -/
theorem proofIrrel_sound [LevelOracle] {Γ : List Expr} {a ta tta b tb ttb : Expr} {u v : Level}
    (hta : InferSem m φ Γ a ta) (htta : InferSem m φ Γ ta tta)
    (hu : RedSem m φ Γ tta (Expr.sort u)) (hu0 : LevelOracle.eq u .zero = true)
    (htb : InferSem m φ Γ b tb) (httb : InferSem m φ Γ tb ttb)
    (hv : RedSem m φ Γ ttb (Expr.sort v)) (hv0 : LevelOracle.eq v .zero = true) :
    DefEqSem m φ Γ a b := by
  intro ρ hs _ _
  rw [eq_pt_of_prop hta htta hu hu0 ρ hs, eq_pt_of_prop htb httb hv hv0 ρ hs]

end DefEq

/-! ## Inference -/

namespace Infer

theorem bvar_sound {Γ : List Expr} {i : Nat} {A : Expr} (h : Γ[i]? = some A) :
    InferSem m φ Γ (Expr.bvar i) (A.liftN (i + 1)) := by
  intro ρ hs
  obtain ⟨hw, hmem⟩ := Sat_get m.M φ hs h
  refine ⟨trivial, ?_, ?_⟩
  · rw [WellDenoted_liftN]; exact hw
  · rw [interp_bvar, interp_liftN]; exact hmem

theorem sort_sound {Γ : List Expr} {u : Level} :
    InferSem m φ Γ (Expr.sort u) (Expr.sort (.succ u)) :=
  fun _ _ => ⟨trivial, trivial, by simp only [interp_sort, Level.eval_succ]; exact univ_mem_succ _⟩

theorem const_sound {Γ : List Expr} {c : Name} {ls : List Level} {ci : ConstInfo}
    (hfind : env.find? c = some ci) (hls : ls.length = ci.lparams.length) :
    InferSem m φ Γ (Expr.const c ls) (ci.type.instL ci.lparams ls) := by
  intro ρ _
  obtain ⟨hw, hmem⟩ := m.type_ok c ci hfind φ ρ ls hls
  exact ⟨trivial, hw, hmem⟩

/-- **`∀`-formation.**  The body denotes a member of `univ (eval v)` at
every point of the domain; the annotation is `zeroness v`, so it
reads `true` exactly when `eval v = 0` — which is exactly when the
product is a truth value (in `univ 0`, impredicatively, whatever the
domain) and when `imax u v` is `0`.  Above `0` the product is a graph
space in `univ (max u v)` by the library's closure law. -/
theorem pi_sound {Γ : List Expr} {A B s t : Expr} {u v : Level} {pw : PropWhen}
    (hA : InferSem m φ Γ A s) (hu : RedSem m φ Γ s (Expr.sort u))
    (hB : InferSem m φ (A :: Γ) B t) (hv : RedSem m φ (A :: Γ) t (Expr.sort v))
    (hz : Level.zeroness v = pw) :
    InferSem m φ Γ (Expr.pi A pw B) (Expr.sort (.imax u v)) := by
  intro ρ hs
  obtain ⟨hwA, hws, hmemA⟩ := hA ρ hs
  obtain ⟨-, hes⟩ := hu ρ hs hws
  rw [hes, interp_sort] at hmemA
  have hbody : ∀ x, x ∈ˢ interp m.M φ ρ A →
      WellDenoted m.M φ (cons x ρ) B ∧ interp m.M φ (cons x ρ) B ∈ˢ univ (Level.eval φ v) := by
    intro x hx
    have hs' : Sat m.M φ (A :: Γ) (cons x ρ) := (Sat_cons m.M φ).mpr ⟨hs, hwA, hx⟩
    obtain ⟨hwB, hwt, hmemB⟩ := hB (cons x ρ) hs'
    obtain ⟨-, het⟩ := hv (cons x ρ) hs' hwt
    rw [het, interp_sort] at hmemB
    exact ⟨hwB, hmemB⟩
  have hzero := holds_of_zeroness (φ := φ) hz
  refine ⟨?_, trivial, ?_⟩
  · rw [WellDenoted_pi]
    refine ⟨hwA, fun x hx => (hbody x hx).1, fun hp x hx => ?_⟩
    have := (hbody x hx).2
    rwa [hzero.mp hp] at this
  · rw [interp_pi, interp_sort, Level.eval_imax]
    by_cases h0 : Level.eval φ v = 0
    · rw [hzero.mpr h0, (Level.imaxNat_eq_zero_iff _ _).mpr h0]
      exact piR_true_mem_univ_zero
    · have hp : pw.holds φ = false := by
        cases hh : pw.holds φ
        · rfl
        · exact absurd (hzero.mp hh) h0
      rw [hp, Level.imaxNat_of_ne_zero h0]
      refine piR_false_mem_univ (by omega) (univ_mono (Nat.le_max_left _ _) hmemA) ?_
      intro x hx
      exact univ_mono (Nat.le_max_right _ _) (hbody x hx).2

/-- **λ.**  The body is inferred under the domain, so the λ's fibres
are the body type's denotations and the λ is a member of the `∀`;
the annotation is checked against the body type's sort `v`, which
makes the λ's clause and the `∀`'s clause of the invariant true.  The
premise that the domain's type is a sort is the checker's, not the
proof's: nothing here uses it. -/
theorem lam_sound {Γ : List Expr} {A b s bt btt : Expr} {u v : Level} {pw : PropWhen}
    (hA : InferSem m φ Γ A s) (_hu : RedSem m φ Γ s (Expr.sort u))
    (hb : InferSem m φ (A :: Γ) b bt)
    (hbt : InferSem m φ (A :: Γ) bt btt) (hv : RedSem m φ (A :: Γ) btt (Expr.sort v))
    (hz : Level.zeroness v = pw) :
    InferSem m φ Γ (Expr.lam A pw b) (Expr.pi A pw bt) := by
  intro ρ hs
  obtain ⟨hwA, -, -⟩ := hA ρ hs
  have hbody : ∀ x, x ∈ˢ interp m.M φ ρ A →
      WellDenoted m.M φ (cons x ρ) b ∧ WellDenoted m.M φ (cons x ρ) bt ∧
      interp m.M φ (cons x ρ) b ∈ˢ interp m.M φ (cons x ρ) bt ∧
      interp m.M φ (cons x ρ) bt ∈ˢ univ (Level.eval φ v) := by
    intro x hx
    have hs' : Sat m.M φ (A :: Γ) (cons x ρ) := (Sat_cons m.M φ).mpr ⟨hs, hwA, hx⟩
    obtain ⟨hwb, hwbt, hmemb⟩ := hb (cons x ρ) hs'
    obtain ⟨-, hwbtt, hmembt⟩ := hbt (cons x ρ) hs'
    obtain ⟨-, hebtt⟩ := hv (cons x ρ) hs' hwbtt
    rw [hebtt, interp_sort] at hmembt
    exact ⟨hwb, hwbt, hmemb, hmembt⟩
  have hzero := holds_of_zeroness (φ := φ) hz
  have hpi : WellDenoted m.M φ ρ (Expr.pi A pw bt) := by
    rw [WellDenoted_pi]
    refine ⟨hwA, fun x hx => (hbody x hx).2.1, fun hp x hx => ?_⟩
    have := (hbody x hx).2.2.2
    rwa [hzero.mp hp] at this
  refine ⟨?_, hpi, ?_⟩
  · rw [WellDenoted_lam]
    refine ⟨hwA, fun x hx => (hbody x hx).1, fun x => interp m.M φ (cons x ρ) bt,
      fun x hx => (hbody x hx).2.2.1, fun hp x hx => ?_⟩
    have := (hbody x hx).2.2.2
    rwa [hzero.mp hp] at this
  · rw [interp_lam, interp_pi]
    exact lamR_mem fun x hx => (hbody x hx).2.2.1

/-- **Application — no Π-injectivity needed.**  The head's type
reduces to a `∀`, whose denotation *is* a product with the head's
denotation a member; the argument's type is definitionally equal to
the domain, so its denotation is in the domain; elimination in the
model gives the membership in the fibre, which is the instantiated
codomain's denotation by the β-substitution lemma.  Equality flows
from "the checker accepted" to "the denotations are equal", never
back, so nothing has to be inverted. -/
theorem app_sound {Γ : List Expr} {f a tf A B ta : Expr} {pw : PropWhen}
    (hf : InferSem m φ Γ f tf) (hr : RedSem m φ Γ tf (Expr.pi A pw B))
    (ha : InferSem m φ Γ a ta) (hd : DefEqSem m φ Γ ta A) :
    InferSem m φ Γ (Expr.app f a) (B.inst a) := by
  intro ρ hs
  obtain ⟨hwf, hwtf, hmemf⟩ := hf ρ hs
  obtain ⟨hwpi, hepi⟩ := hr ρ hs hwtf
  rw [hepi] at hmemf
  obtain ⟨hwa, hwta, hmema⟩ := ha ρ hs
  have hwpi' := hwpi
  rw [WellDenoted_pi] at hwpi'
  rw [hd ρ hs hwta hwpi'.1] at hmema
  refine ⟨WellDenoted_app_of m.M φ hwf hwa hwpi hmemf hmema,
    (WellDenoted_inst0 m.M φ hwa).mpr (hwpi'.2.1 _ hmema), ?_⟩
  rw [interp_app, interp_inst0]
  rw [interp_pi] at hmemf
  exact app_mem_piR hmemf hmema hwpi'.2.2

end Infer

/-! ## The master induction -/

mutual

/-- Every reduction is sound. -/
theorem red_sound [LevelOracle] : ∀ {Γ : List Expr} {e e' : Expr}, Red env Γ e e' → RedSem m φ Γ e e'
  | _, _, _, .refl => Red.refl_sound
  | _, _, _, .trans h₁ h₂ => Red.trans_sound (red_sound h₁) (red_sound h₂)
  | _, _, _, .appFn h => Red.appFn_sound (red_sound h)
  | _, _, _, .betaGate => Red.betaGate_sound
  | _, _, _, .beta hta hd => Red.beta_sound (infer_sound hta) (defeq_sound hd)
  | _, _, _, .delta hfind hv hls => Red.delta_sound hfind hv hls
  | _, _, _, .iota hfind hkind hus hlen hpis hmaj hmeq hrl hctor hcij husj hmlen hpis' hdoms htys
      hI hD hdoms' htys' hI' hD' hlv hP hres hshape hrps hX =>
    Red.iota_sound rfl rfl hfind hkind hus hlen hpis (red_sound hmaj) hmeq hrl hctor hcij husj
      hmlen hpis' hdoms htys (fun p hp => infer_sound (hI p hp)) (fun p hp => defeq_sound (hD p hp))
      hdoms' htys' (fun p hp => infer_sound (hI' p hp)) (fun p hp => defeq_sound (hD' p hp))
      hlv (fun p hp => defeq_sound (hP p hp)) hres hshape hrps
      (fun p hp => defeq_sound (hX p hp))

/-- Every definitional-equality verdict is sound. -/
theorem defeq_sound [LevelOracle] : ∀ {Γ : List Expr} {a b : Expr}, DefEq env Γ a b → DefEqSem m φ Γ a b
  | _, _, _, .refl => DefEq.refl_sound
  | _, _, _, .symm h => DefEq.symm_sound (defeq_sound h)
  | _, _, _, .redL hr h => DefEq.redL_sound (red_sound hr) (defeq_sound h)
  | _, _, _, .sort h => DefEq.sort_sound h
  | _, _, _, .const h => DefEq.const_sound h
  | _, _, _, .pi hA hB => DefEq.pi_sound (defeq_sound hA) (defeq_sound hB)
  | _, _, _, .lam hA hb => DefEq.lam_sound (defeq_sound hA) (defeq_sound hb)
  | _, _, _, .app hf ha => DefEq.app_sound (defeq_sound hf) (defeq_sound ha)
  | _, _, _, .eta htb hr hA hbody =>
    DefEq.eta_sound (infer_sound htb) (red_sound hr) (defeq_sound hA) (defeq_sound hbody)
  | _, _, _, .proofIrrel hta htta hu hu0 htb httb hv hv0 =>
    DefEq.proofIrrel_sound (infer_sound hta) (infer_sound htta) (red_sound hu) hu0
      (infer_sound htb) (infer_sound httb) (red_sound hv) hv0

/-- Every inference is sound. -/
theorem infer_sound [LevelOracle] : ∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T → InferSem m φ Γ e T
  | _, _, _, .bvar h => Infer.bvar_sound h
  | _, _, _, .sort => Infer.sort_sound
  | _, _, _, .const hfind hls => Infer.const_sound hfind hls
  | _, _, _, .pi hA hu hB hv hz =>
    Infer.pi_sound (infer_sound hA) (red_sound hu) (infer_sound hB) (red_sound hv) hz
  | _, _, _, .lam hA hu hb hbt hv hz =>
    Infer.lam_sound (infer_sound hA) (red_sound hu) (infer_sound hb) (infer_sound hbt)
      (red_sound hv) hz
  | _, _, _, .app hf hr ha hd =>
    Infer.app_sound (infer_sound hf) (red_sound hr) (infer_sound ha) (defeq_sound hd)

end

/-! ## The theorem -/

/-- **Soundness of the fragment.**  At every model of the environment
and every valuation: a reduction of a well-denoted term keeps its
denotation and the invariant; two well-denoted terms the checker calls
definitionally equal have equal denotations; an inferred term and its
type are well-denoted, and the term's denotation is a member of the
type's. -/
theorem soundness [LevelOracle] (m : EnvModel V env) (φ : Name → Nat) :
    (∀ {Γ : List Expr} {e e' : Expr}, Red env Γ e e' → RedSem m φ Γ e e') ∧
    (∀ {Γ : List Expr} {a b : Expr}, DefEq env Γ a b → DefEqSem m φ Γ a b) ∧
    (∀ {Γ : List Expr} {e T : Expr}, Infer env Γ e T → InferSem m φ Γ e T) :=
  ⟨red_sound, defeq_sound, infer_sound⟩

/-- **The closed corollary**: a closed term the checker types is a
member of its type, under every model, valuation and environment. -/
theorem closed_infer [LevelOracle] (m : EnvModel V env) (φ : Name → Nat) {e T : Expr}
    (h : Infer env [] e T) (ρ : Nat → V) :
    interp m.M φ ρ e ∈ˢ interp m.M φ ρ T :=
  (infer_sound h ρ (Sat_nil m.M φ ρ)).2.2

end Fragment
