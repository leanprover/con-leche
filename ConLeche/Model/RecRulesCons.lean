module

public import ConLeche.Model.Caps

public section

/-!
# The fired iota contract across a fresh cons (task #161, iota
tier)

`recRules_cons_fresh`, the obligation every value-kind harvest
discharges for the new `EnvModelM` field `rec_rules`.  The statements
live in `Env/EnvModelM.lean` beside `CapsOk` (the field must mention
them); this is the preservation half, `capsOk_cons_fresh`'s sibling.

## Every crossing is FORWARD; no equality-form transfer

The law's reading *premises* (`TVa`, `TVja`, and the `.nested` clause's
`vpa`) need not move **backward** across the cons (and `LitGuardsAgree`
is refutable at a value-kind cons: a `def` named `String.ofList`
completes string support and flips the `str` half).

What makes the backward direction unnecessary is that the readings
sit in *premise* position, so the transfer they need is contravariant:

* `TVa`/`TVja` are ∀-bound premises, so instead of moving the given
  extension reading down, the proof produces the **prefix** reading
  from `EnvModelM.constType`, moves *that* forward
  (`denote_cons_mono`), and identifies the two by determinism —
  the `type_reads`/`type_wellDenotedTy` idiom `declStep_preserves_of_cons` already uses
  three times;
* the `.nested` clause is itself a premise, so proving the prefix form
  of it *consumes* the extension form: a prefix pin reading is moved
  **forward** and fed to the hypothesis in hand.

So the whole preservation runs on `denote_cons_mono`, the only
crossing the campaign has ever shown to hold, and no literal-tier
premise appears — matching what the literal tier's seal established
for the harvests.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env}

/-- The reverse opening introduces no constants, so it preserves
prefix-boundedness (its opener annotations are `.sort .zero`). -/
theorem constsBound_openRev {env₀ : Env} {e : Expr}
    (h : ConstsBound env₀ e) :
    ∀ d n : Nat, ConstsBound env₀ (openRev d n e) := by
  intro d n
  induction n with
  | zero => exact h
  | succ n ih =>
    show ConstsBound env₀ ((openRev d n e).instantiate1
      (.fvar (d + n) (.sort .zero)) 0)
    exact ConstsBound.instantiate1 (by simp) _ 0 ih

/-- **(S)'s `iotaCtorNeverProp` guard is the prefix's**: it reads
`find?` only at the constructor's result family, and that name is
stored whenever the constructor's type resolves — guaranteed here by
`ConstWF` (`EnvModel.wf`) — so any lookup agreeing with the prefix's on
stored names reads it alike. -/
theorem iotaCtorNeverProp_of_agree {env env' : Env}
    (hag : ∀ n, (env.find? n).isSome = true → env'.find? n = env.find? n)
    {cvj : ConstantVal} {usj : List Level}
    (hT : ∀ T us, cvj.type.piResult.getAppFn = .const T us →
      (env.find? T).isSome = true) :
    ConLeche.iotaCtorNeverProp env'.find? cvj usj
      = ConLeche.iotaCtorNeverProp env.find? cvj usj := by
  unfold ConLeche.iotaCtorNeverProp
  match hh : cvj.type.piResult.getAppFn with
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl
  | .const T us =>
    dsimp only
    rw [hag T (hT T us hh)]

/-- **`RecRuleExtra` survives a fresh cons that is not itself a
recursor** (task #342 L10 cons sub-lane): `recRuleLaw_cons_prefix`'s
sibling for the `RecRuleExtra` conjunct.  Every lookup is a prefix
lookup — the environment invariant, not the cons's kind, gives the
rule's constructor stored (`EnvModel.rec_ctors`) — every reading
premise is produced at the prefix and moved FORWARD by
`denote_cons_mono`, and the two leaves the clauses mention
(`acval n`, `acval rl.ctor`) are the prefix's by `acvalWith_ne`.  New
here: the K clause's `∀ Ra` is identified with the main law's own `Ra`
the same way; the arity clause is syntactic, hence untouched; clause
(S)'s `iotaCtorNeverProp` guard, read at the extended environment's
`find?`, agrees with the prefix's reading because it consults `find?`
only at the constructor's result family — a name the constructor's
(resolving) stored type names, hence itself stored, hence not the
fresh one (`iotaCtorNeverProp_cons_of_isSome`). -/
theorem recRuleExtra_ext (mp : EnvModelM V env) {env' : Env}
    {m₂ : EnvModel V env'} (hx : ModelExt mp env' m₂.acval)
    (φ : Name → Nat) {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule}
    (hfE : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) :
    RecRuleExtra m₂ φ n cv mI rP rl := by
  obtain ⟨-, hlaw0, hextra⟩ := mp.rec_rules φ n cv mI rP rules hfE rl hmem
  obtain ⟨⟨cvj', cnP', cnF', hst⟩, -, -⟩ :=
    mp.base2.rec_ctors n cv mI rP rules hfE rl hmem
  have hsC : (env.find? (RecRule.ctor rl)).isSome = true := by rw [hst]; rfl
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP rules rfl rl hmem
  intro us hlen TVa hTVa
  obtain ⟨TVa', hTVa', -, -⟩ := mp.constType 0 n _ us hfE (by exact hlen)
  obtain rfl : TVa' = TVa := by
    refine Option.some.inj (Eq.trans ?_ hTVa)
    exact (hx.denote
      (constsBound_instType mp.base2.wf
        (ConLeche.Env.find?_mem hfE) us) hTVa').symm
  have hpinCB : ∀ lvls pins, RecRule.fire rl = .nested lvls pins → ∀ i : Nat,
      ConstsBound env (ConLeche.Verify.openRev 0 rP
        ((pins.getD i default).instantiateLevelParams cv.levelParams us)) := by
    intro lvls pins hfr' i
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hfr'
    refine constsBound_openRev (constsBound_of_constsResolve _ ?_) 0 rP
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
    by_cases hilt : i < pins.length
    · exact (hpinsWf _ (ConLeche.getD_mem hilt)).2.2.1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  obtain ⟨hK, hCtor⟩ := hextra us hlen TVa' hTVa'
  refine ⟨?_, ?_⟩
  · intro hk
    obtain ⟨hnf, hRalaw⟩ := hK hk
    refine ⟨hnf, fun Ra hRa ρ xs a restR hxl hfit => ?_⟩
    obtain ⟨Ra', hRa0', -, -, -⟩ := hlaw0 us hlen
    obtain rfl : Ra' = Ra := by
      refine Option.some.inj (Eq.trans ?_ hRa)
      exact (hx.denote
        (constsBound_of_constsResolve _ (by
          rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
          exact hRres)) hRa0').symm
    rw [hx.leafOf hfE]
    exact hRalaw Ra' hRa0' ρ xs a restR hxl hfit
  · intro cvj cnP cnF hfcj
    have hfcjE : env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) :=
      hx.back hsC hfcj
    obtain ⟨harity, hnk⟩ := hCtor cvj cnP cnF hfcjE
    refine ⟨harity, ?_⟩
    intro hk
    -- a constructor type's reading at the cons is the prefix's
    have hTVjaOf : ∀ usj : List Level, usj.length = cvj.levelParams.length →
        ∀ TVja : Term, denote m₂.acval env' φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
        denote mp.base2.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja := by
      intro usj husj TVja hTVja
      obtain ⟨TVja', hTVja', -, -⟩ :=
        mp.constType 0 (RecRule.ctor rl) _ usj hfcjE (by exact husj)
      obtain rfl : TVja' = TVja := by
        refine Option.some.inj (Eq.trans ?_ hTVja)
        exact (hx.denote
          (constsBound_instType mp.base2.wf
            (ConLeche.Env.find?_mem hfcjE) usj) hTVja').symm
      exact hTVja'
    have hTVjaTo : ∀ usj : List Level, ∀ TVja : Term,
        denote mp.base2.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
        denote m₂.acval env' φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja := by
      intro usj TVja hTVja
      exact hx.denote
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfcjE) usj) hTVja
    -- (S)/(T)'s `iotaCtorNeverProp` guard is the prefix's
    have hlicE : ∀ lvs : List Level,
        ConLeche.iotaCtorNeverProp env'.find? cvj lvs
          = ConLeche.iotaCtorNeverProp env.find? cvj lvs := by
      intro lvs
      obtain ⟨-, -, hresolve, -, -, -, -⟩ :=
        mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfcjE)
      dsimp only [ConLeche.ConstantInfo.toConstantVal] at hresolve
      have hTiso : ∀ T us', cvj.type.piResult.getAppFn = .const T us' →
          (env.find? T).isSome = true :=
        fun T us' heq' =>
          ConLeche.Expr.find?_isSome_of_piResult_getAppFn_const hresolve heq'
      exact iotaCtorNeverProp_of_agree hx.agree hTiso
    obtain ⟨hS, hT, hPU⟩ := hnk hk
    refine ⟨fun hlic => hS (by rwa [hlicE] at hlic), ?_, ?_⟩
    · intro hlic usj husj TVja hTVja ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hne
      rw [hlicE] at hlic
      have hTVja0 := hTVjaOf usj husj TVja hTVja
      rw [hx.leafOf hst] at hfitR hne
      obtain ⟨usj', ys', TVja', restC', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        hT hlic usj husj TVja hTVja0 ρ xs ys restR restC hxl hyl
          hfitR hfitC hxwd hywd hne
      refine ⟨usj', ys', TVja', restC', h1, h2, hTVjaTo usj' TVja' h3, h4, h5, h6, h7, ?_⟩
      rw [hx.leafOf hst]
      exact h8
    intro usj husj heq TVja hTVja
    have hTVja' := hTVjaOf usj husj TVja hTVja
    obtain ⟨hP, hU⟩ := hPU usj husj heq TVja hTVja'
    refine ⟨?_, ?_⟩
    · intro ρ xs a restR hxl hfit hapt ys restC hfitC
      rw [hx.leafOf hst]
      exact hP ρ xs a restR hxl hfit hapt ys restC hfitC
    · intro ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hplain0 hnested0 hpin0
      have hnested' : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          interp V ρ (Term.mkAppN
            (mp.base2.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          ∀ i, i < RecRule.ctorParams rl →
          ∀ vpa : Term,
            denote mp.base2.acval env φ rP
              (ConLeche.Verify.openRev 0 rP ((pins.getD i default).instantiateLevelParams
                cv.levelParams us)) = some vpa →
            interp V ρ (ys.getD i default) ≠ pt →
            interp V ρ (Term.instRevChain (xs.take rP) vpa) ≠ pt →
            interp V ρ (ys.getD i default)
              = interp V ρ (Term.instRevChain (xs.take rP) vpa) := by
        intro lvls pins hfr' hpt i hi vpa hvpa hney hnex
        refine hnested0 lvls pins hfr' (by rw [hx.leafOf hst]; exact hpt) i hi vpa ?_
          hney hnex
        exact hx.denote
          (hpinCB lvls pins hfr' i) hvpa
      rw [hx.leafOf hst] at hfitR hplain0 hpin0 ⊢
      exact hU ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hplain0 hnested' hpin0

/-- **The fired iota contract survives a fresh cons that is
not itself a recursor.**

The recursor disequality is the cons's kind.  The *constructor*
disequality needs no premise: `EnvModel.rec_ctors` (`RecCtorsStored`)
says every stored recursor rule's constructor is itself **stored**, and
the cons is fresh — so `RecRule.ctor rl ≠ c₀.name` follows from the
environment invariant rather than from the cons's kind.  That is what
lets the **basis** tier use this lemma at its `indInfo`/`ctorInfo`
conses, where a kind premise would be false.

A recursor cons with rules still establishes its *own* rules bespoke —
that is the firing-law work, not a transport.  A recursor cons with
**no** rules (`Empty.rec`) transports here unchanged, which is why the
premise is `rules = []` rather than "not a recursor". -/
theorem recRuleLaw_ext (mp : EnvModelM V env) {env' : Env}
    {m₂ : EnvModel V env'} (hx : ModelExt mp env' m₂.acval)
    (φ : Name → Nat) {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule}
    (hfE : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) :
    RecRuleLaw m₂ φ n cv mI rP rl := by
  obtain ⟨hrPle, hlaw0, hextra⟩ := mp.rec_rules φ n cv mI rP rules hfE rl hmem
  refine ⟨hrPle, fun us hlen => ?_, recRuleExtra_ext mp hx φ hfE hmem⟩
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hlen
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mp.base2.wf.consts _ (ConLeche.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP rules rfl rl hmem
  refine ⟨Ra, ?_, hokRa, ?_, ?_⟩
  · exact hx.denote
      (constsBound_of_constsResolve _ (by
        rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
        exact hRres)) hRa0
  · -- the pins' carried readings, moved forward (the iota seal's
    -- ratified repair: the grading conjunct in the ∃-form crosses
    -- exactly as `Ra`'s does)
    intro lvls pins hn i hi
    obtain ⟨vpa, hvpa, hok⟩ := hpinsOk lvls pins hn i hi
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
    have hpinCR : ConLeche.Expr.constsResolve env (pins.getD i default)
        = true := by
      by_cases hilt : i < pins.length
      · obtain ⟨-, -, hres, -⟩ := hpinsWf _ (ConLeche.getD_mem hilt)
        exact hres
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
    refine ⟨vpa, ?_, ?_⟩
    · exact hx.denote
        (constsBound_openRev (constsBound_of_constsResolve _ (by
          rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
          exact hpinCR)) 0 rP) hvpa
    · -- the guarded grading (part-6 probe repair) crosses by the
      -- determinism trick on its contravariant type reading, exactly
      -- as the inner block's `TVa` does below
      intro ρ zs TVa restR hzl hzok hTVa hfit
      obtain ⟨TVa', hTVa', -, -⟩ :=
        mp.constType 0 n _ us hfE (by exact hlen)
      obtain rfl : TVa' = TVa := by
        refine Option.some.inj (Eq.trans ?_ hTVa)
        exact (hx.denote
          (constsBound_instType mp.base2.wf
            (ConLeche.Env.find?_mem hfE) us) hTVa').symm
      exact hok ρ zs TVa' restR hzl hzok hTVa' hfit
  · intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hψ hyWD hpin hTVa hTVja hfitR hfitC
    -- **the environment invariant, not the install's kind**: the rule's
    -- constructor is stored
    obtain ⟨⟨cvj', cnP', cnF', hst⟩, -, -⟩ :=
      mp.base2.rec_ctors n cv mI rP rules hfE rl hmem
    have hfcjE : env.find? (RecRule.ctor rl)
        = some (.ctorInfo cvj cnP cnF) := hx.back (by rw [hst]; rfl) hfcj
    -- the two stored types: produced at the prefix, moved forward,
    -- identified with the given extension readings by determinism
    obtain ⟨TVa', hTVa', -, -⟩ :=
      mp.constType 0 n _ us hfE (by exact hlen)
    obtain rfl : TVa' = TVa := by
      refine Option.some.inj (Eq.trans ?_ hTVa)
      exact (hx.denote
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfE) us) hTVa').symm
    obtain ⟨TVja', hTVja', -, -⟩ :=
      mp.constType 0 (RecRule.ctor rl) _ usj hfcjE (by exact hujl)
    obtain rfl : TVja' = TVja := by
      refine Option.some.inj (Eq.trans ?_ hTVja)
      exact (hx.denote
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfcjE) usj) hTVja').symm
    -- the two leaves the conclusion mentions are the prefix's
    rw [hx.leafOf hst] at hfitR hpin
    rw [hx.leafOf hfE, hx.leafOf hst]
    exact hlaw cvj cnP cnF hfcjE usj ρ xs ys _ _ restR restC hxl hyl
      hujl hψ hyWD hpin hTVa' hTVja' hfitR hfitC

/-- **The fired iota contract survives a fresh cons that is
not itself a recursor** — `recRuleLaw_cons_prefix` at every stored
row, the freshness supplying the disequality. -/
theorem recRules_cons_fresh (mp : EnvModelM V env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    (hnotrec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      rules = [])
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : RecRules m₂ φ := by
  intro n cv mI rP rules hf rl hmem
  -- the recursor is stored in the prefix: either the cons is not a
  -- recursor at all (the value kinds' `noConfusion`), or it is one
  -- with no rules (a basis recursor whose block installs its ι
  -- content elsewhere), and then `rl ∈ rules` is impossible
  have hnN : n ≠ c₀.name := by
    intro hh
    subst hh
    have hrl := hnotrec cv mI rP rules
      (Option.some.inj ((ConLeche.Env.find?_cons_self c₀ env).symm.trans hf))
    rw [hrl] at hmem
    exact nomatch hmem
  exact recRuleLaw_ext mp (ModelExt.consOf mp hfresh hac) φ
    (by rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hnN hh.symm)] at hf
        exact hf) hmem

/-- **The fired iota contract at a *recursor* cons.**  The
prefix rows are `recRuleLaw_cons_prefix` unchanged; the new
constant's own rows are the block's bespoke firing work, taken here as
a premise.  ENDGAME F's §3 established that all six basis recursors
owe theirs (`Empty.rec` alone has no rules and goes through
`recRules_cons_fresh`). -/
theorem recRules_cons_rec (mp : EnvModelM V env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    {cv₀ : ConstantVal} {mI₀ rP₀ : Nat} {rules₀ : List RecRule}
    (hfresh : env.find? c₀.name = none)
    (hkind : c₀ = .recInfo cv₀ mI₀ rP₀ rules₀)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat)
    (hnew : ∀ rl ∈ rules₀, RecRuleLaw m₂ φ c₀.name cv₀ mI₀ rP₀ rl) :
    RecRules m₂ φ := by
  intro n cv mI rP rules hf rl hmem
  by_cases hnN : n = c₀.name
  · subst hnN
    have hself : c₀ = .recInfo cv mI rP rules :=
      Option.some.inj ((ConLeche.Env.find?_cons_self c₀ env).symm.trans hf)
    have heq : ConstantInfo.recInfo cv₀ mI₀ rP₀ rules₀
        = .recInfo cv mI rP rules := hkind.symm.trans hself
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    exact hnew rl hmem
  · exact recRuleLaw_ext mp (ModelExt.consOf mp hfresh hac) φ
      (by rw [ConLeche.Env.find?_cons, ite_eq_right (fun hh => hnN hh.symm)] at hf
          exact hf) hmem

/-! ## The tower projection law across a fresh cons (task #175 wiring, W5)

`TowerOk` (`Env/EnvModelM.lean`) is keyed on the stored tower-backed
entries; a cons that is not itself a tower entry adds none, and every
stored row transports exactly as `recRuleLaw_cons_prefix`'s: the
lookups the law reads (the entry, the former, the constructor) are
prefix lookups, the two readings it carries (`Ta`, `TCa`) move
**forward** by `denote_cons_mono`, and the two leaves it
mentions (`acval T`, `acval entry.ctor`) are the prefix's by
`acvalWith_ne` — both names are stored, so neither is the fresh one.
The semantic clauses are then the prefix's verbatim. -/

/-- **A prefix tower entry's law crosses an extension keeping the
prefix's readings** (a constant's install or a table's): the entry, its
former and its constructor are prefix lookups, their type readings
cross, and the two leaves the laws read are the prefix's. -/
theorem towerEntryLaw_ext (mp : EnvModelM V env) {env' : Env}
    {m₂ : EnvModel V env'} (hx : ModelExt mp env' m₂.acval)
    (φ : Name → Nat) {T : Name} {i : Nat} {entry : ProjEntry}
    (hfP : env.findProj? T i = some entry) :
    TowerEntryLaw m₂ φ T i entry := by
  obtain ⟨tbl, hfP0, hi, hentry⟩ := ConLeche.Env.findProj?_some hfP
  obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, hO5, cvC, hfC, hlpsC,
    hlaw, hetaL⟩ := mp.tower_ok φ T i entry hfP
  refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, ?_, hlpsT⟩, hO5, cvC, ?_, hlpsC,
    fun us hus => ?_, ?_⟩
  · exact hx.find hfT
  · exact hx.find hfC
  · obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
    refine ⟨⟨Ta, ?_, ?_⟩, ⟨TCa, ?_, ?_⟩⟩
    · -- the body telescope's reading crosses (task #175 S1): the
      -- table is a prefix lookup, its bodies resolve (`EnvWF`)
      refine hx.denote ?_ hTa
      · refine constsBound_of_constsResolve _ ?_
        rw [ConLeche.projTele_constsResolve, ConLeche.Expr.constsResolve_instantiateLevelParams]
        exact (ConLeche.projEntry_body_wf mp.base2.wf hfP).2.2.1
    · intro hg ρ vs x rest hlen hokT hneT hokx hmem hpeel
      rw [hx.leafOf hfT] at hokT hneT hmem
      exact hA hg ρ vs x rest hlen hokT hneT hokx hmem hpeel
    · -- the constructor type's reading crosses (task #175 W6): a
      -- prefix lookup's closed type
      exact hx.denote
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfC) us) hTCa
    · intro hg ρ ys rest hlen hok hfit
      rw [hx.leafOf hfC] at hok ⊢
      exact hB hg ρ ys rest hlen hok hfit
  · -- (C) the η law crosses (task #175 W4c): the former's lookup is a
    -- prefix lookup, its type reading is closed, the leaves are prefix
    -- leaves
    intro cvT' capsT' hfT' us hus
    have hfT'' : env.find? T = some (.indInfo cvT' capsT') := by
      exact hx.back (by rw [hfT]; rfl) hfT'
    obtain ⟨TVa, hTVa, hok, hlaw', hcoh⟩ := hetaL cvT' capsT' hfT'' us hus
    refine ⟨TVa, ?_, hok, ?_, fun he => (hcoh he).transport
      (fun cvC nPc nFc hf₂ => ?_) (fun cvC nPc nFc TCa hf hTCa => ?_)
      (by rw [hx.leafOf hfT]) (fun _ _ _ => rfl)⟩
    · exact hx.denote
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hfT'') us) hTVa
    · intro ρ ts rest x hlen hfit hmem
      rw [hx.leafOf hfT] at hmem
      rw [hx.leafOf hfC]
      exact hlaw' ρ ts rest x hlen hfit hmem
    · exact hx.back (by rw [hfC]; rfl) hf₂
    · exact hx.denote
        (constsBound_instType mp.base2.wf
          (ConLeche.Env.find?_mem hf) us) hTCa

/-- **`TowerOk` at a fresh cons**: every stored entry is a prefix entry
(a constant's install adds no table), and its law crosses. -/
theorem towerOk_cons_fresh (mp : EnvModelM V env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → Term}
    (hfresh : env.find? c₀.name = none)
    (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : TowerOk m₂ φ := by
  intro T i entry hf
  -- the entry is a prefix entry: a constant's install adds no table
  rw [mp.base2.wf.findProj?_cons hfresh] at hf
  exact towerEntryLaw_ext mp (ModelExt.consOf mp hfresh hac) φ hf

end ConLeche.Model
