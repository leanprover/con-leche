module

public import ConLeche.Model.IndRep
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.IndFrame
public import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Model.Steps.BitLevels
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Model.Inductives.MutualRecLaw
import ConLeche.Model.Inductives.FixRecFrames
import ConLeche.Model.Inductives.FixCtorReads
public section

/-!
# The `k`-motive fold kit over a represented block's recursor (task #279 M-B′)

A later block that nests through a stored container `J` has ONE
spellable handle on `J`'s elements: `J`'s stored recursor (DESIGN
§M.1).  The representation clause records the recursor's shape
(`RecReadAt`: its type reads as the `k`-motive tower, its rules as
the generated cores), and this module turns that shape into the two
facts a FOLD `⟦J.rec⟧ p⃗ M⃗ m⃗` spelled from it needs, generically in
the datum, the model and the spine:

* **typing** (`recFold_mem`): the recursor's leaf applied along a spine
  fitting the tower's parameter, motive and minor binders lands in the
  residual tower — the member's index telescope and its major, ending
  in the motive applied — by `mem_type` and the Π-tower fold
  (`mkPisAV_fold_mem`);
* **ι** (`recFold_iota`): at a REAL constructor `C` of the member, the
  fold applied to the constructor's index readings and to `C p⃗ f⃗` is
  the rule's right-hand side applied to the prefix and the fields —
  `rec_rules` (`RecRuleLaw`) at the identity level instantiation, its
  right-hand side identified with the datum's `ruleAV` through
  `RecReadAt`; then (`interp_ruleAV_app`) the right-hand side's λ-tower
  β-reduces to the rule's CORE, which reads (`interp_mutualRuleCoreAV`)
  as the minor at the fields and the inductive hypotheses — each the
  TARGET member's recursor leaf at the SAME prefix, applied to the
  field's index readings and the field.  That last shape is what makes
  a fold spelled at one motive/minor choice compositional across the
  block's members.

Both are stated at an arbitrary frame `ρ` over spines of readings
(`AnnotTerm`s at `ρ`), with the spine's fit (`SpineFit`) as the
hypothesis the consumer discharges; nothing here is specific to the
nested route.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Spines of readings against Π-towers -/

/-! `interp_mkAppN_map` (`Model/IndProjEta.lean`) and `piTeleAV_mkPisAV`
(`Model/Inductives/StructEntryKit.lean`) are the two spine lemmas this
kit reads; they are re-used as they stand. -/

/-- A fitting spine's entries, positionally: value `n` inhabits domain
`n` at the frame extended by the values before it. -/
theorem spineFit_getElem? {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {vs : List V}, SpineFit ρ Fs vs →
      ∀ (n : Nat) (v : V) (F : AnnotTerm), vs[n]? = some v → Fs[n]? = some F →
        v ∈ˢ interp V (consList (vs.take n) ρ) F
  | [], _, _, _, _, _, _, hF => nomatch hF
  | _ :: _, [], h, _, _, _, _, _ => h.elim
  | F :: Fs, v :: vs, h, 0, v', F', hv, hF => by
    obtain rfl := Option.some.inj hv
    obtain rfl := Option.some.inj hF
    exact h.1
  | F :: Fs, v :: vs, h, n + 1, v', F', hv, hF => by
    simp only [List.getElem?_cons_succ] at hv hF
    rw [List.take_succ_cons, consList_cons]
    exact spineFit_getElem? (ρ := cons v ρ) h.2 n v' F' hv hF

omit [SetTheory V] in
/-- The reversed list, read at the mirrored position. -/
theorem getD_reverse_mirror {α : Type _} [Inhabited α] (l : List α) (n : Nat) (hn : n < l.length) :
    l.reverse.getD (l.length - 1 - n) default = l.getD n default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega)]
  congr 2
  omega

/-- **A spine of readings fitting a Π-tower fits it as a telescope**
(`TeleFitPA`), with the tower's body instantiated along the spine as
the residual. -/
theorem teleFitPA_of_spineFit {ρ : Nat → V} {ds : List (Nat × Nat × AnnotTerm)} {C : AnnotTerm}
    {as : List AnnotTerm} (h : SpineFit ρ (ds.map (·.2.2)) (as.map (interp V ρ))) :
    TeleFitPA V ρ (mkPisAV ds C) as (ConLeche.Model.AnnotTerm.instSeq as (ds.length - 1) C) := by
  have hlen : as.length = ds.length := by
    have := SpineFit.length_eq h
    simpa using this
  refine teleFitPA_of_tower ds.length (piTeleAV_mkPisAV ds C) hlen fun n hn => ?_
  have hnas : n < as.length := by omega
  have hnds : n < (ds.map (·.2.2)).length := by simpa using hn
  have hmem := spineFit_getElem? h n (interp V ρ (as.getD n default)) ((ds.map (·.2.2)).getD n default)
    (by rw [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnas]; rfl)
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnds]; rfl)
  rw [show ds.length - 1 - n = (ds.map (·.2.2)).length - 1 - n from by simp,
    getD_reverse_mirror _ n hnds]
  unfold chain
  rw [consN_eq_consList, List.map_take]
  exact hmem

/-- Evaluating a body instantiated along a spine of readings is
evaluating it at the frame extended by the readings' values. -/
theorem interp_instSeq_consList (as : List AnnotTerm) (C : AnnotTerm) (ρ : Nat → V) :
    interp V ρ (ConLeche.Model.AnnotTerm.instSeq as (as.length - 1) C)
      = interp V (consList (as.map (interp V ρ)) ρ) C := by
  rw [interp_instSeq]
  unfold chain
  rw [consN_eq_consList]

omit [SetTheory V] in
/-- Instantiation distributes over an application spine. -/
theorem inst_mkAppN_annot (a : AnnotTerm) (k : Nat) :
    ∀ (as : List AnnotTerm) (f : AnnotTerm),
      (AnnotTerm.mkAppN f as).inst a k = AnnotTerm.mkAppN (f.inst a k) (as.map (·.inst a k))
  | [], _ => rfl
  | b :: as, f => by
    rw [AnnotTerm.mkAppN_cons, inst_mkAppN_annot a k as, List.map_cons, AnnotTerm.mkAppN_cons,
      AnnotTerm.inst_app]

omit [SetTheory V] in
/-- Instantiation along a spine distributes over an application spine. -/
theorem instSeq_mkAppN_annot (ws : List AnnotTerm) :
    ∀ (t : Nat) (f : AnnotTerm) (as : List AnnotTerm),
      ConLeche.Model.AnnotTerm.instSeq ws t (AnnotTerm.mkAppN f as)
        = AnnotTerm.mkAppN (ConLeche.Model.AnnotTerm.instSeq ws t f)
            (as.map (ConLeche.Model.AnnotTerm.instSeq ws t)) := by
  induction ws with
  | nil =>
    intro t f as
    have h : as.map (ConLeche.Model.AnnotTerm.instSeq [] t) = as := by
      rw [List.map_congr_left (l := as) (f := ConLeche.Model.AnnotTerm.instSeq [] t)
        (g := fun a => a) (fun a _ => rfl)]
      exact List.map_id' as
    rw [h]
    rfl
  | cons w ws ih =>
    intro t f as
    rw [AnnotTerm.instSeq_cons, inst_mkAppN_annot, ih, List.map_map]
    rfl

/-- A Π-tower whose binder bits are all zero reads to a truth value. -/
theorem mkPisAV_mem_univZero_of_bits {ds : List (Nat × Nat × AnnotTerm)} {C : AnnotTerm}
    (hne : ds ≠ []) (hz : ∀ d ∈ ds, d.2.1 = 0) (ρ : Nat → V) :
    interp V ρ (mkPisAV ds C) ∈ˢ (univZero : V) := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds =>
    show piR d.2.1 _ _ ∈ˢ _
    rw [hz d List.mem_cons_self]
    exact piR_zero_mem_univZero

/-! ## The recursor's leaf inhabits its tower -/

/-- **The stored recursor's leaf inhabits the tower's reading**
(`mem_type` at `RecReadAt`'s type reading). -/
theorem RecReadAt.leaf_mem {μ : CheckMode} (mp : EnvModelM V μ env) {d : IndRepData V}
    {lps : List Name} {t : Nat} (hR : RecReadAt mp.base2 d lps t) (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (mp.base2.acval (d.recNames t) ψ)
      ∈ˢ interp V ρ (mkPisAV (d.recDataAV mp.base2 ψ t)
          (mutualConcAV d.k d.nAll (d.nIdxAt t) t)) := by
  obtain ⟨cvR', mI', rP', rules', hfind, -, -, -, hread, -, -, -⟩ := hR
  have hname : cvR'.name = d.recNames t := Env.find?_name hfind
  have h := mp.mem_type _ (Env.find?_mem hfind) ψ _ (hread ψ) ρ
  rw [show (ConstantInfo.recInfo cvR' mI' rP' rules').name = cvR'.name from rfl, hname] at h
  exact h

/-! ## The tower, split at the prefix -/

namespace IndRepData

variable (d : IndRepData V)

/-- The recursor tower's LEADING binder data: the parameters, the `k`
motives and the minors (the segment every member's tower shares). -/
@[expose] def recPrefixAV (m : EnvModel V env) (ψ : Name → Nat) : List (Nat × Nat × AnnotTerm) :=
  rebit (d.bb ψ) ((d.ppsM 0 ψ).take d.nP) ++
    motivesDataGoP (fun t => (d.Ls m ψ).getD t default) (d.pinsOf ψ) (fun t => d.nIdxs.getD t 0)
      (fun t => (d.ipss ψ).getD t []) ψ d.nP d.elimL (d.bb ψ) (d.Ls m ψ).length 0 ++
    fixMinorsDataMP d.mems d.tgtsR (fun J => d.pinsOf ψ (d.mems J)) m ψ d.nP (d.bb ψ) (d.cdsR ψ)
      (d.Ls m ψ).length

/-- Member `t`'s tower's TRAILING binder data: its index telescope
lifted under the motives and the minors, and its major. -/
@[expose] def recPostAV (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) :
    List (Nat × Nat × AnnotTerm) :=
  rebit (d.bb ψ) (liftDoms ((d.Ls m ψ).length + (d.cdsR ψ).length) 0 ((d.ipss ψ).getD t [])) ++
    [(0, d.bb ψ, majorAVP ((d.Ls m ψ).getD t default) (d.pinsOf ψ t) d.nP (d.nIdxs.getD t 0)
      (d.Ls m ψ).length (d.cdsR ψ).length)]

/-- The tower is its prefix followed by the member's trailer. -/
theorem recDataAV_split (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) :
    d.recDataAV m ψ t = d.recPrefixAV m ψ ++ d.recPostAV m ψ t := by
  unfold recDataAV recDataAVP recPrefixAV recPostAV bb
  simp only [List.append_assoc]

/-- Every prefix binder carries the elimination bit. -/
theorem mem_recPrefixAV {m : EnvModel V env} {ψ : Name → Nat} {x : Nat × Nat × AnnotTerm}
    (hx : x ∈ d.recPrefixAV m ψ) : x.2.1 = d.bb ψ := by
  simp only [recPrefixAV, List.mem_append] at hx
  rcases hx with (h | h) | h
  · exact mem_rebit h
  · exact mem_motivesDataGoP h
  · exact mem_fixMinorsDataMP h

/-- Every trailer binder carries the elimination bit. -/
theorem mem_recPostAV {m : EnvModel V env} {ψ : Name → Nat} {t : Nat} {x : Nat × Nat × AnnotTerm}
    (hx : x ∈ d.recPostAV m ψ t) : x.2.1 = d.bb ψ := by
  simp only [recPostAV, List.mem_append, List.mem_singleton] at hx
  rcases hx with h | rfl
  · exact mem_rebit h
  · rfl

/-- The trailer is never empty: it ends with the major. -/
theorem recPostAV_ne_nil (m : EnvModel V env) (ψ : Name → Nat) (t : Nat) :
    d.recPostAV m ψ t ≠ [] := by
  unfold recPostAV
  simp

/-- The members' leaves are as many as the members. -/
theorem Ls_length (m : EnvModel V env) (ψ : Name → Nat) : (d.Ls m ψ).length = d.k := by
  simp [Ls]

omit [SetTheory V] in
/-- The recursor's constructor data are as many as the block's
constructors. -/
theorem cdsR_length (ψ : Name → Nat) : (d.cdsR ψ).length = d.nAll := by
  unfold cdsR nAll
  rw [fixCtorDataList_length, ctorsAll, List.length_append]

/-- The prefix has the parameter, motive and minor binders. -/
theorem recPrefixAV_length (m : EnvModel V env) (ψ : Name → Nat)
    (hp : ((d.ppsM 0 ψ).take d.nP).length = d.nP) :
    (d.recPrefixAV m ψ).length = d.nP + d.k + d.nAll := by
  unfold recPrefixAV
  rw [List.length_append, List.length_append, rebit_length, hp, motivesDataGoP_length,
    fixMinorsDataMP_length, Ls_length, cdsR_length]

end IndRepData

/-! ## The fold's typing -/

/-- **The fold's membership**: the recursor's leaf applied along a
spine fitting the prefix — parameters, motives, minors — lands in the
member's trailer tower at the extended frame. -/
theorem recFold_mem {μ : CheckMode} (mp : EnvModelM V μ env) {d : IndRepData V} {lps : List Name}
    {t : Nat} (hR : RecReadAt mp.base2 d lps t) (ψ : Name → Nat) {ρ : Nat → V}
    {as : List AnnotTerm}
    (hfit : SpineFit ρ ((d.recPrefixAV mp.base2 ψ).map (·.2.2)) (as.map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ) as)
      ∈ˢ interp V (consList (as.map (interp V ρ)) ρ)
          (mkPisAV (d.recPostAV mp.base2 ψ t) (mutualConcAV d.k d.nAll (d.nIdxAt t) t)) := by
  have hleaf := hR.leaf_mem mp ψ ρ
  rw [d.recDataAV_split, mkPisAV_append] at hleaf
  rw [interp_mkAppN_map]
  refine mkPisAV_fold_mem (m := d.bb ψ) (fun x hx => by rw [d.mem_recPrefixAV hx]) ?_ hleaf hfit
  intro hb as' _
  exact mkPisAV_mem_univZero_of_bits (d.recPostAV_ne_nil mp.base2 ψ t)
    (fun x hx => by rw [d.mem_recPostAV hx, hb]) _

/-- **The fold applied**: a member of the trailer tower applied along a
fitting spine of index readings and a major lands in the conclusion —
the motive at the indices and the major — at the extended frame.  The
zero-bit side condition (the conclusion is a truth value at `Prop`
motives) is the consumer's: it knows its motives' codomain. -/
theorem recFold_app_mem {d : IndRepData V} {m : EnvModel V env} {ψ : Name → Nat} {t : Nat}
    {ρ : Nat → V} {F : AnnotTerm} {is : List AnnotTerm}
    (hF : interp V ρ F ∈ˢ interp V ρ (mkPisAV (d.recPostAV m ψ t)
      (mutualConcAV d.k d.nAll (d.nIdxAt t) t)))
    (h0 : d.bb ψ = 0 → ∀ vs : List V,
      SpineFit ρ ((d.recPostAV m ψ t).map (·.2.2)) vs →
      interp V (consList vs ρ) (mutualConcAV d.k d.nAll (d.nIdxAt t) t) ∈ˢ (univZero : V))
    (hfit : SpineFit ρ ((d.recPostAV m ψ t).map (·.2.2)) (is.map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN F is)
      ∈ˢ interp V (consList (is.map (interp V ρ)) ρ) (mutualConcAV d.k d.nAll (d.nIdxAt t) t) := by
  rw [interp_mkAppN_map]
  exact mkPisAV_fold_mem (m := d.bb ψ) (fun x hx => by rw [d.mem_recPostAV hx]) h0 hF hfit

/-! ## The rule of a real constructor -/

/-- The recursor's stored rule at a REAL constructor `j` of member `t`:
its firing mode is `.plain` at the block's parameter count and the
constructor's field count, and its right-hand side reads as the
datum's `ruleAV`. -/
theorem RecReadAt.plain_rule {m : EnvModel V env} {d : IndRepData V} {lps : List Name} {t : Nat}
    (hR : RecReadAt m d lps t) {j : Nat} {cA : ConstantVal × Nat}
    (hj : d.ctorsAll[j]? = some cA) (hmem : d.mems j = t) (hreal : j < d.ctorsA.length) :
    ∃ (cvR' : ConstantVal) (mI' rP' : Nat) (rules' : List RecRule) (rl : RecRule),
      env.find? (d.recNames t) = some (.recInfo cvR' mI' rP' rules') ∧
      mI' = d.nP + d.k + d.nAll + d.nIdxAt t ∧ rP' = d.nP + d.k + d.nAll ∧
      (∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvR'.type
        = some (mkPisAV (d.recDataAV m ψ t) (mutualConcAV d.k d.nAll (d.nIdxAt t) t))) ∧
      rl ∈ rules' ∧ rl.ctor = cA.1.name ∧ rl.fire = .plain ∧ rl.ctorParams = d.nP ∧
      rl.nfields = cA.2 ∧
      ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 rl.rhs = some (d.ruleAV m ψ j cA.2) := by
  obtain ⟨cvR', mI', rP', rules', hfind, -, hmI, hrP, hread, -, hrules, -⟩ := hR
  obtain ⟨rl, hrl, hctor, hplain, hrhs⟩ := hrules j cA hj hmem
  obtain ⟨hfire, hcp, hnf⟩ := hplain hreal
  exact ⟨cvR', mI', rP', rules', rl, hfind, hmI, hrP, hread, hrl, hctor, hfire, hcp, hnf, hrhs⟩

omit [SetTheory V] in
/-- Substituting a parameter list for levels that evaluate to the
parameters themselves is the identity assignment. -/
theorem substFn_map_of_eval {φ : Name → Nat} {g : Name → Level}
    (hg : ∀ p, Level.eval φ (g p) = φ p) :
    ∀ (ks : List Name) (n : Name), Level.substFn φ ks (ks.map g) n = φ n
  | [], _ => rfl
  | k :: ks, n => by
    simp only [List.map_cons, Level.substFn]
    split
    · next h => rw [hg, h]
    · exact substFn_map_of_eval hg ks n

namespace IndRepData

/-- Constructor `j`'s index readings instantiated along the
constructor's own spine `ys` (parameters and fields): the index
arguments the recursor is applied to when it fires at `C ys`. -/
@[expose] def ctorIdxAt (d : IndRepData V) (ψ : Name → Nat) (j : Nat) (ys : List AnnotTerm) :
    List AnnotTerm :=
  (d.esF j ψ).map (ConLeche.Model.AnnotTerm.instSeq ys ((d.dsF j ψ).length - 1))

omit [SetTheory V] in
theorem ctorIdxAt_length (d : IndRepData V) (ψ : Name → Nat) (j : Nat) (ys : List AnnotTerm) :
    (d.ctorIdxAt ψ j ys).length = (d.esF j ψ).length := by
  simp [ctorIdxAt]

end IndRepData

/-! ## ι: the fold at a real constructor -/

/-- **The fold fires at a real constructor** (`rec_rules` at the
identity level instantiation, the right-hand side identified with
`ruleAV` through `RecReadAt`): the recursor's leaf applied to the
prefix `pre` (parameters, motives, minors), the constructor's index
readings at the constructor spine `ys = p⃗ f⃗` and the constructor
applied to `ys`, equals the rule's right-hand side applied to the
prefix and the fields.  The two spine fits are the consumer's: the
recursor's full tower at the fired spine, the constructor's tower at
`ys`. -/
theorem recFold_iota {μ : CheckMode} (mp : EnvModelM V μ env) {d : IndRepData V}
    {lps lpsT : List Name} {t : Nat} (hR : RecReadAt mp.base2 d lps t) {j : Nat}
    {cA : ConstantVal × Nat} (hj : d.ctorsAll[j]? = some cA) (hmem : d.mems j = t)
    (hreal : j < d.ctorsA.length)
    (hC : FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems j)) lpsT d.nP (d.nIdxAt (d.mems j))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF j cA (fun i => d.memberName (d.tgts j i)) (fun i => d.nIdxAt (d.tgts j i)))
    (ψ : Name → Nat) {ρ : Nat → V} {pre fs : List AnnotTerm}
    (hpre : pre.length = d.nP + d.k + d.nAll)
    (hfitR : SpineFit ρ ((d.recDataAV mp.base2 ψ t).map (·.2.2))
      ((pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs) ++
        [AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (pre.take d.nP ++ fs)]).map (interp V ρ)))
    (hfitC : SpineFit ρ ((d.dsF j ψ).map (·.2.2)) ((pre.take d.nP ++ fs).map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
        (pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs) ++
          [AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (pre.take d.nP ++ fs)]))
      = interp V ρ (AnnotTerm.mkAppN (d.ruleAV mp.base2 ψ j cA.2) (pre ++ fs)) := by
  obtain ⟨cvR', mI', rP', rules', rl, hfind, hmI, hrP, hread, hrl, hctor, hfire, hcp, hnf, hrhs⟩ :=
    hR.plain_rule hj hmem hreal
  obtain ⟨hfctor, -, hCD⟩ := hC
  -- the law at the identity level instantiation
  have hne : rl.fire ≠ .inert := by rw [hfire]; exact nofun
  obtain ⟨-, hlaw⟩ := mp.rec_rules ψ (d.recNames t) cvR' mI' rP' rules' hfind rl hrl hne
  obtain ⟨Ra, hRa, -, -, hmain⟩ := hlaw (cvR'.levelParams.map .param) (by simp)
  have hid : Level.substFn ψ cvR'.levelParams (cvR'.levelParams.map .param) = ψ :=
    funext fun _ => Level.substFn_map_param
  rw [denotePInstLevels, hid, hrhs ψ] at hRa
  obtain rfl : Ra = d.ruleAV mp.base2 ψ j cA.2 := (Option.some.inj hRa).symm
  -- the constructor's level instantiation: the rule's comparands
  obtain ⟨usj, husj⟩ : ∃ usj : List Level, usj = cA.1.levelParams.map fun p =>
      Level.subst cvR'.levelParams (cvR'.levelParams.map .param) (.param p) := ⟨_, rfl⟩
  have hidj : Level.substFn ψ cA.1.levelParams usj = ψ := by
    rw [husj]
    funext p
    refine substFn_map_of_eval (fun q => ?_) _ p
    rw [Level.eval_subst]
    show Level.substFn ψ cvR'.levelParams (cvR'.levelParams.map .param) q = ψ q
    exact Level.substFn_map_param
  have hlenUj : usj.length = cA.1.levelParams.length := by simp [husj]
  have hlev : Level.substFn ψ cA.1.levelParams usj
      = Level.substFn ψ cA.1.levelParams
          (ConLeche.recFireComparands rl cvR'.levelParams (cvR'.levelParams.map .param)
            cA.1.levelParams [] rP').1 := by
    rw [husj]
    unfold ConLeche.recFireComparands
    rw [hfire]
  -- the lengths
  have hlenC : (d.dsF j ψ).length = d.nP + cA.2 := hCD.len ψ
  have hlenE : (d.esF j ψ).length = d.nIdxAt t := by rw [hCD.lenE ψ, hmem]
  have htake : (pre.take d.nP).length = d.nP := by
    rw [List.length_take, hpre]; omega
  have hys : (pre.take d.nP ++ fs).length = d.nP + cA.2 := by
    have := SpineFit.length_eq hfitC
    simpa [hlenC] using this
  have hxs : (pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs)).length = mI' := by
    rw [List.length_append, hpre, d.ctorIdxAt_length, hlenE, hmI]
  have hys' : (pre.take d.nP ++ fs).length = rl.ctorParams + rl.nfields := by
    rw [hys, hcp, hnf]
  -- the parameter comparison: both spines lead with the parameters
  have hparams : rl.paramsBlind = false → rl.fire = .plain →
      ∀ i, i < rl.ctorParams → i < mI' →
        interp V ρ ((pre.take d.nP ++ fs).getD i default)
          = interp V ρ ((pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs)).getD i default) := by
    intro _ _ i hi _
    rw [hcp] at hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [htake]; exact hi), List.getElem?_take_of_lt hi,
      List.getElem?_append_left (by omega)]
  have hnested : ∀ lvls pins, rl.fire = .nested lvls pins → ∀ i, i < rl.ctorParams →
      ∀ vpa : AnnotTerm,
        denoteMeta mp.base2.acval env ψ rP'
          (ConLeche.Verify.openRev 0 rP'
            ((pins.getD i default).instantiateLevelParams cvR'.levelParams
              (cvR'.levelParams.map .param))) = some vpa →
        interp V ρ ((pre.take d.nP ++ fs).getD i default)
          = interp V ρ (ConLeche.Model.AnnotTerm.instRevChain
              ((pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs)).take rP') vpa) := by
    intro lvls pins h
    rw [hfire] at h
    exact nomatch h
  -- the two types, read at the instantiation
  have hTVa : denoteMeta mp.base2.acval env ψ 0
      (cvR'.type.instantiateLevelParams cvR'.levelParams (cvR'.levelParams.map .param))
      = some (mkPisAV (d.recDataAV mp.base2 ψ t) (mutualConcAV d.k d.nAll (d.nIdxAt t) t)) := by
    rw [denotePInstLevels, hid]; exact hread ψ
  have hTVja : denoteMeta mp.base2.acval env ψ 0
      (cA.1.type.instantiateLevelParams cA.1.levelParams usj)
      = some (mkPisAV (d.dsF j ψ)
          (ctorBodyAVI mp.base2 (d.memberName (d.mems j)) d.nP cA.2 ψ (d.esF j ψ))) := by
    rw [denotePInstLevels, hidj]; exact hCD.read ψ
  -- the two telescope fits
  have hfitR' := teleFitPA_of_spineFit (C := mutualConcAV d.k d.nAll (d.nIdxAt t) t) hfitR
  have hfitC' := teleFitPA_of_spineFit
    (C := ctorBodyAVI mp.base2 (d.memberName (d.mems j)) d.nP cA.2 ψ (d.esF j ψ)) hfitC
  -- the index pin: the constructor's residual's index arguments are the
  -- recursor's index arguments, by construction of `ctorIdxAt`
  have hpin : IotaIndexPin (V := V) ρ
      (ConLeche.Model.AnnotTerm.instSeq (pre.take d.nP ++ fs) ((d.dsF j ψ).length - 1)
        (ctorBodyAVI mp.base2 (d.memberName (d.mems j)) d.nP cA.2 ψ (d.esF j ψ)))
      rl.ctorParams mI' rP' (pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs)) := by
    unfold ctorBodyAVI
    rw [instSeq_mkAppN_annot]
    refine ⟨_, _, rfl, Or.inr ?_, fun i hi => ?_⟩
    · rw [hcp, hmI, hrP, List.length_map, List.length_append, hlenE]
      simp only [paramBvars, List.length_map, List.length_range]
      omega
    · rw [hmI, hrP] at hi
      rw [hcp, hrP]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.map_append,
        List.getElem?_append_right (by simp [paramBvars]),
        List.getElem?_append_right (by rw [hpre]; omega), hpre]
      simp only [paramBvars, List.length_map, List.length_range, Nat.add_sub_cancel_left,
        IndRepData.ctorIdxAt]
  -- the law, fired
  have hmain' := hmain cA.1 d.nP cA.2 (by rw [hctor]; exact hfctor) usj ρ
    (pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs)) (pre.take d.nP ++ fs) _ _
    (ConLeche.Model.AnnotTerm.instSeq
      (pre ++ d.ctorIdxAt ψ j (pre.take d.nP ++ fs) ++
        [AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (pre.take d.nP ++ fs)])
      ((d.recDataAV mp.base2 ψ t).length - 1) (mutualConcAV d.k d.nAll (d.nIdxAt t) t))
    (ConLeche.Model.AnnotTerm.instSeq (pre.take d.nP ++ fs) ((d.dsF j ψ).length - 1)
      (ctorBodyAVI mp.base2 (d.memberName (d.mems j)) d.nP cA.2 ψ (d.esF j ψ)))
    hxs hys' hlenUj hlev hparams hnested hpin hTVa hTVja
  rw [hctor, hidj, hid] at hmain'
  have h := (hmain' hfitR' hfitC').1
  rw [hcp, List.take_left' (by rw [hpre, hrP]), List.drop_left' htake] at h
  exact h

/-! ## β: the right-hand side applied is the core -/

/-- The rule's binder data as a spine fit, from the recursor prefix's
fit and the constructor's fields' fit at the parameter frame (the
fields' binders are lifted under the motives and the minors). -/
theorem ruleData_spineFit {m : EnvModel V env} {ψ : Name → Nat} (d : IndRepData V) {j : Nat}
    {ρ : Nat → V} {pvs fvs : List V}
    (hpre : SpineFit ρ ((d.recPrefixAV m ψ).map (·.2.2)) pvs)
    (hlen : pvs.length = d.nP + d.k + d.nAll)
    (hF : SpineFit (consList (pvs.take d.nP) ρ) (((d.dsF j ψ).drop d.nP).map (·.2.2)) fvs) :
    SpineFit ρ ((ruleDataAVP m ψ (d.Ls m ψ) (d.pinsOf ψ) d.nP d.nIdxs d.elimL
      ((d.ppsM 0 ψ).take d.nP) (d.ipss ψ) (d.cdsR ψ) d.mems d.tgtsR (d.dsF j ψ)).map (·.2))
      (pvs ++ fvs) := by
  have hmap : (ruleDataAVP m ψ (d.Ls m ψ) (d.pinsOf ψ) d.nP d.nIdxs d.elimL
        ((d.ppsM 0 ψ).take d.nP) (d.ipss ψ) (d.cdsR ψ) d.mems d.tgtsR (d.dsF j ψ)).map (·.2)
      = (d.recPrefixAV m ψ).map (·.2.2) ++
        (liftDoms ((d.Ls m ψ).length + (d.cdsR ψ).length) 0 ((d.dsF j ψ).drop d.nP)).map (·.2.2) := by
    unfold ruleDataAVP IndRepData.recPrefixAV IndRepData.bb
    simp only [List.map_map, List.map_append, List.append_assoc, rebit_map_dom, Function.comp_def]
  rw [hmap]
  refine SpineFit.append hpre ?_
  rw [spineFit_liftDoms, d.Ls_length, d.cdsR_length]
  have hsplit : consList pvs ρ = consList (pvs.drop d.nP) (consList (pvs.take d.nP) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hdrop : d.k + d.nAll = (pvs.drop d.nP).length := by
    rw [List.length_drop, hlen]; omega
  rw [hsplit, hdrop, shiftE_consList]
  exact hF

/-- **β at a positive elimination bit**: the rule's right-hand side
applied along a fitting spine is the core at the spine's frame. -/
theorem interp_ruleAV_app_pos {m : EnvModel V env} {ψ : Name → Nat} (d : IndRepData V)
    {j nF : Nat} (hb : d.bb ψ ≠ 0) {ρ : Nat → V} {args : List AnnotTerm}
    (hfit : SpineFit ρ ((ruleDataAVP m ψ (d.Ls m ψ) (d.pinsOf ψ) d.nP d.nIdxs d.elimL
      ((d.ppsM 0 ψ).take d.nP) (d.ipss ψ) (d.cdsR ψ) d.mems d.tgtsR (d.dsF j ψ)).map (·.2))
      (args.map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (d.ruleAV m ψ j nF) args)
      = interp V (consList (args.map (interp V ρ)) ρ)
          (mutualRuleCoreAV (d.bb ψ) (fun t => m.acval (d.recNames t) ψ) (d.tgtsR j) d.nP d.k d.nAll
            nF j (ConLeche.recIdxOf (d.ksR j)) (d.tssR j ψ) (d.eissR j ψ)) := by
  unfold IndRepData.ruleAV
  rw [interp_mkAppN_map]
  exact mkLamsAV_fold (fun x hx => by rw [mem_ruleDataAVP hx]; exact hb) hfit

/-- **β at the zero elimination bit**: the right-hand side is the
proof point, and so is every application of it. -/
theorem interp_ruleAV_app_zero {m : EnvModel V env} {ψ : Name → Nat} (d : IndRepData V)
    {j nF : Nat} (hb : d.bb ψ = 0) (hpps : (d.ppsM 0 ψ).take d.nP ≠ []) (ρ : Nat → V)
    (args : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN (d.ruleAV m ψ j nF) args) = pt := by
  rw [interp_mkAppN_map]
  have hpt : interp V ρ (d.ruleAV m ψ j nF) = pt := by
    unfold IndRepData.ruleAV ruleDataAVP
    obtain ⟨p, ps, hps⟩ : ∃ p ps, (d.ppsM 0 ψ).take d.nP = p :: ps := by
      cases h : (d.ppsM 0 ψ).take d.nP with
      | nil => exact absurd h hpps
      | cons p ps => exact ⟨p, ps, rfl⟩
    rw [hps]
    have hb' : pwBit ψ (Level.zeronessOf d.elimL) = 0 := hb
    simp only [rebit_cons, List.cons_append, List.map_cons, hb']
    exact mkLamsAV_zero_head _ _ _ _
  rw [hpt]
  clear hpt
  induction args.map (interp V ρ) with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, app_pt]; exact ih

/-! ## The core, read at the fired frame -/

/-- **The core is the minor at the fields and the inductive
hypotheses** (`interp_mutualRuleCoreAV` at the datum): each hypothesis
is the λ-tower over the field's telescope of the TARGET member's
recursor leaf applied to the SAME parameters, motives and minors, the
field's index readings and the field along the telescope. -/
theorem interp_ruleCore {m : EnvModel V env} {ψ : Name → Nat} (d : IndRepData V) {j nF : Nat}
    {ρ : Nat → V} {ps Ms Ns fvs : List V}
    (hlenP : ps.length = d.nP) (hlenK : Ms.length = d.k) (hk : 0 < d.k)
    (hlenM : Ns.length = d.nAll) (hlenF : fvs.length = nF) (hjn : j < d.nAll)
    (hks : (d.ksR j).length = nF) :
    interp V (consList fvs (consList Ns (consList Ms (consList ps ρ))))
        (mutualRuleCoreAV (d.bb ψ) (fun t => m.acval (d.recNames t) ψ) (d.tgtsR j) d.nP d.k d.nAll
          nF j (ConLeche.recIdxOf (d.ksR j)) (d.tssR j ψ) (d.eissR j ψ))
      = (fvs ++ (ConLeche.recIdxOf (d.ksR j)).map fun i =>
          lamTower (d.bb ψ) (consList (fvs.take i) (consList ps ρ)) ((d.tssR j ψ).getD i [])
            fun σ' =>
              (ps ++ Ms ++ Ns ++ ((d.eissR j ψ).getD i []).map (interp V σ') ++
                [(Semantics.frameIdx (((d.tssR j ψ).getD i []).length) σ').foldl
                  SetTheory.app (fvs.getD i pt)]).foldl
                SetTheory.app (interp V ρ (m.acval (d.recNames (d.tgtsR j i)) ψ))).foldl
          SetTheory.app (Ns.getD j pt) := by
  subst hks
  rw [← recIdx_rsOf]
  exact interp_mutualRuleCoreAV (ℓ := d.bb ψ) Iff.rfl hlenP hlenK hk hlenM hlenF hjn
    (fun i _ => m.cval_closedL _ ψ)

end ConLeche.Model
