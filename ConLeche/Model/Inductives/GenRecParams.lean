module

public import ConLeche.Model.Inductives.GenRecStage
public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.Inductives.BlockRecData
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.DeclNative
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.StreamConsts
import ConLeche.Verify.Inductives.ClassGenAnnot
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Deep
import ConLeche.Verify.Shift
import ConLeche.Verify.Knot

public section

/-!
# The generated recursors' parameter domains fit the block's

`genParams_fit`: every generated (stored) recursor type's first `nP`
prefix domains read as the block's parameters — a spine fitting the
recursor's rule prefix fits `dR.params` on its first `nP` values.  The
old target check had this from its K6 `isDefEqCore` run (the stream's
parameter domains against the major's former, `tgtGuard_params`); the
generated stage runs no such comparison, and none is needed:

* the generated prefix is SHARED (every generated type is the reset
  prefix's telescope, annotated: `SameDoms`), so it suffices to look at
  ONE recursor whose class is a MEMBER `T_t` (one exists: the member
  recursors' name pins);
* that recursor's major domain is `T_t p⃗ ı⃗` over the prefix's own
  parameter variables (the class key moved to the canonical parameters,
  `classKeyCanon`; a member key's parameters ARE them, `targetMajorOf`);
  the stored type's inference (`checkConstantVal`) infers it, and the
  application rule compares each parameter variable's type — the stored
  prefix domain — with `T_t`'s parameter domain at the earlier
  variables (`inferTypeCore_spine_defeq`); depth invariance moves the
  comparison to the prefix's own depth;
* that comparison is the certified hop's premise
  (`prefixDoms_agree_inst`, the `prefixDoms_agree` of
  `BlockRecPreRun.lean` with the second telescope's domains given as
  terms over the FIRST opening's variables), and the members' parameter
  agreement moves `T_t`'s parameters to the block's.

(Syntactic identity of the stored and the former's domains is NOT
available: annotation keeps an input's written binder data, so the
reset-and-reannotated domains need not equal the former's annotated ones;
the application rule's comparison is what ties them.)
-/

namespace ConLeche

variable {μ : CheckMode}

/-! ## Syntax -/

/-- A term with `n` leading `∀`s has the same first `n` domains as itself. -/
theorem SameDoms.of_stripPis :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {r : Expr},
      e.stripPis n = some (bs, r) → SameDoms n e e
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE A b m, bs, r, h => by
    simp only [Expr.stripPis, Option.map_eq_some_iff] at h
    obtain ⟨⟨bs', r'⟩, h', -⟩ := h
    exact ⟨rfl, SameDoms.of_stripPis n h'⟩
  | n + 1, .bvar _, _, _, h | n + 1, .fvar _ _, _, _, h | n + 1, .sort _, _, _, h
  | n + 1, .const _ _, _, _, h | n + 1, .app _ _, _, _, h | n + 1, .lam _ _ _, _, _, h
  | n + 1, .letE _ _ _, _, _, h | n + 1, .lit _, _, _, h | n + 1, .proj _ _ _, _, _, h => by
    simp [Expr.stripPis] at h

/-- Fewer leading domains. -/
theorem SameDoms.mono :
    ∀ {n m : Nat} {e₁ e₂ : Expr}, m ≤ n → SameDoms n e₁ e₂ → SameDoms m e₁ e₂
  | _, 0, _, _, _, _ => trivial
  | 0, m + 1, _, _, hle, _ => absurd hle (by omega)
  | n + 1, m + 1, .forallE A b _, .forallE A' b' _, hle, h =>
    ⟨h.1, SameDoms.mono (by omega) h.2⟩

/-- A run on a `∀` carries a run on its domain. -/
theorem inferTypeCore_forallE_dom {envK : Env} {F d : Nat} {ty bd s : Expr}
    {mb : BinderMeta} (h : inferTypeCore μ envK F d (.forallE ty bd mb) = .ok s) :
    ∃ F₀ tty, F = F₀ + 1 ∧ inferTypeCore μ envK F₀ d ty = .ok tty := by
  cases F with
  | zero =>
    rw [inferTypeCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ F₀ =>
    rw [inferTypeCore_forallE_eq] at h
    obtain ⟨tty, htty, -⟩ := exceptBind_ok h
    exact ⟨F₀, tty, rfl, htty⟩

/-- **The application rule along a spine**: a run on `f a₀ … aₙ₋₁`, `f`
typed at a telescope with (at least) `m` leading `∀`s, compares every
argument `aₗ` (`l < m`) with the telescope's `l`-th domain at the
earlier arguments. -/
theorem inferTypeCore_spine_defeq {envK : Env} {F d : Nat} :
    ∀ (as : List Expr) {f tf t : Expr} {m : Nat}, m ≤ as.length → SameDoms m tf tf →
      inferTypeCore μ envK F d f = .ok tf →
      inferTypeCore μ envK F d (Expr.mkAppN f as) = .ok t →
      ∀ l, l < m → ∃ D b mb ta, instPisWith (as.take l) tf = some (.forallE D b mb) ∧
        inferTypeCore μ envK F d (as.getD l default) = .ok ta ∧
        isDefEqCore μ envK F d ta D = .ok true
  | [], _, _, _, m, hm, _, _, _, l, hl => absurd hl (by simp at hm; omega)
  | a :: as, f, tf, t, m, hm, hsd, hf, h, l, hl => by
    obtain ⟨tfa, hfa⟩ := Model.inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
    obtain ⟨tf', ty', body', m', hf', hw, rfl, ta, hta, hde⟩ := inferTypeCore_app_inv' hfa
    rw [show tf' = tf from Except.ok.inj (hf'.symm.trans hf)] at hw
    obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    match tf, hsd, hw with
    | .forallE A b mb, hsd, hw =>
      obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (whnf_forallE_eq hw)
      cases l with
      | zero => exact ⟨ty', body', m', ta, rfl, hta, hde⟩
      | succ l =>
        obtain ⟨D, b', mb', ta', hi, hta', hde'⟩ := inferTypeCore_spine_defeq as
          (f := .app f a) (tf := body'.instantiate1 a) (m := m₀) (by simp at hm; omega)
          (SameDoms.instantiate1 m₀ 0 hsd.2) hfa h l (by omega)
        exact ⟨D, b', mb', ta', hi, hta', hde'⟩

/-- An application spine erasure-equal to another: heads and arguments
pairwise. -/
theorem erasedEq_mkAppN_args :
    ∀ (as : List Expr) {as' : List Expr} {f f' : Expr}, as'.length = as.length →
      Expr.ErasedEq (Expr.mkAppN f' as') (Expr.mkAppN f as) →
      Expr.ErasedEq f' f ∧
        ∀ (j : Nat) (x x' : Expr), as[j]? = some x → as'[j]? = some x' → Expr.ErasedEq x' x
  | [], [], _, _, _, h => ⟨h, fun j x x' hx _ => nomatch hx⟩
  | a :: as, a' :: as', f, f', hl, h => by
    obtain ⟨hh, hargs⟩ := erasedEq_mkAppN_args as (as' := as') (f := .app f a) (f' := .app f' a')
      (by simpa using hl) h
    refine ⟨hh.1, fun j x x' hx hx' => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hx'
      subst hx hx'
      exact hh.2
    | succ j => exact hargs j x x' (by simpa using hx) (by simpa using hx')

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo openPisAtFvars closeTelescope
  ClassGen ClassGenScoped SameDoms classGenRecTy classBinder BinderMeta GenRecRun ClassRecTyRun
  FEnv mkFEnv NestState TargetMajor RecShape BlockShape BlockParts instPisWith)

variable {μ : CheckMode}

/-- A leaf of an argument is a leaf of the application spine. -/
theorem fvarLeaves_mkAppN_arg {l : Nat × Expr} :
    ∀ (as : List Expr) {f a : Expr}, a ∈ as → l ∈ a.fvarLeaves →
      l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, ha, _ => nomatch ha
  | b :: as, f, a, ha, hl => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact fvarLeaves_mkAppN_head as (f := .app f a)
        (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl)
    · exact fvarLeaves_mkAppN_arg as (f := .app f b) ha hl

section GenRun

variable {F : Nat} {env₁ envC : Env} {p : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **A member class, as the run checked it**: the member's own
inductive, at the block's levels, over the canonical parameters. -/
theorem genRec_memberClass
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c t : Nat} (hm : (R.Ms.getD c default).member = some t) :
    p.toBlockShape.memberNames.findIdx? (· == (R.Ms.getD c default).ind) = some t ∧
    (R.Ms.getD c default).lvls = p.lps.map .param ∧
    (R.Ms.getD c default).ds = R.ctx.params.take p.nP := by
  by_cases hc : c < R.Ms.length
  · obtain ⟨hlenN, hallN⟩ := ConLeche.classesNfs_run R.hMs
    obtain ⟨hlenK, hallK⟩ := ConLeche.classMajors_run R.hMs₀
    have hc₀ : c < R.Ms₀.length := by omega
    obtain ⟨nfs, hMc, -⟩ := hallN c _ (List.getElem?_eq_getElem hc₀)
    have hck : c < (R.rd.classes.map (ConLeche.classKeyCanon R.ctx.params)).length := by
      omega
    obtain ⟨M, hM, ⟨CM⟩⟩ := hallK c _ (List.getElem?_eq_getElem hck)
    rw [List.getElem?_eq_getElem hc₀, Option.some.injEq] at hM
    have hget : R.Ms.getD c default = { M with nfs := nfs } := by
      rw [List.getD_eq_getElem?_getD, hMc, hM, Option.getD_some]
    rw [hget] at hm ⊢
    have hmaj := CM.major
    cases hmaj with
    | member I t' ms ctorsA hfn ht hms hctors hpar nfs' =>
      simp only [Option.some.injEq] at hm
      subst hm
      exact ⟨ht, rfl, rfl⟩
    | outside => exact nomatch hm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none] at hm
    exact nomatch hm

set_option maxHeartbeats 1600000 in
/-- **A member-class recursor's parameter domains were compared with its
member's**: the stored (generated) type of a recursor whose class is the
member `T_t` infers its major domain `T_t p⃗ ı⃗` — over the prefix's own
parameter variables — and the application rule compares each variable's
type, the stored `l`-th prefix domain, with `T_t`'s `l`-th parameter
domain at the earlier variables; moved to the prefix's depth. -/
theorem genMemberRec_paramDefeq (hμ : μ.verifiedChecks = true) (hwf : ConLeche.EnvWF envC)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hg : ClassGenScoped R.g) {i c : Nat} {rc : RecShape} {cvG : ConstantVal}
    (hc : R.rd.recCls[i]? = some c)
    (T : ClassRecTyRun μ F (mkFEnv envC) R.g p.k rc c cvG) (htgt : rc.tgt < p.k) :
    ∃ I, p.toBlockShape.memberNames.findIdx? (· == I) = some rc.tgt ∧
      ∀ (cvT : ConstantVal) caps, envC.find? I = some (.indInfo cvT caps) →
        cvT.levelParams = p.lps → cvT.type.hasFvar = false → SameDoms p.nP cvT.type cvT.type →
        ∃ (xs : List Expr) (o : Expr) (F' : Nat), openPisAtFvars p.nP cvG.type 0 = some (xs, o) ∧
          ∀ l, l < p.nP → ∃ D b mb, instPisWith (xs.take l) cvT.type = some (.forallE D b mb) ∧
            ConLeche.isDefEqCore μ envC F' p.nP ((xs.map Expr.fvarTypeD).getD l default) D
              = .ok true := by
  have hcv : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) envC
      { rc.cvR with type := T.gty } = .ok cvG := by
    rw [← ConLeche.checkConstantValF_eq]; exact T.hcv
  obtain ⟨-, -, -, -, -, hfv0, type, stype, u0, hann, -, -, hinf, -, hcvEq⟩ :=
    ConLeche.checkConstantVal_inv hcv
  have htype : cvG.type = type := by rw [hcvEq]
  dsimp only at hann hfv0
  obtain ⟨ifs, maj, hmaj, hifl, hgty, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg T.hgty
  -- the class: a member
  have hmem : (R.Ms.getD c default).member = some rc.tgt := by
    have h := T.htgt
    change rc.tgt = (R.Ms.getD c default).member.getD p.k at h
    cases hmm : (R.Ms.getD c default).member with
    | none => rw [hmm] at h; simp at h; omega
    | some t => rw [hmm] at h; simp at h; rw [h]
  obtain ⟨hfi, hlv, hds⟩ := genRec_memberClass R hmem
  obtain ⟨tyI, bodyI, -, -, hmajE⟩ := ConLeche.ClassGen.major_inv hmaj
  change maj = Expr.mkAppN (.const (R.Ms.getD c default).ind (R.Ms.getD c default).lvls)
    ((R.Ms.getD c default).ds ++ ifs) at hmajE
  refine ⟨(R.Ms.getD c default).ind, hfi, ?_⟩
  intro cvT caps hfind hlps hfvT hsdT
  generalize hI : (R.Ms.getD c default).ind = I at hfind hmajE
  rw [hlv, hds] at hmajE
  -- the canonical parameters
  have hplen : R.ctx.params.length = p.nP := hg.params_len
  have hpar : ∀ (j : Nat) (x : Expr), R.ctx.params[j]? = some x →
      ∃ ty, x = .fvar j ty := fun j x hx => by
    obtain ⟨ty, h, -⟩ := hg.params j x hx; exact ⟨ty, h⟩
  rw [List.take_of_length_le (by omega)] at hmajE
  have hpl : R.pre.length = p.nP + R.rd.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  -- nothing to compare without parameters
  by_cases hnP : p.nP = 0
  · refine ⟨[], cvG.type, 0, by rw [hnP]; rfl, fun l hl => absurd hl (by omega)⟩
  -- the reset telescope, annotated
  obtain ⟨s, hm⟩ := ConLeche.classRead_recCls_motive R.hrd c (List.mem_of_getElem? hc)
  have hmv := ConLeche.ClassGen.motVar_eq (g := R.g) hm
  generalize hnds : R.g.pre ++ ifs.map classBinder ++ [(maj, (default : BinderMeta))] = nds
    at hgty hcl
  generalize hB : Expr.mkAppN (R.g.motVar c)
    (ifs ++ [.fvar (R.g.pre.length + ifs.length) maj]) = B at hgty hbb
  have hPlain : ConLeche.Expr.Plain B := by
    rw [← hB, hmv]
    refine ConLeche.Expr.Plain.mkAppN (by simp [ConLeche.Expr.Plain]) fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hxe, -⟩ := (ConLeche.ClassGen.major_scoped hg (by
        have := (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1; omega) hmaj).1 k _
        (List.getElem?_eq_getElem hk)
      rw [hxe]; trivial
    · simp only [List.mem_singleton] at ha
      subst ha; trivial
  rw [hgty] at hann hfv0
  obtain ⟨nds', B', hl', he', hB', hdoms⟩ := ConLeche.annotateCore_closeTelescope nds
    hcl hbb hPlain (Expr.ErasedEq.rfl _) hann
  have hcl' : ∀ q ∈ nds', q.1.looseBVarsBounded 0 = true := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨X, F', nd, hnd, hX, hann'⟩ := hdoms j _ (List.getElem?_eq_getElem hj)
    exact ConLeche.annotateCore_looseBVars F' X hann'
      (looseBVarsBounded_of_erasedEq hX (hcl nd (List.mem_of_getElem? hnd)))
  have hB'b : B'.looseBVarsBounded 0 = true := looseBVarsBounded_of_erasedEq hB' hbb
  obtain ⟨xs, rest, hop, -, hxs⟩ := open_of_erasedEq_closeTelescope nds' 0 B' type hcl' hB'b he'
  have hgA := annotate_syntax hann hfv0
    (ConLeche.closeTelescope_bounded nds 0 B hcl hbb)
  -- the major's position
  generalize hN : R.g.pre.length + ifs.length = N at hB
  have hndsLen : nds.length = N + 1 := by
    rw [← hnds, ← hN]; simp; omega
  have hlxs : xs.length = N + 1 := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop, hl', hndsLen]
  have hNP : p.nP ≤ N := by
    have : R.g.pre.length = R.pre.length := rfl
    omega
  have hndN : nds[N]? = some (maj, default) := by
    rw [← hnds, List.getElem?_append_right (by simp [hN.symm] <;> omega)]
    simp [← hN]
  obtain ⟨xN, hxN⟩ : ∃ x, xs[N]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ndN', hndN'⟩ : ∃ nd', nds'[N]? = some nd' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hl']; omega)⟩
  obtain ⟨X, F', nd, hnd, hX, hannX⟩ := hdoms N _ hndN'
  rw [hndN, Option.some.injEq] at hnd
  subst hnd
  -- the major domain: `I` applied to the prefix's parameter variables
  have hmajR : maj = Expr.mkAppN (.const I (p.lps.map .param)) (R.ctx.params ++ ifs) := hmajE
  have hPmaj : ConLeche.Expr.Plain maj := by
    rw [hmajR]
    refine ConLeche.Expr.Plain.mkAppN (by simp [ConLeche.Expr.Plain]) fun a' ha' => ?_
    rcases List.mem_append.mp ha' with ha' | ha'
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha'
      obtain ⟨ty, hxe⟩ := hpar k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; trivial
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha'
      obtain ⟨ty, hxe, -⟩ := (ConLeche.ClassGen.major_scoped hg (by
        have := (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1; omega) hmaj).1 k _
        (List.getElem?_eq_getElem hk)
      rw [hxe]; trivial
  obtain rfl : ndN'.1 = X :=
    ConLeche.annotateCore_plain F' (ConLeche.Expr.Plain.of_erasedEq hX hPmaj) hannX
  have hMD : Expr.ErasedEq xN.fvarTypeD maj :=
    Expr.ErasedEq.trans (hxs N xN ndN'.1 hxN (by rw [hndN']; rfl)) hX
  rw [hmajR] at hMD
  obtain ⟨f', as', hMDe, hf', has'⟩ := erasedEq_mkAppN_inv _ hMD
  obtain ⟨-, hargs⟩ := ConLeche.erasedEq_mkAppN_args _ has' (hMDe ▸ hMD)
  obtain rfl : f' = .const I (p.lps.map .param) := by
    match f', hf' with
    | .const n us, hf' => obtain ⟨rfl, rfl⟩ := hf'; rfl
  have hlas : as'.length = p.nP + ifs.length := by
    rw [has', List.length_append, hplen]
  -- the openers' shape
  have hidx := ConLeche.openPisAtFvars_index _ _ _ hop
  have hwty : Expr.WScoped 0 type := Expr.WScoped.of_not_hasFvar hgA.1
  have hxNe : ∃ tN, xN = .fvar N tN := by
    obtain ⟨tN, h⟩ := hidx N xN hxN; exact ⟨tN, by simpa using h⟩
  obtain ⟨tN, rfl⟩ := hxNe
  simp only [Expr.fvarTypeD] at hMDe
  -- the parameter arguments ARE the openers
  have hargEq : ∀ j, j < p.nP → as'[j]? = xs[j]? := by
    intro j hj
    obtain ⟨x', hx'⟩ : ∃ x', as'[j]? = some x' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨pj, hpj⟩ : ∃ x, R.ctx.params[j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨tyj, rfl⟩ := hpar j _ hpj
    have he := hargs j _ x' (by rw [List.getElem?_append_left (by omega), hpj]) hx'
    obtain ⟨T', rfl⟩ : ∃ T', x' = .fvar j T' := by
      match x', he with
      | .fvar j' T', he => exact ⟨T', by rw [show j' = j from he]⟩
    have hleaf : (j, T') ∈ (Expr.fvar N (Expr.mkAppN (.const I (p.lps.map .param)) as')).fvarLeaves := by
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ (fvarLeaves_mkAppN_arg as' (List.mem_of_getElem? hx')
        (by simp [Expr.fvarLeaves]))
    rw [← hMDe] at hleaf
    rcases ConLeche.Verify.openPisAtFvars_leaves _ hop _
        (Or.inr ⟨_, List.mem_of_getElem? hxN, hleaf⟩) with hl | hl
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hgA.1] at hl; exact nomatch hl
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hl
    obtain ⟨ty, hty⟩ := hidx q _ hq
    simp only [Expr.fvar.injEq, Nat.zero_add] at hty
    obtain ⟨rfl, rfl⟩ := hty
    rw [hx', hq]
  -- the inference, down to the major domain
  rw [hl', hndsLen] at hop
  obtain ⟨xsN, xs1, o, hopN, hop1, hxsplit⟩ := openPisAtFvars_split N (m := 1) hop
  have hlxsN : xsN.length = N := ConLeche.Verify.openPisAtFvars_length _ hopN
  obtain ⟨dom, bo, mbo, rfl⟩ : ∃ dom bo mbo, o = .forallE dom bo mbo := by
    cases o <;> first | exact ⟨_, _, _, rfl⟩ | simp [openPisAtFvars] at hop1
  simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop1
  obtain ⟨rfl, -⟩ := hop1
  have hdom : dom = tN := by
    rw [hxsplit, List.getElem?_append_right (by omega), hlxsN, Nat.sub_self] at hxN
    simp only [Nat.zero_add, List.getElem?_cons_zero, Option.some.injEq, Expr.fvar.injEq] at hxN
    exact hxN.2
  subst hdom
  obtain ⟨N₁, rfl⟩ : ∃ N₁, N = N₁ + 1 := ⟨N - 1, by omega⟩
  obtain ⟨bt, u, hbt, -⟩ := inferTypeCore_openPis_body hμ N₁ hopN hinf
  rw [Nat.zero_add] at hbt
  obtain ⟨F₀, tty, rfl, htty⟩ := ConLeche.inferTypeCore_forallE_dom hbt
  rw [hMDe] at htty
  obtain ⟨tf, hconst⟩ := inferTypeCore_mkAppN_fn_inv as' htty
  have htf : tf = cvT.type := by
    obtain ⟨ci, hci, -, rfl⟩ := ConLeche.inferTypeCore_const_inv hconst
    rw [hfind, Option.some.injEq] at hci
    subst hci
    change cvT.type.instantiateLevelParams cvT.levelParams (p.lps.map .param) = cvT.type
    rw [hlps]
    exact ConLeche.Expr.instantiateLevelParams_self _ _
  subst htf
  obtain ⟨o', hopP⟩ := ConLeche.openPisAtFvars_prefix p.nP (N₁ + 1 + 1) type 0 (by omega) hop
  refine ⟨xs.take p.nP, o', F₀, by rw [htype]; exact hopP, fun l hl => ?_⟩
  obtain ⟨D, b, mb, ta, hinst, hta, hde⟩ := ConLeche.inferTypeCore_spine_defeq as'
    (m := p.nP) (by omega) hsdT hconst htty l hl
  -- the argument: the `l`-th opener
  obtain ⟨xl, hxl⟩ : ∃ x, xs[l]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨Al, hAl⟩ := hidx l xl hxl
  rw [Nat.zero_add] at hAl
  subst hAl
  have hasl : as'.getD l default = .fvar l Al := by
    rw [List.getD_eq_getElem?_getD, hargEq l hl, hxl, Option.getD_some]
  rw [hasl] at hta
  obtain ⟨F₁, rfl⟩ : ∃ F₁, F₀ = F₁ + 1 := ⟨F₀ - 1, by have := inferTypeCore_pos hta; omega⟩
  obtain ⟨-, htaA⟩ := ConLeche.Rules.inferTypeCore_fvar_inv hta
  rw [htaA] at hde
  have htake : as'.take l = xs.take l := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < l
    · rw [List.getElem?_take, List.getElem?_take, if_pos hj, if_pos hj, hargEq j (by omega)]
    · rw [List.getElem?_take, List.getElem?_take, if_neg hj, if_neg hj]
  rw [htake] at hinst
  refine ⟨D, b, mb, by rw [List.take_take, Nat.min_eq_left (by omega)]; exact hinst, ?_⟩
  have hgetA : ((xs.take p.nP).map Expr.fvarTypeD).getD l default = Al := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, if_pos hl, hxl]
    rfl
  rw [hgetA]
  -- the scopes, and the move to the prefix's depth
  have hwA : Expr.WScoped l Al := by
    have := openPisAtFvars_typeWScoped (N₁ + 1 + 1) hop hwty l _ hxl
    simpa [Expr.fvarTypeD] using this
  have hwArgs : ∀ a ∈ xs.take l, Expr.WScoped l a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hjl : j < l := by rw [List.length_take] at hj; omega
    have hxj : xs[j]? = some (xs.take l)[j] := by
      rw [← List.getElem?_eq_getElem hj, List.getElem?_take, if_pos hjl]
    obtain ⟨Aj, hAj⟩ := hidx j _ hxj
    rw [hAj, Nat.zero_add]
    have := openPisAtFvars_typeWScoped (N₁ + 1 + 1) hop hwty j _ hxj
    rw [hAj] at this
    simp only [Expr.WScoped]
    exact ⟨hjl, by simpa [Expr.fvarTypeD] using this⟩
  have hwD : Expr.WScoped l D := by
    have h := ConLeche.wscoped_instPisWith hwArgs (Expr.WScoped.of_not_hasFvar hfvT) hinst
    simp only [Expr.WScoped] at h
    exact h.1
  rw [← ConLeche.isDefEqCore_depth_inv hwf (F₁ + 1) (d₁ := N₁ + 1) (d₂ := p.nP)
    (Expr.WScoped.to_wscopedB (hwA.mono (by omega)))
    (Expr.WScoped.to_wscopedB (hwD.mono (by omega)))
    (Expr.WScoped.to_wscopedB (hwA.mono (by omega)))
    (Expr.WScoped.to_wscopedB (hwD.mono (by omega)))]
  exact hde

/-- **The generated recursors share their parameter openers**: every
generated type is a telescope over the same reset prefix, annotated
(`SameDoms`), so its first `nP` opened variables are the same. -/
theorem genRec_paramOpeners_eq (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hg : ClassGenScoped R.g) {i i' c c' : Nat} {rc rc' : RecShape} {cvG cvG' : ConstantVal}
    (hrc : p.recs[i]? = some rc) (hc : R.rd.recCls[i]? = some c)
    (T : ClassRecTyRun μ F (mkFEnv envC) R.g p.k rc c cvG)
    (hrc' : p.recs[i']? = some rc') (hc' : R.rd.recCls[i']? = some c')
    (T' : ClassRecTyRun μ F (mkFEnv envC) R.g p.k rc' c' cvG')
    {xs xs' : List Expr} {o o' : Expr}
    (hop : openPisAtFvars p.nP cvG.type 0 = some (xs, o))
    (hop' : openPisAtFvars p.nP cvG'.type 0 = some (xs', o')) : xs = xs' := by
  obtain ⟨-, ⟨Y, B, hY⟩, -⟩ := genRecTy_run hμ R hg hrc hc T
  obtain ⟨-, ⟨Y', B', hY'⟩, -⟩ := genRecTy_run hμ R hg hrc' hc' T'
  have hpl : R.pre.length = p.nP + R.rd.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hs := ConLeche.SameDoms.closeTelescope_append R.pre Y Y' 0 B B'
  have hsA := ConLeche.SameDoms.annotate _ hs hY hY'
  exact ConLeche.SameDoms.open p.nP (ConLeche.SameDoms.mono (by omega) hsA) hop hop'

/-- **A member-targeting recursor exists** (the member recursors' name
pins, at a block declaring a family). -/
theorem genRec_memberRec_exists
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) :
    ∃ (i : Nat) (rc : RecShape), p.recs[i]? = some rc ∧ rc.tgt < p.k := by
  have hset := (ConLeche.targetRecPins_inv R.pins).nameSet
  unfold ConLeche.blockRecNameSetOk at hset
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at hset
  obtain ⟨⟨hlen, -⟩, -⟩ := hset
  have hk := R.hk
  have hne : (p.recs.filter fun rc => decide (rc.tgt < p.k)) ≠ [] := by
    intro h0
    have : (p.recs.filter fun rc => decide (rc.tgt < p.k)).length = p.members.length := hlen
    rw [h0] at this
    have hk' : 0 < p.toBlockShape.members.length := hk
    simp at this
    omega
  obtain ⟨rc, hrc⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter] at hrc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrc.1
  exact ⟨i, _, List.getElem?_eq_getElem hi, by simpa using hrc.2⟩

/-- **A former's domain at another opening's variables**: `T`'s `l`-th
parameter domain, instantiated at the first `l` variables of an opening
of a closed type, is scoped at `l`, bvar-closed, has only that
opening's variables as leaves, and is (up to erasure) the domain `T`'s
OWN opening binds. -/
theorem instDom_facts {tyA cvT : Expr} {n l : Nat} {xs tfvs : List Expr} {oA oT : Expr}
    {D b : Expr} {mb : BinderMeta}
    (hopA : openPisAtFvars n tyA 0 = some (xs, oA)) (hwA : Expr.WScoped 0 tyA)
    (hopT : openPisAtFvars n cvT 0 = some (tfvs, oT)) (hfvT : cvT.hasFvar = false)
    (hbT : cvT.looseBVarsBounded 0 = true) (hl : l < n)
    (hinst : instPisWith (xs.take l) cvT = some (.forallE D b mb)) :
    Expr.WScoped l D ∧ D.looseBVarsBounded 0 = true ∧
      (∀ lf ∈ D.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ xs) ∧
      ∃ x, tfvs[l]? = some x ∧ Expr.ErasedEq x.fvarTypeD D := by
  have hidx := ConLeche.openPisAtFvars_index _ _ _ hopA
  have hlx : xs.length = n := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hlt : tfvs.length = n := ConLeche.Verify.openPisAtFvars_length _ hopT
  -- the arguments: the opening's variables below `l`
  have hargs : ∀ a ∈ xs.take l, ∃ j Aj, j < l ∧ xs[j]? = some a ∧ a = .fvar j Aj := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hjl : j < l := by rw [List.length_take] at hj; omega
    have hxj : xs[j]? = some (xs.take l)[j] := by
      rw [← List.getElem?_eq_getElem hj, List.getElem?_take, if_pos hjl]
    obtain ⟨Aj, hAj⟩ := hidx j _ hxj
    exact ⟨j, Aj, hjl, hxj, by rw [hAj, Nat.zero_add]⟩
  have hwArgs : ∀ a ∈ xs.take l, Expr.WScoped l a := by
    intro a ha
    obtain ⟨j, Aj, hjl, hxj, rfl⟩ := hargs a ha
    have := openPisAtFvars_typeWScoped n hopA hwA j _ hxj
    simp only [Expr.WScoped]
    exact ⟨hjl, by simpa [Expr.fvarTypeD] using this⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ConLeche.wscoped_instPisWith hwArgs (Expr.WScoped.of_not_hasFvar hfvT) hinst
    simp only [Expr.WScoped] at h
    exact h.1
  · have h := ConLeche.looseBVarsBounded_instPisWith (fun a ha => by
      obtain ⟨j, Aj, -, -, rfl⟩ := hargs a ha; rfl) hbT hinst
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    exact h.1
  · intro lf hlf
    have hlf' : lf ∈ (Expr.forallE D b mb).fvarLeaves := by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hlf
    rcases ConLeche.fvarLeaves_instPisWith hinst lf hlf' with h | ⟨a, ha, h⟩
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfvT] at h; exact nomatch h
    · obtain ⟨j, Aj, -, hxj, rfl⟩ := hargs a ha
      simp only [Expr.fvarLeaves, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_of_getElem? hxj
      · exact openerType_leaves hopA hwA hxj lf (by simpa [Expr.fvarTypeD] using h)
  · -- `T`'s own opening at `l`, and its `l`-th variable
    obtain ⟨oTl, hopTl⟩ := ConLeche.openPisAtFvars_prefix l n cvT 0 (by omega) hopT
    obtain ⟨oTl1, hopTl1⟩ := ConLeche.openPisAtFvars_prefix (l + 1) n cvT 0 (by omega) hopT
    obtain ⟨f₁, f₂, o₁, hA1, hB1, hsplit⟩ := openPisAtFvars_split l (m := 1) hopTl1
    obtain ⟨rfl, rfl⟩ : f₁ = tfvs.take l ∧ oTl = o₁ := by
      have := Option.some.inj (hA1.symm.trans hopTl)
      exact ⟨congrArg Prod.fst this, (congrArg Prod.snd this).symm⟩
    obtain ⟨dom', b', m', rfl⟩ : ∃ dom' b' m', oTl = .forallE dom' b' m' := by
      cases oTl <;> first | exact ⟨_, _, _, rfl⟩ | simp [openPisAtFvars] at hB1
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hB1
    obtain ⟨rfl, -⟩ := hB1
    have htl : tfvs[l]? = some (.fvar l dom') := by
      have h1 : (tfvs.take (l + 1))[l]? = tfvs[l]? := by
        rw [List.getElem?_take, if_pos (by omega)]
      rw [← h1, hsplit, List.getElem?_append_right (by simp; omega), List.length_take,
        Nat.min_eq_left (by omega), Nat.sub_self]
      simp
    have hinstT := instPisWith_of_openPis l hopTl
    have hE : Expr.ErasedEqL (tfvs.take l) (xs.take l) := by
      refine erasedEqL_of_fvarIdx _ _ 0 (fun j x hx => ?_) (fun j x hx => ?_)
        (by simp [hlx, hlt])
      · have hj : j < l := by
          have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
        rw [List.getElem?_take, if_pos hj] at hx
        exact ConLeche.openPisAtFvars_index _ _ _ hopT j x hx
      · have hj : j < l := by
          have := (List.getElem?_eq_some_iff.mp hx).1; simp at this; omega
        rw [List.getElem?_take, if_pos hj] at hx
        exact hidx j x hx
    obtain ⟨r', hr', hEr⟩ := instPisWith_erasedEq hE (Expr.ErasedEq.rfl cvT) hinstT
    rw [hinst, Option.some.injEq] at hr'
    subst hr'
    exact ⟨_, htl, hEr.2.1⟩

end GenRun

/-! ## The certified hop, against terms over the first opening's variables -/

section PrefixDomsInst

universe w

variable {V : Type w} [SetTheory V]

variable {envT : Env} (hμ : μ.verifiedChecks = true)
  (mp : EnvModelM V μ envT) {ψ : Name → Nat} {fuel rP : Nat}
  {tyA : Expr} {fvsA : List Expr} {oA : Expr}
  (hopA : openPisAtFvars rP tyA 0 = some (fvsA, oA))
  (hwA : Expr.WScoped 0 tyA) (hbA : tyA.looseBVarsBounded 0 = true)
  {domsA domsB : List AnnotTerm}
  (hlenA : domsA.length = rP) (hlenB : domsB.length = rP)
  (hdA : ∀ (i : Nat) (x : Expr), fvsA[i]? = some x →
    denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (domsA.getD i default))
  {bs : List Expr}
  (hwbs : ∀ i, i < rP → Expr.WScoped i (bs.getD i default))
  (hbbs : ∀ i, i < rP → (bs.getD i default).looseBVarsBounded 0 = true)
  (hleafbs : ∀ i, i < rP → ∀ lf ∈ (bs.getD i default).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsA)
  (hdB : ∀ i, i < rP →
    denoteMeta mp.base2.acval envT ψ i (bs.getD i default) = some (domsB.getD i default))
  (hokA : ∀ i, i < rP → ∀ (ρ : Nat → V) (ys : List V),
    SpineFit ρ (domsA.take i) ys → WellDenotedV V (consList ys ρ) (domsA.getD i default))
  (hokB : ∀ i, i < rP → ∀ (ρ : Nat → V) (ys : List V),
    SpineFit ρ (domsB.take i) ys → WellDenotedV V (consList ys ρ) (domsB.getD i default))
  (hdeq : ∀ i, i < rP →
    ConLeche.isDefEqCore μ envT fuel rP ((fvsA.map Expr.fvarTypeD).getD i default)
        (bs.getD i default) = .ok true)

include hμ hopA hwA hbA hlenA hlenB hdA hwbs hbbs hleafbs hdB hokA hokB hdeq in
/-- **The certified hop's reading half, against terms over the first
opening's variables** — `prefixDoms_agree` with the second telescope's
`l`-th domain given as a term `bs l` whose variables are the FIRST
opening's (`hleafbs`): its `CtxOk` is then the first opening's own, and
no agreement below `l` is needed for it. -/
theorem prefixDoms_agree_inst :
    ∀ l, l < rP → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ domsA ys →
      interp V (consList (ys.take l) ρ₁) (domsA.getD l default)
        = interp V (consList (ys.take l) ρ₁) (domsB.getD l default) := by
  obtain ⟨-, -, ihd, -⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) fuel
  have hlA : fvsA.length = rP := ConLeche.Verify.openPisAtFvars_length _ hopA
  have hlbA := (ConLeche.Verify.openPisAtFvars_bounded _ hopA hbA).2
  have hentA : ∀ i, i < rP → domsA.reverse[rP - 1 - i]? = some (domsA.getD i default) :=
    fun i hi => getElem?_reverse_entry hlenA hi
  intro l
  induction l using Nat.strongRecOn with
  | _ l IH =>
    intro hl ρ₁ ys hfitY
    have hylen : ys.length = rP := by rw [SpineFit.length_eq hfitY, hlenA]
    have hokAf : ∀ i, i < l → ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
        WellDenotedV V (shiftE (rP - i) 0 ρ) (domsA.getD i default) := by
      intro i hi ρ hρ
      obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
      rw [shiftE_consList_take i hzlen]
      exact hokA i (by omega) ρ₂ (zs.take i) (spineFit_take_any hfitZ i)
    -- the two subjects
    obtain ⟨xA, hxA⟩ : ∃ x, fvsA[l]? = some x :=
      ⟨fvsA[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hsubA : (fvsA.map Expr.fvarTypeD).getD l default = Expr.fvarTypeD xA := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hxA]; rfl
    -- `CtxOk` for both, at the FIRST opening's context
    have hctxA : CtxOk mp.base2 ψ rP domsA.reverse (Expr.fvarTypeD xA) :=
      ctxOk_openerType hopA hwA (by simp [hlenA]) hdA hentA hl hxA
        (fun i hi ρ hρ => rfl) hokAf
    have hctxB : CtxOk mp.base2 ψ rP domsA.reverse (bs.getD l default) :=
      ctxOk_of_openers_congr mp.base2.acval_closed (Aa := fun i => domsA.getD i default)
        (Ba := fun i => domsA.getD i default) (by simp [hlenA])
        (by simpa using ConLeche.openPisAtFvars_index rP tyA 0 hopA)
        (by simpa using (ConLeche.openPisAtFvars_WScoped rP tyA 0 hopA hwA).1)
        hdA (hleafbs l hl) (Expr.fvarLeaves_lt_of_wscoped (hwbs l hl))
        (fun i hi => hentA i (by omega))
        (fun _ _ _ _ _ => rfl) (fun i hi _ ρ hρ => hokAf i hi ρ hρ)
    -- the readings at the opening's own depth
    have hwsA : Expr.WScoped rP (Expr.fvarTypeD xA) := by
      have := openPisAtFvars_typeWScoped rP hopA hwA l xA hxA
      rw [Nat.zero_add] at this
      exact this.mono (by omega)
    have hwsB : Expr.WScoped rP (bs.getD l default) := (hwbs l hl).mono (by omega)
    have hrdA : denoteMeta mp.base2.acval envT ψ rP (Expr.fvarTypeD xA)
        = some ((domsA.getD l default).liftN (rP - l) 0) := by
      have hw := openPisAtFvars_typeWScoped rP hopA hwA l xA hxA
      rw [Nat.zero_add] at hw
      rw [denoteMeta_lift mp.base2.acval_closed hw rP (by omega), hdA l xA hxA]
      rfl
    have hrdB : denoteMeta mp.base2.acval envT ψ rP (bs.getD l default)
        = some ((domsB.getD l default).liftN (rP - l) 0) := by
      rw [denoteMeta_lift mp.base2.acval_closed (hwbs l hl) rP (by omega), hdB l hl]
      rfl
    -- the gradings at the opening's own depth
    have hokAl : ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
        WellDenotedV V ρ ((domsA.getD l default).liftN (rP - l) 0) := by
      intro ρ hρ
      refine (WellDenotedV_liftN V (rP - l) _ 0 ρ).mpr ?_
      obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
      rw [shiftE_consList_take l hzlen]
      exact hokA l hl ρ₂ (zs.take l) (spineFit_take_any hfitZ l)
    have hokBl : ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
        WellDenotedV V ρ ((domsB.getD l default).liftN (rP - l) 0) := by
      intro ρ hρ
      refine (WellDenotedV_liftN V (rP - l) _ 0 ρ).mpr ?_
      obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
      rw [shiftE_consList_take l hzlen]
      refine hokB l hl ρ₂ (zs.take l) ?_
      refine spineFit_congr_walk (by rw [List.length_take, List.length_take, hlenA, hlenB]) ?_
        (spineFit_take_any hfitZ l)
      intro j hj
      rw [List.length_take, hlenA] at hj
      have hjl : j < l := by omega
      rw [getD_take_of_lt hjl, getD_take_of_lt hjl, List.take_take,
        show min j l = j from by omega]
      exact IH j hjl (by omega) ρ₂ zs hfitZ
    -- the hop
    have hlbAx := hlbA xA (List.mem_of_getElem? hxA)
    have hLA := leavesBounded_of_openers hlbA (openerType_leaves hopA hwA hxA)
    have hLB := leavesBounded_of_openers hlbA (hleafbs l hl)
    have hsat : Sat V domsA.reverse (consList ys ρ₁) := by
      simpa using sat_of_spineFit (Sat_nil V ρ₁) hfitY
    have heq : interp V (consList ys ρ₁) ((domsA.getD l default).liftN (rP - l) 0)
        = interp V (consList ys ρ₁) ((domsB.getD l default).liftN (rP - l) 0) :=
      ihd (hsubA ▸ hdeq l hl) hwsA hlbAx hLA hwsB (hbbs l hl) hLB
        hctxA hctxB hrdA hrdB hokAl hokBl (consList ys ρ₁) hsat
    rw [interp_liftN, interp_liftN, shiftE_consList_take l hylen] at heq
    exact heq

include hμ hopA hwA hbA hlenA hlenB hdA hwbs hbbs hleafbs hdB hokA hokB hdeq in
/-- **The certified hop, against terms over the first opening's
variables**: a fitting spine of the first opening's domains fits the
terms'. -/
theorem prefixDoms_spineFit_inst {ρ₀ : Nat → V} {xs : List V} (hfit : SpineFit ρ₀ domsA xs) :
    SpineFit ρ₀ domsB xs :=
  spineFit_congr_walk (by rw [hlenA, hlenB])
    (fun l hl => prefixDoms_agree_inst hμ mp hopA hwA hbA hlenA hlenB hdA hwbs hbbs hleafbs hdB
      hokA hokB hdeq l (by omega) ρ₀ xs hfit) hfit

end PrefixDomsInst

/-! ## The parameters' fit -/

section Fit

universe w'

variable {V : Type w'} [SetTheory V]

set_option maxHeartbeats 1600000 in
/-- **The generated recursors' parameter domains fit the block's**, at
the members' run facts (`BlockMembersRun`): a spine fitting any stored
recursor's rule prefix fits the block's parameters on its first `nP`
values. -/
theorem genParams_fit_run (hμ : μ.verifiedChecks = true) {F : Nat} {envI envC : Env}
    {pp : BlockParts} {nestedBit : Bool} {pos : NestState} {cvTas : List ConstantVal}
    {block : List ConstantInfo} {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} (mpC : EnvModelM V μ envC)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hg : ClassGenScoped R.g) {dR : BlockData V}
    (hmr : BlockMembersRun mpC.base2 dR pp.toBlockShape cvTas) :
    ∀ c, c < (ConLeche.tgtRs out).length → ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (ConLeche.tgtRs out) ψ c)
        xs →
      SpineFit ρ (dR.params ψ) (xs.take dR.nP) := by
  intro c hc ψ ρ xs hfit
  have h := recStage_of_gen hμ R hg
  obtain ⟨hnPq, hkq, hlenCv, hcvF, hmsF, -, hparIff⟩ := hmr
  have hnPq' : dR.nP = pp.nP := hnPq
  -- recursor `c`
  have hlenT : (ConLeche.tgtRs out).length = pp.recs.length := by
    obtain ⟨S⟩ := h; exact S.len
  obtain ⟨rc, hrc⟩ : ∃ rc, pp.recs[c]? = some rc := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨cc, cvG, rhss, hcc, -, ⟨T⟩, ho, -, -⟩ := genRecRun_at R hrc
  have hr : (ConLeche.tgtRs out)[c]? = some (cvG, rhss, (R.Ms.getD cc default).nIdx,
      (R.Ms.getD cc default).ctors) := by
    simp [ConLeche.tgtRs, List.getElem?_map, ho]
  -- a member recursor, and its comparison
  obtain ⟨i0, rc0, hrc0, htgt⟩ := genRec_memberRec_exists R
  obtain ⟨c0, cvG0, -, hc0, -, ⟨T0⟩, -, -, -⟩ := genRecRun_at R hrc0
  obtain ⟨I, hfi, hall⟩ := genMemberRec_paramDefeq hμ mpC.base2.wf R hg hc0 T0 htgt
  -- its member's former
  have hkt : rc0.tgt < dR.k := by rw [hkq]; exact htgt
  obtain ⟨cvTP, hcvT⟩ : ∃ cv, cvTas[rc0.tgt]? = some cv :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨hnm, hlpsT, ⟨caps, hfindT⟩, hfvT, hbndT, hFD⟩ := hcvF _ _ hcvT
  have hI : I = cvTP.name := by
    obtain ⟨hlt, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hmem : pp.toBlockShape.members[rc0.tgt]? = some (pp.toBlockShape.members[rc0.tgt]'(by
      simpa [ConLeche.BlockShape.memberNames] using hlt)) := List.getElem?_eq_getElem _
    obtain ⟨hnm', -⟩ := hmsF _ _ hmem
    have hI' : pp.toBlockShape.memberNames[rc0.tgt] = I := by simpa using hbeq
    rw [← hI', ← hnm]
    simp only [ConLeche.BlockShape.memberNames, List.getElem_map]
    exact hnm'.symm
  subst hI
  obtain ⟨bsT, sT, hstrip⟩ := hFD.syn
  have hsdT : SameDoms pp.nP cvTP.type cvTP.type :=
    ConLeche.SameDoms.mono (by rw [← hnPq']; omega) (ConLeche.SameDoms.of_stripPis _ hstrip)
  obtain ⟨xs0, o0, F', hop0, hdeqs⟩ := hall cvTP caps hfindT hlpsT hfvT hsdT
  -- recursor `c`'s parameter openers are the same
  obtain ⟨fvsL, conclL, hopL, -, -, hlenRds, -, hbind, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have hle := blockRecHrPle (p := pp) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hrP, -, -⟩ := genRecTy_run hμ R hg hrc hcc T
  obtain ⟨-, -, hRc⟩ := ConLeche.recShape_at (q := pp.toBlockShape) hrc
  have hpl : R.pre.length = pp.nP + R.rd.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hroom : pp.nP ≤ pp.toBlockShape.rulePrefixAt c := by
    rw [hRc, hrP, hpl]; exact Nat.le_add_right _ _
  obtain ⟨oc, hopc⟩ := ConLeche.openPisAtFvars_prefix pp.nP _ cvG.type 0 (by omega) hopL
  have hxs : fvsL.take pp.nP = xs0 := genRec_paramOpeners_eq hμ R hg hrc hcc T hrc0 hc0 T0 hopc hop0
  rw [hxs] at hopc
  obtain ⟨hwA, hbA⟩ := recStage_tyClosed h hr
  -- the FIRST telescope: recursor `c`'s parameter domains
  have hlenPd := blockRulePdomsAV_length hμ mpC h hr ψ
  generalize hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (ConLeche.tgtRs out) ψ c
    = pdoms at hfit hlenPd
  have hlenA : (pdoms.take pp.nP).length = pp.nP := by
    rw [List.length_take, hlenPd]; omega
  have hdA : ∀ (i : Nat) (x : Expr), xs0[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((pdoms.take pp.nP).getD i default) := by
    intro i x hx
    have hi : i < pp.nP := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [← hxs, List.length_take] at this; omega
    have hx' : fvsL[i]? = some x := by
      rw [← hxs, List.getElem?_take, if_pos hi] at hx; exact hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbind i x hx'
    rw [hreadD, getD_take_of_lt hi, ← hPd, blockRulePdomsAV, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_take, if_pos (by omega), hpd]
    rfl
  have hgrA := blockRulePdomsAV_graded hμ mpC h hr ψ
  rw [hPd] at hgrA
  have hokA : ∀ i, i < pp.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((pdoms.take pp.nP).take i) ys →
      WellDenotedV V (consList ys ρ') ((pdoms.take pp.nP).getD i default) := by
    intro i hi ρ' ys hys
    rw [List.take_take, Nat.min_eq_left (by omega)] at hys
    rw [getD_take_of_lt hi]
    exact hgrA i (by omega) ρ' ys hys
  -- the SECOND telescope: the member's parameter domains
  have hppsLen : (dR.ppsM rc0.tgt ψ).length = dR.nP + dR.nIdxAt rc0.tgt := hFD.len ψ
  obtain ⟨tfvs, trest, hopT⟩ := ConLeche.SameDoms.open_isSome pp.nP (d := 0) hsdT
  obtain ⟨ppsT, bT, hstT, -, -, hbindT⟩ :=
    denoteMeta_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) pp.nP hopT (hFD.read ψ)
  have hppsT : ppsT = (dR.ppsM rc0.tgt ψ).take pp.nP := by
    have := stripPisAV_mkPisAV_take pp.nP (dR.ppsM rc0.tgt ψ)
      (.sort (dR.resSort.eval ψ)) (by rw [hppsLen, hnPq']; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hdBT : ∀ (i : Nat) (x : Expr), tfvs[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x)
        = some ((((dR.ppsM rc0.tgt ψ).take dR.nP).map (·.2.2)).getD i default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbindT i x hx
    rw [Nat.zero_add] at hreadD
    rw [hreadD, hnPq', ← hppsT, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
    rfl
  have hlenB : (((dR.ppsM rc0.tgt ψ).take dR.nP).map (·.2.2)).length = pp.nP := by
    rw [List.length_map, List.length_take, hppsLen]; omega
  have hokB : ∀ i, i < pp.nP → ∀ (ρ' : Nat → V) (ys : List V),
      SpineFit ρ' ((((dR.ppsM rc0.tgt ψ).take dR.nP).map (·.2.2)).take i) ys →
      WellDenotedV V (consList ys ρ') ((((dR.ppsM rc0.tgt ψ).take dR.nP).map (·.2.2)).getD i
        default) := by
    intro i hi ρ' ys hys
    exact prefixDoms_graded_of_tower (V := V) (cc := .sort (dR.resSort.eval ψ))
      (by rw [hppsLen]; omega) (fun ρ'' => hFD.okTy ψ ρ'') (by omega) hys
  -- the compared terms
  let Dof : Nat → Expr := fun l =>
    match instPisWith (xs0.take l) cvTP.type with
    | some (.forallE D _ _) => D
    | _ => default
  have hDof : ∀ l, l < pp.nP → ∃ b mb, instPisWith (xs0.take l) cvTP.type
      = some (.forallE (Dof l) b mb) ∧
      ConLeche.isDefEqCore μ envC F' pp.nP ((xs0.map Expr.fvarTypeD).getD l default) (Dof l)
        = .ok true := by
    intro l hl
    obtain ⟨D, b, mb, hinst, hde⟩ := hdeqs l hl
    have hD : Dof l = D := by simp only [Dof, hinst]
    rw [hD]
    exact ⟨b, mb, hinst, hde⟩
  have hbsget : ∀ l, l < pp.nP → ((List.range pp.nP).map Dof).getD l default = Dof l := by
    intro l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]; rfl
  have hfacts : ∀ l, l < pp.nP → Expr.WScoped l (Dof l) ∧ (Dof l).looseBVarsBounded 0 = true ∧
      (∀ lf ∈ (Dof l).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ xs0) ∧
      ∃ x, tfvs[l]? = some x ∧ Expr.ErasedEq x.fvarTypeD (Dof l) := by
    intro l hl
    obtain ⟨b, mb, hinst, -⟩ := hDof l hl
    exact instDom_facts hopc hwA hopT hfvT hbndT hl hinst
  have hfitA : SpineFit ρ (pdoms.take pp.nP) (xs.take pp.nP) :=
    spineFit_take hfit (by rw [hlenPd]; omega)
  have hfitB := prefixDoms_spineFit_inst (V := V) (fuel := F') hμ mpC hopc hwA hbA hlenA hlenB hdA
    (bs := (List.range pp.nP).map Dof)
    (fun l hl => by rw [hbsget l hl]; exact (hfacts l hl).1)
    (fun l hl => by rw [hbsget l hl]; exact (hfacts l hl).2.1)
    (fun l hl => by rw [hbsget l hl]; exact (hfacts l hl).2.2.1)
    (fun l hl => by
      rw [hbsget l hl]
      obtain ⟨x, hx, hE⟩ := (hfacts l hl).2.2.2
      rw [← denoteMeta_erasedEq hE, hdBT l x hx])
    hokA hokB (fun l hl => by
      rw [hbsget l hl]
      obtain ⟨_, _, -, hde⟩ := hDof l hl
      exact hde) hfitA
  -- the members' parameter agreement
  have hlenPD : (dR.params ψ).length = dR.nP := by
    obtain ⟨cvT0, hcvT0⟩ : ∃ cvT0, cvTas[0]? = some cvT0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, -, -, -, -, hFD0⟩ := hcvF _ _ hcvT0
    rw [BlockData.params, List.length_map, List.length_take, hFD0.len ψ]; omega
  have hsat : Sat V ((((dR.ppsM rc0.tgt ψ).take dR.nP).map (·.2.2)).reverse)
      (consList (xs.take pp.nP) ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfitB
  rw [hnPq']
  exact spineFit_of_sat_consList (by rw [hfitB.length_eq, hlenB, hlenPD, hnPq'])
    ((hparIff _ hkt ψ _).mp hsat)

end Fit

end ConLeche.Model
