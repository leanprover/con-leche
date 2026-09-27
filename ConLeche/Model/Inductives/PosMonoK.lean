module

public import ConLeche.Model.Inductives.UseMonoK
public import ConLeche.Verify.Inductives.UseOkK
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Verify.Cached.Erase
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge

public section

/-!
# The key-named positivity derivation is monotone (PRIMREC / NESTKN-M3)

`posDK_mono`: every judgment of a key-named positivity derivation
(`PosDKH`, `Verify/Inductives/PosDerivK.lean`) reads monotonically in the
holes, by ONE induction on the derivation.  The motive `MonoJK`:

* `field`/`tele` — along every hole relation at the judgment's layout
  (`HoleRelK`), at a site whose layout material is in the context
  (`LaySiteK`), the reading grows (the whnf step by `red_sound`, the member
  holes, the MET flexible families at their index count, the own holes at
  `DsF`, a container instance by its use);
* `ctors`/`node` — the node's walk and its frame fact (`CtorsMonoK`,
  `FrameMonoK`, `posDK_node_mono`);
* `use` — the used container's carrier grows between the user's key frames,
  its index telescope reads the same there (N2) (`UseConclK`, from
  `useMonoK`: the node's frame fact along the image of the user's relation);
* `bind` — a met family's binding grows as a value at the family's index
  count (`HoleOnVal`): a family of the user, the user's own hole at `DsF`, or
  a key used in turn (`holeOnVal_key`);
* `syn` — nothing (its uses serve the cache, never the reading).

The use case needs, at the user, the node's base instantiated by the match:
the bindings' readings and their fit to the families' types, the node's
parameters in the image context, … — the semantic side of the match
(`UseBridgeK`).  `posDK_mono` takes it as a hypothesis on the hook `hk`; the
hook that makes it hold is the kernel-facing part of M3 (`UseOkK`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey LayoutK LayoutOutK
  instPisWith fueledOps PosDKH PosJK PosKind UseHookK groupCtors grpSub matchStepK thetaK
  ParamOkK)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (ctx : NestCtx)

/-- **What a use proves** at its user (depth `d`, the user's spelling `ps`
read `psa`, along `R`): the used container is a member of a recorded block,
its parameter count is the spelling's, its index count is the one the user's
N2 check computed, its index telescope reads the same at the two key frames
of every related pair, and its carrier grows between them. -/
@[expose] def UseConclK (L : LayoutK) (kc : NestKey) (ps : List Expr) (d : Nat)
    (psa : List AnnotTerm) (R : FrameRel V) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = kc.cname ∧ ∃ cv caps,
    env.find? kc.cname = some (.indInfo cv caps) ∧
    (D.params (Level.substFn φ cv.levelParams kc.lvls)).length = ps.length ∧
    (∃ nI cty, ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨kc.cname, kc.lvls, ps⟩ = .ok (nI, cty) ∧
      (D.ids mm (Level.substFn φ cv.levelParams kc.lvls)).length = nI) ∧
    (∀ ρ ρ', R ρ ρ' → TeleEq (keyFrame psa d ρ) (keyFrame psa d ρ')
      (D.ids mm (Level.substFn φ cv.levelParams kc.lvls))) ∧
    ∀ ρ ρ', R ρ ρ' →
      FamLe (D.idx (Level.substFn φ cv.levelParams kc.lvls) (keyFrame psa d ρ) mm)
        (D.carrier (Level.substFn φ cv.levelParams kc.lvls) (keyFrame psa d ρ) mm)
        (D.carrier (Level.substFn φ cv.levelParams kc.lvls) (keyFrame psa d ρ') mm)

/-- **What a derivation proves** of its judgment's reading (see the module
docstring). -/
@[expose] def MonoJK : PosJK → Prop
  | .field L met dep _ e k _ =>
    (k.flat = false → ContCover mp ctx) → L.hi ≤ dep → Frame dep e →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ dep Δa e → denoteMeta mp.base2.acval env φ dep e = some ea →
      Graded V Δa ea → HoleRelK mp.base2 φ ctx L met dep Δa R →
      LaySiteK mp.base2 φ ctx L dep Δa → MonoOn R ea
  | .tele L met nF j cur ks _ res =>
    ((∃ k ∈ ks, k.flat = false) → ContCover mp ctx) → Frame (L.hi + j) cur →
    ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (L.hi + j) Δa cur →
      denoteMeta mp.base2.acval env φ (L.hi + j) cur = some ca → Graded V Δa ca →
      HoleRelK mp.base2 φ ctx L met (L.hi + j) Δa R → LaySiteK mp.base2 φ ctx L (L.hi + j) Δa →
      PiPosThen (ResultAt mp.base2 φ ctx.nP L.hi (L.hi + j + nF) res) nF R ca
  | .ctors L met cs => CtorsMonoK mp φ ctx L met cs
  | .node kc lo met => FrameMonoK mp φ ctx kc lo met
  | .use L met kc ps =>
    ContCover mp ctx → ∀ {d : Nat}, L.hi ≤ d → ∀ {Δa : List AnnotTerm} {R : FrameRel V},
      HoleRelK mp.base2 φ ctx L met d Δa R → LaySiteK mp.base2 φ ctx L d Δa → Δa.length = d →
      (∀ x ∈ ps, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
        CtxOkP mp.base2 φ d Δa x) →
      ∀ {psa : List AnnotTerm}, DenoteMetaSpine mp.base2.acval env φ d ps psa →
      ∀ {is : List Expr} {wa : AnnotTerm},
        denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const kc.cname kc.lvls) (ps ++ is))
          = some wa → Graded V Δa wa →
      UseConclK mp φ ctx L kc ps d psa R
  | .bind L met b =>
    ContCover mp ctx → ∀ {d : Nat}, L.hi ≤ d → ∀ {Δa : List AnnotTerm} {R : FrameRel V},
      HoleRelK mp.base2 φ ctx L met d Δa R → LaySiteK mp.base2 φ ctx L d Δa → Δa.length = d →
      Expr.WScoped L.hi b → b.looseBVarsBounded 0 = true → Expr.LeavesBounded b →
      CtxOkP mp.base2 φ d Δa b →
      ∀ {ba : AnnotTerm}, denoteMeta mp.base2.acval env φ d b = some ba → Graded V Δa ba →
      ∀ nI, ConLeche.BindArityK ctx L b nI → HoleOnVal R ba nI
  | .syn _ _ _ => True

/-- **The semantic side of a use's match** (the bridge the use case needs):
from a use rule's premises (with its hook) and the bind judgments' motive,
at a user site — the node's head is no member and not `Quot`, the used
container takes the spelling's parameter count, and the node's base is
instantiated by the match: the bindings read (`xs`), fit the families' types
(`tya`), the MET families' bindings grow, and the node's parameters are
scoped, read and in the image context, reading there as the user's
spelling. -/
@[expose] def UseBridgeK (ops : ConLeche.CheckerOps CheckM) (hk : UseHookK) : Prop :=
  ∀ {L : LayoutK} {met : List Nat} {kc kn : NestKey} {ps : List Expr} {lo : LayoutOutK}
    {metc : List Nat} {rs : List (List (Nat × Expr))} {bs : List (Nat × Expr)},
    (∃ r, ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨kc.cname, kc.lvls, ps⟩ = .ok r) →
    PosDKH ops env ctx hk (.node kn lo metc) →
    kc.cname ∈ lo.ginfo.map (·.1) → kc.lvls = kn.lvls → kc.ds = kn.ds →
    lo.L.dsF.length = ps.length →
    (lo.L.dsF.zip ps).mapM (matchStepK ctx L lo.L.nF) = .ok rs →
    ConLeche.bindInnerK ctx L (ConLeche.nodeOfK lo) (List.range lo.L.nF).reverse rs.flatten
      = .ok bs →
    (∀ j, j < lo.L.nF → bs.any (·.1 == j) = true) →
    (∀ x ∈ lo.L.dsF.zip ps, ParamOkK ops env ctx L lo.merged (thetaK ctx lo.L.nF bs) x.1 x.2) →
    hk L kc kn ps lo metc bs →
    (∀ b ∈ bs, b.1 ∈ metc → MonoJK mp φ ctx (.bind L met b.2)) →
    ContCover mp ctx → ∀ {d : Nat}, L.hi ≤ d → ∀ {Δa : List AnnotTerm} {R : FrameRel V},
    HoleRelK mp.base2 φ ctx L met d Δa R → LaySiteK mp.base2 φ ctx L d Δa → Δa.length = d →
    (∀ x ∈ ps, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOkP mp.base2 φ d Δa x) →
    ∀ {psa : List AnnotTerm}, DenoteMetaSpine mp.base2.acval env φ d ps psa →
    (ctx.names.contains kn.cname = false ∧ kn.cname ≠ ConLeche.quotName) ∧
    (∃ Lc, ConLeche.nestContainer ctx kc.cname = some (ps.length, Lc)) ∧
    ∃ (xs tya dsa : List AnnotTerm), xs.length = lo.L.nF ∧ tya.length = lo.L.nF ∧
      (∀ ρ, Sat V Δa ρ →
        SpineFit (dropV (d - ctx.hiAt 0) ρ) tya (xs.map (interp V ρ))) ∧
      (∀ (j : Nat) (key : NestKey) (nI : Nat), j < lo.L.nF → lo.L.fams[j]? = some (key, nI) →
        j ∈ metc → ∀ hj : j < xs.length, HoleOnVal R xs[j] nI) ∧
      (∀ x ∈ lo.L.dsF, Expr.WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true) ∧
      (∀ x ∈ lo.L.dsF, Expr.LeavesBounded x) ∧
      LaySiteK mp.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF)
        (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) ∧
      DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa ∧
      (∀ x ∈ lo.L.dsF, CtxOkP mp.base2 φ (ctx.hiAt 0 + lo.L.nF)
        (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) x) ∧
      (∀ ρ, Sat V Δa ρ →
        dsa.map (interp V (useVal xs (d - ctx.hiAt 0) ρ)) = psa.map (interp V ρ))

end Motive

variable {φ : Name → Nat}

/-- A key frame read `k` positions deeper, of the lifted parameters. -/
theorem keyFrame_liftN (dsa : List AnnotTerm) (h k : Nat) (ρ : Nat → V) :
    keyFrame (dsa.map (AnnotTerm.liftN k · 0)) (h + k) ρ = keyFrame dsa h (dropV k ρ) := by
  unfold keyFrame
  rw [List.map_map]
  congr 1
  · exact List.map_congr_left fun a _ => interp_liftN_drop k ρ a
  · funext j; unfold dropV; congr 1; omega

/-- A spine's head and arguments are as bvar-closed as the spine. -/
theorem looseBVarsBounded_mkAppN_inv {k : Nat} :
    ∀ {xs : List Expr} {f : Expr}, (Expr.mkAppN f xs).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true ∧ ∀ x ∈ xs, x.looseBVarsBounded k = true
  | [], _, h => ⟨h, fun _ hx => nomatch hx⟩
  | a :: as, f, h => by
    obtain ⟨hfa, has⟩ := looseBVarsBounded_mkAppN_inv (xs := as) (f := .app f a) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hfa
    refine ⟨hfa.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfa.2
    · exact has x hx

/-- **THE KEY-NAMED DERIVATION IS MONOTONE** (see the module docstring), given
the semantic side of the uses' matches (`UseBridgeK`) at the derivation's
hook. -/
theorem posDK_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F : Nat} {hk : UseHookK}
    (hbr : UseBridgeK mp φ ctx (fueledOps .verified F) hk) :
    ∀ {j : PosJK}, PosDKH (fueledOps .verified F) env ctx hk j → MonoJK mp φ ctx j := by
  intro j h
  induction h with
  | @const L met dep kb e w hw hocc =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    exact mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw _ wa hwa _ =>
      (ConstOn.of_noBVar hR.agree (denoteMeta_noBVar_of_nestOcc dep w hfrw.1 hhi hocc hwa)).monoOn
  | @pi L met dep kb e a b bm k nb hw hocc ha hb ihb =>
    intro hcov hhi hfr Δa ea R hC hea hgr hR hlay
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree
      (denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi ha hta)
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    exact MonoOn.pi 0 _ hA (ihb hcov (by omega) (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd)
      hCop hba hgB (hR.under hhi hA.monoOn) (hlay.under ta))
  | @hole L met dep kb e w i ty hw hocc hfn hlo hhi' hlen hpar hfree =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteMetaSpine.length_eq hsp
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have ht : i - ctx.nP < ctx.names.length := by
      simp only [ConLeche.NestCtx.hiAt] at hhi'; omega
    have hh := hR.member (i - ctx.nP) ht
    rw [show dep - 1 - (ctx.nP + (i - ctx.nP)) = dep - 1 - i by omega, ← hlen, hlenv] at hh
    exact MonoOn.holeApp hh hvs
  | @famHole L met dep kb e w i ty key nI hw hocc hfn hlo hhi' hj hfam hlen hfree hmet =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have hh := hR.fam (i - ctx.hiAt 0) key nI hj hfam hmet
    rw [show dep - 1 - (ctx.hiAt 0 + (i - ctx.hiAt 0)) = dep - 1 - i by omega, ← hlen,
      DenoteMetaSpine.length_eq hsp] at hh
    exact MonoOn.holeApp hh hvs
  | @ownHole L met dep kb e w i ty g hw hocc hfn hlo hhi' hj hg hle hpar hfree har =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine mono_of_whnf hin hw hfr hC hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ w.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    rw [← List.take_append_drop L.dsF.length w.getAppArgs] at hsp
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
    have hvs₂ := constOn_spine hR.agree hhi hsp₂ fun a ha =>
      ⟨hwsargs a (List.mem_of_mem_drop ha), hfree a ha⟩
    have hsp₁' : DenoteMetaSpine mp.base2.acval env φ dep L.dsF vs₁ := by
      rw [← hpar]; exact hsp₁
    have hh := hR.own (i - ctx.hiAt 0 - L.nF) g hg vs₁ hsp₁' vs₂.length (by
      have h2 := DenoteMetaSpine.length_eq hsp₂
      rw [List.length_drop] at h2
      omega)
    rw [show dep - 1 - (ctx.hiAt 0 + L.nF + (i - ctx.hiAt 0 - L.nF)) = dep - 1 - i by omega] at hh
    exact MonoOn.holeAppArgs hh hvs₂
  | @cont L met dep kb e w n us Lc nPc nI cty hw hocc hfn hnm hC hquot hlen hidx hds hnI huse
      ihu =>
    intro hcovk hhid hfr Δa ea R hC' hea hgr hR hlay
    have hcov := hcovk rfl
    refine mono_of_whnf hin hw hfr hC' hea hgr hR.dom fun hfrw hCw wa hwa hgw => ?_
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    generalize hargs : w.getAppArgs = args at hspine hlen hidx hds hnI huse ihu
    subst hspine
    have hwsargs := (wScoped_mkAppN _ hfrw.1).2
    have hbbargs := (looseBVarsBounded_mkAppN_inv hfrw.2.1).2
    have hdl : (args.take nPc).length = nPc := by rw [List.length_take]; omega
    have hps : ∀ x ∈ args.take nPc, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP mp.base2 φ dep Δa x := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
          (ConLeche.Expr.fvarB_le (hds x hx).2),
        ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1),
        fun l hl => hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl),
        hCw.of_subset fun l hl => leaves_mkAppN_arg (List.mem_of_mem_take hx) hl⟩
    rw [← List.take_append_drop nPc args] at hwa
    obtain ⟨fa, vs, hfa, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
    obtain ⟨vs₁, vs₂, -, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
    obtain ⟨D, hD, mm, hmm, hn, cv, caps, hf, hlenP, ⟨nI', cty', hnI', hids⟩, -, hle⟩ :=
      ihu hcov hhid hR hlay hC'.1 hps hsp₁ hwa hgw
    change D.member mm = n at hn
    subst hn
    rw [hnI] at hnI'
    obtain ⟨rfl, -⟩ : nI = nI' ∧ cty = cty' := by simpa using hnI'
    have hdrop : ∀ σ : Nat → V, dropV (dep - dep) σ = σ := by
      intro σ; funext i; simp [dropV]
    refine monoOn_of_famLe mp hD hmm hf (Nat.le_refl dep) hwa (by rw [hlenP])
      (by rw [List.length_drop, hids]; omega) (fun x hx => hwsargs x (List.mem_of_mem_take hx))
      hsp₁ hR.dom hgw (fun isa hisa => constOn_spine hR.agree hhid hisa fun a ha =>
        ⟨hwsargs a (List.mem_of_mem_drop ha), hidx a ha⟩) fun ρ ρ' hr => ?_
    rw [hdrop, hdrop]
    exact hle ρ ρ' hr
  | teleNil =>
    intro _ hfr Δa ca R _ hca _ hR _
    exact ⟨hR.agree, by simpa using hca, by simpa using hfr.1⟩
  | @teleCons L met nF j a b bm k nd ks nds res ha hs hb iha _ ihb =>
    intro hcovk hfr Δa ca R hC hca hgr hR hlay
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    have hA := iha (fun hk => hcovk ⟨k, List.mem_cons_self, hk⟩) (by omega) ⟨hws.1, hbb.1, hLa⟩
      hC.forallE_ty hta hgA hR hlay
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show L.hi + j + 1 = L.hi + (j + 1) by omega] at hCop hfr' hba
    have hrest := ihb (fun ⟨k', hk', hkf⟩ => hcovk ⟨k', List.mem_cons_of_mem _ hk', hkf⟩)
      hfr' hCop hba hgB
      (by rw [show L.hi + (j + 1) = L.hi + j + 1 by omega]; exact hR.under (by omega) hA)
      (by rw [show L.hi + (j + 1) = L.hi + j + 1 by omega]; exact hlay.under ta)
    rw [show L.hi + j + (nF + 1) = L.hi + (j + 1) + nF by omega]
    exact ⟨hA, hrest⟩
  | ctorsNil =>
    intro _ Δ R _ _ _ x hx
    exact nomatch hx
  | @ctorsCons L met cv nF crest cs ks nds cur htele hu4 hres hidx hrest ihtele ihrest =>
    intro hcov Δ R hR hlay hprem x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨ca, hfr, hC, hca, hgr⟩ := hprem _ List.mem_cons_self
      refine ⟨ca, cur, hca, hres, hidx, ?_⟩
      have := ihtele (fun _ => hcov) (by simpa using hfr) (by simpa using hC) (by simpa using hca)
        hgr (by simpa using hR) (by simpa using hlay)
      simpa using this
    · exact ihrest hcov hR hlay (fun y hy => hprem y (List.mem_cons_of_mem _ hy)) x hx
  | @node kc lo met hlay hwalk ih =>
    exact posDK_node_mono mp hin (ConLeche.nestLayoutK_spec hlay) ih
  | @use L met kc kn ps lo metc rs bs hinst hk52 hnode hgrp hlv hkds hlen hbs hinner hall hpar
      hbind hhook ihnode ihbind =>
    intro hcov d hd Δa R hR hlay hΔ hps psa hpsa is wa hwa hgr
    obtain ⟨hhd, hnPc, xs, tya, dsa, hxl, htyl, hsat, hmet, hdsw, hLds, hlayc, hdsa, hCds, hpos⟩ :=
      hbr hinst hnode hgrp hlv hkds hlen hbs hinner hall hpar hhook ihbind hcov hd hR hlay hΔ hps
        hpsa
    have hspec := ConLeche.PosDKH.node_spec hnode
    have hlvl : lo.L.lvls = kc.lvls := by rw [hspec.2.2.2.1, hlv]
    rw [← hlvl] at hwa
    obtain ⟨D, hD, mm, hmm, hn, cv, caps, hf, hnd, hlenP, hle⟩ := useMonoK mp hcov hspec hhd ihnode
      hR hd hΔ hgrp hwa hgr (fun x hx => Expr.WScoped.mono hd (hps x hx).1) hnPc hlen hpsa hxl
      htyl hsat hmet hdsw hLds hlayc hdsa hCds hpos
    rw [hlvl] at hlenP hle hwa
    obtain ⟨⟨nI, cty⟩, hnI⟩ := hinst
    -- N2 at the user
    obtain ⟨psa0, hpsa0, rfl⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hd
      (fun x hx => (hps x hx).1) hpsa
    obtain ⟨fa, vs, hfa, -, -⟩ := denoteMeta_mkAppN_inv hwa
    rw [← hn] at hfa
    obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK (by rw [hn]; exact hf) hfa
    change kc.lvls.length = cv.levelParams.length at hul
    have hrun : ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨D.member mm, kc.lvls, ps⟩
        = .ok (nI, cty) := by rw [hn]; exact hnI
    obtain ⟨-, hids, hte⟩ := n2_link mp hD hmm hcov.find hrun (by rw [hn]; exact hf) hnd hul
      hlenP (fun x hx => ⟨(hps x hx).1, (hps x hx).2.1⟩) hpsa0
    have hkf : ∀ σ : Nat → V, keyFrame (psa0.map (AnnotTerm.liftN (d - L.hi) · 0)) d σ
        = keyFrame psa0 L.hi (dropV (d - L.hi) σ) := by
      intro σ
      have := keyFrame_liftN psa0 L.hi (d - L.hi) σ
      rwa [show L.hi + (d - L.hi) = d by omega] at this
    refine ⟨D, hD, mm, hmm, hn, cv, caps, hf, hlenP, ⟨nI, cty, hnI, hids⟩, fun ρ ρ' hr => ?_, hle⟩
    rw [hkf, hkf]
    refine hte _ _ fun i hi => ?_
    refine hR.agree ρ ρ' hr (i + (d - L.hi)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  | @bindFam L met i ty hlo hhi hmet =>
    intro hcov d hd Δa R hR hlay hΔ hws hbb hLb hC ba hba hgr nI har
    rw [denoteMeta_fvar] at hba
    cases hba
    obtain ⟨key, hk⟩ := har.1 i ty rfl hlo hhi
    have hh := hR.fam (i - ctx.hiAt 0) key nI (by omega) hk hmet
    rw [show d - 1 - (ctx.hiAt 0 + (i - ctx.hiAt 0)) = d - 1 - i by omega] at hh
    intro ρ ρ' hr as has
    rw [interp_bvar, interp_bvar]
    exact hh ρ ρ' hr as has
  | @bindOwn L met b i ty hfn hlo hhi =>
    intro hcov d hd Δa R hR hlay hΔ hws hbb hLb hC ba hba hgr nI har
    obtain ⟨hargs, g, hg, hni⟩ := har.2.1 i ty hfn hlo hhi
    have hspine := Expr.mkAppN_getApp b
    rw [hfn, hargs] at hspine
    rw [← hspine] at hba
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hba
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hh := hR.own (i - ctx.hiAt 0 - L.nF) g hg vs hsp nI hni
    rw [show d - 1 - (ctx.hiAt 0 + L.nF + (i - ctx.hiAt 0 - L.nF)) = d - 1 - i by
      have := hR.hiEq; omega] at hh
    intro ρ ρ' hr as has
    rw [interp_mkAppN_foldl, interp_mkAppN_foldl, interp_bvar, interp_bvar, ← List.foldl_append,
      ← List.foldl_append]
    exact hh ρ ρ' hr as has
  | @bindKey L met b n us hfn huse ihu =>
    intro hcov d hd Δa R hR hlay hΔ hws hbb hLb hC ba hba hgr nI har
    have hspine := Expr.mkAppN_getApp b
    rw [hfn] at hspine
    have hws' := hws
    rw [← hspine] at hws' hba
    have hbb' := hbb
    rw [← hspine] at hbb'
    have hwsargs := (wScoped_mkAppN _ hws').2
    have hbbargs := (looseBVarsBounded_mkAppN_inv hbb').2
    have hps : ∀ x ∈ b.getAppArgs, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP mp.base2 φ d Δa x := fun x hx =>
      ⟨hwsargs x hx, hbbargs x hx,
        fun l hl => hLb l (by rw [← hspine]; exact leaves_mkAppN_arg hx hl),
        hC.of_subset fun l hl => by rw [← hspine]; exact leaves_mkAppN_arg hx hl⟩
    obtain ⟨fa, psa, hfa, hpsa, rfl⟩ := denoteMeta_mkAppN_inv hba
    have hba' : denoteMeta mp.base2.acval env φ d
        (Expr.mkAppN (.const n us) (b.getAppArgs ++ [])) = some (AnnotTerm.mkAppN fa psa) := by
      rw [List.append_nil]; exact hba
    obtain ⟨D, hD, mm, hmm, hn, cv, caps, hf, hlenP, ⟨nI', cty', hnI', hids⟩, hte, hle⟩ :=
      ihu hcov hd hR hlay hΔ hps hpsa hba' hgr
    obtain ⟨-, cty2, hnI2⟩ := har.2.2 n us hfn
    change ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨n, us, b.getAppArgs⟩ = _ at hnI'
    rw [hnI2] at hnI'
    obtain ⟨rfl, -⟩ : nI = nI' ∧ cty2 = cty' := by simpa using hnI'
    change D.member mm = n at hn
    subst hn
    rw [← hids]
    exact holeOnVal_key mp hD hmm hf hba hlenP.symm
      (fun x hx => Expr.WScoped.mono hd (hwsargs x hx)) hpsa hR.dom hgr hte hle
  | synNil => trivial
  | synUse => trivial

/-- **A derived member constructor is positive** (`memberCtorD_mono`'s form,
for the key-named derivation): every field's reading monotone under the
earlier ones along the frameless hole relation, the result's indices
hole-free — coverage needed only when some field's kind is not flat. -/
theorem memberCtorDK_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F nF : Nat} {hk : UseHookK}
    (hbr : UseBridgeK mp φ ctx (fueledOps .verified F) hk) {crest : Expr} {ks : List PosKind}
    {tyN : Expr} (hd : ConLeche.MemberCtorDKH (fueledOps .verified F) env ctx hk nF crest ks tyN)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContCover mp ctx)
    (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) :
    PiPosThen (ResultIdxConst ctx.nP) nF R ca := by
  obtain ⟨met, nds, res, htele, -, -, hhead, hok, -⟩ := hd
  have hroot : (ConLeche.rootLayoutK ctx).hi + 0 = ctx.hiAt 0 := by simp [ConLeche.rootLayoutK]
  have := posDK_mono mp hin hbr htele hcov (by rw [hroot]; exact hfr) (by rw [hroot]; exact hC)
    (by rw [hroot]; exact hca) hgr (by rw [hroot]; exact holeRelK_root hR)
    (by rw [hroot]; exact laySiteK_root)
  have hrh : (ConLeche.rootLayoutK ctx).hi = ctx.hiAt 0 := rfl
  rw [hrh, Nat.add_zero] at this
  exact PiPosThen.mono (fun _ _ h => resultIdxConst_of_resultAt (Nat.le_add_right _ _) hhead hok h)
    nF R ca this

end ConLeche.Model
