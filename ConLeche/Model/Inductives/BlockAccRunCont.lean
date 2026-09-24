module

public import ConLeche.Model.Inductives.BlockAccRun
public import ConLeche.Model.Inductives.BlockPosRunCont
public import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Model.Rules.Inputs

public section

/-!
# `NestedAccOwed` from the container case (lane ACCMODEL)

The block step of the accessibility route: at a block the install
walked with the route switch on, the hole operator is accessible with
one bound of the level (`NestedAccOwed`), GIVEN the container case
(`ContAccProvider`: at a walk's context with coverage, a state
invariant holding of the empty state under which the container case of
the run inversion is accessible — the resume note's item "ContAcc").

The twin of `blockCtorPos_of_run_gen`'s container branch: the state
invariant threaded through the block's constructors (each constructor's
run keeps it — `nestMemberCtor_acc` at the EMPTY relation), every
constructor's telescope accessible along the accessibility relation
(`blockCtorAcc_of_walk`), then `LfpDatum.accTuple_holeOp`.

This is a CONDITIONAL checkpoint (charter: conditional forms are not
solutions); it is discharged when `ContAccProvider` is proved.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckM NestCtx NestHole NestState NestFieldKind
  BlockParts BlockShape instPisWith nestAbstract nestMemberCtor fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-- **The container case, provided** (OWED — lane ACCMODEL's item
"ContAcc"): at a walk's context with coverage, a state invariant holding
of the empty state under which the container case is accessible. -/
@[expose] def ContAccProvider (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (mk : EnvModelM V .verified env) (ψ : Name → Nat) (ctx : NestCtx) (wl : Nat),
    ContCover mk ctx → ∃ I : NestState → Prop, I {} ∧
      ∀ (F : Nat) (rec : List NestHole → Nat → Nat → Expr → NestState →
          CheckM (NestFieldKind × Expr × NestState)),
        NestPosAcc mk.base2 ψ wl ctx (fun _ => True) I rec →
        ContAcc mk.base2 ψ wl ctx (fun _ => True) I F rec

/-- The empty relation is an accessibility hole relation of any context. -/
theorem holeRelA_empty {env : Env} (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (d : Nat) (Δa : List AnnotTerm) :
    HoleRelA m φ ctx [] d Δa (fun _ _ => False) where
  dom := fun _ _ h => h.elim
  agree := fun _ _ h => h.elim
  frame := fun _ _ h => by simp at h
  dsScoped := fun _ _ h => by simp at h
  symm := fun _ _ h => h.elim
  rich := fun _ _ h => h.elim

/-- Nothing to bound along a relation relating no frames. -/
theorem teleSmall_empty {wl : Nat} :
    ∀ (n : Nat) (R : FrameRel V) (ca : AnnotTerm), (∀ ρ ρ', ¬ R ρ ρ') → TeleSmall wl n R ca
  | 0, _, _, _ => trivial
  | n + 1, _, .pi _ _ _ B, h => ⟨fun ρ ρ₀ hR => absurd hR (h ρ ρ₀),
      teleSmall_empty n _ B fun _ _ ⟨_, ρ, ρ', _, _, hR, _⟩ => h ρ ρ' hR⟩
  | _ + 1, _, .bvar _, _ | _ + 1, _, .sort _, _ | _ + 1, _, .const _ _, _
  | _ + 1, _, .app _ _, _ | _ + 1, _, .lam _ _ _, _ | _ + 1, _, .eqE _ _, _
  | _ + 1, _, .fst _, _ | _ + 1, _, .snd _, _ | _ + 1, _, .prf, _ => trivial

/-- **`NestedAccOwed` from the container case** (see the module
docstring). -/
theorem nestedAccOwed_of_provider {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true)
    (F : Nat) (hprov : ContAccProvider V) : NestedAccOwed V μ F := by
  intro env mp d lps cvTas p₁ isRec p ctorsAs posKs hN hcore hH hrun hnames hlps hnP hnIdxs _ hk
    _ hinst hlenCA hctorsAs hclosed hnfs _ hcov ψ ρp hs hw hIdx _ hG
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨mk, hbk, hcovk⟩ := hcov
  obtain ⟨kinds, nfs⟩ := posKs
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv_gen hrun
  obtain ⟨cvTa0', fvsP', rest', holes', hcv0', hop0', hholes', hthr⟩ :=
    ConLeche.checkBlockPositivity_inv_I hrun
  rw [hcv0] at hcv0'
  obtain rfl := Option.some.inj hcv0'
  rw [hop0] at hop0'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using hop0'
  rw [hholes] at hholes'
  obtain rfl := Option.some.inj hholes'
  generalize hctx : p.nestCtx fvsP env.find? env.consts = ctx at hholes hall hthr
  have hcN : ctx.names = p.memberNames := by rw [← hctx]; rfl
  have hcC : ContCover mk ctx :=
    contCover_of (by rw [hcN]; exact hcovk) (fun n => by rw [← hctx]; rfl) (by rw [← hctx]; rfl)
  have hcore' : BlockHoleCtxFacts mk.base2 d lps cvTas p₁ isRec := by rw [hbk]; exact hcore
  have hin := Rules.RulesInputs.ofSem mk ψ
  obtain ⟨I, hI0, hprovI⟩ := hprov mk ψ ctx (d.w ψ) hcC
  have hkN : d.toLfp.k ≤ d.toLfp.N := Nat.le_add_right _ _
  -- the state invariant, threaded: every block constructor's run keeps it
  have hstep : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
      instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest →
      ∀ st₀ ks tyN st₁, (nfs.getD c []).getD j default = tyN → I st₀ →
        nestMemberCtor (fueledOps .verified F) env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) →
        I st₁ := by
    intro c' cs hcs j' cA hcA crest hcrest st₀ ks tyN st₁ hnf hI hm
    have hc' : c' < d.k := by
      rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hcs).1
    rw [hctorsAs c' hc'] at hcs
    obtain rfl := Option.some.inj hcs
    obtain ⟨hCf, hCb⟩ := hclosed c' j' cA hcA
    obtain ⟨crest', -, hcrest', -, -, ⟨ty, hty⟩, -⟩ :=
      hall c' (d.ctorsM c') (hctorsAs c' hc') j' cA hcA
    rw [← hctx] at hcrest hcrest' hm hty
    rw [hcrest] at hcrest'
    obtain rfl := Option.some.inj hcrest'
    obtain ⟨ab, abN, hhi, hca, -, -, -, -, hfr, hCP, hgr, -⟩ :=
      blockCtorHoleCtx hin hN hcore' hnames hlps hnP hnIdxs hk hcv0 hop0
        (by rw [hctx]; exact hholes) hcA hCf hCb hcrest hty hm
        (by rw [hnfs c' j' cA hcA]; exact hnf)
    rw [← hhi] at hca hgr hfr hCP
    rw [hctx] at hca hgr hfr hCP hm
    exact (nestMemberCtor_acc hin ctx F hw (hprovI F) hm (fun _ _ => trivial) hfr hI hCP hca hgr
      (holeRelA_empty mk.base2 ψ ctx _ _) (teleSmall_empty _ _ _ fun _ _ h => h)).2
  -- every constructor's telescope, accessible
  have hper : ∀ c j, ∃ oa : (Nat → Bool) × (Nat → (Nat → V) → V),
      c < d.toLfp.N → j < d.toLfp.nctors c →
        TeleAccP (d.w ψ) oa.2 0 (d.toLfp.MemberQ ψ) (d.toLfp.accRel ψ ρp) (d.absF ψ c j) ∧
        (∀ l τ τ', TAgr d.k oa.1 l τ τ' → oa.2 l τ = oa.2 l τ') ∧
        (∀ (i : Nat) (G : AnnotTerm), (d.absF ψ c j)[i]? = some G → oa.1 i = true →
          ∀ τ τ', TAgr d.k oa.1 i τ τ' → interp V τ G = interp V τ' G) ∧
        (∀ X X', InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
          InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X' →
          ∀ fs, SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs →
            SpineFit (d.toLfp.frame ψ ρp X') (d.absF ψ c j) fs →
            ∀ e ∈ d.absE ψ c j, interp V (consList fs (d.toLfp.frame ψ ρp X)) e
              = interp V (consList fs (d.toLfp.frame ψ ρp X')) e) := by
    intro c j
    by_cases hcj' : c < d.toLfp.N ∧ j < d.toLfp.nctors c
    · obtain ⟨hc, hj⟩ := hcj'
      have hck : c < d.k := by
        have : c < d.k + d.nInst := hc
        omega
      have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
      obtain ⟨crest, st₀, ks, tyN, st₁, hcrest, hI₀, hm, hnf⟩ :=
        hthr I hI0 hstep c (d.ctorsM c) (hctorsAs c hck) j _ hcj
      obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
      obtain ⟨crest', -, hcrest', -, -, ⟨ty, hty⟩, -⟩ :=
        hall c (d.ctorsM c) (hctorsAs c hck) j _ hcj
      rw [hcrest] at hcrest'
      obtain rfl := Option.some.inj hcrest'
      rw [← hctx] at hcrest hm hty hprovI
      obtain ⟨ord, Af, h1, h2, h3, h4⟩ := blockCtorAcc_of_walk hin hN hcore' hnames hlps hnP
        hnIdxs hk hcv0 hop0 (by rw [hctx]; exact hholes) hcj hCf hCb hcrest
        (P := fun _ => True) (I := I) (hprovI F) hm (fun _ _ => trivial) hI₀ hty
        (by rw [hnfs c j _ hcj]; exact hnf) hs hw (hG c hc j hj)
      exact ⟨(ord, Af), fun _ _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨(fun _ => true, fun _ _ => empty), fun hc hj => absurd ⟨hc, hj⟩ hcj'⟩
  -- the hole operator
  have hok : d.toLfp.HoleTmOk ψ ρp := fun m hm =>
    ⟨⟨(hH.parsLen ψ m hm).trans (hH.lenP ψ).symm, hH.parsSat ψ m hm ρp hs⟩,
      fun _ => (hIdx m (Nat.lt_of_lt_of_le hm hkN)).2⟩
  have happ : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c → d.toLfp.HolesApplied ψ c j :=
    fun c hc j hj => blockHolesApplied hH ψ hc hj
  have hres : ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
      (d.toLfp.resIdx ψ c j).length = (d.toLfp.ids c ψ).length := by
    intro c hc j hj
    show (d.absE ψ c j).length = (d.IdsM c ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ c hc j hj
  let oa : Nat → Nat → (Nat → Bool) × (Nat → (Nat → V) → V) :=
    fun c j => Classical.choose (hper c j)
  have hoa : ∀ c j, c < d.toLfp.N → j < d.toLfp.nctors c → _ :=
    fun c j => Classical.choose_spec (hper c j)
  exact LfpDatum.accTuple_holeOp hw hok hkN happ hres (fun c j => (oa c j).1)
    (fun c j => (oa c j).2) (fun c hc j hj => (hoa c j hc hj).2.1)
    (fun c hc j hj => (hoa c j hc hj).2.2.1) (fun c hc j hj => (hoa c j hc hj).1)
    (fun c hc j hj => (hoa c j hc hj).2.2.2)

end ConLeche.Model
