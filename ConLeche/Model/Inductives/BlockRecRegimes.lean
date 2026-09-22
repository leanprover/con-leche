module

public import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Semantics.Tower.BlockRecKitI
import ConLeche.Semantics.Tower.BlockRecIndI
import ConLeche.SetModel.WfRec
public import ConLeche.SetTheory.Derive.TransClosure

public section

/-!
# The three regimes, wired to the block's representation (task #315, M5)

`blockRecStaged_of`'s `hrecP` is, through `blockRecAV_iota`
(`Semantics/Tower/BlockRecI.lean`), the family premise
`BlockRecPre`.  Its three fields are owed by three different tiers,
and this file is where they meet:

| field | who proves it |
|---|---|
| `hTy` | O-2 — the recursor's stored type reads to `mkPisAV rds concl` and the reading is a set of the family's level (`BlockRecRead.lean`) |
| `hEq` | the ι equations' grading, `hEq_iotaEqsAV_of` at the rule data |
| `hCand` | **the recursion theorem** — one of the three regimes |

and the regimes are:

* **WF** (`w ≠ 0 ∧ ℓ ≠ 0`) — `famCand_hCand` at a `WfRecKit` family:
  the recursion is over the tagged union of the classes' carriers,
  ∈-smaller elements are the predecessors, and the depth obligation is
  `blockData_mkDepth` below — the block's injections put a
  constructor's fields ∈-below the constructed value;
* **IND** (`ℓ = 0`) — `indCand_hCand`: the candidate is the point and
  the regime is the induction principle plus `ResidueOk` at every
  fitting spine;
* **SQ** (`w = 0 ∧ ℓ ≠ 0`) — `famCand_hCand` at the squash kit, whose
  step is the residue read at the SOURCE spine (`BlockRecSqI.lean`).

Nothing here re-proves a regime: each is a theorem of the semantics
tier, and what this file adds is the *dispatch* and the one fact about
the representation the WF regime needs that `BlockModelAt` does not
carry.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `mkDepth` — the WF regime's depth obligation, at the block's
representation

`BlockModelAt` carries `mkZero` and `mkInj` but no depth law, because
no earlier consumer needed one: the lfp route pins the predecessor set
by `mkInj`, and the ∈-recursion does not.  At the uniform tuple
encoding the law is one rewrite of `mem_tc_inj_mkTower`
(`SetModel/WfRec.lean`), off the SAME `hinj` hypothesis
`blockModelAt_of_stages` already takes. -/

/-- **The constructor's fields are ∈-below the constructed value.**
The WF regime's encoding-depth obligation at the block's injections. -/
theorem blockData_mkDepth {d : BlockData V}
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    {ψ : Name → Nat} (hw : d.w ψ ≠ 0) (c j : Nat) (fs : List V) {a : V} (ha : a ∈ fs) :
    a ∈ˢ ConLeche.SetTheory.tc (d.inj ψ c j fs) := by
  rw [hinj, if_neg hw]
  exact mem_tc_inj_mkTower j fs ha

/-- The reflexive field's half: the image of a graph field at an
argument is ∈-below the constructed value. -/
theorem blockData_mkDepth_app {d : BlockData V}
    (hinj : ∀ (ψ : Name → Nat) (c j : Nat) (fs : List V),
      d.inj ψ c j fs = if d.w ψ = 0 then (pt : V) else inj j (mkTower (fs ++ [pt])))
    {ψ : Name → Nat} (hw : d.w ψ ≠ 0) (c j : Nat) (fs : List V) {g : V} (hg : g ∈ fs)
    {A x : V} {B : V → V} (hpi : g ∈ˢ piSet A B) (hx : x ∈ˢ A) :
    app g x ∈ˢ ConLeche.SetTheory.tc (d.inj ψ c j fs) := by
  rw [hinj, if_neg hw]
  exact app_field_mem_tc hg hpi hx

/-! ## `BlockRecPre`, assembled -/

section Pre

variable {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **The family premise, assembled** — the shape `blockRecAV_iota`
consumes, with its three fields in the form their owners prove them:
the types' reading (O-2), the ι equations' grading
(`hEq_iotaEqsAV_of`), and the recursion theorem (a regime). -/
theorem blockRecPre_of
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (hCand : ∃ cand : Nat → V, (∀ c, c < K → cand c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K cand ρ) e) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ where
  hTy := hTy
  hEq := hEq_iotaEqsAV_of hwd
  hCand := hCand

end Pre

/-! ## The three regimes, as the dispatch reads them

Each is `blockRecPre_of` at the `hCand` its own tier proves.  The
regimes are DISJOINT and EXHAUSTIVE on the pair `(w, ℓ)`: `ℓ = 0` is
IND (every conclusion is a proposition — D-d makes it one bit for the
family), `ℓ ≠ 0 ∧ w ≠ 0` is WF, and `ℓ ≠ 0 ∧ w = 0` is SQ, where the
guard leaves a lone non-nested block with at most one constructor
under the subsingleton criterion. -/

section Regimes

variable {ℓ s K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **Regimes WF and SQ**: the candidate is the class kit's recursor,
and `ResidueOk` at the rule's own spine is the kit's step
(`famCand_hCand`'s `hst`). -/
theorem blockRecPre_kit
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    (hTyE : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)])))
    (hst : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).st
          (tagged c
            (D.tupOf c ((es c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)))
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c ((es c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))))
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ))))
              (consList (xs ++ fs) (chainFrame K (famCand D) ρ))) (Rb c j)) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ :=
  blockRecPre_of hTy hwd (famCand_hCand D hℓ hTyE hbits hpl hrule hst)

/-- **Regime IND** (`ℓ = 0`): the candidate is the point, and the two
obligations are the induction principle and `ResidueOk` at `ℓ = 0` —
the residue's reading is a member of a truth value. -/
theorem blockRecPre_ind
    (hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c))
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)))
    (hind : ∀ c, c < K → (pt : V) ∈ˢ interp V ρ (RecTy c))
    (hres : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∃ T : V, T ∈ˢ (univZero : V) ∧
        interp V
            (consList
              ((ihs c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
              (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Rb c j) ∈ˢ T) :
    BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ :=
  blockRecPre_of hTy hwd (indCand_hCand hind hres)

/-- **`ResidueOk` IS regime IND's `hres`** at `ℓ = 0`: a residue that
is graded and lands in a truth value is what `indCand_hCand` asks
for. -/
theorem hres_of_residueOk {c j : Nat} {xs fs : List V} {T : V}
    (hT : T ∈ˢ (univZero : V))
    (h : ResidueOk V (Rb c j)
      ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
      (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ)) T) :
    ∃ T : V, T ∈ˢ (univZero : V) ∧
      interp V
          (consList
            ((ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
            (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Rb c j) ∈ˢ T :=
  ⟨T, hT, h.2⟩

end Regimes

/-! ## G3 — a guarded call's ARGUMENTS are certified against the
telescope

The residue's typing run infers the opened body at the CONSTRUCTORS'
environment, and a guarded call's node `ih_r a⃗` is an application
spine there.  What the regimes need of it — at `ℓ = 0` for the IND
step, and at the WF kit's graph for `hst` — is that each argument
`a_t` was certified against the ih opener's own domain, i.e. against
the field's telescope.  That is one INVERSION of the typing relation,
and it is clean at the `.full` grade because the io site
(`Infer.appSkip`, which certifies no argument at all) is not
available there: `appSkip` is stated at `.io` only.

(At `.io` the claim is FALSE, and that is the io licence, not an
omission: `Model/IOLicense.lean`'s `io_domain_transfer` is what pays
for it.  The rule stage runs `inferType` at the checker's certified
grade, so the `.full` inversion is the one that applies.) -/

/-- **The application node, inverted at the full grade** — the head's
type reduces to a `∀` and the argument is certified against its
domain.  `Infer.appSkip` is `.io`-only, so at `.full` there is exactly
one way to infer an application. -/
theorem infer_app_inv_full {env : Env} {d : Nat} {f a T : Expr}
    (h : ConLeche.Rules.Infer env .full d (.app f a) T) :
    ∃ (tf ty body ta : Expr) (mt : ConLeche.BinderMeta),
      ConLeche.Rules.Infer env .full d f tf ∧
      ConLeche.Rules.Red env d tf (.forallE ty body mt) ∧
      ConLeche.Rules.Infer env .full d a ta ∧
      ConLeche.Rules.DefEq env d ta ty ∧
      T = body.instantiate1 a := by
  cases h with
  | app hf hr ha hd => exact ⟨_, _, _, _, _, hf, hr, ha, hd, rfl⟩

/-- The head of a `.full`-inferred application spine is itself
inferred. -/
theorem infer_mkAppN_head {env : Env} {d : Nat} :
    ∀ (cs : List Expr) {g T : Expr},
      ConLeche.Rules.Infer env .full d (Expr.mkAppN g cs) T →
      ∃ tg : Expr, ConLeche.Rules.Infer env .full d g tg
  | [], _, T, h => ⟨T, h⟩
  | c :: cs, g, T, h => by
    obtain ⟨tg, hg⟩ := infer_mkAppN_head cs (g := .app g c) h
    obtain ⟨tf, -, -, -, -, hif, -, -, -, -⟩ := infer_app_inv_full hg
    exact ⟨tf, hif⟩

/-- **G3**: every argument of a `.full`-inferred application spine is
CERTIFIED — inferred, and definitionally equal to the domain the
head's type peeled to.  At a guarded call `ih_r a⃗` in the residue,
that domain is the `ih` opener's own, i.e. the field's telescope
binder, which is what puts `a⃗` in the telescope. -/
theorem infer_mkAppN_inv_full {env : Env} {d : Nat} :
    ∀ (as : List Expr) {f T : Expr},
      ConLeche.Rules.Infer env .full d (Expr.mkAppN f as) T →
      ∀ a ∈ as, ∃ ta ty : Expr,
        ConLeche.Rules.Infer env .full d a ta ∧ ConLeche.Rules.DefEq env d ta ty
  | [], _, _, _, a, ha => absurd ha (List.not_mem_nil)
  | b :: bs, f, T, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨tg, hg⟩ := infer_mkAppN_head bs (g := .app f a) h
      obtain ⟨-, ty, -, ta, -, -, -, hia, hd, -⟩ := infer_app_inv_full hg
      exact ⟨ta, ty, hia, hd⟩
    · exact infer_mkAppN_inv_full bs (f := .app f b) h a ha'

/-! ### G3 as a TELESCOPE certificate

`infer_mkAppN_inv_full` above says each argument is certified, but
against an EXISTENTIAL domain, which no consumer can use: the fit the
regimes need is a chain of memberships in the ih opener's OWN
telescope.  What names those domains is `Certs` (`Rules/Rel.lean`),
the relation whose soundness (`certs_sound` → `CertsSem`) already
concludes `TeleFitPA` — the fit itself.  So G3's usable form is
"the spine is a `Certs` walk of the head's type".

The obstruction is that `Infer.app` REDUCES the head's type at every
step (`Red env d tf (.forallE ty body mt)`) while `Certs` peels a
LITERAL `∀`.  They meet because an ih opener's type IS a literal
Π-tower and reduction cannot move it: `Red` out of a `∀` or a sort is
the identity (`red_rigidTy`), since the only rules whose subject is
neither an application, a projection nor a literal are `refl`,
`trans`, `delta` and the three RESCUES — and `unfoldDefinition` is
`none` off a non-`const` head while a rescue's subject has a
constant-headed inferred type, which a `∀`'s (a sort) is not. -/

/-- A sort's and a `∀`'s inferred type is a SORT — the fact that
closes the rescue rules in `red_rigidTy`. -/
theorem infer_rigidTy_sort {env : Env} {g : ConLeche.Rules.Grade} {d : Nat} {s t : Expr}
    (h : ConLeche.Rules.Infer env g d s t)
    (hs : (∃ u, s = .sort u) ∨ (∃ A B mb, s = .forallE A B mb)) :
    ∃ u, t = .sort u := by
  rcases hs with ⟨u, rfl⟩ | ⟨A, B, mb, rfl⟩
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩

/-- A sort and a `∀` are their own application head, so no
constant-headed premise can be about them. -/
theorem getAppFn_rigidTy {e : Expr} {n : ConLeche.Name} {us : List ConLeche.Level}
    (hs : (∃ u, e = .sort u) ∨ (∃ A B mb, e = .forallE A B mb))
    (h : e.getAppFn = .const n us) : False := by
  rcases hs with ⟨u, rfl⟩ | ⟨A, B, mb, rfl⟩
  · rw [show (Expr.sort u).getAppFn = Expr.sort u from rfl] at h
    exact ConLeche.Expr.noConfusion h
  · rw [show (Expr.forallE A B mb).getAppFn = Expr.forallE A B mb from rfl] at h
    exact ConLeche.Expr.noConfusion h

/-- `Red`'s motive for `red_rigidTy` — a single `Prop` in the subject
and the reduct, as `RedSem` is, so that the equation compiler can
recurse on the derivation alone. -/
@[expose] def RedRigid (s e : Expr) : Prop :=
  ((∃ u, s = .sort u) ∨ (∃ A B mb, s = .forallE A B mb)) → e = s

/-- The motive at a subject that is neither a sort nor a `∀` — the
nine rules whose subject is an application, a projection or a
literal. -/
theorem redRigid_absurd {s e : Expr}
    (hne : ∀ u : ConLeche.Level, s ≠ .sort u)
    (hne2 : ∀ (A B : Expr) (mb : ConLeche.BinderMeta), s ≠ .forallE A B mb) :
    RedRigid s e := by
  rintro (⟨u, hu⟩ | ⟨A, B, mb, hu⟩)
  · exact absurd hu (hne u)
  · exact absurd hu (hne2 A B mb)

/-- The motive composes along `Red.trans`. -/
theorem redRigid_trans {e₁ e₂ e₃ : Expr} (h₁ : RedRigid e₁ e₂) (h₂ : RedRigid e₂ e₃) :
    RedRigid e₁ e₃ := fun hs => by
  have a1 := h₁ hs
  have a2 := h₂ (by rw [a1]; exact hs)
  rw [a2, a1]

/-- The motive at a RESCUE: the subject's io-inferred type is
constant-headed after reduction, and a sort's is not. -/
theorem redRigid_rescue {env : Env} {d : Nat} {major tm tmaj fab : Expr}
    {T : ConLeche.Name} {ust : List ConLeche.Level}
    (htm : ConLeche.Rules.Infer env .io d major tm) (ihm : RedRigid tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust) : RedRigid major fab := fun hs => by
  obtain ⟨u, rfl⟩ := infer_rigidTy_sort htm hs
  rw [ihm (Or.inl ⟨u, rfl⟩)] at hthead
  exact absurd hthead (fun h => getAppFn_rigidTy (Or.inl ⟨u, rfl⟩) h)

/-- **Reduction is the identity on a sort and on a `∀`.**  The two
shapes travel together: a rescue constrains its subject only through
the subject's io-inferred type, and a `∀`'s inferred type is a sort,
so the sort case is what closes the `∀` case.

`Red` is mutually inductive, so this is written with the equation
compiler (as `red_sound` is) and not with `induction`; the hypothesis
lives in the motive (`RedRigid`) and every recursive call is in TERM
position, for the same reason — a trailing premise whose type mentions
the subject, or a recursive call under a tactic block, blocks the
structural elimination. -/
theorem red_rigidTy {env : Env} {d : Nat} :
    ∀ {s e : Expr}, ConLeche.Rules.Red env d s e → RedRigid s e
  | _, _, .refl => fun _ => rfl
  | _, _, .trans h₁ h₂ => redRigid_trans (red_rigidTy h₁) (red_rigidTy h₂)
  | _, _, .appFn .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .projArg .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .betaGate .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .beta .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .natLit .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .strLit .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .natSucc .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .natOp .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .proj .. => redRigid_absurd (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  | _, _, .delta hu => fun hs => by
    rcases hs with ⟨u, hq⟩ | ⟨A, B, mb, hq⟩
    · subst hq
      rw [show ConLeche.unfoldDefinition env (Expr.sort u) = none from rfl] at hu
      exact absurd hu (by simp)
    · subst hq
      rw [show ConLeche.unfoldDefinition env (Expr.forallE A B mb) = none from rfl] at hu
      exact absurd hu (by simp)
  | _, _, .iota hhead .. => fun hs => absurd hhead (fun h => getAppFn_rigidTy hs h)
  | _, _, .rescueK _ _ _ _ _ htm htmaj hthead .. =>
    redRigid_rescue htm (red_rigidTy htmaj) hthead
  | _, _, .rescueEta _ _ _ _ _ htm htmaj hthead .. =>
    redRigid_rescue htm (red_rigidTy htmaj) hthead
  | _, _, .rescueAnd _ _ _ _ htm htmaj hthead .. =>
    redRigid_rescue htm (red_rigidTy htmaj) hthead

/-- **Every grade implies the io grade.**  `Certs` certifies its
arguments at `.io`, `Infer.app` at the grade of the spine; the one
place the two differ is the λ rule's domain check, whose premises are
guarded by `g = .full` and therefore vacuous at `.io`.

The grade is a VARIABLE here and not `.full`: a fixed index is not a
variable, and the structural elimination of an inductive FAMILY needs
one. -/
theorem infer_io_of_grade {env : Env} :
    ∀ {g : ConLeche.Rules.Grade} {d : Nat} {e t : Expr},
      ConLeche.Rules.Infer env g d e t → ConLeche.Rules.Infer env .io d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar h => .fvar h
  | _, _, _, _, .const h1 h2 h3 => .const h1 h2 h3
  | _, _, _, _, .natLit h => .natLit h
  | _, _, _, _, .strLit h => .strLit h
  | _, _, _, _, .forallE h1 h2 h3 h4 h5 =>
    .forallE (infer_io_of_grade h1) h2 (infer_io_of_grade h3) h4 h5
  | _, _, _, _, .lam _ _ hb hpw hio hred hz =>
    .lam (s := .sort .zero) (u := .zero)
      (fun h => ConLeche.Rules.Grade.noConfusion h)
      (fun h => ConLeche.Rules.Grade.noConfusion h) (infer_io_of_grade hb) hpw hio hred hz
  | _, _, _, _, .app hf hr ha hd =>
    .app (infer_io_of_grade hf) hr (infer_io_of_grade ha) hd
  | _, _, _, _, .appSkip hf hr hn => .appSkip (infer_io_of_grade hf) hr hn
  | _, _, _, _, .proj hp hr h1 h2 h3 h4 h5 =>
    .proj (infer_io_of_grade hp) hr h1 h2 h3 h4 h5

/-- **The head's type is a literal Π-tower deep enough for the
spine**, the domains instantiated along it — the hypothesis under
which `Infer.app`'s reduction step is the identity
(`red_rigidTy`). -/
inductive PiSpine : Expr → List Expr → Prop
  | nil {T : Expr} : PiSpine T []
  | cons {ty body a : Expr} {mb : ConLeche.BinderMeta} {as : List Expr} :
      PiSpine (body.instantiate1 a) as → PiSpine (.forallE ty body mb) (a :: as)

/-! ### `PiSpine`, from the run's own Π-count

`PiSpine` is what `certs_of_infer_mkAppN` needs of the head's type,
and the run states its Π-tower with `stripPis` (`checkBlockRule`'s
third opening, `blockIhPis`' binders).  The two meet through ONE
observation: `stripPis` peels a `∀` without instantiating and
`PiSpine` peels it WITH, and `instantiate1` maps a `∀` to a `∀`, so
"has at least `n` leading `∀`s" survives every instantiation the
spine performs. -/

/-- Instantiation preserves the leading Π-count. -/
theorem stripPis_isSome_instantiate1 :
    ∀ (n : Nat) {e : Expr} (a : Expr) (k : Nat),
      (e.stripPis n).isSome = true → ((e.instantiate1 a k).stripPis n).isSome = true
  | 0, _, _, _, _ => rfl
  | n + 1, e, a, k, h => by
    cases e with
    | forallE ty body mb =>
      have hb : (body.stripPis n).isSome = true := by
        simpa only [ConLeche.Expr.stripPis, Option.isSome_map] using h
      show ((Expr.forallE (ty.instantiate1 a k) (body.instantiate1 a (k + 1)) mb).stripPis
        (n + 1)).isSome = true
      simp only [ConLeche.Expr.stripPis, Option.isSome_map]
      exact stripPis_isSome_instantiate1 n a (k + 1) hb
    | _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- **The seam**: a head type with at least as many leading `∀`s as
the spine has arguments IS a `PiSpine`. -/
theorem piSpine_of_stripPis :
    ∀ (as : List Expr) {e : Expr}, (e.stripPis as.length).isSome = true → PiSpine e as
  | [], _, _ => .nil
  | a :: as, e, h => by
    cases e with
    | forallE ty body mb =>
      have hb : (body.stripPis as.length).isSome = true := by
        simpa only [List.length_cons, ConLeche.Expr.stripPis, Option.isSome_map] using h
      exact .cons (piSpine_of_stripPis as (stripPis_isSome_instantiate1 as.length a 0 hb))
    | _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- A generated Π-tower has its own length's worth of leading `∀`s —
the shape `blockIhPis` gives every `ih` opener. -/
theorem stripPis_isSome_mkPisOf :
    ∀ (tele : List (Expr × ConLeche.BinderMeta)) (body : Expr) (n : Nat),
      n ≤ tele.length → ((Expr.mkPisOf tele body).stripPis n).isSome = true
  | _, _, 0, _ => rfl
  | (ty, mt) :: tele, body, n + 1, h => by
    show ((Expr.forallE ty (Expr.mkPisOf tele body) mt).stripPis (n + 1)).isSome = true
    simp only [ConLeche.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_mkPisOf tele body n (by simpa using h)

/-- **`PiSpine` at a generated tower**, the form the `ih` opener's
stored type takes. -/
theorem piSpine_mkPisOf {tele : List (Expr × ConLeche.BinderMeta)} {body : Expr}
    {as : List Expr} (h : as.length ≤ tele.length) :
    PiSpine (Expr.mkPisOf tele body) as :=
  piSpine_of_stripPis as (stripPis_isSome_mkPisOf tele body as.length h)

/-! ### The opener's stored type, as the run leaves it (`hop`'s kit)

`openPisAtFvars_fvarTypeD` (`Model/Inductives/FixRecReadDefs.lean`)
says the `r`-th opener's STORED type is the `r`-th `∀`-binder domain of
the peeled term, with the `r` earlier openers `instSeq`'d — so the
run's identification of `tyOp` (`M5M-opener-REPORT.md` §4.1) is that
binder list plus TWO generic facts, and these are they:

* `stripPis_instantiateList` — opening a Π-tower's frame opens its
  binders, each at its own depth (the `∀` clause of
  `Expr.instantiateList` raises the cut, which is exactly the offset
  the `l`-th binder stands at);
* `instantiateList_split` — the peel's `instSeq` and the frame's
  `instantiateList` COMPOSE into one opening, which is the single
  `FvarList` the reading battery
  (`denoteMeta_blockIhOpenerTy`) takes.
-/

/-- **Opening commutes with the Π-peel**, binderwise: the `q`-th
binder of the opened tower is the `q`-th binder opened at cut
`k + q`. -/
theorem stripPis_instantiateList (L : List Expr) :
    ∀ (n : Nat) {e : Expr} {bs : List (Expr × ConLeche.BinderMeta)} {body : Expr} (k : Nat),
      e.stripPis n = some (bs, body) →
      ∃ bs' : List (Expr × ConLeche.BinderMeta),
        (e.instantiateList L k).stripPis n = some (bs', body.instantiateList L (k + n)) ∧
        bs'.length = bs.length ∧
        ∀ (q : Nat) (b : Expr × ConLeche.BinderMeta), bs[q]? = some b →
          bs'[q]? = some (b.1.instantiateList L (k + q), b.2)
  | 0, e, bs, body, k, h => by
    simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp [ConLeche.Expr.stripPis], rfl, fun q b hb => nomatch hb⟩
  | n + 1, e, bs, body, k, h => by
    match e with
    | .forallE ty b mb =>
      simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₀, body₀⟩, hst, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨bs', hst', hlen', hidx'⟩ := stripPis_instantiateList L n (k + 1) hst
      refine ⟨(ty.instantiateList L k, mb) :: bs', ?_, by simp [hlen'], ?_⟩
      · rw [Expr.instantiateList, ConLeche.Expr.stripPis, hst',
          show k + (n + 1) = k + 1 + n from by omega]
        simp only [Option.map_some]
      · intro q c hc
        cases q with
        | zero =>
          obtain rfl : c = (ty, mb) := by simpa using hc.symm
          simp
        | succ q =>
          have := hidx' q c (by simpa using hc)
          rw [List.getElem?_cons_succ]
          rw [show k + 1 + q = k + (q + 1) from by omega] at this
          exact this
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .lam _ _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- **The peel's spine and the frame's opening COMPOSE.**  A term
opened at cut `n` and then at cut `0` by a list of length `n` is
opened once by the concatenation — which is the single opening list
`FvarList` describes, and the one the reading battery takes. -/
theorem instantiateList_split :
    ∀ (P L : List Expr) (e : Expr) (d : Nat),
      (e.instantiateList L (d + P.length)).instantiateList P d = e.instantiateList (P ++ L) d
  | [], L, e, d => by simp [Expr.instantiateList_nil]
  | v :: P', L, e, d => by
    rw [show d + (v :: P').length = d + 1 + P'.length from by
        simp only [List.length_cons]; omega,
      Expr.instantiateList_cons P' (e.instantiateList L (d + 1 + P'.length)) v d,
      instantiateList_split P' L e (d + 1), List.cons_append,
      Expr.instantiateList_cons (P' ++ L) e v d]

/-- **G3, in the form a consumer can use.**  A `.full`-inferred spine
whose head's inferred type is pinned (an fvar's is: `Infer.fvar`
reads the stored annotation) and is a literal Π-tower IS a `Certs`
walk of that tower — so `certs_sound` gives `CertsSem`, whose
conclusion is the `TeleFitPA` the fit needs.

The two hypotheses are exactly what an `ih` opener supplies: its
inferred type is its stored type, and that type is the generated
Π-tower over the field's telescope. -/
theorem certs_of_infer_mkAppN {env : Env} {d : Nat} :
    ∀ (as : List Expr) {f T tf : Expr},
      ConLeche.Rules.Infer env .full d (Expr.mkAppN f as) T →
      (∀ t, ConLeche.Rules.Infer env .full d f t → t = tf) →
      PiSpine tf as →
      ConLeche.Rules.Certs env d false tf as
  | [], _, _, _, _, _, _ => .nil
  | b :: bs, f, T, tf, h, hdet, hpi => by
    cases hpi with
    | cons hrest =>
      obtain ⟨tg, hg⟩ := infer_mkAppN_head bs (g := .app f b) h
      obtain ⟨tf₀, ty₀, body₀, ta, mt₀, hif, hred, hia, hdq, rfl⟩ := infer_app_inv_full hg
      obtain rfl := hdet tf₀ hif
      have heq := red_rigidTy hred (Or.inr ⟨_, _, _, rfl⟩)
      injection heq with e1 e2 e3
      subst e1; subst e2; subst e3
      refine .cert (infer_io_of_grade hia) hdq ?_
      refine certs_of_infer_mkAppN bs (f := .app f b) h ?_ hrest
      intro t ht
      obtain ⟨tf₁, ty₁, body₁, ta₁, mt₁, hif₁, hred₁, -, -, rfl⟩ := infer_app_inv_full ht
      obtain rfl := hdet tf₁ hif₁
      have heq₁ := red_rigidTy hred₁ (Or.inr ⟨_, _, _, rfl⟩)
      injection heq₁ with f1 f2 f3
      subst f1; subst f2; subst f3
      rfl

end ConLeche.Model
