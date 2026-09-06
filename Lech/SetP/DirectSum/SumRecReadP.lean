import Lech.SetP.Direct.DirectRecReadP
import Lech.Verify.Direct.SumRec
import Lech.Semantics.Tower.SumRec

/-!
# The generated sum recursor's readings (task #175 sum-types, indexed)

`Lech/SetP/Direct/DirectRecReadP.lean` at a constructor list over
an indexed family: the generated recursor type reads to the Π-tower
over `sumRecDataAV` (parameters, motive over the index telescope, one
minor per constructor, the index telescope again, major), with the
core `motive ı⃗ t`, and rule `j` reads to the λ-tower over
`sumRuleDataAV` at constructor `j`'s field data, with the core
`minor_j f⃗`.  The minor entries are read by one induction over the
constructor list (`denoteP_minorsPis` / `denoteP_minorsLams`), the
accumulated variables (the motive first, then the earlier minors)
threaded as `extras`.

The one genuinely new reading is the minor's conclusion
`motive e⃗ (C p⃗ f⃗)`: the constructor's index expressions, spelled at
the recursor frame (under the extras), read to the constructor's own
index readings lifted above the fields
(`denoteSpineP_idxArgs_lift`) — obtained by reading the whole opened
residual `T p⃗ e⃗` at that frame and inverting the application spine.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Syntactic bookkeeping -/

/-- A closed instantiation sequence commutes with a strip. -/
theorem stripPis_instSeq :
    ∀ (sp : List Expr) (t : Nat) {e : Expr} {n : Nat}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      sp.length ≤ t + 1 →
      e.stripPis n = some (bs, body) →
      ∃ bs', (Expr.instSeq sp t e).stripPis n = some (bs', Expr.instSeq sp (t + n) body)
  | [], _, _, _, bs, _, _, h => ⟨bs, h⟩
  | a :: sp, t, e, n, bs, body, hlen, h => by
    obtain ⟨bs', h', -⟩ := Lech.stripPis_instantiate1_full (v := a) n t h
    obtain ⟨bs'', h''⟩ := stripPis_instSeq sp (t - 1) (by simp at hlen; omega) h'
    refine ⟨bs'', ?_⟩
    show (Expr.instSeq sp (t - 1) (e.instantiate1 a t)).stripPis n
      = some (bs'', Expr.instSeq sp (t + n - 1) (body.instantiate1 a (t + n)))
    rw [h'']
    congr 2
    rcases sp with _ | ⟨b, sp⟩
    · rfl
    · have : 1 ≤ t := by simp at hlen; omega
      congr 1
      omega

theorem directPsAt_zero (n : Nat) :
    Lech.directPsAt 0 n = (List.range n).map fun k => Expr.bvar (n - 1 - k) := by
  simp [Lech.directPsAt]

/-- The index variables' spine one under (the major), instantiated at
the index variables. -/
theorem map_instSeq_directPsAt_one (ifvs : List Expr) (nIdx : Nat)
    (hcl : ∀ a ∈ ifvs, a.looseBVarsBounded 0 = true) (hlen : ifvs.length = nIdx) :
    (Lech.directPsAt 1 nIdx).map (Expr.instSeq ifvs nIdx) = ifvs := by
  apply List.ext_getElem
  · simp [Lech.directPsAt, hlen]
  · intro k h1 h2
    have hk : k < nIdx := by simpa [Lech.directPsAt] using h1
    simp only [Lech.directPsAt, List.getElem_map, List.getElem_range]
    have := Expr.instSeq_bvar ifvs nIdx (1 + nIdx - 1 - k) hcl (by omega) (by omega)
    rw [show nIdx - (1 + nIdx - 1 - k) = k from by omega, List.getElem?_eq_getElem h2] at this
    exact (Option.some.inj this).symm

/-- A closed spine is fixed by an instantiation sequence. -/
theorem map_instSeq_closed (sp : List Expr) (t : Nat) {xs : List Expr}
    (hcl : ∀ a ∈ xs, a.looseBVarsBounded 0 = true) :
    xs.map (Expr.instSeq sp t) = xs := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map]
  exact Expr.instSeq_eq_self _ _ (hcl _ (List.getElem_mem h2))

/-- A closed spine is fixed by an instantiation. -/
theorem map_instantiate1_closed {xs : List Expr} (hcl : ∀ a ∈ xs, a.looseBVarsBounded 0 = true)
    (v : Expr) (k : Nat) : xs.map (·.instantiate1 v k) = xs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map]
  exact Expr.instantiate1_eq_self
    (Expr.looseBVarsBounded_mono (Nat.zero_le k) (hcl _ (List.getElem_mem h2)))

/-! ## `AVExpr` bookkeeping -/

theorem liftN_mkAppN (n k : Nat) : ∀ (as : List AVExpr) (f : AVExpr),
    AVExpr.liftN n (AVExpr.mkAppN f as) k
      = AVExpr.mkAppN (AVExpr.liftN n f k) (as.map fun a => AVExpr.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AVExpr.mkAppN_cons, List.map_cons, liftN_mkAppN n k as, AVExpr.liftN_app]

theorem AVExpr.mkAppN_append_one : ∀ (as : List AVExpr) (f a : AVExpr),
    AVExpr.mkAppN f (as ++ [a]) = .app (AVExpr.mkAppN f as) a
  | [], _, _ => rfl
  | b :: as, f, a => by
    simp only [List.cons_append, AVExpr.mkAppN_cons]
    exact AVExpr.mkAppN_append_one as _ a

theorem mkAppN_inj_args :
    ∀ {as bs : List AVExpr} {f g : AVExpr},
      AVExpr.mkAppN f as = AVExpr.mkAppN g bs → as.length = bs.length → f = g ∧ as = bs
  | [], [], _, _, h, _ => ⟨h, rfl⟩
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | a :: as, b :: bs, f, g, h, hl => by
    simp only [AVExpr.mkAppN_cons] at h
    obtain ⟨hfg, hab⟩ := mkAppN_inj_args h (by simpa using hl)
    obtain ⟨rfl, rfl⟩ := AVExpr.app.inj hfg
    exact ⟨rfl, by rw [hab]⟩

/-- A leaf fixed by every one-step lift is fixed by every lift. -/
theorem liftN_eq_self_of_one {e : AVExpr} (h : ∀ k, AVExpr.liftN 1 e k = e) :
    ∀ (n k : Nat), AVExpr.liftN n e k = e
  | 0, k => AVExpr.liftN_zero e k
  | n + 1, k => by
    rw [show n + 1 = 1 + n from by omega, ← AVExpr.liftN_liftN e 1 n k,
      liftN_eq_self_of_one h n k, h k]

theorem DenoteSpineP.append_inv {acval : Name → (Name → Nat) → AVExpr} {d : Nat} :
    ∀ {as bs : List Expr} {vs : List AVExpr},
      DenoteSpineP acval env φ d (as ++ bs) vs →
      ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧
        DenoteSpineP acval env φ d as vs₁ ∧ DenoteSpineP acval env φ d bs vs₂
  | [], bs, vs, h => ⟨[], vs, rfl, .nil, h⟩
  | a :: as, bs, vs, h => by
    rw [List.cons_append] at h
    cases h with
    | cons ha htl =>
      obtain ⟨vs₁, vs₂, rfl, h1, h2⟩ := DenoteSpineP.append_inv htl
      exact ⟨_ :: vs₁, vs₂, rfl, .cons ha h1, h2⟩

theorem DenoteSpineP.unique {acval : Name → (Name → Nat) → AVExpr} {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List AVExpr},
      DenoteSpineP acval env φ d as vs → DenoteSpineP acval env φ d as vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons ha h, .cons ha' h' => by
    rw [Option.some.inj (ha.symm.trans ha'), DenoteSpineP.unique h h']

/-! ## The entries -/

/-- The motive's domain reading `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` at the
parameters' frame, over the former's index data `ips`. -/
def motiveAVI {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat) (nP nIdx : Nat)
    (ℓ : Level) (ips : List (Nat × Nat × AVExpr)) : AVExpr :=
  mkPisAV (rebit (pwBit ψ PropWhen.never) ips)
    (.pi 0 (pwBit ψ PropWhen.never)
      (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx))
      (.sort (ℓ.eval ψ)))

/-- The minor premise's domain reading at offset `o` (the motive and
`o - 1` earlier minors above the parameters): the constructor's field
data lifted `o` under, bits reset to `b`, over the motive at the
constructor's index readings (lifted `o` above the fields) and the
constructor spine. -/
def minorAVAt {env : Env} (m : EnvS2Core V env) (C : Name) (ψ : Name → Nat) (nP nF b o : Nat)
    (ds : List (Nat × Nat × AVExpr)) (Es : List AVExpr) : AVExpr :=
  mkPisAV (rebit b (liftDoms o 0 (ds.drop nP)))
    (AVExpr.mkAppN (.bvar (nF + o - 1))
      ((Es.map fun E => E.liftN o nF) ++
        [AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)]))

/-- The major premise's domain reading under the motive, `n` minors
and the index variables: the family at the parameters and the index
variables. -/
def majorAVAt {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat) (nP nIdx n : Nat) :
    AVExpr :=
  AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + 1 + n + nIdx) ++ fieldBvars nIdx)

/-- A constructor datum: name, field count, field data, index readings. -/
abbrev CtorDatum := Name × Nat × List (Nat × Nat × AVExpr) × List AVExpr

/-- The minor entries, one per constructor datum, from offset `o`. -/
def sumMinorsData {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (nP b : Nat) :
    List CtorDatum → Nat → List (Nat × Nat × AVExpr)
  | [], _ => []
  | (C, nF, ds, Es) :: cs, o =>
    (0, b, minorAVAt m C ψ nP nF b o ds Es) :: sumMinorsData m ψ nP b cs (o + 1)

theorem sumMinorsData_length {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (cds : List CtorDatum) (o : Nat), (sumMinorsData m ψ nP b cds o).length = cds.length
  | [], _ => rfl
  | (_, _, _, _) :: cs, o => by simp [sumMinorsData, sumMinorsData_length cs (o + 1)]

theorem mem_sumMinorsData {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ {cds : List CtorDatum} {o : Nat} {d : Nat × Nat × AVExpr},
      d ∈ sumMinorsData m ψ nP b cds o → d.2.1 = b
  | [], _, _, h => nomatch h
  | (_, _, _, _) :: cs, o, d, h => by
    simp only [sumMinorsData, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_sumMinorsData h

/-- **The generated sum recursor type's binder data**: parameters,
motive, minors, the index telescope (lifted under the motive and the
minors), major. -/
def sumRecDataAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AVExpr))
    (cds : List CtorDatum) : List (Nat × Nat × AVExpr) :=
  rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
    sumMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 ips) ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), majorAVAt m T ψ nP nIdx cds.length)]

/-- **Rule `j`'s binder data**: the recursor's parameter, motive and
minor entries, then constructor `j`'s field data lifted `n + 1`
under. -/
def sumRuleDataAV {env : Env} (m : EnvS2Core V env) (T : Name) (ψ : Name → Nat)
    (nP nIdx : Nat) (ℓ : Level) (pps ips : List (Nat × Nat × AVExpr))
    (cds : List CtorDatum) (ds : List (Nat × Nat × AVExpr)) :
    List (Nat × AVExpr) :=
  (rebit (pwBit ψ (Level.zeronessOf ℓ)) pps ++
    [(0, pwBit ψ (Level.zeronessOf ℓ), motiveAVI m T ψ nP nIdx ℓ ips)] ++
    sumMinorsData m ψ nP (pwBit ψ (Level.zeronessOf ℓ)) cds 1 ++
    rebit (pwBit ψ (Level.zeronessOf ℓ)) (liftDoms (cds.length + 1) 0 (ds.drop nP))).map
    fun d : Nat × Nat × AVExpr => (d.2.1, d.2.2)

/-- Rule `j`'s core: minor `j` at the field variables. -/
def sumRuleCoreAV (nF n j : Nat) : AVExpr :=
  AVExpr.mkAppN (.bvar (nF + n - 1 - j)) (fieldBvars nF)

/-! ## The per-constructor reading premise -/

/-- What the readings need of one constructor `(C, nF, cty)` and its
datum `(C, nF, ds, Es)`: stored at the block's level parameters,
closed, its telescope strips to the family at the parameter variables
and `nIdx` index expressions, and it reads to the Π-tower over `ds`
ending in the family at the parameter variables and the index
readings `Es`. -/
structure CtorRead {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (c : Name × Nat × Expr) (cd : CtorDatum) : Prop where
  name : cd.1 = c.1
  nF : cd.2.1 = c.2.1
  find : ∃ ci : ConstantInfo, env.find? c.1 = some ci ∧ ci.toConstantVal.levelParams = lps
  hasFvar : c.2.2.hasFvar = false
  bounded : c.2.2.looseBVarsBounded 0 = true
  resid : ∃ (cbs : List (Name × Expr × BinderMeta)) (es : List Expr),
    c.2.2.stripPis (nP + c.2.1)
      = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt c.2.1 nP ++ es)) ∧
    es.length = nIdx
  read : denoteP m.acval env ψ 0 c.2.2
    = some (mkPisAV cd.2.2.1 (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP c.2.1 ++ cd.2.2.2)))
  len : cd.2.2.1.length = nP + c.2.1
  lenE : cd.2.2.2.length = nIdx

theorem CtorRead.strip {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {c : Name × Nat × Expr} {cd : CtorDatum}
    (h : CtorRead m ψ T lps nP nIdx c cd) : (c.2.2.stripPis (nP + c.2.1)).isSome = true := by
  obtain ⟨cbs, es, hs, -⟩ := h.resid
  rw [hs]; rfl

/-- The constructors' reading premises, positionally. -/
inductive CtorReads {env : Env} (m : EnvS2Core V env) (ψ : Name → Nat) (T : Name)
    (lps : List Name) (nP nIdx : Nat) : List (Name × Nat × Expr) → List CtorDatum → Prop
  | nil : CtorReads m ψ T lps nP nIdx [] []
  | cons {c cd cs cds} : CtorRead m ψ T lps nP nIdx c cd → CtorReads m ψ T lps nP nIdx cs cds →
      CtorReads m ψ T lps nP nIdx (c :: cs) (cd :: cds)

theorem CtorReads.length_eq {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List CtorDatum},
      CtorReads m ψ T lps nP nIdx ctors cds → cds.length = ctors.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [CtorReads.length_eq h]

theorem CtorReads.getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List CtorDatum},
      CtorReads m ψ T lps nP nIdx ctors cds →
      ∀ {i : Nat} {c : Name × Nat × Expr}, ctors[i]? = some c →
        ∃ cd, cds[i]? = some cd ∧ CtorRead m ψ T lps nP nIdx c cd
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hr htl, i, c, h => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hr⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨cd, hcd, hR⟩ := CtorReads.getElem? htl h
      exact ⟨cd, by simpa using hcd, hR⟩

/-! ## The cores -/

/-- A constant at the parameter variables and `nF` more variables
above `o` extras reads to its leaf at the parameter and field
variables. -/
theorem denoteP_famSpine_at {m : EnvS2Core V env} {ψ : Name → Nat} {C : Name}
    {lps : List Name} {ci : ConstantInfo} (hfC : env.find? C = some ci)
    (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF o : Nat} {tfvs xFvs : List Expr}
    (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + k) nm ty) :
    denoteP m.acval env ψ (nP + o + nF) (Expr.mkAppN (.const C (lps.map .param)) (tfvs ++ xFvs))
      = some (AVExpr.mkAppN (m.acval C ψ) (paramBvarsAt nP (nP + o + nF) ++ fieldBvars nF)) := by
  have hspP : DenoteSpineP m.acval env ψ (nP + o + nF) tfvs (paramBvarsAt nP (nP + o + nF)) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + o + nF) tfvs 0
      (fun k x hx => by
        obtain ⟨nm, ty, h⟩ := hidxT k x hx
        exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩)
    rw [hlenT] at this
    have he : ((List.range nP).map fun k => AVExpr.bvar (nP + o + nF - 1 - (0 + k)))
        = paramBvarsAt nP (nP + o + nF) := by
      unfold paramBvarsAt
      apply List.map_congr_left
      intro k _
      rw [Nat.zero_add]
    rwa [he] at this
  have hspX : DenoteSpineP m.acval env ψ (nP + o + nF) xFvs (fieldBvars nF) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + o + nF) xFvs
      (nP + o) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AVExpr.bvar (nP + o + nF - 1 - (nP + o + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  have hconst : denoteP m.acval env ψ (nP + o + nF) (.const C (lps.map .param))
      = some (m.acval C ψ) := by
    rw [denoteP_const hfC (by rw [hlpsC]; simp), hlpsC, Level.substFn_param_self]
  exact denoteP_mkAppN (hspP.append hspX) hconst

/-- **The constructor's index expressions at the recursor frame.**
Under `o` extras and the field variables, the residual's index
expressions read to the constructor's own index readings lifted `o`
above the fields: the opened residual `T p⃗ e⃗` reads to the lifted
constructor body, whose spine is inverted. -/
theorem denoteSpineP_idxArgs_lift {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nF nIdx o : Nat} {crest0 : Expr} {fbs : List (Name × Expr × BinderMeta)} {es : List Expr}
    (hsF : crest0.stripPis nF
      = some (fbs, Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt nF nP ++ es)))
    {ds : List (Nat × Nat × AVExpr)} {Es : List AVExpr}
    {tfvs xFvs : List Expr} (hlenT : tfvs.length = nP) (hlenX : xFvs.length = nF)
    (hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + o + k) nm ty)
    (hcreadO : denoteP m.acval env ψ (nP + o) (Expr.instSeq tfvs (nP - 1) crest0)
      = some (mkPisAV (liftDoms o 0 (ds.drop nP))
          ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF)))
    (hlenD : ds.length = nP + nF) (hlenE : Es.length = nIdx) (hlenes : es.length = nIdx) :
    DenoteSpineP m.acval env ψ (nP + o + nF)
      (es.map fun e => Expr.instSeq xFvs (nF - 1) (Expr.instSeq tfvs (nP + nF - 1) e))
      (Es.map fun E => E.liftN o nF) := by
  have hclX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxX q a hq
    rfl
  have hnil : tfvs = [] ∨ nP - 1 + nF = nP + nF - 1 := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the opened residual at the frame
  obtain ⟨fbs', hsF'⟩ := stripPis_instSeq tfvs (nP - 1) (by omega) hsF
  obtain ⟨ds', hci⟩ := Lech.instPisAt_of_stripPis xFvs (by rw [hlenX]; exact hsF')
  have hstX : stripPisAV nF (mkPisAV (liftDoms o 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF))
      = some (liftDoms o 0 (ds.drop nP),
          (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF) := by
    have := stripPisAV_mkPisAV (liftDoms o 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN o nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have htele := piTeleP_of_stripPisAV hstX
  have hread := instPisAt_openerResP xFvs hci (j := nP + o) hidxX hcreadO (by rw [hlenX]; exact htele)
  rw [hlenX] at hread
  -- the residual, instantiated: the family at the parameter variables and the instantiated
  -- index expressions
  have hres : Expr.instSeq xFvs (nF - 1) (Expr.instSeq tfvs (nP - 1 + nF)
      (Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt nF nP ++ es)))
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ es.map fun e => Expr.instSeq xFvs (nF - 1) (Expr.instSeq tfvs (nP + nF - 1) e)) := by
    rw [instSeq_idx_congr (sp := tfvs) (t := nP - 1 + nF) (t' := nP + nF - 1) _ hnil,
      Expr.instSeq_mkAppN, Expr.instSeq_mkAppN, List.map_append, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + nF - 1 = nF + nP - 1 from by omega,
      Lech.map_instSeq_directPsAt tfvs nF nP hclT (by omega), List.take_of_length_le (by omega),
      map_instSeq_closed xFvs (nF - 1) hclT, List.map_map,
      show nF + nP - 1 = nP + nF - 1 from by omega]
    rfl
  rw [hres] at hread
  obtain ⟨fa, vs, hfa, hsp, heq⟩ := denoteP_mkAppN_inv hread
  have hfa' : fa = m.acval T ψ := by
    rw [denoteP_const hfT (by rw [hlpsT]; simp), hlpsT, Level.substFn_param_self] at hfa
    exact (Option.some.inj hfa).symm
  subst hfa'
  rw [liftN_mkAppN, liftN_eq_self_of_one (m.acval_closed T ψ), List.map_append] at heq
  have hlenV : vs.length = nP + nIdx := by
    have := hsp.length
    simp [hlenT, hlenes] at this
    omega
  obtain ⟨-, hvs⟩ := mkAppN_inj_args heq (by simp [paramBvars, hlenV, hlenE])
  obtain ⟨vs₁, vs₂, rfl, h1, h2⟩ := DenoteSpineP.append_inv hsp
  have hlen1 : vs₁.length = nP := by rw [← h1.length, hlenT]
  obtain ⟨-, rfl⟩ := List.append_inj hvs.symm (by simp [paramBvars, hlen1])
  exact h2

/-- Rule `j`'s core `minor_j f⃗`, read at the full frame under the
motive and `n` minors. -/
theorem denoteP_ruleCore_at {m : EnvS2Core V env} {ψ : Name → Nat} {nP nF n j : Nat}
    {xFvs : List Expr} {nmK : Name} {tyK : Expr} (hlenX : xFvs.length = nF) (hj : j < n)
    (hidxX : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + 1 + n + k) nm ty) :
    denoteP m.acval env ψ (nP + 1 + n + nF) (Expr.mkAppN (.fvar (nP + 1 + j) nmK tyK) xFvs)
      = some (sumRuleCoreAV nF n j) := by
  have hspX : DenoteSpineP m.acval env ψ (nP + 1 + n + nF) xFvs (fieldBvars nF) := by
    have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nF) xFvs
      (nP + 1 + n) hidxX
    rw [hlenX] at this
    have he : ((List.range nF).map fun k => AVExpr.bvar (nP + 1 + n + nF - 1 - (nP + 1 + n + k)))
        = fieldBvars nF := by
      unfold fieldBvars
      apply List.map_congr_left
      intro k _
      congr 1
      omega
    rwa [he] at this
  rw [denoteP_mkAppN hspX (by rw [denoteP_fvar]),
    show nP + 1 + n + nF - 1 - (nP + 1 + j) = nF + n - 1 - j from by omega]
  rfl

/-! ## The minor premise -/

set_option maxHeartbeats 1600000 in
/-- **The minor premise at offset `o`**, instantiated at the
parameters and the `o` extras, reads to `minorAVAt`. -/
theorem denoteP_minorAt {m : EnvS2Core V env} {ψ : Name → Nat} {T C : Name} {lps : List Name}
    {ciT ci : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    (hfC : env.find? C = some ci) (hlpsC : ci.toConstantVal.levelParams = lps)
    {nP nF nIdx : Nat} {pw : PropWhen} {cty mty : Expr} {extras : List Expr}
    (hmin : Lech.directMinorTyI C lps nP nF extras.length pw cty = some mty)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hresid : ∃ (cbs : List (Name × Expr × BinderMeta)) (es : List Expr),
      cty.stripPis (nP + nF)
        = some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt nF nP ++ es)) ∧
      es.length = nIdx)
    {ds : List (Nat × Nat × AVExpr)} {Es : List AVExpr}
    (hCread : denoteP m.acval env ψ 0 cty
      = some (mkPisAV ds (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es))))
    (hlenD : ds.length = nP + nF) (hlenE : Es.length = nIdx)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a)
    (ho : 0 < extras.length)
    (hidxE : ∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) :
    denoteP m.acval env ψ (nP + extras.length)
        (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty)
      = some (minorAVAt m C ψ nP nF (pwBit ψ pw) extras.length ds Es) := by
  obtain ⟨cbs, fbs, crest0, res, hsC, hsF, hrep⟩ := Lech.directMinorTyI_unfold hmin
  obtain ⟨cbs', es, hsAll, hlenes⟩ := hresid
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := by rw [hsAll]; rfl
  -- the residual's shape
  have hres : res = Expr.mkAppN (.const T (lps.map .param)) (Lech.directPsAt nF nP ++ es) := by
    have := (Lech.stripPis_append nP hsC hsF).symm.trans hsAll
    exact (Prod.mk.injEq _ _ _ _ ▸ Option.some.inj this).2
  subst hres
  have hargs : ((Expr.mkAppN (.const T (lps.map .param))
      (Lech.directPsAt nF nP ++ es)).getAppArgs).drop nP = es := by
    rw [Expr.getAppArgs_mkAppN, show (Expr.const T (lps.map .param)).getAppArgs = [] from rfl,
      List.nil_append, List.drop_left' (by simp [Lech.directPsAt])]
  rw [hargs] at hrep
  have hes : ∀ e ∈ es, e.looseBVarsBounded (nP + nF) = true := by
    intro e he
    have hb := Expr.stripPis_body_bounded (nP + nF) hsAll hCb
    rw [Nat.zero_add] at hb
    exact Lech.looseBVarsBounded_getAppArgs hb e
      (by rw [Expr.getAppArgs_mkAppN]; exact List.mem_append_right _ (List.mem_append_right _ he))
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxT q a hq
    rfl
  have hclE : ∀ a ∈ extras, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE q a hq
    rfl
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb; rwa [Nat.zero_add] at this
  have hmin' := Lech.replacePisPw_instSeq (tfvs ++ extras) (nP + extras.length - 1)
    (by simp [hlenT]; omega) hrep
  rw [Lech.instSeq_minorTele tfvs extras hlenT hclT hcb0] at hmin'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + extras.length) hcstrip
  have hcreadO := ctorResidual_read_lift hcread hcw hlenD extras.length
  have hstX : stripPisAV nF (mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF))
      = some (liftDoms extras.length 0 (ds.drop nP),
          (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF) := by
    have := stripPisAV_mkPisAV (liftDoms extras.length 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN extras.length nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hminor := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nF hmin' hopX
    hcreadO hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨mfv, hhead⟩ : ∃ mfv, extras[0]? = some mfv :=
    ⟨_, List.getElem?_eq_getElem ho⟩
  obtain ⟨nmM, tyM, rfl⟩ := hidxE 0 mfv hhead
  rw [Nat.add_zero] at hhead
  rw [Lech.instSeq_minorBodyI_at tfvs extras xFvs hlenT hlenX hclT hclE hclX hhead hes] at hminor
  -- the core's reading: the motive variable at the index readings and the constructor spine
  have hspI := denoteSpineP_idxArgs_lift hfT hlpsT (o := extras.length) hsF hlenT hlenX hclT hidxX
    hcreadO hlenD hlenE hlenes
  have hspine := denoteP_famSpine_at (m := m) (ψ := ψ) hfC hlpsC (o := extras.length) hlenT hlenX hidxT hidxX
  rw [denoteP_mkAppN (hspI.append (.cons hspine .nil)) (by rw [denoteP_fvar]),
    Option.map_some] at hminor
  rw [hminor]
  unfold minorAVAt
  rw [show nP + extras.length + nF - 1 - nP = nF + extras.length - 1 from by omega]

/-! ## The minors' telescopes -/

set_option maxHeartbeats 1600000 in
/-- **The `∀`-telescope of minors** reads to the Π-tower over
`sumMinorsData`, the body read under the motive and all minors. -/
theorem denoteP_minorsPis {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List CtorDatum}
      {body mins : Expr} {extras : List Expr},
      CtorReads m ψ T lps nP nIdx ctors cds →
      Lech.directMinorsPisI lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) ∧
        denoteP m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteP m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkPisAV (sumMinorsData m ψ nP (pwBit ψ pw) cds extras.length))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [Lech.directMinorsPisI_nil hmin]
    simp only [List.length_nil, Nat.add_zero, sumMinorsData]
    cases denoteP m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds, Es⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    subst hC' hnF'
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Lech.directMinorsPisI_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    -- the binder
    rw [Expr.instSeq_forallE (tfvs ++ extras) (nP + extras.length - 1) _ _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteP_forallE,
      denoteP_minorAt hfT hlpsT hfC hlpsC hmty hc.hasFvar hc.bounded hc.resid hc.read hc.len
        hc.lenE hlenT hidxT hspW ho hidxE]
    -- the rest, at the minor's variable
    generalize hmk : Expr.fvar (nP + extras.length) (Lech.Name.lastStr C)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          simp at this
          omega
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Lech.Name.lastStr C,
          Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : Lech.directMinorsPisI lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteP_minorsPis hfT hlpsT hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteP m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

set_option maxHeartbeats 1600000 in
/-- **The `λ`-telescope of minors** reads to the λ-tower over
`sumMinorsData`'s domains, the body read under the motive and all
minors. -/
theorem denoteP_minorsLams {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {pw : PropWhen} {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    ∀ {ctors : List (Name × Nat × Expr)} {cds : List CtorDatum}
      {body mins : Expr} {extras : List Expr},
      CtorReads m ψ T lps nP nIdx ctors cds →
      Lech.directMinorsLamsI lps nP pw ctors extras.length body = some mins →
      0 < extras.length →
      (∀ (k : Nat) (x : Expr), extras[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) →
      ∃ extras' : List Expr, extras'.length = ctors.length + extras.length ∧
        (∀ (k : Nat) (x : Expr), extras'[k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty) ∧
        denoteP m.acval env ψ (nP + extras.length)
            (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mins)
          = (denoteP m.acval env ψ (nP + extras.length + ctors.length)
              (Expr.instSeq (tfvs ++ extras') (nP + extras.length + ctors.length - 1) body)).map
              (mkLamsAV ((sumMinorsData m ψ nP (pwBit ψ pw) cds extras.length).map
                fun d => (d.2.1, d.2.2)))
  | [], cds, body, mins, extras, hcr, hmin, _, hidxE => by
    cases hcr with
    | nil =>
    refine ⟨extras, by simp, hidxE, ?_⟩
    rw [Lech.directMinorsLamsI_nil hmin]
    simp only [List.length_nil, Nat.add_zero, sumMinorsData, List.map_nil]
    cases denoteP m.acval env ψ (nP + extras.length)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) body) <;> rfl
  | (C, nF, cty) :: cs, cds, body, mins, extras, hcr, hmin, ho, hidxE => by
    cases hcr with
    | @cons _ cd _ cds' hc hcs =>
    obtain ⟨C', nF', ds, Es⟩ := cd
    have hC' : C = C' := hc.name.symm
    have hnF' : nF = nF' := hc.nF.symm
    subst hC' hnF'
    obtain ⟨ci, hfC, hlpsC⟩ := hc.find
    obtain ⟨mty, rest, hmty, hrest, rfl⟩ := Lech.directMinorsLamsI_cons hmin
    have hlenTE : (tfvs ++ extras).length = nP + extras.length := by simp [hlenT]
    rw [Lech.instSeq_lam (tfvs ++ extras) (nP + extras.length - 1) _ _ _ _ (by omega),
      show nP + extras.length - 1 + 1 = nP + extras.length from by omega,
      denoteP_lam,
      denoteP_minorAt hfT hlpsT hfC hlpsC hmty hc.hasFvar hc.bounded hc.resid hc.read hc.len
        hc.lenE hlenT hidxT hspW ho hidxE]
    generalize hmk : Expr.fvar (nP + extras.length) (Lech.Name.lastStr C)
      (Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty) = mkfv
    have hY : (Expr.instSeq (tfvs ++ extras) (nP + extras.length) rest).instantiate1 mkfv 0
        = Expr.instSeq (tfvs ++ (extras ++ [mkfv])) (nP + (extras ++ [mkfv]).length - 1) rest := by
      rw [← List.append_assoc, Expr.instSeq_append (tfvs ++ extras) [mkfv], hlenTE,
        List.length_append, List.length_singleton,
        show nP + (extras.length + 1) - 1 = nP + extras.length from by omega, Nat.sub_self]
      rfl
    have hidxE' : ∀ (k : Nat) (x : Expr), (extras ++ [mkfv])[k]? = some x →
        ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
      intro k x hx
      by_cases hk : k < extras.length
      · rw [List.getElem?_append_left hk] at hx
        exact hidxE k x hx
      · rw [List.getElem?_append_right (by omega)] at hx
        have hk0 : k - extras.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          simp at this
          omega
        rw [hk0] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        refine ⟨Lech.Name.lastStr C,
          Expr.instSeq (tfvs ++ extras) (nP + extras.length - 1) mty, ?_⟩
        rw [← hmk]
        congr 1
        omega
    have hrest' : Lech.directMinorsLamsI lps nP pw cs (extras ++ [mkfv]).length body
        = some rest := by
      rw [List.length_append, List.length_singleton]; exact hrest
    obtain ⟨extras', hlenE', hidxE'', hread⟩ :=
      denoteP_minorsLams hfT hlpsT hlenT hidxT hspW hcs hrest' (by simp) hidxE'
    rw [show nP + extras.length + 1 = nP + (extras ++ [mkfv]).length from by simp; omega, hY, hread]
    refine ⟨extras', by simp [hlenE']; omega, hidxE'', ?_⟩
    have harith : nP + (extras.length + 1) + cs.length = nP + extras.length + (cs.length + 1) := by
      omega
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, harith]
    cases denoteP m.acval env ψ (nP + extras.length + (cs.length + 1))
      (Expr.instSeq (tfvs ++ extras') (nP + extras.length + (cs.length + 1) - 1) body) <;> rfl

/-! ## The motive -/

/-- **The motive's type**, instantiated at the parameters, reads to
`motiveAVI` over the former's index data. -/
theorem denoteP_motiveI {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name} {lps : List Name}
    {ciT : ConstantInfo} (hfT : env.find? T = some ciT)
    (hlpsT : ciT.toConstantVal.levelParams = lps)
    {nP nIdx : Nat} {ℓ : Level} {tty itele motiveTy : Expr}
    {tbs : List (Name × Expr × BinderMeta)}
    (hsT : tty.stripPis nP = some (tbs, itele))
    (hmot : Lech.directMotiveTyI T lps nP nIdx ℓ itele = some motiveTy)
    (hTf : tty.hasFvar = false) (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {ppsAll : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx)
    {tfvs : List Expr} (hlenT : tfvs.length = nP)
    (hidxT : ∀ (k : Nat) (x : Expr), tfvs[k]? = some x → ∃ nm ty, x = Expr.fvar k nm ty)
    (hspW : ∀ (i : Nat) (a : Expr), tfvs[i]? = some a → Expr.WScoped (0 + i + 1) a) :
    denoteP m.acval env ψ nP (Expr.instSeq tfvs (nP - 1) motiveTy)
      = some (motiveAVI m T ψ nP nIdx ℓ (ppsAll.drop nP)) := by
  have hclT : ∀ a ∈ tfvs, a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxT q a hq
    rfl
  have hnil : tfvs = [] ∨ nP - 1 + nIdx = nIdx + nP - 1 := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  unfold Lech.directMotiveTyI at hmot
  have hmot' := Lech.replacePisPw_instSeq tfvs (nP - 1) (by omega) hmot
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hTf hTread hlenP hsT hstripT hlenT hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome nIdx nP htstrip
  have hstI : stripPisAV nIdx (mkPisAV (ppsAll.drop nP) (.sort w))
      = some (ppsAll.drop nP, .sort w) := by
    have := stripPisAV_mkPisAV (ppsAll.drop nP) (AVExpr.sort w)
    rwa [List.length_drop, hlenP, Nat.add_sub_cancel_left] at this
  have hmotive := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nIdx hmot' hopI
    htread hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the body, instantiated at the parameters and the index variables
  have hdom1 : Expr.instSeq tfvs (nP - 1 + nIdx) (Lech.directFamI T lps nP nIdx 0 0)
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)) := by
    unfold Lech.directFamI
    rw [instSeq_idx_congr (sp := tfvs) (t := nP - 1 + nIdx) (t' := nIdx + nP - 1) _ hnil,
      Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show 0 + 0 + nIdx = nIdx from by omega,
      Lech.map_instSeq_directPsAt tfvs nIdx nP hclT (by omega), List.take_of_length_le (by omega),
      directPsAt_zero, Lech.map_instSeq_fieldBvars_above tfvs (nIdx + nP - 1) nIdx
        (by rw [hlenT]; omega)]
  have hdom2 : Expr.instSeq ifvs (nIdx - 1) (Expr.mkAppN (.const T (lps.map .param))
      (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)))
      = Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      map_instSeq_closed ifvs (nIdx - 1) hclT,
      Lech.map_instSeq_fieldBvars ifvs nIdx hclI hlenI]
  have hbody : Expr.instSeq ifvs (nIdx - 1) (Expr.instSeq tfvs (nP - 1 + nIdx)
      (.forallE (.str .anonymous "t") (Lech.directFamI T lps nP nIdx 0 0) (.sort ℓ)
        ⟨.default, .never⟩))
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
          (.sort ℓ) ⟨.default, .never⟩ := by
    rw [Expr.instSeq_forallE tfvs (nP - 1 + nIdx) _ _ _ _ (by omega), hdom1,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl,
      Expr.instSeq_forallE ifvs (nIdx - 1) _ _ _ _ (by omega), hdom2,
      Expr.instSeq_eq_self _ _ (e := Expr.sort ℓ) rfl]
  rw [hbody] at hmotive
  have hspine := denoteP_famSpine_at (m := m) (ψ := ψ) hfT hlpsT (o := 0) hlenT hlenI hidxT
    (fun k x hx => by rw [Nat.add_zero]; exact hidxI k x hx)
  rw [Nat.add_zero] at hspine
  have hpi : denoteP m.acval env ψ (nP + nIdx)
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
        (.sort ℓ) ⟨.default, .never⟩)
      = some (.pi 0 (pwBit ψ PropWhen.never)
          (AVExpr.mkAppN (m.acval T ψ) (paramBvarsAt nP (nP + nIdx) ++ fieldBvars nIdx))
          (.sort (ℓ.eval ψ))) := by
    rw [denoteP_forallE, hspine, Expr.instantiate1_sort, denoteP_sort]
    rfl
  rw [hpi, Option.map_some] at hmotive
  exact hmotive

/-! ## The generated type -/

set_option maxHeartbeats 3200000 in
/-- **The generated sum recursor type reads to the Π-tower over
`sumRecDataAV`** with the core `motive ı⃗ t`. -/
theorem denoteP_directRecTyI {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr)} {cds : List CtorDatum}
    (hcr : CtorReads m ψ T lps nP nIdx ctors cds)
    {tty recTy : Expr}
    (hgen : Lech.directRecTyI T lps elim large nP nIdx tty ctors = some recTy)
    (hTf : tty.hasFvar = false) (hTb : tty.looseBVarsBounded 0 = true)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {ppsAll : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx) :
    denoteP m.acval env ψ 0 recTy
      = some (mkPisAV (sumRecDataAV m T ψ nP nIdx (Lech.directElimLevel elim large)
            (ppsAll.take nP) (ppsAll.drop nP) cds)
          (recConcAV cds.length nIdx)) := by
  obtain ⟨tbs, itele, motiveTy, major, minors, hsT, hmot, hmaj, hmin, hrec⟩ :=
    Lech.directRecTyI_unfold hgen
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  generalize hn : ctors.length = n at hmaj hmin hlenC
  generalize hℓ : Lech.directElimLevel elim large = ℓ at hrec hmaj hmin hmot ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hrec hmaj hmin ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV ppsAll (.sort w))
      = some (ppsAll.take nP, mkPisAV (ppsAll.drop nP) (.sort w)) :=
    stripPisAV_mkPisAV_take nP ppsAll _ (by omega)
  rw [denoteP_replacePisPw nP hrec hopT hTread hst, Nat.zero_add]
  -- the motive binder, instantiated at the parameters
  rw [Expr.instSeq_forallE tfvs (nP - 1) _ _ _ _ (by omega),
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hmotive := denoteP_motiveI hfT hlpsT hsT hmot hTf hstripT hTread hlenP hlenT hidxT hspW
  rw [denoteP_forallE, hmotive]
  -- the minors, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (Expr.instSeq tfvs (nP - 1) motiveTy)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : Lech.directMinorsPisI lps nP pw ctors [mfv].length major = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteP_minorsPis hfT hlpsT hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  -- the index telescope, under the motive and the minors
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE' q a hq
    rfl
  have hclTE : ∀ a ∈ tfvs ++ extras', a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hclT a h
    · exact hclE' a h
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  obtain ⟨mfv', hhead⟩ : ∃ x, extras'[0]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨nmM, tyM, rfl⟩ := hidxE' 0 mfv' hhead
  rw [Nat.add_zero] at hhead
  have htb0 : itele.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsT hTb; rwa [Nat.zero_add] at this
  have hmaj' := Lech.replacePisPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hmaj
  have hres := Lech.instSeq_minorTele tfvs extras' hlenT hclT htb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hmaj'
  obtain ⟨htread, htw, htstrip⟩ := ctorResidual hTf hTread hlenP hsT hstripT hlenT hidxT hspW
  obtain ⟨ifvs, irest, hopI⟩ := openPisAtFvars_of_stripPis_isSome nIdx (nP + 1 + n) htstrip
  have htreadN : denoteP m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) itele)
      = some (mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (.sort w)) := by
    have := ctorResidual_read_lift htread htw hlenP (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega, AVExpr.liftN_sort] at this
  have hstI : stripPisAV nIdx (mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (.sort w))
      = some (liftDoms (n + 1) 0 (ppsAll.drop nP), .sort w) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ppsAll.drop nP)) (AVExpr.sort w)
    rwa [liftDoms_length, List.length_drop, hlenP, Nat.add_sub_cancel_left] at this
  have hmajR := denoteP_replacePisPw (acval := m.acval) (env := env) (φ := ψ) nIdx hmaj' hopI
    htreadN hstI
  obtain ⟨hlenI, hidxI, hclI⟩ := opening_vars_at hopI
  -- the major and the conclusion, instantiated
  have hnilI : ifvs = [] ∨ nIdx - 1 + 1 = nIdx := by
    rcases Nat.eq_zero_or_pos nIdx with h0 | hpos
    · left; rw [h0] at hlenI; exact List.eq_nil_of_length_eq_zero hlenI
    · right; omega
  have hdom1 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx)
      (Lech.directFamI T lps nP nIdx (n + 1) 0)
      = Expr.mkAppN (.const T (lps.map .param))
          (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)) := by
    unfold Lech.directFamI
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      show nP + 1 + n - 1 + nIdx = (0 + (n + 1) + nIdx) + nP - 1 from by omega,
      Lech.map_instSeq_directPsAt (tfvs ++ extras') (0 + (n + 1) + nIdx) nP hclTE
        (by rw [hlenTE]; omega),
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      directPsAt_zero, Lech.map_instSeq_fieldBvars_above (tfvs ++ extras') _ nIdx
        (by rw [hlenTE]; omega)]
  have hcod1 : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1)
      (Expr.mkAppN (.bvar (nIdx + n + 1)) (Lech.directPsAt 1 nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar nP nmM tyM) (Lech.directPsAt 1 nIdx ++ [.bvar 0]) := by
    have hhead' : Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1)
        (.bvar (nIdx + n + 1)) = Expr.fvar nP nmM tyM := by
      have := Expr.instSeq_bvar (tfvs ++ extras') (nP + 1 + n - 1 + nIdx + 1) (nIdx + n + 1)
        hclTE (by omega) (by rw [hlenTE]; omega)
      rw [show nP + 1 + n - 1 + nIdx + 1 - (nIdx + n + 1) = nP from by omega,
        List.getElem?_append_right (by omega), hlenT, Nat.sub_self, hhead] at this
      exact (Option.some.inj this).symm
    rw [Expr.instSeq_mkAppN, hhead', List.map_append]
    congr 2
    · refine (List.map_congr_left ?_).trans (List.map_id _)
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      exact Lech.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)
    · simp only [List.map_cons, List.map_nil]
      rw [Lech.instSeq_bvar_lt _ _ _ (by rw [hlenTE]; omega)]
  have hdom2 : Expr.instSeq ifvs (nIdx - 1) (Expr.mkAppN (.const T (lps.map .param))
      (tfvs ++ (List.range nIdx).map fun k => Expr.bvar (nIdx - 1 - k)))
      = Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs) := by
    rw [Expr.instSeq_mkAppN, List.map_append,
      Expr.instSeq_eq_self _ _ (e := Expr.const T (lps.map .param)) rfl,
      map_instSeq_closed ifvs (nIdx - 1) hclT,
      Lech.map_instSeq_fieldBvars ifvs nIdx hclI hlenI]
  have hcod2 : Expr.instSeq ifvs (nIdx - 1 + 1)
      (Expr.mkAppN (.fvar nP nmM tyM) (Lech.directPsAt 1 nIdx ++ [.bvar 0]))
      = Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0]) := by
    rw [instSeq_idx_congr (sp := ifvs) (t := nIdx - 1 + 1) (t' := nIdx) _ hnilI,
      Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ (e := Expr.fvar nP nmM tyM) rfl,
      List.map_append, map_instSeq_directPsAt_one ifvs nIdx hclI hlenI]
    simp only [List.map_cons, List.map_nil]
    rw [Lech.instSeq_bvar_lt ifvs _ 0 (by omega)]
  have hbody : Expr.instSeq ifvs (nIdx - 1) (Expr.instSeq (tfvs ++ extras') (nP + 1 + n - 1 + nIdx)
      (.forallE (.str .anonymous "t") (Lech.directFamI T lps nP nIdx (n + 1) 0)
        (Expr.mkAppN (.bvar (nIdx + n + 1)) (Lech.directPsAt 1 nIdx ++ [.bvar 0]))
        ⟨.default, pw⟩))
      = .forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
          (Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0])) ⟨.default, pw⟩ := by
    rw [Expr.instSeq_forallE (tfvs ++ extras') (nP + 1 + n - 1 + nIdx) _ _ _ _
        (by rw [hlenTE]; omega), hdom1, hcod1,
      Expr.instSeq_forallE ifvs (nIdx - 1) _ _ _ _ (by omega), hdom2, hcod2]
  rw [hbody] at hmajR
  -- the major's reading
  have hspine := denoteP_famSpine_at (m := m) (ψ := ψ) hfT hlpsT (o := 1 + n) hlenT hlenI hidxT
    (fun k x hx => by rw [show nP + (1 + n) + k = nP + 1 + n + k from by omega]; exact hidxI k x hx)
  rw [show nP + (1 + n) + nIdx = nP + 1 + n + nIdx from by omega] at hspine
  have hconc : denoteP m.acval env ψ (nP + 1 + n + nIdx + 1)
      ((Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0])).instantiate1
        (.fvar (nP + 1 + n + nIdx) (.str .anonymous "t")
          (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))) 0)
      = some (recConcAV n nIdx) := by
    rw [Expr.mkAppN_instantiate1, List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [Expr.instantiate1_eq_self (e := Expr.fvar nP nmM tyM) rfl,
      map_instantiate1_closed hclI]
    simp +decide only [Expr.instantiate1, ↓reduceIte]
    have hspI : DenoteSpineP m.acval env ψ (nP + 1 + n + nIdx + 1) ifvs (idxVarsAV nIdx 1) := by
      have := denoteSpineP_fvars (acval := m.acval) (env := env) (φ := ψ) (nP + 1 + n + nIdx + 1)
        ifvs (nP + 1 + n) hidxI
      rw [hlenI] at this
      have he : ((List.range nIdx).map fun k =>
          AVExpr.bvar (nP + 1 + n + nIdx + 1 - 1 - (nP + 1 + n + k))) = idxVarsAV nIdx 1 := by
        unfold idxVarsAV
        apply List.map_congr_left
        intro k _
        congr 1
        omega
      rwa [he] at this
    rw [denoteP_mkAppN (hspI.append (.cons (denoteP_fvar _ _ _ _ _) .nil)) (denoteP_fvar _ _ _ _ _),
      show nP + 1 + n + nIdx + 1 - 1 - nP = 1 + nIdx + n from by omega,
      show nP + 1 + n + nIdx + 1 - 1 - (nP + 1 + n + nIdx) = 0 from by omega,
      AVExpr.mkAppN_append_one]
    rfl
  have hpi : denoteP m.acval env ψ (nP + 1 + n + nIdx)
      (.forallE (.str .anonymous "t") (Expr.mkAppN (.const T (lps.map .param)) (tfvs ++ ifvs))
        (Expr.mkAppN (.fvar nP nmM tyM) (ifvs ++ [.bvar 0])) ⟨.default, pw⟩)
      = some (.pi 0 (pwBit ψ pw) (majorAVAt m T ψ nP nIdx n) (recConcAV n nIdx)) := by
    rw [denoteP_forallE, hspine, hconc]
    rfl
  rw [hpi, Option.map_some] at hmajR
  rw [hmajR]
  -- assembly
  subst hpw
  rw [← hlenC]
  unfold sumRecDataAV majorAVAt
  rw [mkPisAV_append, mkPisAV_append, mkPisAV_append, mkPisAV_append, hlenC]
  rfl

/-! ## The generated rule -/

set_option maxHeartbeats 3200000 in
/-- **Rule `j` reads to the λ-tower over `sumRuleDataAV`** at
constructor `j`'s data, with the core `minor_j f⃗`. -/
theorem denoteP_directRecRhsI {m : EnvS2Core V env} {ψ : Name → Nat} {T : Name}
    {lps : List Name} {elim : Name} {large : Bool} {nP nIdx j : Nat} {ciT : ConstantInfo}
    (hfT : env.find? T = some ciT) (hlpsT : ciT.toConstantVal.levelParams = lps)
    {ctors : List (Name × Nat × Expr)} {cds : List CtorDatum}
    (hcr : CtorReads m ψ T lps nP nIdx ctors cds)
    {tty rhs : Expr}
    (hgen : Lech.directRecRhsI T lps elim large nP nIdx tty ctors j = some rhs)
    (hTf : tty.hasFvar = false)
    (hstripT : (tty.stripPis (nP + nIdx)).isSome = true)
    {tfvs : List Expr} {trest : Expr} (hopT : openPisAtFvars nP tty 0 = some (tfvs, trest))
    {ppsAll : List (Nat × Nat × AVExpr)} {w : Nat}
    (hTread : denoteP m.acval env ψ 0 tty = some (mkPisAV ppsAll (.sort w)))
    (hlenP : ppsAll.length = nP + nIdx)
    {C : Name} {nF : Nat} {ds : List (Nat × Nat × AVExpr)} {Es : List AVExpr}
    (hjd : cds[j]? = some (C, nF, ds, Es)) :
    denoteP m.acval env ψ 0 rhs
      = some (mkLamsAV (sumRuleDataAV m T ψ nP nIdx (Lech.directElimLevel elim large)
            (ppsAll.take nP) (ppsAll.drop nP) cds ds)
          (sumRuleCoreAV nF cds.length j)) := by
  obtain ⟨C₀, nF₀, cty, tbs, cbs, itele, motiveTy, crest0, inner, minors, hj, hsT, hmot, hsC,
    hinner, hmin, hr⟩ := Lech.directRecRhsI_unfold hgen
  obtain ⟨cd, hjd', hc⟩ := hcr.getElem? hj
  obtain ⟨rfl⟩ := Option.some.inj (hjd'.symm.trans hjd)
  have hC0 : C = C₀ := hc.name
  have hnF0 : nF = nF₀ := hc.nF
  subst hC0 hnF0
  have hCread := hc.read
  have hlenD : ds.length = nP + nF := hc.len
  have hCb : cty.looseBVarsBounded 0 = true := hc.bounded
  have hCf : cty.hasFvar = false := hc.hasFvar
  have hstripC : (cty.stripPis (nP + nF)).isSome = true := hc.strip
  obtain ⟨hlenT, hidxT, hclT, hspW⟩ := opening_vars hopT hTf
  have hlenC : cds.length = ctors.length := hcr.length_eq
  have hjn : j < ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  generalize hn : ctors.length = n at hinner hlenC hjn
  generalize hℓ : Lech.directElimLevel elim large = ℓ at hr hmin hinner hmot ⊢
  generalize hpw : Level.zeronessOf ℓ = pw at hr hmin hinner ⊢
  have hnil : tfvs = [] ∨ nP - 1 + 1 = nP := by
    rcases Nat.eq_zero_or_pos nP with h0 | hpos
    · left; rw [h0] at hlenT; exact List.eq_nil_of_length_eq_zero hlenT
    · right; omega
  -- the parameter prefix
  have hst : stripPisAV nP (mkPisAV ppsAll (.sort w))
      = some (ppsAll.take nP, mkPisAV (ppsAll.drop nP) (.sort w)) :=
    stripPisAV_mkPisAV_take nP ppsAll _ (by omega)
  rw [denoteP_pisToLamsPw nP hr hopT hTread hst, Nat.zero_add]
  -- the motive binder
  rw [Lech.instSeq_lam tfvs (nP - 1) _ _ _ _ (by omega),
    instSeq_idx_congr (sp := tfvs) (t := nP - 1 + 1) (t' := nP) minors hnil]
  have hmotive := denoteP_motiveI hfT hlpsT hsT hmot hTf hstripT hTread hlenP hlenT hidxT hspW
  rw [denoteP_lam, hmotive]
  -- the minors, at the motive's variable
  generalize hmfv : (Expr.fvar nP (.str .anonymous "motive")
    (Expr.instSeq tfvs (nP - 1) motiveTy)) = mfv
  have hX : (Expr.instSeq tfvs nP minors).instantiate1 mfv 0
      = Expr.instSeq (tfvs ++ [mfv]) nP minors := by
    rw [Expr.instSeq_append, hlenT, Nat.sub_self]
    rfl
  have hidxE : ∀ (k : Nat) (x : Expr), [mfv][k]? = some x → ∃ nm ty, x = Expr.fvar (nP + k) nm ty := by
    intro k x hx
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, by rw [← hmfv, Nat.add_zero]⟩
    | succ k => simp at hx
  have hmin' : Lech.directMinorsLamsI lps nP pw ctors [mfv].length inner = some minors := by
    rw [List.length_singleton]; exact hmin
  obtain ⟨extras', hlenE', hidxE', hread⟩ :=
    denoteP_minorsLams hfT hlpsT hlenT hidxT hspW hcr hmin' (by simp) hidxE
  rw [hn, List.length_singleton] at hlenE' hread
  rw [Nat.add_sub_cancel] at hread
  rw [hX, hread]
  -- the inner λ-telescope, at the motive's and the minors' variables
  have hclE' : ∀ a ∈ extras', a.looseBVarsBounded 0 = true := fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxE' q a hq
    rfl
  have hlenTE : (tfvs ++ extras').length = nP + 1 + n := by simp [hlenT, hlenE']; omega
  have hcb0 : crest0.looseBVarsBounded nP = true := by
    have := Expr.stripPis_body_bounded nP hsC hCb; rwa [Nat.zero_add] at this
  have hinner' := Lech.pisToLamsPw_instSeq (tfvs ++ extras') (nP + 1 + n - 1)
    (by rw [hlenTE]; omega) hinner
  have hres := Lech.instSeq_minorTele tfvs extras' hlenT hclT hcb0
  rw [hlenE', show nP + (n + 1) - 1 = nP + 1 + n - 1 from by omega] at hres
  rw [hres] at hinner'
  obtain ⟨hcread, hcw, hcstrip⟩ := ctorResidual hCf hCread hlenD hsC hstripC hlenT hidxT hspW
  obtain ⟨xFvs, xrest, hopX⟩ := openPisAtFvars_of_stripPis_isSome nF (nP + 1 + n) hcstrip
  have hcreadN : denoteP m.acval env ψ (nP + 1 + n) (Expr.instSeq tfvs (nP - 1) crest0)
      = some (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
          ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF)) := by
    have := ctorResidual_read_lift hcread hcw hlenD (n + 1)
    rwa [show nP + (n + 1) = nP + 1 + n from by omega] at this
  have hstX : stripPisAV nF (mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF))
      = some (liftDoms (n + 1) 0 (ds.drop nP),
          (AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF) := by
    have := stripPisAV_mkPisAV (liftDoms (n + 1) 0 (ds.drop nP))
      ((AVExpr.mkAppN (m.acval T ψ) (paramBvars nP nF ++ Es)).liftN (n + 1) nF)
    rwa [liftDoms_length, List.length_drop, hlenD, Nat.add_sub_cancel_left] at this
  have hinnerR := denoteP_pisToLamsPw (acval := m.acval) (env := env) (φ := ψ) nF hinner' hopX
    hcreadN hstX
  obtain ⟨hlenX, hidxX, hclX⟩ := opening_vars_at hopX
  obtain ⟨mkfv, hjE⟩ : ∃ x, extras'[j + 1]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨nmK, tyK, rfl⟩ := hidxE' (j + 1) mkfv hjE
  have hrb := Lech.instSeq_ruleBody_at tfvs extras' xFvs hlenT hlenX hclT hclE' hclX hjE
  rw [hlenE', show nP + (n + 1) - 1 + nF = nP + 1 + n - 1 + nF from by omega,
    show nF + (n + 1 - 1) - 1 - j = nF + n - 1 - j from by omega] at hrb
  rw [hrb, show nP + 1 + n + nF = nP + 1 + n + nF from rfl] at hinnerR
  have hidxX' : ∀ (k : Nat) (x : Expr), xFvs[k]? = some x →
      ∃ nm ty, x = Expr.fvar (nP + 1 + n + k) nm ty := hidxX
  rw [show Expr.fvar (nP + (j + 1)) nmK tyK = Expr.fvar (nP + 1 + j) nmK tyK from by
      congr 1; omega,
    denoteP_ruleCore_at hlenX hjn hidxX', Option.map_some] at hinnerR
  rw [hinnerR]
  -- assembly
  subst hpw
  rw [← hlenC]
  unfold sumRuleDataAV
  rw [List.map_append, List.map_append, List.map_append, mkLamsAV_append, mkLamsAV_append,
    mkLamsAV_append, rebit_map_lam, rebit_map_lam, hlenC]
  rfl

end Lech.SetP
