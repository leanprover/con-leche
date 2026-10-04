module

public import Fragment.Read
public import Fragment.InstallDef

@[expose] public section

/-!
# Reading the recursor's declaration, part 1

Small bridges the installation of a recursor needs, in three groups:

* **Contexts**: the invariant of an abstraction over a context from a
  semantic bound on its body (`WellDenoted_mkLams_sem`), the invariant
  moved by the one lifting as the interpretation is
  (`WellDenoted_atCtx`), the
  abstraction over a lifted telescope (`Reader.lamCtx_liftCtx_atCtx`),
  suffixes of a well-denoted context (`CtxWD_drop`) and fitting values
  as satisfaction (`Sat_of_fits`).
* **Level instantiation**: the value walks through `instL`
  (`TeleFitV_instL`, `piBodyV_instL`) and the substituted valuation
  read back positionally (`map_substVal_eq`).

And one fact about the model of a block: **the motive is inhabited on
the family** (`IndSpec.motive_inhabited`) — by induction over the
family from the minors' typing, without uniqueness of decodings, since
at a proposition the inductive hypotheses are inhabited truth values,
whatever their value.
-/

namespace Fragment
open SetLib UnivLib IndLib

universe u

variable {V : Type u} [IndLib V]

/-! ## Contexts -/

/-- The invariant of an abstraction over a context, from a semantic
bound: the domains are well-denoted, the body is well-denoted and lies
in `G` under fitting values, and at a proposition `G` is a truth
value. -/
theorem WellDenoted_mkLams_sem (M : Name → List Nat → V) (φ : Name → Nat) {pw : PropWhen} :
    ∀ {Γ : List Expr} {b : Expr} {ρ : Nat → V} {G : (Nat → V) → V}, CtxWD M φ ρ Γ →
      (∀ vs, FitsVals M φ ρ Γ vs →
        WellDenoted M φ (consList vs ρ) b ∧ interp M φ (consList vs ρ) b ∈ˢ G (consList vs ρ)) →
      (pw.holds φ = true → ∀ vs, FitsVals M φ ρ Γ vs → G (consList vs ρ) ∈ˢ (univ 0 : V)) →
      WellDenoted M φ ρ (Expr.mkLams pw Γ b)
  | [], b, ρ, G, _, hb, _ => (hb [] trivial).1
  | A :: Γ, b, ρ, G, hctx, hb, hG => by
    rw [Expr.mkLams_cons]
    refine WellDenoted_mkLams_sem M φ
      (G := fun ρ' => piR (pw.holds φ) (interp M φ ρ' A) fun x => G (cons x ρ')) hctx.1
      (fun vs hvs => ⟨?_, ?_⟩) (fun hp _ _ => by rw [hp]; exact piR_true_mem_univ_zero)
    · rw [WellDenoted_lam]
      refine ⟨hctx.2 vs hvs, fun x hx => (hb (x :: vs) ⟨hvs, hx⟩).1,
        fun x => G (cons x (consList vs ρ)), fun x hx => (hb (x :: vs) ⟨hvs, hx⟩).2,
        fun hp x hx => hG hp (x :: vs) ⟨hvs, hx⟩⟩
    · rw [interp_lam]
      exact lamR_mem (fun x hx => (hb (x :: vs) ⟨hvs, hx⟩).2) fun hp x hx => hG hp (x :: vs) ⟨hvs, hx⟩

omit [IndLib V] in
/-- The environment the one lifting shifts to (the environment
computation of `interp_atCtx`, on its own). -/
theorem shiftE_atCtx {nF k l o d : Nat} {ys ihs fs os ps : List V} (ρ : Nat → V)
    (hy : ys.length = d) (hi : ihs.length = l) (hf : fs.length = nF) (ho : os.length = o)
    (hk : k ≤ nF) :
    shiftE (nF - k + l) d (shiftE o (nF + l + d)
        (consList ys (consList ihs (consList fs (consList os (consList ps ρ))))))
      = consList ys (consList (fs.drop (nF - k)) (consList ps ρ)) := by
  have hnk : nF - k + k = nF := Nat.sub_add_cancel hk
  have h1 : consList ys (consList ihs (consList fs (consList os (consList ps ρ)))) =
      consList (ys ++ ihs ++ fs) (consList os (consList ps ρ)) := by
    simp [consList_append]
  rw [h1, shiftE_consList_mid (by simp [hy, hi, hf]; omega) ho]
  have h2 : ys ++ ihs ++ fs = ys ++ ((ihs ++ fs.take (nF - k)) ++ fs.drop (nF - k)) := by
    simp [List.take_append_drop]
  rw [h2, consList_append, consList_append,
    shiftE_consList_mid hy (by simp [hi, hf, List.length_take]; omega)]

/-- The invariant is moved by the one lifting as the interpretation is
(`interp_atCtx`). -/
theorem WellDenoted_atCtx (M : Name → List Nat → V) (φ : Name → Nat) {nF k l o d : Nat}
    {ys ihs fs os ps : List V} (ρ : Nat → V) (e : Expr)
    (hy : ys.length = d) (hi : ihs.length = l) (hf : fs.length = nF) (ho : os.length = o)
    (hk : k ≤ nF) :
    WellDenoted M φ (consList ys (consList ihs (consList fs (consList os (consList ps ρ)))))
        (Expr.atCtx nF k l o d e)
      ↔ WellDenoted M φ (consList ys (consList (fs.drop (nF - k)) (consList ps ρ))) e := by
  rw [Expr.atCtx, WellDenoted_liftN, WellDenoted_liftN, shiftE_atCtx ρ hy hi hf ho hk]

/-- The abstraction over a lifted telescope is the abstraction over
the telescope at its own frame (the `lamCtx` twin of
`Reader.piCtx_liftCtx_atCtx`). -/
theorem IndSpec.Reader.lamCtx_liftCtx_atCtx {S : IndSpec} {M : Name → List Nat → V} {φ : Name → Nat}
    {env : Env} {F : List Nat → List V → List V → V} {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ F M' φ') {nF k l o : Nat} {ihsE fs os ps : List V} {ρ : Nat → V}
    (hi : ihsE.length = l) (hf : fs.length = nF) (ho : os.length = o) (hk : k ≤ nF)
    (hps : ps.length = S.nP) (p : Bool) :
    ∀ (tele : List Expr),
      (∀ t T, tele[t]? = some T →
        Expr.Scoped env S.lparams (S.nP + k + (tele.length - 1 - t)) T) →
      ∀ (F : (Nat → V) → V),
        lamCtx M' φ' p (consList ihsE (consList fs (consList os (consList ps ρ))))
            (Expr.liftCtx (fun t T => Expr.atCtx nF k l o t T) tele) F
          = lamCtx M (S.ψ (S.lparams.map φ)) p (consList (fs.drop (nF - k)) (envP ps)) tele
              fun ρ' => F (consList (readEnv tele.length ρ')
                (consList ihsE (consList fs (consList os (consList ps ρ)))))
  | [], _, F => by simp [readEnv]
  | T :: rest, hsc, F => by
    have hsc' : ∀ t T', rest[t]? = some T' →
        Expr.Scoped env S.lparams (S.nP + k + (rest.length - 1 - t)) T' := by
      intro t T' hT'
      have := hsc (t + 1) T' (by simpa using hT')
      simpa [Nat.sub_sub, Nat.add_comm] using this
    simp only [Expr.liftCtx_cons, lamCtx_cons]
    rw [R.lamCtx_liftCtx_atCtx hi hf ho hk hps p rest hsc']
    refine lamCtx_congr M _ fun ys hys => ?_
    have hl := FitsVals_length M _ hys
    rw [readEnv_consList hl, interp_atCtx M' φ' ρ T hl hi hf ho hk]
    have hT : interp M' φ' (consList ys (consList (fs.drop (nF - k)) (consList ps ρ))) T
        = interp M (S.ψ (S.lparams.map φ)) (consList ys (consList (fs.drop (nF - k)) (envP ps))) T := by
      rw [← consList_append ys (fs.drop (nF - k)) (consList ps ρ),
        ← consList_append ys (fs.drop (nF - k)) (envP ps)]
      refine R.read (hsc 0 T rfl) ?_
      simp only [List.length_append, hl, List.length_drop, hf, hps, List.length_cons,
        Nat.add_sub_cancel]
      omega
    rw [hT]
    refine lamR_congr fun x hx => ?_
    rw [show cons x (consList ys (consList (fs.drop (nF - k)) (envP ps)))
        = consList (x :: ys) (consList (fs.drop (nF - k)) (envP ps)) from rfl,
      readEnv_consList (by simp [hl])]
    rfl

/-- The domains of a suffix of a context are well-denoted. -/
theorem CtxWD_drop (M : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} :
    ∀ {Γ : List Expr} (i : Nat), CtxWD M φ ρ Γ → CtxWD M φ ρ (Γ.drop i)
  | [], _, _ => by rw [List.drop_nil]; trivial
  | _ :: _, 0, h => h
  | _ :: Γ, i + 1, h => by rw [List.drop_succ_cons]; exact CtxWD_drop M φ i h.1

/-- Fitting values under well-denoted domains satisfy the context
(`Sat`). -/
theorem Sat_of_fits (M : Name → List Nat → V) (φ : Name → Nat) {ρ : Nat → V} :
    ∀ {Γ : List Expr} {vs : List V}, CtxWD M φ ρ Γ → FitsVals M φ ρ Γ vs →
      Sat M φ Γ (consList vs ρ)
  | [], [], _, _ => trivial
  | [], _ :: _, _, hfit => hfit.elim
  | _ :: _, [], _, hfit => hfit.elim
  | A :: Γ, v :: vs, hctx, hfit => by
    rw [consList_cons, Sat_cons]
    exact ⟨Sat_of_fits M φ hctx.1 hfit.1, hctx.2 vs hfit.1, hfit.2⟩

/-! ## Level instantiation -/

/-- A value walk along a level-instantiated telescope is the walk at
the composed valuation. -/
theorem TeleFitV_instL (M : Name → List Nat → V) (φ : Name → Nat) (ps : List Name)
    (ls : List Level) : ∀ {ρ : Nat → V} {T : Expr} {vs : List V},
    TeleFitV M φ ρ (T.instL ps ls) vs ↔ TeleFitV M (Level.substVal φ ps ls) ρ T vs
  | _, _, [] => ⟨fun _ => TeleFitV_nil _ _ _ _, fun _ => TeleFitV_nil _ _ _ _⟩
  | ρ, .pi A pw B, v :: vs => by
    rw [Expr.instL_pi, TeleFitV_pi_cons, TeleFitV_pi_cons, interp_instL, TeleFitV_instL]
  | _, .bvar _, _ :: _ => Iff.rfl
  | _, .sort _, _ :: _ => Iff.rfl
  | _, .const _ _, _ :: _ => Iff.rfl
  | _, .app _ _, _ :: _ => Iff.rfl
  | _, .lam _ _ _, _ :: _ => Iff.rfl

omit [IndLib V] in
/-- The body a level-instantiated telescope leaves is the body the
telescope leaves, instantiated. -/
theorem piBodyV_instL (ps : List Name) (ls : List Level) : ∀ {ρ : Nat → V} {T : Expr} {vs : List V},
    piBodyV ρ (T.instL ps ls) vs = (piBodyV ρ T vs).map fun p => (p.1.instL ps ls, p.2)
  | ρ, T, [] => by rw [piBodyV_nil, piBodyV_nil, Option.map_some]
  | ρ, .pi A pw B, v :: vs => by
    rw [Expr.instL_pi]
    exact piBodyV_instL ps ls
  | _, .bvar _, _ :: _ => rfl
  | _, .sort _, _ :: _ => rfl
  | _, .const _ _, _ :: _ => rfl
  | _, .app _ _, _ :: _ => rfl
  | _, .lam _ _ _, _ :: _ => rfl

/-- With distinct level parameters, instantiating them and evaluating
is evaluating their substitutes: the concrete levels, read back
positionally, are the substituted valuation on the parameters. -/
theorem map_substVal_eq (φ : Name → Nat) :
    ∀ {ps : List Name}, ps.Nodup → ∀ {ls : List Level}, ls.length = ps.length →
      ps.map (Level.substVal φ ps ls) = ls.map (Level.eval φ)
  | [], _, [], _ => rfl
  | [], _, _ :: _, hlen => by simp at hlen
  | _ :: _, _, [], hlen => by simp at hlen
  | p :: ps, hnd, l :: ls, hlen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · simp [Level.substVal, Level.lookupLevel]
    · rw [← map_substVal_eq φ hnd' hlen]
      apply List.map_congr_left
      intro n hn
      have hnp : (n == p) = false := by
        simpa using fun h : n = p => hp (h ▸ hn)
      simp [Level.substVal, Level.lookupLevel, List.lookup_cons, hnp]

/-! ## The motive is inhabited on the family -/

/-- Pairwise witnesses along a list. -/
theorem ListRel.exists {α β : Type _} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, R a b) → ∃ bs, ListRel R l bs
  | [], _ => ⟨[], trivial⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := ListRel.exists fun a' ha' => h a' (List.mem_cons_of_mem a ha')
    exact ⟨b :: bs, hb, hbs⟩

/-- Some member of a set, if it has one; the point if not. -/
noncomputable def pickMem (A : V) : V :=
  open Classical in if h : ∃ v, v ∈ˢ A then Classical.choose h else pt

theorem pickMem_mem {A : V} (h : ∃ v, v ∈ˢ A) : pickMem A ∈ˢ A := by
  unfold pickMem; rw [dite_eq_left h]; exact Classical.choose_spec h

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- The indices of a member of the family fit the index context, once
every constructor's index expressions fit at fitting fields. -/
theorem idx_fits_of_mem_Fam {ps : List V} (hnr : S.NoRecDep) (hb : S.DomsBounded M ls ps)
    (hco : S.ContOk M ls ps)
    (hidx : ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → ∀ fs,
      S.FitsFields M ls (S.Fam M ls ps) ps c.fields fs →
      FitsVals M (S.ψ ls) (envP ps) S.indices (S.idxVals M ls (consList fs (envP ps)) c.idx))
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) :
    FitsVals M (S.ψ ls) (envP ps) S.indices is := by
  obtain ⟨j, c, fs, hc, hfit, his, -⟩ := (S.mem_Fam M ls hnr hb hco).mp ht
  rw [his]
  exact hidx j c hc fs hfit

/-- **The motive is inhabited on the family** (without uniqueness of
decodings): by induction over the family, from the minors' typing — at
a proposition the inductive hypotheses are inhabited truth values, so
their values need not be the recursor's. -/
theorem motive_inhabited {ps : List V} (hpl : S.nest = none) (hnr : S.NoRecDep)
    (hb : S.DomsBounded M ls ps) (q : Bool)
    (m : V) (mins : List V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOk M ls q ps m mins j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) : ∃ v, v ∈ˢ appList m (is.reverse ++ [t]) := by
  have hco := S.contOk_of_plain M ls hpl ps
  refine S.Fam_induction M ls hnr hb hco (fun is t => ∃ v, v ∈ˢ appList m (is.reverse ++ [t])) ?_ is t ht
  intro is t hs
  obtain ⟨j, c, fs, hc, hfit, his, rfl⟩ := hs
  have hfitF := S.FitsFields_of_sep M ls hco _ hfit
  subst his
  -- the inductive hypotheses: one inhabitant of each hypothesis' type
  obtain ⟨ihs, hihs⟩ : ∃ ihs, ListRel (S.IhTyped M ls q ps m fs) c.recFields ihs := by
    refine ListRel.exists fun kf hkf => ?_
    obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
    have hget := S.FitsFields_get M ls hfit hf hk
    obtain ⟨k, f⟩ := kf
    cases f with
    | ordinary _ => simp [Field.isRec] at hrec
    | container =>
      rw [S.fieldSet_container_none M ls hpl] at hget
      exact absurd hget (not_mem_empty _)
    | reflexive tele es =>
      dsimp only [fieldSet] at hget
      dsimp only [IhTyped]
      refine ⟨lamCtx M (S.ψ ls) q _ tele fun ρ' => pickMem (appList m ((S.idxVals M ls ρ' es).reverse ++
        [appList (fieldVal fs k) (readEnv tele.length ρ').reverse])),
        lamCtx_mem_piCtx M _ (fun ys hys => ?_) fun hq ys hys => ?_⟩
      · have hlen := FitsVals_length M _ hys
        have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
        refine pickMem_mem ?_
        simp only [readEnv_consList hlen]
        exact (mem_sep.mp hmem).2
      · have hlen := FitsVals_length M _ hys
        have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
        simp only [readEnv_consList hlen]
        exact hmo hq _ _ (mem_sep.mp hmem).1
  exact ⟨_, hmin j c hc fs hfitF ihs hihs⟩

end IndSpec

end Fragment
