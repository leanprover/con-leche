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
* **Telescopes of sets**: fitting a telescope read from expressions
  (`TeleS_fits_toTeleS`) and its boundedness (`toTeleS_bounded_of`).

And one fact about the model of a block: **the motive is inhabited on
the family** (`IndSpec.motive_inhabited`) — by induction over the
family from the minors' typing, without uniqueness of witnesses, since
at a proposition the inductive hypotheses are inhabited truth values,
whatever their value.
-/

namespace Fragment
open SetLib IndLib

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
    {env : Env} {M' : Name → List Nat → V} {φ' : Name → Nat}
    (R : S.Reader (env := env) M φ M' φ') {nF k l o : Nat} {ihsE fs os ps : List V} {ρ : Nat → V}
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

/-! ## Telescopes of sets -/

/-- Fitting a telescope of sets built from expressions is fitting the
expressions' context (values outermost first vs. innermost first). -/
theorem TeleS_fits_toTeleS (M : Name → List Nat → V) (φ : Name → Nat) :
    ∀ (L : List Expr) (ρ : Nat → V) (ys : List V),
      (toTeleS M φ ρ L).Fits ys ↔ FitsVals M φ ρ L.reverse ys.reverse
  | [], ρ, [] => Iff.rfl
  | [], ρ, y :: ys => by
    rw [List.reverse_cons, List.reverse_nil]
    constructor
    · exact fun h => h.elim
    · intro h
      have := FitsVals_length M φ h
      simp at this
  | T :: L, ρ, [] => by
    rw [List.reverse_cons, List.reverse_nil]
    constructor
    · exact fun h => h.elim
    · intro h
      have := FitsVals_length M φ h
      simp at this
  | T :: L, ρ, y :: ys => by
    rw [List.reverse_cons, List.reverse_cons]
    show (y ∈ˢ interp M φ ρ T ∧ (toTeleS M φ (cons y ρ) L).Fits ys) ↔ _
    rw [TeleS_fits_toTeleS M φ L (cons y ρ) ys]
    by_cases hlen : ys.length = L.length
    · rw [FitsVals_append M φ (by simp [hlen]), FitsVals_cons, consList_cons, consList_nil]
      simp only [FitsVals_nil_nil, true_and]
    · constructor
      · rintro ⟨-, h⟩
        exact absurd (by simpa using FitsVals_length M φ h) hlen
      · intro h
        exact absurd (by simpa using FitsVals_length M φ h) hlen

/-- A telescope of sets is bounded when each expression's set is a
member of the universe under every fitting prefix (entry `t` of the
outermost-first `L` has the first `t` entries before it, which as an
innermost-first context are `L.reverse.drop (L.length - t)`). -/
theorem toTeleS_bounded_of (M : Name → List Nat → V) (φ : Name → Nat) (n : Nat) :
    ∀ (L : List Expr) (ρ : Nat → V),
      (∀ t T, L[t]? = some T → ∀ ys, FitsVals M φ ρ (L.reverse.drop (L.length - t)) ys →
        interp M φ (consList ys ρ) T ∈ˢ (univ n : V)) →
      TeleS.Bounded n (toTeleS M φ ρ L)
  | [], _, _ => trivial
  | T :: L, ρ, h => by
    refine ⟨?_, fun y hy => ?_⟩
    · have := h 0 T rfl [] (by rw [List.drop_eq_nil_iff.mpr (by simp)]; trivial)
      simpa using this
    · refine toTeleS_bounded_of M φ n L (cons y ρ) fun t T' hT' ys hys => ?_
      have ht : t < L.length := (List.getElem?_eq_some_iff.mp hT').1
      have hl := FitsVals_length M φ hys
      have := h (t + 1) T' (by simpa using hT') (ys ++ [y]) ?_
      · rwa [consList_append] at this
      · rw [List.reverse_cons, List.length_cons, Nat.add_sub_add_right,
          List.drop_append_of_le_length (by simp only [List.length_reverse]; omega),
          FitsVals_append M φ (by rw [hl])]
        exact ⟨⟨trivial, hy⟩, hys⟩

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
  unfold pickMem; rw [dif_pos h]; exact Classical.choose_spec h

namespace IndSpec

variable (S : IndSpec) (M : Name → List Nat → V) (ls : List Nat)

/-- A member of a fibre has every property of the members it stands
for: above a proposition it is itself a member; at a proposition it is
the point, which is what every member stands for. -/
theorem memb_of_fibre {ps is : List V} {v : V} {Q : V → Prop}
    (hv : v ∈ˢ fibreR (S.z ls) (S.bound M ls ps is) fun x => S.Mem M ls ps is x ∧ Q (S.memb ls x)) :
    Q v := by
  unfold memb at hv
  cases hz : S.z ls
  · rw [hz] at hv
    simpa using (mem_fibreR_false.mp hv).2.2
  · rw [hz] at hv
    obtain ⟨rfl, y, -, hQ⟩ := mem_fibreR_true.mp hv
    simpa using hQ

/-- The indices of a member of the family fit the index context, once
every constructor's index expressions fit at fitting fields. -/
theorem idx_fits_of_mem_Fam {ps : List V}
    (hidx : ∀ (j : Nat) (c : CtorSpec), S.ctors[j]? = some c → ∀ fs,
      S.FitsFields M ls (S.bound M ls) (S.Mem M ls) ps c.fields fs →
      FitsVals M (S.ψ ls) (envP ps) S.indices (S.idxVals M ls (consList fs (envP ps)) c.idx))
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) :
    FitsVals M (S.ψ ls) (envP ps) S.indices is := by
  refine S.memb_of_fibre M ls (Q := fun _ => FitsVals M (S.ψ ls) (envP ps) S.indices is)
    (fibreR_mono (fun x hx => ⟨hx, ?_⟩) _ ht)
  obtain ⟨j, c, fs, hc, hfit, his, -⟩ := Lfp.unfold (S.stepT_mono M ls (S.bound M ls)) hx
  dsimp only at hfit his
  rw [his]
  exact hidx j c hc fs hfit

/-- **The motive is inhabited on the family** (without uniqueness of
witnesses): by induction over the family, from the minors' typing — at
a proposition the inductive hypotheses are inhabited truth values, so
their values need not be the recursor's. -/
theorem motive_inhabited (q : Bool) {ps : List V} (m : V) (mins : List V)
    (hmin : ∀ j c, S.ctors[j]? = some c → S.MinorOk M ls q ps m mins j c)
    (hmo : q = true → ∀ is t, t ∈ˢ S.Fam M ls ps is → appList m (is.reverse ++ [t]) ∈ˢ (univ 0 : V))
    {is : List V} {t : V} (ht : t ∈ˢ S.Fam M ls ps is) : ∃ v, v ∈ˢ appList m (is.reverse ++ [t]) := by
  suffices key : ∀ ps' is x, S.Mem M ls ps' is x → ps' = ps →
      ∃ v, v ∈ˢ appList m (is.reverse ++ [S.memb ls x]) by
    refine S.memb_of_fibre M ls (ps := ps) (is := is)
      (Q := fun t => ∃ v, v ∈ˢ appList m (is.reverse ++ [t])) ?_
    exact fibreR_mono (fun x hx => ⟨hx, key ps is x hx rfl⟩) _ ht
  intro ps' is x hm
  refine S.Mem_ind M ls
    (P := fun ps' is x => ps' = ps → ∃ v, v ∈ˢ appList m (is.reverse ++ [S.memb ls x])) ?_ hm
  intro ps' is x hs hps
  subst hps
  obtain ⟨j, c, fs, hc, hfit, his, hx⟩ := hs
  have hfitM := S.FitsFields_mono M ls (fun _ _ _ h => h.1) ps' hfit
  subst his hx
  have hmemb : S.memb ls (tag j (tuple fs.reverse)) = S.ctorVal ls j fs := rfl
  rw [hmemb]
  have hget' : ∀ {k : Nat} {f : Field}, c.fields[c.fields.length - 1 - k]? = some f →
      k < c.fields.length → fieldVal fs k ∈ˢ S.fieldSet M ls (S.bound M ls)
        (fun a is x => S.Mem M ls a is x ∧ (a = ps' →
          ∃ v, v ∈ˢ appList m (is.reverse ++ [S.memb ls x]))) ps' (earlier fs k) f :=
    fun hf hk => S.FitsFields_get M ls hfit hf hk
  -- the inductive hypotheses: one inhabitant of each hypothesis' type
  obtain ⟨ihs, hihs⟩ : ∃ ihs, ListRel (S.IhTyped M ls q ps' m fs) c.recFields ihs := by
    refine ListRel.exists fun kf hkf => ?_
    obtain ⟨hf, hk, hrec⟩ := mem_recFields hkf
    have hget := hget' hf hk
    obtain ⟨k, f⟩ := kf
    cases f with
    | ordinary _ => simp [Field.isRec] at hrec
    | recursive es =>
      dsimp only [fieldSet] at hget
      dsimp only [IhTyped]
      exact S.memb_of_fibre M ls (Q := fun t => ∃ v, v ∈ˢ appList m (_ ++ [t]))
        (fibreR_mono (fun x hx => ⟨hx.1, hx.2 rfl⟩) _ hget)
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
        exact S.memb_of_fibre M ls (Q := fun t => ∃ v, v ∈ˢ appList m (_ ++ [t]))
          (fibreR_mono (fun x hx => ⟨hx.1, hx.2 rfl⟩) _ hmem)
      · have hlen := FitsVals_length M _ hys
        have hmem := appList_mem_of_piCtx M (S.ψ ls) hget hys
        simp only [readEnv_consList hlen]
        exact hmo hq _ _ (fibreR_mono (fun x hx => hx.1) _ hmem)
  exact ⟨_, hmin j c hc fs hfitM ihs hihs⟩

end IndSpec

end Fragment
