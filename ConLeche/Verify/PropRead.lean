module

public import ConLeche.Kernel.PropRead
public import ConLeche.Verify.Shift
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import ConLeche.Kernel.PropWhen
import all ConLeche.Kernel.PropWhen

public section

/-!
# The head-symbol prop-ness readers under the verification walks
(task #168)

The readers (`ConLeche/Kernel/PropRead.lean`) look only at head symbols,
arities and binder data, none of which a free-variable shift touches —
so every reader commutes with `shiftFrom`, which is all the
deep-embedding lemma family (`ConLeche/Verify/Deep.lean`) needs of them.

The β clause (task #301) recurses into a λ's body, so the laws are
inductions over `typePWAt` rather than case splits on the head; the
inversions come in two grades.  The **general** one is `typePWAt`'s own
equations; the **licence's** one (`typePWAt_some_inv_noBeta`, and the
`typeSortPW`/`headProofPW`/`proofPW` inversions built on it) is stated
at `beta := false`, where the reader answers only at the four head
shapes the squash-regime licence has a model theorem for.
-/

namespace ConLeche

open Expr

theorem Expr.numArgs_shiftFrom {p : Nat} :
    ∀ (e : Expr), (shiftFrom p e).numArgs = e.numArgs := by
  intro e
  induction e <;> simp_all [shiftFrom, numArgs]
  case fvar => split <;> rfl

theorem residualPW_peelNeverPis_shiftFrom {p : Nat} :
    ∀ (k : Nat) (e : Expr),
      residualPW ((shiftFrom p e).peelNeverPis k) =
        residualPW (e.peelNeverPis k) := by
  intro k
  induction k with
  | zero =>
    intro e
    cases e <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
  | succ k ih =>
    intro e
    cases e <;> try rfl
    case fvar => simp only [shiftFrom]; split <;> rfl
    case forallE ty b m =>
      simp only [shiftFrom, peelNeverPis]
      split
      · exact ih b
      · rfl

/-- **The reader commutes with a shift**, at every arity and either
grade: the shift copies binder data, keeps head shapes and only bumps
`fvar` indices, and the one place a declared type is read is through
`residualPW ∘ peelNeverPis`. -/
theorem typePWAt_shiftFrom (find? : Name → Option ConstantInfo) (beta : Bool)
    {p : Nat} :
    ∀ (e : Expr) (n : Nat),
      typePWAt find? beta (shiftFrom p e) n = typePWAt find? beta e n := by
  intro e
  induction e with
  | fvar idx ty _ =>
    intro n
    simp only [shiftFrom]
    split <;> simp only [typePWAt, residualPW_peelNeverPis_shiftFrom]
  | app f a ihf _ => intro n; exact ihf (n + 1)
  | lam ty b m _ ihb =>
    intro n
    cases n with
    | zero => rfl
    | succ n => show (if beta then _ else _) = (if beta then _ else _); rw [ihb n]
  | _ => intro n; cases n <;> rfl

theorem headTypePW_shiftFrom (find? : Name → Option ConstantInfo)
    (beta : Bool) {p : Nat} (h : Expr) (n : Nat) :
    headTypePW find? beta (shiftFrom p h) n = headTypePW find? beta h n :=
  typePWAt_shiftFrom find? beta h n

theorem typeSortPW_shiftFrom (find? : Name → Option ConstantInfo)
    (beta : Bool) {p : Nat} (T : Expr) :
    typeSortPW find? beta (shiftFrom p T) = typeSortPW find? beta T :=
  typePWAt_shiftFrom find? beta T 0

theorem headProofPW_shiftFrom (find? : Name → Option ConstantInfo)
    (beta : Bool) {p : Nat} (h : Expr) :
    headProofPW find? beta (shiftFrom p h) = headProofPW find? beta h := by
  cases h <;> try rfl
  case fvar =>
    simp only [shiftFrom]
    split <;> simp only [headProofPW, typeSortPW_shiftFrom]

/-- `proofPW` through the total `lamPw` reader (the shape the walks
rewrite). -/
theorem proofPW_eq (find? : Name → Option ConstantInfo) (beta : Bool) (a : Expr) :
    proofPW find? beta a =
      match a.lamPw with
      | some pw => some pw
      | none => headProofPW find? beta a.getAppFn := by
  cases a <;> rfl

theorem proofPW_shiftFrom (find? : Name → Option ConstantInfo) (beta : Bool)
    {p : Nat} (a : Expr) :
    proofPW find? beta (shiftFrom p a) = proofPW find? beta a := by
  rw [proofPW_eq, proofPW_eq, lamPw_shiftFrom, getAppFn_shiftFrom,
    headProofPW_shiftFrom]

theorem notProofFast_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    notProofFast find? (shiftFrom p a) = notProofFast find? a := by
  simp only [notProofFast, proofPW_shiftFrom]

theorem isProofFast_shiftFrom (find? : Name → Option ConstantInfo) {p : Nat}
    (a : Expr) :
    isProofFast find? (shiftFrom p a) = isProofFast find? a := by
  simp only [isProofFast, proofPW_shiftFrom]

/-! ## Inversions — what a reader's answer says about the term

The "yes" arm's licence (`ConLeche/Model/Steps/IrrelFast.lean`) consumes
the readers through these: each `some` verdict is one of finitely many
head shapes with the datum spelled out.  They are stated at the
licence's grade (`beta := false`), where a λ head is exactly the shape
the reader declines at. -/

theorem Expr.numArgs_eq_length : ∀ (e : Expr), e.numArgs = e.getAppArgs.length := by
  intro e
  induction e <;> simp_all [numArgs, getAppArgs]

theorem Expr.lamPw_some_inv {a : Expr} {pw : PropWhen} (h : a.lamPw = some pw) :
    ∃ ty bd mb, a = .lam ty bd mb ∧ pw = mb.pw := by
  cases a <;> simp only [lamPw, reduceCtorEq, Option.some.injEq] at h
  exact ⟨_, _, _, rfl, h.symm⟩

theorem Expr.peelNeverPis_zero_inv {T R : Expr} (h : T.peelNeverPis 0 = some R) :
    T = R := Option.some.inj h

theorem Expr.peelNeverPis_succ_inv {k : Nat} {T R : Expr}
    (h : T.peelNeverPis (k + 1) = some R) :
    ∃ ty b m, T = .forallE ty b m ∧ m.pw.isNever = true ∧
      b.peelNeverPis k = some R := by
  cases T <;> simp only [peelNeverPis, reduceCtorEq] at h
  case forallE ty b m =>
    split at h
    · exact ⟨ty, b, m, rfl, ‹_›, h⟩
    · exact nomatch h

/-- Peeling commutes with term instantiation at any offset: the
binders and their data are untouched, a `Sort` residual stays. -/
theorem Expr.peelNeverPis_instantiate1 : ∀ (k : Nat) {T : Expr} {u : Level}
    (v : Expr) (off : Nat), T.peelNeverPis k = some (.sort u) →
    (T.instantiate1 v off).peelNeverPis k = some (.sort u) := by
  intro k
  induction k with
  | zero =>
    intro T u v off h
    obtain rfl := Expr.peelNeverPis_zero_inv h
    rfl
  | succ k ih =>
    intro T u v off h
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv h
    simp only [instantiate1, peelNeverPis, hnev, if_true]
    exact ih v (off + 1) hb

/-- Peeling commutes with level instantiation: a `.never` datum
instantiates to `.never`, a `Sort` residual to its instance. -/
theorem Expr.peelNeverPis_instantiateLevelParams : ∀ (k : Nat) {T : Expr}
    {u : Level} (ks : List Name) (vs : List Level),
    T.peelNeverPis k = some (.sort u) →
    (T.instantiateLevelParams ks vs).peelNeverPis k =
      some (.sort (Level.subst ks vs u)) := by
  intro k
  induction k with
  | zero =>
    intro T u ks vs h
    obtain rfl := Expr.peelNeverPis_zero_inv h
    rfl
  | succ k ih =>
    intro T u ks vs h
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv h
    have hnev' : (Level.substPW ks vs m.pw).isNever = true := by
      cases hpw : m.pw with
      | never => rfl
      | ifAllZero ps => rw [hpw] at hnev; simp at hnev
    show (if (Level.substPW ks vs m.pw).isNever then
        (b.instantiateLevelParams ks vs).peelNeverPis k else none) = _
    rw [hnev']
    exact ih ks vs hb

/-- A successful peel is a successful `stripPis` with the same
residual. -/
theorem Expr.stripPis_of_peelNeverPis : ∀ (k : Nat) {T R : Expr},
    T.peelNeverPis k = some R → ∃ bs, T.stripPis k = some (bs, R) := by
  intro k
  induction k with
  | zero =>
    intro T R h
    obtain rfl := Expr.peelNeverPis_zero_inv h
    exact ⟨[], rfl⟩
  | succ k ih =>
    intro T R h
    obtain ⟨ty, b, m, rfl, -, hb⟩ := Expr.peelNeverPis_succ_inv h
    obtain ⟨bs, hbs⟩ := ih hb
    exact ⟨(ty, m) :: bs, by simp [stripPis, hbs]⟩

theorem Expr.hasFvar_of_getAppFn_fvar : ∀ {e : Expr} {idx : Nat}
    {ty : Expr}, e.getAppFn = .fvar idx ty → e.hasFvar = true := by
  intro e
  induction e <;> intro idx ty h <;> simp_all [getAppFn, hasFvar]

theorem residualPW_some_inv {o : Option Expr} {pw : PropWhen}
    (h : residualPW o = some pw) :
    ∃ u, o = some (.sort u) ∧ pw = Level.zeronessOf u := by
  match o, h with
  | some (.sort u), h => exact ⟨u, rfl, (Option.some.inj h).symm⟩
  | none, h => exact nomatch h
  | some (.bvar _), h | some (.fvar _ _), h | some (.const _ _), h
  | some (.app _ _), h | some (.lam _ _ _), h | some (.forallE _ _ _), h
  | some (.letE _ _ _), h | some (.lit _), h | some (.proj _ _ _), h =>
    exact nomatch h

/-! ## The spine and the equations -/

/-- **The reader peels the spine into the arity**: reading a term at
`n` further arguments is reading its head at all of them. -/
theorem typePWAt_spine (find? : Name → Option ConstantInfo) (beta : Bool) :
    ∀ (e : Expr) (n : Nat),
      typePWAt find? beta e n = typePWAt find? beta e.getAppFn (e.numArgs + n) := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro n
    show typePWAt find? beta f (n + 1) = _
    rw [ihf (n + 1)]
    show _ = typePWAt find? beta f.getAppFn (f.numArgs + 1 + n)
    rw [show f.numArgs + (n + 1) = f.numArgs + 1 + n from by omega]
  | _ => intro n; simp only [Expr.getAppFn, Expr.numArgs, Nat.zero_add]

/-- `typeSortPW` through the two special cases (the shape the
inversion rewrites). -/
theorem typeSortPW_eq (find? : Name → Option ConstantInfo) (beta : Bool) (T : Expr) :
    typeSortPW find? beta T =
      match T with
      | .forallE _ _ m => some m.pw
      | .sort _ => some .never
      | T => headTypePW find? beta T.getAppFn T.getAppArgs.length := by
  have hz : ∀ e : Expr, typePWAt find? beta e 0
      = headTypePW find? beta e.getAppFn e.getAppArgs.length := by
    intro e
    rw [typePWAt_spine, Nat.add_zero, headTypePW, Expr.numArgs_eq_length]
  cases T <;> first
    | rfl
    | (show typePWAt find? beta _ 0 = _; rw [hz])

/-- **The licence's inversion**: at `beta := false` the reader answers
only at a constant head, an fvar head, an unapplied `∀` (its own
datum) or an unapplied `Sort` (`.never`) — the four shapes
`prf_of_isProofFast` has a model theorem for.  A λ head is where it
declines, which is what keeps the licence off β redexes. -/
theorem typePWAt_some_inv_noBeta (find? : Name → Option ConstantInfo) :
    ∀ (e : Expr) (n : Nat) (pw : PropWhen), typePWAt find? false e n = some pw →
    (∃ I us ci u, e.getAppFn = .const I us ∧ find? I = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ci.toConstantVal.type.peelNeverPis (e.numArgs + n) = some (.sort u) ∧
        pw = Level.substPW ci.toConstantVal.levelParams us (Level.zeronessOf u)) ∨
    (∃ idx ty u, e.getAppFn = .fvar idx ty ∧
        ty.peelNeverPis (e.numArgs + n) = some (.sort u) ∧ pw = Level.zeronessOf u) ∨
    (∃ A B mb, e = .forallE A B mb ∧ pw = mb.pw) ∨
    pw = .never := by
  intro e
  induction e with
  | const I us =>
    intro n pw h
    simp only [typePWAt] at h
    cases hf : find? I with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next hnt =>
        split at h
        · next hlen =>
          cases hr : residualPW (ci.toConstantVal.type.peelNeverPis n) with
          | none => rw [hr] at h; exact nomatch h
          | some pw0 =>
            rw [hr] at h
            obtain ⟨u, hu, rfl⟩ := residualPW_some_inv hr
            refine Or.inl ⟨I, us, ci, u, rfl, hf, Bool.eq_false_iff.mpr hnt, hlen,
              ?_, (Option.some.inj h).symm⟩
            show ci.toConstantVal.type.peelNeverPis (0 + n) = some (.sort u)
            rw [Nat.zero_add]; exact hu
        · exact nomatch h
  | fvar idx ty _ =>
    intro n pw h
    obtain ⟨u, hu, rfl⟩ := residualPW_some_inv h
    refine Or.inr (Or.inl ⟨idx, ty, u, rfl, ?_, rfl⟩)
    show ty.peelNeverPis (0 + n) = some (.sort u)
    rw [Nat.zero_add]; exact hu
  | app f a ihf _ =>
    intro n pw h
    have h' : typePWAt find? false f (n + 1) = some pw := h
    rcases ihf (n + 1) pw h' with
      ⟨I, us, ci, u, hfn, hf, hnt, hlen, hpeel, rfl⟩ |
      ⟨idx, ty, u, hfn, hpeel, rfl⟩ | ⟨A, B, mb, rfl, rfl⟩ | rfl
    · refine Or.inl ⟨I, us, ci, u, hfn, hf, hnt, hlen, ?_, rfl⟩
      rw [show (Expr.app f a).numArgs + n = f.numArgs + (n + 1) from by
        show f.numArgs + 1 + n = _; omega]
      exact hpeel
    · refine Or.inr (Or.inl ⟨idx, ty, u, hfn, ?_, rfl⟩)
      rw [show (Expr.app f a).numArgs + n = f.numArgs + (n + 1) from by
        show f.numArgs + 1 + n = _; omega]
      exact hpeel
    · exact absurd h' (by simp [typePWAt])
    · exact Or.inr (Or.inr (Or.inr rfl))
  | forallE ty b m _ _ =>
    intro n pw h
    cases n with
    | zero => exact Or.inr (Or.inr (Or.inl ⟨ty, b, m, rfl, (Option.some.inj h).symm⟩))
    | succ n => exact nomatch h
  | sort u =>
    intro n pw h
    cases n with
    | zero => exact Or.inr (Or.inr (Or.inr (Option.some.inj h).symm))
    | succ n => exact nomatch h
  | lam ty b m _ _ =>
    intro n pw h
    cases n with
    | zero => exact nomatch h
    | succ n => exact nomatch h
  | _ => intro n pw h; cases n <;> exact nomatch h

theorem headTypePW_some_inv (find? : Name → Option ConstantInfo) {hd : Expr}
    {k : Nat} {pw : PropWhen} (h : headTypePW find? false hd k = some pw) :
    (∃ I us ci u, hd.getAppFn = .const I us ∧ find? I = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ci.toConstantVal.type.peelNeverPis (hd.numArgs + k) = some (.sort u) ∧
        pw = Level.substPW ci.toConstantVal.levelParams us (Level.zeronessOf u)) ∨
    (∃ idx ty u, hd.getAppFn = .fvar idx ty ∧
        ty.peelNeverPis (hd.numArgs + k) = some (.sort u) ∧ pw = Level.zeronessOf u) ∨
    (∃ A B mb, hd = .forallE A B mb ∧ pw = mb.pw) ∨
    pw = .never :=
  typePWAt_some_inv_noBeta find? hd k pw h

theorem typeSortPW_some_inv (find? : Name → Option ConstantInfo) {T : Expr}
    {pw : PropWhen} (h : typeSortPW find? false T = some pw) :
    (∃ A B mb, T = .forallE A B mb ∧ pw = mb.pw) ∨
    pw = .never ∨
    (∃ I us ci u, T.getAppFn = .const I us ∧ find? I = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ci.toConstantVal.type.peelNeverPis T.getAppArgs.length =
          some (.sort u) ∧
        pw = Level.substPW ci.toConstantVal.levelParams us
          (Level.zeronessOf u)) ∨
    (∃ idx ty u, T.getAppFn = .fvar idx ty ∧
        ty.peelNeverPis T.getAppArgs.length = some (.sort u) ∧
        pw = Level.zeronessOf u) := by
  have hlen : T.numArgs + 0 = T.getAppArgs.length := by
    rw [Nat.add_zero, Expr.numArgs_eq_length]
  rcases typePWAt_some_inv_noBeta find? T 0 pw h with
    ⟨I, us, ci, u, hfn, hf, hnt, hlenl, hpeel, rfl⟩ |
    ⟨idx, ty, u, hfn, hpeel, rfl⟩ | ⟨A, B, mb, rfl, rfl⟩ | rfl
  · rw [hlen] at hpeel
    exact Or.inr (Or.inr (Or.inl ⟨I, us, ci, u, hfn, hf, hnt, hlenl, hpeel, rfl⟩))
  · rw [hlen] at hpeel
    exact Or.inr (Or.inr (Or.inr ⟨idx, ty, u, hfn, hpeel, rfl⟩))
  · exact Or.inl ⟨A, B, mb, rfl, rfl⟩
  · exact Or.inr (Or.inl rfl)

theorem headProofPW_some_inv (find? : Name → Option ConstantInfo) {hd : Expr}
    {pw : PropWhen} (h : headProofPW find? false hd = some pw) :
    (∃ c us ci, hd = .const c us ∧ find? c = some ci ∧
        ci.isTowerEntry = false ∧
        us.length = ci.toConstantVal.levelParams.length ∧
        ∃ pw0, typeSortPW find? false ci.toConstantVal.type = some pw0 ∧
          pw = Level.substPW ci.toConstantVal.levelParams us pw0) ∨
    (∃ idx ty, hd = .fvar idx ty ∧ typeSortPW find? false ty = some pw) ∨
    pw = .never := by
  cases hd <;> simp only [headProofPW, reduceCtorEq, Option.some.injEq] at h
  case const c us =>
    cases hf : find? c with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      dsimp only at h
      split at h
      · exact nomatch h
      · next hnt =>
        split at h
        · next hlen =>
          cases hts : typeSortPW find? false ci.toConstantVal.type with
          | none => rw [hts] at h; simp at h
          | some pw0 =>
            rw [hts] at h
            exact Or.inl ⟨c, us, ci, rfl, hf, Bool.eq_false_iff.mpr hnt, hlen,
              pw0, hts, (Option.some.inj h).symm⟩
        · exact nomatch h
  case fvar idx ty => exact Or.inr (Or.inl ⟨idx, ty, rfl, h⟩)
  case lam ty b m => exact nomatch h
  all_goals exact Or.inr (Or.inr h.symm)

theorem proofPW_some_inv (find? : Name → Option ConstantInfo) {a : Expr}
    {pw : PropWhen} (h : proofPW find? false a = some pw) :
    (∃ ty bd mb, a = .lam ty bd mb ∧ pw = mb.pw) ∨
    (a.lamPw = none ∧ headProofPW find? false a.getAppFn = some pw) := by
  rw [proofPW_eq] at h
  cases hl : a.lamPw with
  | some p =>
    rw [hl] at h
    obtain ⟨ty, bd, mb, rfl, rfl⟩ := Expr.lamPw_some_inv hl
    exact Or.inl ⟨ty, bd, mb, rfl, (Option.some.inj h).symm⟩
  | none => rw [hl] at h; exact Or.inr ⟨rfl, h⟩

theorem isProofFast_inv (find? : Name → Option ConstantInfo) {a : Expr}
    (h : isProofFast find? a = true) :
    ∃ pw, proofPW find? false a = some pw ∧ pw.isProp = true := by
  unfold isProofFast at h
  cases hp : proofPW find? false a with
  | none => rw [hp] at h; exact nomatch h
  | some pw => rw [hp] at h; exact ⟨pw, rfl, h⟩

@[simp] theorem PropWhen.isProp_never : PropWhen.isProp .never = false := by rfl

@[simp] theorem Level.substPW_never (ks : List Name) (vs : List Level) :
    Level.substPW ks vs .never = .never := by rfl

end ConLeche
