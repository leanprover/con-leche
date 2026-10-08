module

public import ConLeche.Cached.InstallShape

public section

/-!
# The trusted↔P agreement floor (#172)

Whenever the cached driver (`ConLeche/Cached/ParsedC.lean`) at the
trusted config and at the verified config both **accept** a stream, the
two installed environments carry the same constants, in the same order,
with the same install skeletons — and in particular the same names and
the same count.

There is one driver, `checkDecls mode`, and the floor is the skeleton
spec proved **once, for every `mode : CheckMode`** (`checkDecls_skels`);
the agreement of two modes is its two instances glued by `Eq.trans`.
The certification-only work the trusted mode omits
(`mode.verifiedChecks`, group A, and `mode.certs`) is invisible to the
skeleton by construction — the spec forgets everything a core computes
— which is exactly why the proof is mode-generic without a case
split.

Nothing here reasons about the cores.  The floor's whole content is
that the fold is *the same fold* at every config; the inductive-block
clause installs constants under **environment-dependent guards**, so
the induction runs on the *install skeleton* — exactly the data those
guards read, and nothing a core computes — and the names corollary
falls out.  At `.axiomDecl` the push-or-not decision is a function of
the header name alone — the `sorryAx` record installs nothing, and
`stdAxiomOkF` is `false` off `propext`/`choice`, so every other
accepted axiom installs exactly one `.axiomInfo`.

Scope (DESIGN, "TASK #172 — BATCH B7"): accept verdicts only.
-/

namespace ConLeche.Cached

open ConLeche

variable {pins : List NatOpPinSet}

/-- Phase A's accepting run installs the stream's skeletons. -/
theorem installRun_skels (mode : CheckMode) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck}
    {q : Nat × FEnv × Array PendingCheck}
    (h : InstallRun mode pins ds p q) {sk : List InstallSkel} (hp : SkelIs p.2.1 sk) :
    SkelIs q.2.1 (ds.foldl (fun sk pd => declCSkels pd sk) sk) := by
  induction h generalizing sk with
  | nil p => exact hp
  | @cons pd ds p p₁ q hstep rest ih =>
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    rw [List.foldl_cons]
    exact ih (annotStepC_skels mode p.1 hp p.2.2 pd {} (fe₁, pend₁) s₁ hstepC)

/-- **The skeleton spec, at every mode.**  This is the floor's whole
content: one fold, one proof. -/
theorem checkDecls_skels {mode : CheckMode} {ds : Array Declaration}
    {env : Env} (h : checkDecls mode pins ds = .ok env) :
    envSkels env = streamSkels ds.toList := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked mode h
  obtain ⟨n, r⟩ := fc.1.run
  exact (installRun_skels mode r skelIs_empty).2

/-- **The floor, direct-parse route.**  Whenever the cached driver at
two modes — in particular the trusted (`.trusted`) and the verified
(`.verified`) mode the binary ships — both accept the same stream, the
two installed environments carry the same install skeletons.  Stated
for any two modes; the shipped pair is the instance
`.trusted` / `.verified` (`trusted_agrees_skels_shipped`). -/
theorem trusted_agrees_skels_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envSkels envN = envSkels envP :=
  (checkDecls_skels hN).trans (checkDecls_skels hP).symm

/-- The census's sentence: the accepted declaration **names** agree. -/
theorem trusted_agrees_names_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envN.consts.map ConstantInfo.name = envP.consts.map ConstantInfo.name := by
  have h := congrArg (List.map skelName) (trusted_agrees_skels_D hP hN)
  simpa [envSkels, List.map_map, Function.comp_def] using h

/-- … and so do the accepted declaration **counts**. -/
theorem trusted_agrees_count_D {μP μT : CheckMode} {ds : Array Declaration}
    {envP envN : Env}
    (hP : checkDecls μP pins ds = .ok envP)
    (hN : checkDecls μT pins ds = .ok envN) :
    envN.consts.length = envP.consts.length := by
  have h := congrArg List.length (trusted_agrees_skels_D hP hN)
  simpa [envSkels] using h

/-- The shipped pair, spelled out: `--trusted` and `--verified` agree on
the install skeletons whenever both accept. -/
theorem trusted_agrees_skels_shipped {ds : Array Declaration} {envP envT : Env}
    (hP : checkDecls .verified pins ds = .ok envP)
    (hT : checkDecls .trusted pins ds = .ok envT) :
    envSkels envT = envSkels envP :=
  trusted_agrees_skels_D hP hT

end ConLeche.Cached
