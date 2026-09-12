module

public import ConLeche.Frontend.Prelude
public import ConLeche.Cached.Installed

@[expose] public section

/-!
# What the binary accepts, as pure content — and what a file that
proves `False` looks like

The main theorem and its corollaries (`ConLeche/Challenge.lean`) are
about `checkDecls`, the fold over the PARSED stream.  This module names
the two things a reader needs to carry a corollary from the parsed
stream to the FILE the binary was handed:

* `pipelineAccepts file` — the driver's accept path (`checkMain` in
  `Main.lean`), stripped of its IO: the built-in prelude parses, the
  file's content parses with the in-process modeller on (the driver's
  defaults — the only switches are debug environment variables), and
  the verified fold accepts the parsed list prepared with the prelude
  (`preparePrelude`, `ConLeche/Frontend/Prepare.lean`).  The driver
  prints its success line from exactly these three facts and from
  nothing else; the one thing it does differently is that it reads the
  file in chunks, which `parseChunks_ok_parseExportD`
  (`ConLeche/Verify/Frontend/Chunks.lean`) shows makes no difference.
* `hasProofOfFalse file` — the file declares a theorem of type `False`,
  said as a string template in the exporter's own line shapes: a name
  entry for `False`, an expression entry for the constant `False`, a
  name entry for the theorem's own name, and the theorem record whose
  `type` is that expression.  The parts before, between and after the
  four lines are arbitrary strings — anything at all, well-formed or
  not — and the indices `i`, `j`, `k`, `v` and the theorem's name are
  arbitrary too.

The statement `no_False_declaration` (`ConLeche/Challenge.lean`) then
reads: a file that matches the template is never accepted.
-/

namespace ConLeche

open ConLeche.Cached (checkDecls)

/-- **The file declares a theorem of type `False`.**  Four lines of the
lean4export format, in this order, each on a line of its own, with
anything at all before, between and after them:

* `{"in":i,"str":{"pre":0,"str":"False"}}` — name entry `i` is `False`;
* `{"ie":j,"const":{"name":i,"us":[]}}` — expression entry `j` is the
  constant `False`;
* `{"in":k,"str":{"pre":0,"str":"<name>"}}` — name entry `k` is the
  theorem's own name, any name;
* `{"thm":{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}}` —
  a theorem named `k` whose type is `j` and whose proof is expression
  entry `v`, whatever that is.

The five string parts are unconstrained: a part may hold any number of
further lines, including malformed ones — then the file does not parse
and is not accepted for that reason.  The only thing the template fixes
is that the four lines appear, whole, in this order. -/
def hasProofOfFalse (file : String) : Prop :=
  ∃ (before between₁ between₂ between₃ after : String) (i j k v : Nat) (name : String),
    file =
      before ++ "\n" ++
      s!"\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}" ++ "\n" ++
      between₁ ++ "\n" ++
      s!"\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}" ++ "\n" ++
      between₂ ++ "\n" ++
      s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++ "\n" ++
      between₃ ++ "\n" ++
      s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}" ++ "\n" ++
      after

/-- **The binary accepts the file's content.**  The pure content of
`checkMain`'s accept path (`Main.lean`): the built-in prelude parses to
`pre`; the file parses, with the in-process modeller on
(`inModel := true`, the driver's default; `census := false`, the
driver's default — the census switch stops before the fold and never
accepts); and the verified fold `checkDecls` accepts the parsed
declarations prepared with the prelude — `preparePrelude` puts the
prelude's records first and hoists the ground of the pinned `Nat`
operations, and the parsed records are all still there.  The driver
prints its success line from these three facts and from nothing else. -/
def pipelineAccepts (file : String) : Prop :=
  ∃ (pre : Frontend.PreludeIx) (r : Frontend.ParseResultD) (env : Env),
    Frontend.builtinPreludeE = .ok pre ∧
    Frontend.parseExportD file (inModel := true) (census := false) = .ok r ∧
    checkDecls .verified (Frontend.preparePrelude pre r.decls.toList) = .ok env

/-- **The binary accepts the chunks it read.**  `pipelineAccepts` with
the parse the binary actually runs: `parseChunks`, the streaming
reader's loop over the chunks the file handle hands out
(`parseExportHandleD` is this loop with the reads interleaved). -/
def streamingAccepts (chunks : List ByteArray) : Prop :=
  ∃ (pre : Frontend.PreludeIx) (r : Frontend.ParseResultD) (env : Env),
    Frontend.builtinPreludeE = .ok pre ∧
    Frontend.parseChunks (inModel := true) (census := false) chunks = .ok r ∧
    checkDecls .verified (Frontend.preparePrelude pre r.decls.toList) = .ok env

end ConLeche
