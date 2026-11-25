# Writing OVERVIEW.md

`OVERVIEW.md` is the human-facing tour of ConLeche. It states current
facts for a reader who knows Lean but not this code. These rules apply
to every edit of it (and of the agent-editable parts of `README.md`).

## Shape

* One idea per paragraph. A paragraph that needs more than about 150
  words is two paragraphs, a list, or a table.
* Each section and subsection opens with one or two sentences that say
  what it covers and why the reader wants it.
* Enumerations are bullet lists; parallel facts (modules, flags,
  invariants per case) are tables or lists, never a run-on paragraph.
* Short subsections with descriptive headings beat a long section.
* Link to the code instead of retelling it: name the definition or
  theorem, link it, and say in a sentence what it means. Quote a
  statement (a fenced `lean` block) only where the reader needs its
  exact form; the quote gate keeps quotes in sync.

## Content

* Current facts only: no task numbers, no history ("formerly", "now",
  "since"), no removed mechanisms, not even in contrast.
* No measurements or performance numbers, unless the number is itself
  the documented fact (a default, a limit).
* Say what a reader needs to understand or use the system. Mechanism
  detail that only a maintainer of that code needs belongs in the doc
  comment of that code, or nowhere.
* Never call open questions about Lean's metatheory (subject
  reduction, confluence, Π-injectivity) "hard" or "open"; say what the
  proof does not need.

## Sentences

* Short sentences, active voice, simple tenses. Define a term at its
  first use. The `simple-english` skill is a good check.
* Words: "Π-type" or "function space", not "product"; "let-expression",
  not "local definition"; "a lambda-expression", not "a λ" in prose.
  Never "load-bearing" or "licenses" ("needed", "used", "justifies").
