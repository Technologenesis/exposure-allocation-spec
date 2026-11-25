# Working in a lean-spec-viewer project

You are working in (or creating) a Lean 4 repo whose generated spec page is the
**primary interface between the developer and this codebase**. The developer watches
the page, not the files: they see the contract's English, the Lean beneath it, and
proof badges that flip from `unproved` to `proved` as you make progress. Your job is
to keep that page true. Everything on it is either prose you wrote next to the code
or a fact the harness observed from the program — there is no third channel.

Three rules dominate everything else:

1. **Spec first, then implementation.** Do not write code until you are writing to
   an approved spec. All work starts in `Spec/`: when asked for new behavior, write
   or change the clauses, show the developer on the page, and get their explicit
   approval before touching `Impl/` or `Proof/`. In harness sessions this is
   enforced: the session has a workflow phase ("spec" or "impl"), the writable file
   set follows it, and only the developer can switch phases, from the page. A spec
   change re-opens the gate for what it touches.
2. **The English is the contract; the Lean is how the code is checked against it.**
   When they disagree, change the English first, then the Lean, and keep them saying
   the same thing.
3. **Never write status.** Build state, proof state, clause counts — all of it is
   derived. Prose like "all clauses proved" or "TODO: unproven" in a comment is a lie
   waiting to happen and duplicates the badges.

## Project layout

A fresh project looks like this:

```
myspec/
  lakefile.toml        -- three libs; warningAsError on
  lean-toolchain       -- pinned, e.g. leanprover/lean4:v4.29.1
  Spec.lean            -- the ROOT FILE: imports + package summary
  Spec/                -- the contract: what the page shows
    Inputs.lean        -- (file split is yours; classification is automatic)
    Vocabulary.lean
    Clauses.lean
    Contract.lean
  Impl/                -- the implementation under specification
    ...
  Proof/               -- one theorem per clause + the assembled instance
    ...
```

`lakefile.toml` essentials:

```toml
name = "myspec"
defaultTargets = ["Spec", "Impl", "Proof"]

[leanOptions]
warningAsError = true   # REQUIRED by the harness's "proved" semantics: a passing
                        # build must mean sorry-free, and sorry is a warning
maxHeartbeats = 50000   # optional tripwire: keep proofs cheap and linear

[[lean_lib]]
name = "Spec"
[[lean_lib]]
name = "Impl"
[[lean_lib]]
name = "Proof"

[[require]]            # the default scaffold adds this: CSLib, and through it
name = "cslib"         # Mathlib — reuse their definitions, lemmas, and tactics
scope = "leanprover"   # rather than reinventing them
rev = "main"
```

(The scaffolder runs `lake update cslib`; dependency changes afterwards are the
developer's.) Dependency direction is one-way: `Impl` imports `Spec`, `Proof` imports both,
`Spec` imports nothing of theirs. The spec must make sense with the other two
directories deleted.

**The root file** is how the viewer finds everything: the one top-level `.lean`
whose module doc opens with `# Title`. It holds the imports of the spec's section
files (their order is the item order within each page section) and the package
summary — the page title, a one-or-two-sentence description, and optionally
`@output <filename>` (default `spec.html`):

```lean
import Spec.Inputs
import Spec.Vocabulary
import Spec.Clauses
import Spec.Contract

/-!
# Widget pricing

Given a widget and a book of quotes, decide the price to publish. This is the
contract of `priceWidget` in widget-service.
-/
```

## How the page is assembled

The skeleton is entirely the tool's; comments never create structure. Declarations
in the root file's imports are classified by shape:

| Slot | What lands there | Rendered |
|---|---|---|
| Vocabulary › Types | `structure` / `inductive` | name heading (code-styled), prose, code |
| Vocabulary › Propositions | Prop-valued defs the contract does **not** name | same |
| Vocabulary › Definitions | any other untagged declaration | same |
| Constants | parameterless value defs (`def x : Int := 5`) | one table: Name, Value, Notes |
| Contract | Type-valued defs | the contract first, then its Clauses subsection |
| Contract › Clauses | Prop-valued defs the contract **names** | plain-title heading + proof badge, prose, code |

**A clause is not a tag — it is contract membership.** The contract is a Type-valued
definition (typically a subtype `{ out // C₁ ∧ C₂ ∧ … }` over the implementation's
signature); every Prop it names becomes a clause, gets a proof badge, and counts
toward the header's "N of M clauses proved". To add an obligation, define the Prop
and conjoin it into the contract: it appears on the page as `unproved` immediately.
Remove it from the contract and it reverts to an ordinary proposition.

Anchors, for navigation and links: sections `vocabulary`, `constants`, `contract`;
subsections `types`, `propositions`, `definitions`, `clauses`; every declaration
`def-<LeanName>`. Backtick any defined name in prose or code and the page links it
to its definition automatically.

## Derived status — what makes "proved"

The header badges and per-clause badges are observed, never written:

- **build passing / failing** — `lake build` under the repo's own flags. With
  `warningAsError` on, a passing build is also machine-checked sorry-free.
- **A clause is `proved`** when (a) a **sorry-free declaration outside the spec's
  pages** — i.e. in `Proof/` or `Impl/` — **names it** (the coverage scan is
  textual: state one theorem per clause, named for it, e.g.
  `theorem decide_riskOff : ∀ i, RiskOffIsImmediate i (decide i) := …`), and
  (b) the build passes. A declaration containing `sorry`/`admit` is no proof;
  such a clause is simply `unproved`. `unverified` means the build was skipped.
- The server rebuilds the page on every save: instantly with `verifying…` badges,
  then again when its background `lake build` settles them.

## Comment rules

A comment is an annotation of a definite code object — a doc comment on the
declaration it documents. One exception: a file may have a **top-level summary**,
a single `/-! ... -/` module doc before its first declaration, rendered at the head
of the section that declaration lands in. A module doc anywhere else is an error.

- **Headings** may appear only in summaries, strictly below the auto-assembled
  header above them: under a level-3 subsection that means `####` or deeper; the
  package summary (under the level-1 title) allows `##` or deeper. A heading in a
  declaration's doc comment is an error.
- **Tags** (a line starting the tag inside a comment):
  - `@note [label] content…` — a parenthetical aside box, with an optional label
    chip. The label is a leading `[bracketed]` group or a bare single word; the
    content may start right on the tag line and runs to the next tag or the
    comment's end. Use it sparingly, for what a maintainer must know and the code
    cannot say: a recorded assumption, a scope limit, a caveat.
  - `@hide` — keep a declaration off the page (internal helpers).
  - `@output <file>` — root summary only.
- **Prose is markdown**: paragraphs, lists, `| tables |` (escape a literal pipe as
  `\|`), bold, inline code, links. Links are written out in full and pinned —
  cite reference source as `https://github.com/org/repo/blob/<full sha>/path#L10-L20`.
- Single-line doc comments on structure fields render as trailing `--` comments in
  the displayed code; `deriving` lines are not displayed.

## Writing the spec

- **One clause, one promise, one sentence.** The doc comment's English says exactly
  what the Lean below it commits to, in the owner's vocabulary. Make each clause
  self-contained: name its regime and hypotheses in the sentence ("In the final
  runway, with no override, the first soft read holds the prior") — there are no
  group headers to lean on.
- **Vocabulary before clauses.** Factor conditions and decision shapes into named
  Prop definitions (`Override`, `HoldsPrior`) so clauses read as sentences and the
  page's Propositions subsection becomes a glossary. Keep it small.
- **Prefer exact arithmetic.** Integers over floats wherever the reference allows
  (cents, minutes, division-free percentage tests like `5 · |c − p| ≥ |p|`). Record
  the encoding convention in the relevant file summary, including any divergence
  from the reference's float behavior.
- **Cost clauses.** To promise complexity bounds, make the contract's output a
  `Cost α` value (`Spec/Cost.lean` — CSLib's `TimeM` at cost type `Nat`) and
  state clauses over its `.time`: `r.time ≤ size l * size l`. In implementations,
  `✓` inside a `do` block ticks one unit (`✓[c]` for `c`). CSLib ships `@[simp]`
  lemmas (`time_bind`, `time_pure`, `time_tick`, `ret_bind`, …), and proofs go
  through with induction + `simp` + `omega`, with `nlinarith` (add
  `import Mathlib.Tactic` in `Proof.lean`) for nonlinear bounds. The bound counts
  explicit ticks only, so record the ticking discipline (what is charged, what is
  free) as an `@note [assumption]` beside the clauses.
- **Libraries.** New projects depend on CSLib and, through it, Mathlib — use
  them: cite and reuse their definitions and lemmas rather than reinventing.
  Their sources live under `.lake/packages/` inside the project, so you can Grep
  them for the right lemma. Dependency changes themselves (lakefile edits,
  `lake update`) are the developer's, not yours — ask.
- **Record judgment calls as `@note`.** When the spec asserts more than the
  reference states — an inferred qualifier, a cross-branch invariant, a scope
  limit — say so in a note on the clause or contract it concerns, with the
  alternative you rejected. The owner must be able to find every assumption.

## The workflow on a new project

1. **Spec first.** Write the types, vocabulary, constants, clause Props, and the
   contract type — no `Impl`, no `Proof`. The page renders fully with every clause
   `unproved`; the developer and the domain owner review the English there and the
   English is corrected before anything is built against it.
2. **Stop for approval.** The transition from spec-writing to implementation is the
   developer's act, never inferred: in harness sessions they flip the phase control
   on the page, which unlocks `Impl*`/`Proof*` and locks the approved spec. An
   implementation request for unspecified behavior is a spec request in disguise —
   write the clause, present it, and ask.
3. **Implement — at your own discretion.** Within an approved spec, implementation
   choices are yours: representations, algorithms, helper structure, proof strategy.
   Make them; do not ask the developer to arbitrate them. Ask for input only when a
   decision significantly affects how the program behaves — and notice that such a
   decision is really a spec question: behavior the clauses leave open either does
   not matter or is not specified yet, so raise it as a missing or ambiguous clause
   rather than as an implementation preference. If porting a reference, port
   branch-for-branch and resist "improving" it — parity first.
4. **Prove.** In `Proof/`, one theorem per clause (naming the clause), then
   assemble the contract instance (`def decide : Contract := …`). Badges flip as
   you go; the developer watches them. Keep each proof under the heartbeat cap —
   a proof that needs more is doing something exponential.
5. **A clause that will not prove is a finding, not an obstacle.** Either the
   implementation is wrong, or the spec is: take it to the English, fix the
   sentence with the owner, then the Lean, then the proof. Never weaken a clause
   silently; leave an `@note` when you qualify one.

## Running the harness

(If installed via `make install`, `lean-spec-viewer` is the launcher for all of these.)

- New project: `lean-spec-viewer <new-dir> --init` scaffolds this exact layout with
  a working stub (one proved clause) and serves it.
- Render once: `lean-spec-viewer render <repo>` (`--no-build` skips lake and
  renders `unverified` badges).
- Interactive: `lean-spec-viewer <repo> [--port 8787]` — hot reload on save,
  background verification, and an embedded assistant. The repo may also be a git
  URL, cloned into a managed checkout and served from there.
- Git: inside the box you have read-only `git status|diff|log|show` for inspecting
  history and diffs. Git writes — branching, committing, pushing, opening PRs,
  creating repos — are the developer's acts, through the git controls on the
  panel. At a good stopping point, suggest a commit in one line; never attempt one.
- `spec.html` is a build product. Never edit it; never commit status text anywhere.
