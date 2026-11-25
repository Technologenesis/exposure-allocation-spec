# Exposure allocation

A machine-checked specification, in Lean 4, of an exposure-allocation problem:
given a pool of capital, credit lines with hard spending limits, indivisible
assets of several types with fixed costs, and preferred ratios across credit
lines and across asset types, decide which assets to buy and which credit line
pays for each one.

Built as a **lean-spec-viewer** project: the contract lives in `Spec/` as English-plus-Lean doc comments, the
implementation in `Impl*`, and one theorem per clause in `Proof*`. The viewer
renders `spec.html` — the spec page with derived build and proof badges — from
the Lean sources; `AGENT.md` (vendored from the viewer) is the patterns document
for agents working in this layout.

```
lake build                              # verify: warningAsError ⇒ passing = sorry-free
lean-spec-viewer .                      # serve the spec page interactively
lean-spec-viewer render .               # render spec.html once
```

Depends on CSLib (and through it Mathlib) for the `Cost` monad behind the
complexity clauses. First build fetches and elaborates the dependencies; run
`lake exe cache get` first if a Mathlib build cache is available for the pinned
toolchain.
