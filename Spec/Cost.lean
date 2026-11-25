import Cslib.Algorithms.Lean.TimeM

/-!
Cost accounting comes from CSLib's `TimeM`: a computation that returns a value
(`.ret`) and accumulates a time cost (`.time`), with `✓` ticking one unit inside
`do` blocks. A bound counts explicit ticks only, so the ticking discipline is
part of the spec: record it beside the clauses that rely on it.
-/

open Cslib.Algorithms.Lean in
/-- A computation returning `α` with a `Nat` time cost (CSLib's `TimeM`). -/
abbrev Cost (α : Type) := TimeM Nat α
