-- A credit line's hard limit, not the pool, is what binds.
import Impl

/-!
The pool could afford everything, but line 0 may spend only 40 and line 1 only
30, so most of the capital cannot be deployed at all. The clause under test is
`WithinLimits`: whatever comes back, no line is over its limit.
-/

def problem : Problem where
  lineCount := 2
  typeCount := 2
  assetCount := 4
  pool := 500
  limit := fun i => [40, 30].getD i.val 0
  cost := fun i => [40, 30, 25, 25].getD i.val 0
  assetType := fun i => if [0, 1, 0, 1].getD i.val 0 = 0 then 0 else 1
  lineRatio := fun i => [5000, 5000].getD i.val 0
  typeRatio := fun i => [5000, 5000].getD i.val 0
  typeTolerance := 4000
  lineTolerance := 4000
  lineRatiosSumToOne := by decide
  typeRatiosSumToOne := by decide

def answer : Allocation problem := allocate problem

#eval (List.finRange problem.assetCount).map fun i => ((answer.buyer i).map Fin.val)
#eval (List.finRange problem.lineCount).map fun l => lineSpend answer l
#eval deployed answer
