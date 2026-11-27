-- A small allocation: one line, two types, everything affordable.
import Impl

/-!
The easy case, to see the shape of an answer. One credit line, so the line mix
is whatever it is; two asset types wanting 50/50, and four assets that can make
it exactly.
-/

def problem : Problem where
  lineCount := 1
  typeCount := 2
  assetCount := 4
  pool := 100
  limit := fun _ => 100
  cost := fun i => [30, 20, 25, 25].getD i.val 0
  assetType := fun i => if [0, 0, 1, 1].getD i.val 0 = 0 then 0 else 1
  lineRatio := fun _ => 10000
  typeRatio := fun i => [5000, 5000].getD i.val 0
  typeTolerance := 1000
  lineTolerance := 10000
  lineRatiosSumToOne := by decide
  typeRatiosSumToOne := by decide

def answer : Allocation problem := allocate problem

#eval (List.finRange problem.assetCount).map fun i => ((answer.buyer i).map Fin.val)
#eval deployed answer
#eval (List.finRange problem.typeCount).map fun t => typeTotal answer t
