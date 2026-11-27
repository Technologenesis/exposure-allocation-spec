-- The input that tells ranked balancing apart from weighted balancing.
import Impl

/-!
Two credit lines that want a **25 / 75** split, two asset types that want
**50 / 50**, and five assets on offer. The pool buys exactly 120 either way, so
the contract's tie-break on balance is what decides — and the two readings of
"best balanced" disagree about it.

* Buying **assets 0 and 1** (60 each, one of each type) makes the asset-type mix
  perfect, but the two assets are the same size, so the credit lines end up
  60 / 60 when they wanted 30 / 90.
* Buying **assets 0, 2, 3 and 4** pushes the type mix slightly off, and lets the
  lines land on 30 / 90 exactly.

Ranked balancing takes the first: asset types outrank credit lines, so a perfect
type mix wins at any cost to the lines. Weighted balancing takes the second: the
small type penalty is outweighed by the large line gain.

Run it before the spec changes and after, and read the first line of output.
-/

def problem : Problem where
  lineCount := 2
  typeCount := 2
  assetCount := 5
  pool := 120
  limit := fun _ => 120                                    -- no line is binding
  cost := fun i => [60, 60, 10, 30, 20].getD i.val 0
  assetType := fun i => if [0, 1, 0, 1, 1].getD i.val 0 = 0 then 0 else 1
  lineRatio := fun i => [2500, 7500].getD i.val 0          -- the lines want 25/75
  typeRatio := fun i => [5000, 5000].getD i.val 0          -- the types want 50/50
  typeTolerance := 6000
  lineTolerance := 6000
  lineRatiosSumToOne := by decide
  typeRatiosSumToOne := by decide

def answer : Allocation problem := allocate problem

-- Which line buys each asset, `none` where the asset is left alone.
#eval (List.finRange problem.assetCount).map fun i => ((answer.buyer i).map Fin.val)

-- What each credit line spends. The lines wanted 30 and 90.
#eval (List.finRange problem.lineCount).map fun l => lineSpend answer l

-- What each asset type received. The types wanted 60 and 60.
#eval (List.finRange problem.typeCount).map fun t => typeTotal answer t

#eval deployed answer
#eval typeImbalance answer
#eval lineImbalance answer
