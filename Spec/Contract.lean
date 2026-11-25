import Spec.Clauses

/-- For every allocation request, a choice of which assets to buy and which
credit line pays for each. It stays within the pool, every spending limit, and
both mix tolerances. No further single asset could be added, and no feasible
allocation deploying the same amount is better balanced, asset types first.
@note [satisfiable] A solution always exists. Buying nothing is feasible, so take
the largest feasible deployment and, among feasible allocations at that amount,
the best balanced. That allocation is maximal, because any addition would deploy
more. -/
def Contract : Type :=
  (p : Problem) → { x : Allocation p //
    WithinPool x ∧ WithinLimits x ∧ TypeMixWithinBound x ∧ LineMixWithinBound x ∧
    DeploysMaximal x ∧ BestBalanced x }
