import Spec.Vocabulary

/-- The allocation deploys no more than the pool. -/
def WithinPool {p : Problem} (x : Allocation p) : Prop :=
  deployed x ≤ p.pool

/-- No credit line spends more than its spending limit. -/
def WithinLimits {p : Problem} (x : Allocation p) : Prop :=
  ∀ l, lineSpend x l ≤ p.limit l

/-- The asset-type mix is within the asset-type tolerance of its ratios: the
total distance Σ\|actual share − preferred share\| is at most
`typeTolerance ÷ RatioScale`. An allocation that deploys nothing meets this
trivially. -/
def TypeMixWithinBound {p : Problem} (x : Allocation p) : Prop :=
  typeImbalance x ≤ p.typeTolerance * deployed x

/-- The credit-line mix is within the credit-line tolerance of its ratios: the
total distance Σ\|actual share − preferred share\| is at most
`lineTolerance ÷ RatioScale`. An allocation that deploys nothing meets this
trivially.
@note [guarantee] Both mixes have their own hard bound, so asset-type balance is
never bought by abandoning the credit-line mix, or the reverse. Priority between
them only applies inside both bounds (see `BestBalanced`). -/
def LineMixWithinBound {p : Problem} (x : Allocation p) : Prop :=
  lineImbalance x ≤ p.lineTolerance * deployed x

/-- An allocation is feasible when it stays within the pool, every spending
limit, and both mix tolerances. -/
def Feasible {p : Problem} (x : Allocation p) : Prop :=
  WithinPool x ∧ WithinLimits x ∧ TypeMixWithinBound x ∧ LineMixWithinBound x

/-- No unbought asset could be added: buying any one of them, by any credit line,
would break the pool, that line's limit, or a mix tolerance.
@note [objective] This is maximal deployment, not maximum: it rules out single
additions only. Because the mix tolerances are not monotone, an allocation can be
stuck here even though buying two assets together would stay within the bounds.
Maximum deployment (no feasible allocation deploys more) was rejected as a
knapsack-hard requirement. -/
def DeploysMaximal {p : Problem} (x : Allocation p) : Prop :=
  ∀ i l, x.buyer i = none → ¬ Feasible (withPurchase x i l)

/-- Among all feasible allocations that deploy the same amount, none is better
balanced: none has a smaller asset-type imbalance, or an equal one with a smaller
credit-line imbalance.
@note [objective] Balance is truly optimal, but only compared at equal
deployment. Comparing across deployment amounts would let a smaller, better
balanced allocation (ultimately the empty one) win over deploying capital.
Imbalance is measured as a sum of absolute gaps (L1). Squared gaps and max-min
fill were the alternatives; L1 stays exact in integers and matches the tolerances.
@note [assumption] Asset types rank strictly ahead of credit lines: any
improvement to the asset-type mix outweighs any loss on the credit-line mix,
within `LineMixWithinBound`. -/
def BestBalanced {p : Problem} (x : Allocation p) : Prop :=
  ∀ y : Allocation p, Feasible y → deployed y = deployed x →
    BalancedAtLeastAsWellAs x y
