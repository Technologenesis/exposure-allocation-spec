import Spec.Inputs

/-- What credit line `l` spends: the cost of every asset it buys. -/
def lineSpend {p : Problem} (x : Allocation p) (l : Fin p.lineCount) : Nat :=
  total (fun i => if x.buyer i = some l then p.cost i else 0)

/-- What asset type `t` receives: the cost of every bought asset of that type. -/
def typeTotal {p : Problem} (x : Allocation p) (t : Fin p.typeCount) : Nat :=
  total (fun i => if (x.buyer i).isSome ∧ p.assetType i = t then p.cost i else 0)

/-- All the capital the allocation deploys: the cost of every bought asset. -/
def deployed {p : Problem} (x : Allocation p) : Nat :=
  total (fun i => if (x.buyer i).isSome then p.cost i else 0)

/-- The distance between two amounts, `|a − b|`. -/
def gap (a b : Nat) : Nat := (a - b) + (b - a)

/-- How far the asset-type mix is from its ratios: the sum, over asset types, of
the gap between what the type received and its ratio share of the deployed
capital, cross-multiplied by `RatioScale`. Divided by `RatioScale × deployed`, it
is the total-variation-style distance Σ\|actual share − preferred share\|. -/
def typeImbalance {p : Problem} (x : Allocation p) : Nat :=
  total (fun t => gap (RatioScale * typeTotal x t) (p.typeRatio t * deployed x))

/-- How far the credit-line mix is from its ratios, measured the same way as
`typeImbalance`. -/
def lineImbalance {p : Problem} (x : Allocation p) : Nat :=
  total (fun l => gap (RatioScale * lineSpend x l) (p.lineRatio l * deployed x))

/-- The allocation `x` with one more asset `i` bought by credit line `l`. -/
def withPurchase {p : Problem} (x : Allocation p) (i : Fin p.assetCount)
    (l : Fin p.lineCount) : Allocation p :=
  ⟨fun j => if j = i then some l else x.buyer j⟩

/-- `x` is balanced at least as well as `y`: asset types first, then credit lines.
Its asset-type imbalance is smaller, or the two are equal and its credit-line
imbalance is no larger. -/
def BalancedAtLeastAsWellAs {p : Problem} (x y : Allocation p) : Prop :=
  typeImbalance x < typeImbalance y ∨
    (typeImbalance x = typeImbalance y ∧ lineImbalance x ≤ lineImbalance y)
