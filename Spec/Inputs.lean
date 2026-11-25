/-!
All money is in **integer cents** (`Nat`), so every amount is exact. Ratios and
tolerances are in **basis points**: a ratio map adds up to one when its entries sum
to `RatioScale`. Credit lines are numbered `0 … lineCount − 1`, asset types
`0 … typeCount − 1`, and the individual assets on offer `0 … assetCount − 1`.
Every ratio test in the spec cross-multiplies, so it never divides.
-/

/-- One whole, in basis points. A ratio of `2500` means one quarter. -/
def RatioScale : Nat := 10000

/-- The sum of a finite family of naturals, e.g. one credit line's spend across
all assets. -/
def total {n : Nat} (f : Fin n → Nat) : Nat := (List.ofFn f).sum

/-- One allocation request: the capital pool, the credit lines that fund it (each
with a hard spending limit), the assets on offer (each indivisible, with its type
and cost), the two preferred mixes, and how far each mix may stray. -/
structure Problem where
  /-- How many credit lines there are. -/
  lineCount : Nat
  /-- How many asset types there are. -/
  typeCount : Nat
  /-- How many individual assets are on offer. -/
  assetCount : Nat
  /-- The capital to deploy, in cents. -/
  pool : Nat
  /-- Each credit line's spending limit, in cents. -/
  limit : Fin lineCount → Nat
  /-- What each asset costs, in cents. An asset is bought whole or not at all. -/
  cost : Fin assetCount → Nat
  /-- Which asset type each asset belongs to. -/
  assetType : Fin assetCount → Fin typeCount
  /-- Each credit line's preferred share of the deployed capital, in basis points. -/
  lineRatio : Fin lineCount → Nat
  /-- Each asset type's preferred share of the deployed capital, in basis points. -/
  typeRatio : Fin typeCount → Nat
  /-- How far the asset-type mix may stray from its ratios, in basis points. -/
  typeTolerance : Nat
  /-- How far the credit-line mix may stray from its ratios, in basis points. -/
  lineTolerance : Nat
  /-- The credit-line ratios add up to one. -/
  lineRatiosSumToOne : total lineRatio = RatioScale
  /-- The asset-type ratios add up to one. -/
  typeRatiosSumToOne : total typeRatio = RatioScale

/-- An allocation: for each asset, the credit line that buys it, if any. -/
structure Allocation (p : Problem) where
  /-- The credit line that pays the whole cost of asset `i`, or `none` if unbought. -/
  buyer : Fin p.assetCount → Option (Fin p.lineCount)
