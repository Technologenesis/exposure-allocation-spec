import Spec.Inputs
import Spec.Cost
import Spec.Vocabulary
import Spec.Clauses
import Spec.Contract

/-!
# Exposure allocation

Given a pool of capital, credit lines with hard spending limits, indivisible
assets of several types with fixed costs, and preferred ratios across credit
lines and across asset types, decide which assets to buy and which credit line
pays for each one.
-/
