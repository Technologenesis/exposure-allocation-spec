import Spec

/-!
The allocator searches exhaustively. It lists every allocation (each asset either
unbought or bought by one of the credit lines), keeps the feasible ones, and
returns the one that ranks highest: most capital deployed, then the smallest
asset-type imbalance, then the smallest credit-line imbalance, then the most
assets bought (so a free asset is never left on the table). There are
`(lineCount + 1) ^ assetCount` candidates.
-/

/-- How many assets `x` buys. -/
def boughtCount {p : Problem} (x : Allocation p) : Nat :=
  total (fun i => if (x.buyer i).isSome then 1 else 0)

/-- `x` ranks at least as high as `y`: more deployed; or equal deployment and
better asset-type balance; then credit-line balance; then more assets bought. -/
def RanksAtLeast {p : Problem} (x y : Allocation p) : Prop :=
  deployed y < deployed x ∨
    (deployed y = deployed x ∧
      (typeImbalance x < typeImbalance y ∨
        (typeImbalance x = typeImbalance y ∧
          (lineImbalance x < lineImbalance y ∨
            (lineImbalance x = lineImbalance y ∧ boughtCount y ≤ boughtCount x)))))

instance {p : Problem} (x y : Allocation p) : Decidable (RanksAtLeast x y) := by
  unfold RanksAtLeast; infer_instance

/-- Scan `js`, keeping the current best admitted candidate `c`; a new admitted
candidate replaces it only when `c` does not dominate it. -/
def pickBest {α : Type} (ok : α → Bool) (dom : α → α → Bool) : Option α → List α → Option α
  | c, [] => c
  | none, j :: js => pickBest ok dom (if ok j then some j else none) js
  | some c, j :: js => pickBest ok dom (if ok j && !dom c j then some j else some c) js

/-- Every function `Fin n → α` whose values are drawn from `opts`. -/
def allChoices {α : Type} (opts : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [fun i => i.elim0]
  | n + 1 => (allChoices opts n).flatMap fun f =>
      opts.map fun a => Fin.cases (motive := fun _ => α) a f

/-- Who may buy an asset: nobody, or any one credit line. -/
def buyerOptions (m : Nat) : List (Option (Fin m)) :=
  none :: (List.finRange m).map some

/-- Every allocation of the problem. -/
def candidates (p : Problem) : List (Allocation p) :=
  (allChoices (buyerOptions p.lineCount) p.assetCount).map Allocation.mk

/-- The feasibility test, computed. -/
def isFeasible {p : Problem} (x : Allocation p) : Bool :=
  decide (deployed x ≤ p.pool) &&
    (List.finRange p.lineCount).all (fun l => decide (lineSpend x l ≤ p.limit l)) &&
    decide (typeImbalance x ≤ p.typeTolerance * deployed x) &&
    decide (lineImbalance x ≤ p.lineTolerance * deployed x)

/-- The allocation that buys nothing. -/
def nothingBought (p : Problem) : Allocation p := ⟨fun _ => none⟩

/-- The allocation: the highest-ranked feasible candidate. -/
def allocate (p : Problem) : Allocation p :=
  (pickBest isFeasible (fun x y => decide (RanksAtLeast x y)) none (candidates p)).getD
    (nothingBought p)
