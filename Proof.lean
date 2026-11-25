import Proof.Lemmas

/-! `allocate` meets the contract: it returns a feasible allocation that ranks at
least as high as every feasible allocation, and each clause follows from that. -/

theorem allocate_best (p : Problem) :
    Feasible (allocate p) ∧ ∀ y : Allocation p, Feasible y → RanksAtLeast (allocate p) y := by
  obtain ⟨k, hk⟩ := pickBest_exists isFeasible (fun x y => decide (RanksAtLeast x y))
    (candidates p) none
    (Or.inr ⟨nothingBought p, mem_candidates _,
      (isFeasible_iff _).mpr (nothingBought_feasible p)⟩)
  obtain ⟨h1, h2, _⟩ := pickBest_spec isFeasible (fun x y => decide (RanksAtLeast x y))
    ranks_refl ranks_total ranks_trans (candidates p) none (fun _ e => by cases e) k hk
  have ha : allocate p = k := by unfold allocate; rw [hk]; rfl
  rw [ha]
  refine ⟨(isFeasible_iff k).mp h1, fun y hy => ?_⟩
  have := h2 y (mem_candidates y) ((isFeasible_iff y).mpr hy)
  simpa using this

theorem allocate_withinPool (p : Problem) : WithinPool (allocate p) :=
  (allocate_best p).1.1

theorem allocate_withinLimits (p : Problem) : WithinLimits (allocate p) :=
  (allocate_best p).1.2.1

theorem allocate_typeMixWithinBound (p : Problem) : TypeMixWithinBound (allocate p) :=
  (allocate_best p).1.2.2.1

theorem allocate_lineMixWithinBound (p : Problem) : LineMixWithinBound (allocate p) :=
  (allocate_best p).1.2.2.2

theorem allocate_deploysMaximal (p : Problem) : DeploysMaximal (allocate p) := by
  intro i l hi hf
  exact not_ranksAtLeast_withPurchase _ i l hi ((allocate_best p).2 _ hf)

theorem allocate_bestBalanced (p : Problem) : BestBalanced (allocate p) := by
  intro y hy hd
  have h := (allocate_best p).2 y hy
  unfold RanksAtLeast at h
  unfold BalancedAtLeastAsWellAs
  omega

/-- The implementation meets the contract. -/
def allocateContract : Contract := fun p =>
  ⟨allocate p, allocate_withinPool p, allocate_withinLimits p,
    allocate_typeMixWithinBound p, allocate_lineMixWithinBound p,
    allocate_deploysMaximal p, allocate_bestBalanced p⟩
