import Impl

/-! Generic lemmas: sums over `Fin n`, the best-pick scan, enumeration
completeness, and how buying one more asset moves the measures. -/

theorem total_succ {n : Nat} (f : Fin (n + 1) → Nat) :
    total f = f 0 + total (fun i => f i.succ) := by
  simp [total, List.ofFn_succ]

theorem total_zero : ∀ {n : Nat}, total (fun _ : Fin n => 0) = 0
  | 0 => by simp [total]
  | _ + 1 => by rw [total_succ]; simp [total_zero]

/-- Raising one entry by `c` raises the sum by `c`. -/
theorem total_single : ∀ {n : Nat} (f g : Fin n → Nat) (i : Fin n) (c : Nat),
    (∀ j, j ≠ i → g j = f j) → g i = f i + c → total g = total f + c
  | 0, _, _, i, _, _, _ => i.elim0
  | n + 1, f, g, i, c, hne, hi => by
    rw [total_succ g, total_succ f]
    cases i using Fin.cases with
    | zero =>
      have h : (fun j : Fin n => g j.succ) = fun j => f j.succ := by
        funext j; exact hne _ (Fin.succ_ne_zero j)
      rw [h, hi]; omega
    | succ k =>
      have ih := total_single (fun j : Fin n => f j.succ) (fun j => g j.succ) k c
        (fun j hj => hne _ (fun e => hj (Fin.succ_inj.mp e))) hi
      rw [ih, hne 0 (Fin.succ_ne_zero k).symm]; omega

theorem pickBest_spec {α : Type} (ok : α → Bool) (dom : α → α → Bool)
    (refl : ∀ a, dom a a = true) (tot : ∀ a b, dom a b = true ∨ dom b a = true)
    (trans : ∀ a b c, dom a b = true → dom b c = true → dom a c = true) :
    ∀ (js : List α) (c : Option α), (∀ c₀, c = some c₀ → ok c₀ = true) →
    ∀ k, pickBest ok dom c js = some k →
      ok k = true ∧ (∀ j ∈ js, ok j = true → dom k j = true) ∧
        (∀ c₀, c = some c₀ → dom k c₀ = true) := by
  intro js
  induction js with
  | nil =>
    intro c hc k h
    simp only [pickBest] at h
    subst h
    refine ⟨hc k rfl, by simp, ?_⟩
    intro c₀ e
    cases e
    exact refl _
  | cons j js ih =>
    intro c hc k h
    cases c with
    | none =>
      simp only [pickBest] at h
      have hc' : ∀ c₀, (if ok j = true then some j else none) = some c₀ → ok c₀ = true := by
        intro c₀ e
        by_cases hj : ok j = true
        · rw [ite_eq_left hj] at e; cases e; exact hj
        · rw [ite_eq_right hj] at e; cases e
      obtain ⟨h1, h2, h3⟩ := ih _ hc' k h
      refine ⟨h1, ?_, by simp⟩
      intro j' hj' hok
      rcases List.mem_cons.mp hj' with rfl | hj'
      · exact h3 j' (by simp [hok])
      · exact h2 j' hj' hok
    | some c₀ =>
      simp only [pickBest] at h
      have hc0 := hc c₀ rfl
      by_cases hs : (ok j && !dom c₀ j) = true
      · rw [ite_eq_left hs] at h
        have hs' : ok j = true ∧ dom c₀ j = false := by simpa using hs
        obtain ⟨h1, h2, h3⟩ := ih (some j) (fun c e => by cases e; exact hs'.1) k h
        have hkj := h3 j rfl
        refine ⟨h1, ?_, ?_⟩
        · intro j' hj' hok
          rcases List.mem_cons.mp hj' with rfl | hj'
          · exact hkj
          · exact h2 j' hj' hok
        · intro c e
          cases e
          rcases tot c₀ j with h | h
          · rw [hs'.2] at h; cases h
          · exact trans _ _ _ hkj h
      · rw [ite_eq_right hs] at h
        have hs' : ok j = true → dom c₀ j = true := by
          intro hj; simp [hj] at hs; exact hs
        obtain ⟨h1, h2, h3⟩ := ih (some c₀) (fun c e => by cases e; exact hc0) k h
        have hkc := h3 c₀ rfl
        refine ⟨h1, ?_, ?_⟩
        · intro j' hj' hok
          rcases List.mem_cons.mp hj' with rfl | hj'
          · exact trans _ _ _ hkc (hs' hok)
          · exact h2 j' hj' hok
        · intro c e
          cases e
          exact hkc

theorem pickBest_exists {α : Type} (ok : α → Bool) (dom : α → α → Bool) :
    ∀ (js : List α) (c : Option α), (c.isSome ∨ ∃ j ∈ js, ok j = true) →
    ∃ k, pickBest ok dom c js = some k := by
  intro js
  induction js with
  | nil =>
    intro c h
    rcases h with h | ⟨j, hj, _⟩
    · cases c with
      | none => simp at h
      | some k => exact ⟨k, rfl⟩
    · simp at hj
  | cons j js ih =>
    intro c h
    cases c with
    | none =>
      simp only [pickBest]
      apply ih
      by_cases hj : ok j = true
      · left; simp [hj]
      · right
        rcases h with h | ⟨j', hj', hok⟩
        · simp at h
        · rcases List.mem_cons.mp hj' with rfl | hj'
          · exact absurd hok hj
          · exact ⟨j', hj', hok⟩
    | some c₀ =>
      simp only [pickBest]
      apply ih
      left
      split <;> simp

/-! ### The ranking is a total preorder -/

theorem ranks_refl {p : Problem} (a : Allocation p) : decide (RanksAtLeast a a) = true :=
  decide_eq_true (Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, Nat.le_refl _⟩⟩⟩)

theorem ranks_total {p : Problem} (a b : Allocation p) :
    decide (RanksAtLeast a b) = true ∨ decide (RanksAtLeast b a) = true := by
  simp only [decide_eq_true_eq, RanksAtLeast]; omega

theorem ranks_trans {p : Problem} (a b c : Allocation p) :
    decide (RanksAtLeast a b) = true → decide (RanksAtLeast b c) = true →
      decide (RanksAtLeast a c) = true := by
  simp only [decide_eq_true_eq, RanksAtLeast]; omega

/-! ### Every allocation is a candidate -/

theorem allChoices_complete {α : Type} (opts : List α) :
    ∀ (n : Nat) (g : Fin n → α), (∀ i, g i ∈ opts) → g ∈ allChoices opts n
  | 0, g, _ => by
    simp only [allChoices]
    exact List.mem_singleton.mpr (funext fun i => i.elim0)
  | n + 1, g, hg => by
    simp only [allChoices]
    refine List.mem_flatMap.mpr
      ⟨fun i => g i.succ, allChoices_complete opts n _ (fun i => hg _), ?_⟩
    refine List.mem_map.mpr ⟨g 0, hg 0, ?_⟩
    funext i
    cases i using Fin.cases <;> simp

theorem buyerOptions_complete (m : Nat) (o : Option (Fin m)) : o ∈ buyerOptions m := by
  cases o <;> simp [buyerOptions, List.mem_finRange]

theorem mem_candidates {p : Problem} (x : Allocation p) : x ∈ candidates p :=
  List.mem_map.mpr
    ⟨x.buyer, allChoices_complete _ _ _ (fun _ => buyerOptions_complete _ _), rfl⟩

/-! ### Feasibility -/

theorem isFeasible_iff {p : Problem} (x : Allocation p) : isFeasible x = true ↔ Feasible x := by
  simp [isFeasible, Feasible, WithinPool, WithinLimits, TypeMixWithinBound,
    LineMixWithinBound, List.all_eq_true, List.mem_finRange, and_assoc]

theorem nothingBought_feasible (p : Problem) : Feasible (nothingBought p) := by
  have hl : ∀ l, lineSpend (nothingBought p) l = 0 := fun _ => by
    simp [lineSpend, nothingBought, total_zero]
  have ht : ∀ t, typeTotal (nothingBought p) t = 0 := fun _ => by
    simp [typeTotal, nothingBought, total_zero]
  have hd : deployed (nothingBought p) = 0 := by
    simp [deployed, nothingBought, total_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [WithinPool, hd]
  · intro l; simp [hl]
  · simp [TypeMixWithinBound, typeImbalance, ht, hd, gap, total_zero]
  · simp [LineMixWithinBound, lineImbalance, hl, hd, gap, total_zero]

/-! ### Buying one more asset -/

theorem deployed_withPurchase {p : Problem} (x : Allocation p) (i : Fin p.assetCount)
    (l : Fin p.lineCount) (hi : x.buyer i = none) :
    deployed (withPurchase x i l) = deployed x + p.cost i := by
  unfold deployed
  exact total_single _ _ i _ (fun j hj => by simp [withPurchase, hj])
    (by simp [withPurchase, hi])

theorem boughtCount_withPurchase {p : Problem} (x : Allocation p) (i : Fin p.assetCount)
    (l : Fin p.lineCount) (hi : x.buyer i = none) :
    boughtCount (withPurchase x i l) = boughtCount x + 1 := by
  unfold boughtCount
  exact total_single _ _ i _ (fun j hj => by simp [withPurchase, hj])
    (by simp [withPurchase, hi])

theorem lineSpend_withPurchase_free {p : Problem} (x : Allocation p) (i : Fin p.assetCount)
    (l : Fin p.lineCount) (hi : x.buyer i = none) (hc : p.cost i = 0) :
    lineSpend (withPurchase x i l) = lineSpend x := by
  funext l'
  unfold lineSpend
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp [withPurchase, hi, hc]
  · simp [withPurchase, hj]

theorem typeTotal_withPurchase_free {p : Problem} (x : Allocation p) (i : Fin p.assetCount)
    (l : Fin p.lineCount) (hi : x.buyer i = none) (hc : p.cost i = 0) :
    typeTotal (withPurchase x i l) = typeTotal x := by
  funext t
  unfold typeTotal
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp [withPurchase, hi, hc]
  · simp [withPurchase, hj]

/-- Buying one more asset always ranks strictly higher: it deploys more, or (for a
free asset) leaves both mixes unchanged and buys one more asset. -/
theorem not_ranksAtLeast_withPurchase {p : Problem} (x : Allocation p) (i : Fin p.assetCount)
    (l : Fin p.lineCount) (hi : x.buyer i = none) : ¬ RanksAtLeast x (withPurchase x i l) := by
  intro h
  have hd := deployed_withPurchase x i l hi
  have hn := boughtCount_withPurchase x i l hi
  unfold RanksAtLeast at h
  rw [hd, hn] at h
  by_cases hc : p.cost i = 0
  · have e1 : typeImbalance (withPurchase x i l) = typeImbalance x := by
      simp only [typeImbalance, typeTotal_withPurchase_free x i l hi hc, hd, hc, Nat.add_zero]
    have e2 : lineImbalance (withPurchase x i l) = lineImbalance x := by
      simp only [lineImbalance, lineSpend_withPurchase_free x i l hi hc, hd, hc, Nat.add_zero]
    rw [e1, e2] at h
    omega
  · omega
