import OTSelector.Probability.CountingProcess.FiniteEventCountTop
import OTSelector.Probability.CountingProcess.JumpCounting

/-!
# Exact bridge from finite event labels to generalized jump times

This file identifies the generalized jump time indexed by the left count at a finite event
label with that label itself.  The argument uses the finite-event filter cardinalities and the
existing pathwise jump-time lemmas; it does not unfold `jumpTime` as an infimum.
-/

open Filter Set
open scoped NNReal Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*}

/-- The generalized jump indexed by the left count at a finite event label is that label.

The finite labels are assumed pairwise distinct so that the inherited generalized jump-time
injectivity can be used to rule out a strictly earlier generalized jump at the same horizon.
-/
theorem finiteEventCountTop_jumpTime_eq_untop_countBefore {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (i : Fin m)
    (hi : ξ i ω ≠ ⊤)
    (hξ : ∀ j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l) :
    jumpTime (fun t ω' ↦ finiteEventCountTop ξ t ω')
        (countBefore (fun t ω' ↦ finiteEventCountTop ξ t ω')
          ((ξ i ω).untop hi) ω) ω = (ξ i ω).untop hi := by
  let N : ℝ≥0 → Ω → ℕ := fun t ω' ↦ finiteEventCountTop ξ t ω'
  let q : ℝ≥0 := (ξ i ω).untop hi
  let k : ℕ := countBefore N q ω
  have hq_coe : (q : WithTop ℝ≥0) = ξ i ω := by
    exact WithTop.coe_untop _ _
  let C : Finset (Fin m) := Finset.univ.filter
    (fun j ↦ ξ j ω < (q : WithTop ℝ≥0))
  let B : Finset (Fin m) := Finset.univ.filter
    (fun j ↦ ξ j ω ≤ (q : WithTop ℝ≥0))
  have hCB : C ⊆ B := by
    intro j hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.le⟩
  have hiB : i ∈ B := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hq_coe.symm.le⟩
  have hiC : i ∉ C := by
    intro hiC'
    exact (not_lt_of_ge hq_coe.le) (Finset.mem_filter.mp hiC').2
  have hCneB : C ≠ B := by
    intro hCB'
    apply hiC
    rw [hCB']
    exact hiB
  have hCsubB : C ⊂ B :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hCB, hCneB⟩
  have hcard_lt : C.card < B.card := Finset.card_lt_card hCsubB
  have hcount_eq : countBefore N q ω = C.card := by
    simpa [N, C] using
      (countBefore_finiteEventCountTop_eq_card_filter_lt ξ ω q)
  have hkq : k < N q ω := by
    calc
      k = C.card := by simpa [k] using hcount_eq
      _ < B.card := hcard_lt
      _ = N q ω := by rfl
  have hmono : Monotone (fun t ↦ N t ω) := by
    intro s t hst
    exact finiteEventCountTop_mono ξ ω hst
  have hrc : ∀ t, ContinuousWithinAt
      (fun s ↦ (N s ω : ℝ)) (Ici t) t := by
    intro t
    simpa [N] using finiteEventCountTop_rightContinuous ξ ω t
  have hτ_le : jumpTime N k ω ≤ q := jumpTime_le_of_lt hkq
  have hinj : Set.InjOn (fun l ↦ jumpTime N l ω) (Iio (N q ω)) := by
    simpa [N] using
      (finiteEventCountTop_jumpTime_injOn ξ ω hξ
        (finiteEventCountTop_rightContinuous ξ ω) q)
  have hnot_lt : ¬jumpTime N k ω < q := by
    intro hτ_lt
    have hk_before : k < countBefore N q ω :=
      (jumpTime_lt_iff_lt_countBefore hmono hrc hinj hkq).mp hτ_lt
    change k < k at hk_before
    exact (Nat.lt_irrefl k) hk_before
  have hq_le : q ≤ jumpTime N k ω := le_of_not_gt hnot_lt
  have hτ_eq : jumpTime N k ω = q := le_antisymm hτ_le hq_le
  simpa [N, q, k] using hτ_eq

/-- Public form of `finiteEventCountTop_jumpTime_eq_untop_countBefore` with the filter-card index.
-/
theorem finiteEventCountTop_jumpTime_eq_of_event_filter_card {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (i : Fin m)
    (hi : ξ i ω ≠ ⊤)
    (hξ : ∀ j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l) :
    jumpTime (fun t ω' ↦ finiteEventCountTop ξ t ω')
        ((Finset.univ.filter
          (fun j ↦ ξ j ω < ((ξ i ω).untop hi : WithTop ℝ≥0))).card) ω =
      (ξ i ω).untop hi := by
  have hbridge := finiteEventCountTop_jumpTime_eq_untop_countBefore ξ ω i hi hξ
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt ξ ω ((ξ i ω).untop hi)] at hbridge
  exact hbridge

end OTSelector.CountingProcess
