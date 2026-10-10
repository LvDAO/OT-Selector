import OTSelector.Probability.CountingProcess.FiniteEventJumpBridge

/-!
# Pathwise integral for a finite labelled counting path

For a finite family of labels, the pathwise counting integral is just the sum of the
integrand over the labels which have been attained.  The top value is treated as an
unattained fallback.  This file is deliberately pathwise: no filtration, measurability,
or intensity hypothesis is used.
-/

open Filter Set
open scoped NNReal Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*}

/-- The finite real representative of a top-valued label.

The value at `⊤` is arbitrary (and is never used by the attained-label sum); choosing zero
makes the definition total and avoids dependent proof terms in finite sums.
-/
noncomputable def finiteEventTimeValue {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (i : Fin m) : ℝ≥0 :=
  if hi : ξ i ω ≠ ⊤ then (ξ i ω).untop hi else 0

@[simp]
theorem finiteEventTimeValue_coe {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) (i : Fin m)
    (hi : ξ i ω ≠ ⊤) :
    (finiteEventTimeValue ξ ω i : WithTop ℝ≥0) = ξ i ω := by
  rw [finiteEventTimeValue, dite_eq_left hi]
  exact WithTop.coe_untop _ _

/-!
The main statement uses `finiteEventTimeValue` so that the right-hand side is an ordinary
finite sum.  On the branch `ξ i ω ≤ t`, the value is automatically finite, hence this is
equivalent to writing an explicit dependent `untop` proof in that branch.
-/

theorem countingIntegral_finiteEventCountTop_eq_sum {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (H : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hξ : ∀ j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l) :
    countingIntegral (fun s ω' ↦ finiteEventCountTop ξ s ω') H t ω =
      ∑ i : Fin m, if ξ i ω ≤ (t : WithTop ℝ≥0) then
        H (finiteEventTimeValue ξ ω i) ω else 0 := by
  classical
  let N : ℝ≥0 → Ω → ℕ := fun s ω' ↦ finiteEventCountTop ξ s ω'
  let A : Finset ℕ := Finset.range (N t ω)
  let B : Finset (Fin m) :=
    Finset.univ.filter (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0))
  let G : Fin m → ℝ := fun i ↦
    if ξ i ω ≤ (t : WithTop ℝ≥0) then
      H (finiteEventTimeValue ξ ω i) ω else 0

  have hmono : Monotone (fun s : ℝ≥0 ↦ N s ω) := by
    intro s u hsu
    simpa [N] using finiteEventCountTop_mono ξ ω hsu
  have hrc : ∀ s, ContinuousWithinAt
      (fun u : ℝ≥0 ↦ (N u ω : ℝ)) (Ici s) s := by
    intro s
    simpa [N] using finiteEventCountTop_rightContinuous ξ ω s
  have hinj : Set.InjOn (fun k ↦ jumpTime N k ω) (Iio (N t ω)) := by
    simpa [N] using
      (finiteEventCountTop_jumpTime_injOn ξ ω hξ
        (finiteEventCountTop_rightContinuous ξ ω) t)

  /- Choose the label represented by each attained generalized jump. -/
  let f : ∀ k ∈ A, Fin m := fun k hk ↦
    Classical.choose (finiteEventCountTop_jumpTime_mem ξ ω (by
      simpa [A, N] using hk))
  have hf_spec : ∀ (k : ℕ) (hk : k ∈ A),
      ξ (f k hk) ω ≠ ⊤ ∧
        ξ (f k hk) ω = (jumpTime N k ω : WithTop ℝ≥0) := by
    intro k hk
    dsimp [f]
    exact Classical.choose_spec (finiteEventCountTop_jumpTime_mem ξ ω (by
      simpa [A, N] using hk))

  have hf_mem : ∀ (k : ℕ) (hk : k ∈ A), f k hk ∈ B := by
    intro k hk
    have hkt : k < N t ω := by simpa [A] using hk
    have hfk := hf_spec k hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hfk.2]
    exact WithTop.coe_le_coe.mpr (jumpTime_le_of_lt hkt)

  have hf_inj : ∀ (k₁ : ℕ) (hk₁ : k₁ ∈ A) (k₂ : ℕ) (hk₂ : k₂ ∈ A),
      f k₁ hk₁ = f k₂ hk₂ → k₁ = k₂ := by
    intro k₁ hk₁ k₂ hk₂ hsame
    have htimeTop : (jumpTime N k₁ ω : WithTop ℝ≥0) =
        (jumpTime N k₂ ω : WithTop ℝ≥0) := by
      calc
        (jumpTime N k₁ ω : WithTop ℝ≥0) = ξ (f k₁ hk₁) ω :=
          (hf_spec k₁ hk₁).2.symm
        _ = ξ (f k₂ hk₂) ω := congrArg (fun i ↦ ξ i ω) hsame
        _ = (jumpTime N k₂ ω : WithTop ℝ≥0) := (hf_spec k₂ hk₂).2
    have htime : jumpTime N k₁ ω = jumpTime N k₂ ω :=
      WithTop.coe_eq_coe.mp htimeTop
    apply hinj
    · simpa [A] using hk₁
    · simpa [A] using hk₂
    · exact htime

  /- The left count at a finite label is strictly below the count at that label. -/
  have hbefore_lt : ∀ (i : Fin m) (hi : i ∈ B),
      countBefore N ((ξ i ω).untop (by
        intro htop
        apply WithTop.not_top_le_coe t
        rw [← htop]
        exact (Finset.mem_filter.mp hi).2)) ω <
        N ((ξ i ω).untop (by
          intro htop
          apply WithTop.not_top_le_coe t
          rw [← htop]
          exact (Finset.mem_filter.mp hi).2)) ω := by
    intro i hi
    have hi_le : ξ i ω ≤ (t : WithTop ℝ≥0) := (Finset.mem_filter.mp hi).2
    have hi_top : ξ i ω ≠ ⊤ := by
      intro htop
      apply WithTop.not_top_le_coe t
      rw [← htop]
      exact hi_le
    let q : ℝ≥0 := (ξ i ω).untop hi_top
    let C : Finset (Fin m) :=
      Finset.univ.filter (fun j ↦ ξ j ω < (q : WithTop ℝ≥0))
    let D : Finset (Fin m) :=
      Finset.univ.filter (fun j ↦ ξ j ω ≤ (q : WithTop ℝ≥0))
    have hq_coe : (q : WithTop ℝ≥0) = ξ i ω := by
      exact WithTop.coe_untop _ _
    have hCD : C ⊆ D := by
      intro j hj
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.le⟩
    have hiD : i ∈ D := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rw [← hq_coe]⟩
    have hiC : i ∉ C := by
      intro hic
      exact (not_lt_of_ge (by rw [← hq_coe]))
        (Finset.mem_filter.mp hic).2
    have hCDne : C ≠ D := by
      intro hEq
      apply hiC
      rw [hEq]
      exact hiD
    have hCDss : C ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hCD, hCDne⟩
    have hcard : C.card < D.card := Finset.card_lt_card hCDss
    calc
      countBefore N q ω = C.card := by
        simpa [N, C, q] using
          (countBefore_finiteEventCountTop_eq_card_filter_lt ξ ω q)
      _ < D.card := hcard
      _ = N q ω := by simp [N, D, finiteEventCountTop]

  have hf_surj : ∀ (i : Fin m) (hi : i ∈ B),
      ∃ k, ∃ hk : k ∈ A, f k hk = i := by
    intro i hi
    have hi_le : ξ i ω ≤ (t : WithTop ℝ≥0) := (Finset.mem_filter.mp hi).2
    have hi_top : ξ i ω ≠ ⊤ := by
      intro htop
      apply WithTop.not_top_le_coe t
      rw [← htop]
      exact hi_le
    let q : ℝ≥0 := (ξ i ω).untop hi_top
    have hq_coe : (q : WithTop ℝ≥0) = ξ i ω := by
      exact WithTop.coe_untop _ _
    have hq_le : q ≤ t := by
      apply WithTop.coe_le_coe.mp
      rw [hq_coe]
      exact hi_le
    have hkq : countBefore N q ω < N q ω := by
      exact hbefore_lt i hi
    have hjump : jumpTime N (countBefore N q ω) ω = q := by
      simpa [N, q] using
        (finiteEventCountTop_jumpTime_eq_untop_countBefore ξ ω i hi_top hξ)
    have hkt : countBefore N q ω < N t ω := by
      apply lt_of_jumpTime_le hmono hrc ⟨q, hkq⟩
      rw [hjump]
      exact hq_le
    have hkA : countBefore N q ω ∈ A := by simpa [A] using hkt
    refine ⟨countBefore N q ω, hkA, ?_⟩
    have hfk := hf_spec (countBefore N q ω) hkA
    have hval : ξ (f (countBefore N q ω) hkA) ω = ξ i ω := by
      calc
        ξ (f (countBefore N q ω) hkA) ω =
            (jumpTime N (countBefore N q ω) ω : WithTop ℝ≥0) := hfk.2
        _ = (q : WithTop ℝ≥0) := by rw [hjump]
        _ = ξ i ω := hq_coe
    exact hξ _ _ hfk.1 hi_top hval

  have hf_term : ∀ (k : ℕ) (hk : k ∈ A),
      H (jumpTime N k ω) ω = G (f k hk) := by
    intro k hk
    have hfk := hf_spec k hk
    have hcond : ξ (f k hk) ω ≤ (t : WithTop ℝ≥0) :=
      (Finset.mem_filter.mp (hf_mem k hk)).2
    have htime : finiteEventTimeValue ξ ω (f k hk) = jumpTime N k ω := by
      apply WithTop.coe_eq_coe.mp
      calc
        (finiteEventTimeValue ξ ω (f k hk) : WithTop ℝ≥0) =
            ξ (f k hk) ω := finiteEventTimeValue_coe ξ ω _ hfk.1
        _ = (jumpTime N k ω : WithTop ℝ≥0) := hfk.2
    simp only [G, ite_eq_left hcond]
    rw [htime]

  have hsum_bij :
      (∑ k ∈ A, H (jumpTime N k ω) ω) = ∑ i ∈ B, G i := by
    apply Finset.sum_bij f
    · exact hf_mem
    · exact hf_inj
    · exact hf_surj
    · exact hf_term

  have hsum_filter : (∑ i ∈ B, G i) = ∑ i : Fin m, G i := by
    change (∑ i ∈ (Finset.univ.filter
      (fun i : Fin m ↦ ξ i ω ≤ (t : WithTop ℝ≥0))), G i) = ∑ i : Fin m, G i
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ξ i ω ≤ (t : WithTop ℝ≥0)
    · simp only [ite_eq_left h]
    · simp only [ite_eq_right h]
      change 0 = (if ξ i ω ≤ (t : WithTop ℝ≥0) then
        H (finiteEventTimeValue ξ ω i) ω else 0)
      rw [ite_eq_right h]

  simpa [countingIntegral, A, N, G] using hsum_bij.trans hsum_filter

end OTSelector.CountingProcess
