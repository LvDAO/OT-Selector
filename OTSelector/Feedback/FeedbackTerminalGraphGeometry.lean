import OTSelector.Feedback.FeedbackStoppedGraphEnergyBridge

/-!
# Deterministic terminal geometry of the increasing graph matching

The statements in this file are pathwise.  A graph may be the recursive graph, a frozen
horizon graph, or a stopped continuation graph.  The cut convention is right-closed on the
retained side: a rank is terminal precisely when `H < graphRankRightEndpoint`.
-/

open Set
open scoped BigOperators Classical NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-! ## Endpoint and rank sets -/

/-- Source intersections strictly to the right of the cut, counted by source labels. -/
noncomputable def graphSourceRightEndpointCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    H < sample.sourceIntersection graph i).card

/-- Target intersections strictly to the right of the cut, counted by target labels. -/
noncomputable def graphTargetRightEndpointCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin n =>
    H < sample.targetIntersection graph j).card

/-- Source intersections at or to the left of the cut. -/
noncomputable def graphSourceCutCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    sample.sourceIntersection graph i ≤ H).card

/-- Target intersections at or to the left of the cut. -/
noncomputable def graphTargetCutCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin n =>
    sample.targetIntersection graph j ≤ H).card

/-- Source intersections in the closed backward window `[H-L,H]`. -/
noncomputable def graphSourceBackwardWindowCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H L : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    H - L ≤ sample.sourceIntersection graph i ∧
      sample.sourceIntersection graph i ≤ H).card

/-- Target intersections in the closed backward window `[H-L,H]`. -/
noncomputable def graphTargetBackwardWindowCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H L : ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin n =>
    H - L ≤ sample.targetIntersection graph j ∧
      sample.targetIntersection graph j ≤ H).card

/-- Source intersections strictly below a threshold. -/
private noncomputable def graphSourceBelowCount {lam : ℝ}
    (graph : FeedbackGraph lam) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin n =>
    sample.sourceIntersection graph i < x).card

/-- Target intersections strictly below a threshold. -/
private noncomputable def graphTargetBelowCount {lam : ℝ}
    (graph : FeedbackGraph lam) (x : ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin n =>
    sample.targetIntersection graph j < x).card

/-- Ranks whose increasing same-rank edge has an endpoint strictly to the right of `H`. -/
noncomputable def graphTerminalRankSet {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun r => sample.GraphRightTerminalRank graph H r

/-- Number of terminal ranks. -/
noncomputable def graphTerminalRankCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  (sample.graphTerminalRankSet graph H).card

/-- Ranks whose same-rank edge crosses the cut `H`. -/
noncomputable def graphCrossingRankSet {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun r =>
    sample.graphRankLeftEndpoint graph r ≤ H ∧
      H < sample.graphRankRightEndpoint graph r

/-- Number of increasing same-rank edges crossing the cut. -/
noncomputable def graphCrossingRankCount {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  (sample.graphCrossingRankSet graph H).card

/-- The absolute discrepancy of the two sorted endpoint counts at the cut. -/
noncomputable def graphRankCountDiscrepancy {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℕ :=
  Int.natAbs ((sample.graphSourceCutCount graph H : ℤ) -
    (sample.graphTargetCutCount graph H : ℤ))

private theorem natAbs_int_sub_natCast (a b : ℕ) :
    Int.natAbs ((a : ℤ) - (b : ℤ)) =
      if b ≤ a then a - b else b - a := by
  by_cases h : b ≤ a
  · have hz : 0 ≤ (a : ℤ) - (b : ℤ) := by
      omega
    have hcast :
        ((Int.natAbs ((a : ℤ) - (b : ℤ)) : ℕ) : ℤ) =
          ((a - b : ℕ) : ℤ) := by
      calc
        ((Int.natAbs ((a : ℤ) - (b : ℤ)) : ℕ) : ℤ) =
            (a : ℤ) - (b : ℤ) := Int.natAbs_of_nonneg hz
        _ = ((a - b : ℕ) : ℤ) := by omega
    have hnat : Int.natAbs ((a : ℤ) - (b : ℤ)) = a - b := by
      exact_mod_cast hcast
    simp [h, hnat]
  · have hba : a ≤ b := Nat.le_of_lt (lt_of_not_ge h)
    have hz : (a : ℤ) - (b : ℤ) ≤ 0 := by
      omega
    have hcast :
        ((Int.natAbs ((a : ℤ) - (b : ℤ)) : ℕ) : ℤ) =
          ((b - a : ℕ) : ℤ) := by
      calc
        ((Int.natAbs ((a : ℤ) - (b : ℤ)) : ℕ) : ℤ) =
            |(a : ℤ) - (b : ℤ)| := Int.natCast_natAbs _
        _ = -((a : ℤ) - (b : ℤ)) := abs_of_nonpos hz
        _ = ((b - a : ℕ) : ℤ) := by omega
    have hnat : Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by
      exact_mod_cast hcast
    simp [h, hnat]

private theorem card_fin_filter_val_interval {a b : ℕ}
    (hb : b ≤ n) :
    (Finset.univ.filter fun r : Fin n => a ≤ r.val ∧ r.val < b).card =
      b - a := by
  let s : Finset ℕ := Finset.Ico a b
  let t : Finset (Fin n) :=
    Finset.univ.filter fun r : Fin n => a ≤ r.val ∧ r.val < b
  have hcard : s.card = t.card := by
    apply Finset.card_bij (s := s) (t := t) (fun (k : ℕ) hk =>
      ⟨k, lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 hb⟩)
    · intro k hk
      have hk' : a ≤ k ∧ k < b := Finset.mem_Ico.mp hk
      simpa [t] using hk'
    · intro k hk k' hk' heq
      exact congrArg Fin.val heq
    · intro r hr
      refine ⟨r.val, ?_, ?_⟩
      · have hr' : a ≤ r.val ∧ r.val < b := by simpa [t] using hr
        exact Finset.mem_Ico.mpr hr'
      · apply Fin.ext
        rfl
  rw [show s.card = b - a by simp [s, Nat.card_Ico]] at hcard
  exact hcard.symm

private theorem graphSourceRank_le_cut_iff {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) (r : Fin n) :
    sample.graphSourceIntersectionAtRank graph r ≤ H ↔
      r.val < sample.graphSourceCutCount graph H := by
  unfold graphSourceIntersectionAtRank graphSourceCutCount
  exact CountingProcess.tupleSort_apply_le_iff_lt_card
    (fun i : Fin n => sample.sourceIntersection graph i) r H

private theorem graphTargetRank_le_cut_iff {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) (r : Fin n) :
    sample.graphTargetIntersectionAtRank graph r ≤ H ↔
      r.val < sample.graphTargetCutCount graph H := by
  unfold graphTargetIntersectionAtRank graphTargetCutCount
  exact CountingProcess.tupleSort_apply_le_iff_lt_card
    (fun j : Fin n => sample.targetIntersection graph j) r H

private theorem graphSourceRank_ge_of_below_count_le {lam : ℝ}
    (graph : FeedbackGraph lam) (x : ℝ) (r : Fin n)
    (hidx : sample.graphSourceBelowCount graph x ≤ r.val) :
    x ≤ sample.graphSourceIntersectionAtRank graph r := by
  change (Finset.univ.filter fun i : Fin n =>
      sample.sourceIntersection graph i < x).card ≤ r.val at hidx
  change x ≤ sample.sourceIntersection graph
    (Tuple.sort (fun i : Fin n => sample.sourceIntersection graph i) r)
  by_contra hnot
  have hlt :
      (fun i : Fin n => sample.sourceIntersection graph i)
          (Tuple.sort (fun i : Fin n => sample.sourceIntersection graph i) r) < x :=
    lt_of_not_ge hnot
  let values := fun i : Fin n => sample.sourceIntersection graph i
  have hcard := CountingProcess.tupleSort_apply_le_iff_lt_card values r
    (values (Tuple.sort values r))
  have hsubset :
      (Finset.univ : Finset (Fin n)).filter
          (fun i : Fin n => values i ≤ values (Tuple.sort values r)) ⊆
        (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => values i < x) := by
    intro i hi
    have hi' : values i ≤ values (Tuple.sort values r) := by simpa using hi
    have hi'' : i ∈ (Finset.univ : Finset (Fin n)) := by simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_lt hi' hlt
  have hltcard : r.val <
      (Finset.univ.filter (fun i : Fin n => values i < x)).card :=
    lt_of_lt_of_le (hcard.mp le_rfl) (Finset.card_le_card hsubset)
  exact (Nat.not_lt_of_ge hidx) hltcard

private theorem graphTargetRank_ge_of_below_count_le {lam : ℝ}
    (graph : FeedbackGraph lam) (x : ℝ) (r : Fin n)
    (hidx : sample.graphTargetBelowCount graph x ≤ r.val) :
    x ≤ sample.graphTargetIntersectionAtRank graph r := by
  change (Finset.univ.filter fun j : Fin n =>
      sample.targetIntersection graph j < x).card ≤ r.val at hidx
  change x ≤ sample.targetIntersection graph
    (Tuple.sort (fun j : Fin n => sample.targetIntersection graph j) r)
  by_contra hnot
  have hlt :
      (fun j : Fin n => sample.targetIntersection graph j)
          (Tuple.sort (fun j : Fin n => sample.targetIntersection graph j) r) < x :=
    lt_of_not_ge hnot
  let values := fun j : Fin n => sample.targetIntersection graph j
  have hcard := CountingProcess.tupleSort_apply_le_iff_lt_card values r
    (values (Tuple.sort values r))
  have hsubset :
      (Finset.univ : Finset (Fin n)).filter
          (fun j : Fin n => values j ≤ values (Tuple.sort values r)) ⊆
        (Finset.univ : Finset (Fin n)).filter (fun j : Fin n => values j < x) := by
    intro j hj
    have hj' : values j ≤ values (Tuple.sort values r) := by simpa using hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_lt hj' hlt
  have hltcard : r.val <
      (Finset.univ.filter (fun j : Fin n => values j < x)).card :=
    lt_of_lt_of_le (hcard.mp le_rfl) (Finset.card_le_card hsubset)
  exact (Nat.not_lt_of_ge hidx) hltcard

/-! ## Terminal count and crossing discrepancy -/

theorem graphTerminalRank_iff {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) (r : Fin n) :
    r ∈ sample.graphTerminalRankSet graph H ↔
      H < sample.graphRankRightEndpoint graph r := by
  change r ∈ Finset.univ.filter (fun r =>
    sample.GraphRightTerminalRank graph H r) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, GraphRightTerminalRank]

theorem graphTerminalRankCount_le_rightEndpointCounts {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) :
    sample.graphTerminalRankCount graph H ≤
      sample.graphSourceRightEndpointCount graph H +
        sample.graphTargetRightEndpointCount graph H := by
  classical
  let source := fun i : Fin n => sample.sourceIntersection graph i
  let target := fun j : Fin n => sample.targetIntersection graph j
  let sourceRight : Finset (Fin n) := Finset.univ.filter fun i => H < source i
  let targetRight : Finset (Fin n) := Finset.univ.filter fun j => H < target j
  let sourceRankRight : Finset (Fin n) :=
    Finset.univ.filter fun r => H < sample.graphSourceIntersectionAtRank graph r
  let targetRankRight : Finset (Fin n) :=
    Finset.univ.filter fun r => H < sample.graphTargetIntersectionAtRank graph r
  have hsourceCard : sourceRankRight.card = sourceRight.card := by
    apply Finset.card_equiv (Tuple.sort source)
    intro r
    simp only [sourceRankRight, sourceRight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  have htargetCard : targetRankRight.card = targetRight.card := by
    apply Finset.card_equiv (Tuple.sort target)
    intro r
    simp only [targetRankRight, targetRight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  have hsubset : sample.graphTerminalRankSet graph H ⊆
      sourceRankRight ∪ targetRankRight := by
    intro r hr
    have hterm : H < sample.graphRankRightEndpoint graph r :=
      (sample.graphTerminalRank_iff graph H r).mp hr
    by_cases hs : H < sample.graphSourceIntersectionAtRank graph r
    · exact Finset.mem_union_left _ (by simpa [sourceRankRight] using hs)
    · have hsource : sample.graphSourceIntersectionAtRank graph r ≤ H :=
        le_of_not_gt hs
      have ht : H < sample.graphTargetIntersectionAtRank graph r := by
        by_contra ht
        have htarget : sample.graphTargetIntersectionAtRank graph r ≤ H :=
          le_of_not_gt ht
        have hright : sample.graphRankRightEndpoint graph r ≤ H :=
          max_le hsource htarget
        exact (not_lt_of_ge hright) hterm
      exact Finset.mem_union_right _ (by simpa [targetRankRight] using ht)
  calc
    sample.graphTerminalRankCount graph H =
        (sample.graphTerminalRankSet graph H).card := rfl
    _ ≤ (sourceRankRight ∪ targetRankRight).card :=
      Finset.card_le_card hsubset
    _ ≤ sourceRankRight.card + targetRankRight.card := Finset.card_union_le _ _
    _ = sourceRight.card + targetRight.card := by rw [hsourceCard, htargetCard]
    _ = sample.graphSourceRightEndpointCount graph H +
        sample.graphTargetRightEndpointCount graph H := by
      rfl

theorem graphCrossingRank_iff {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) (r : Fin n) :
    r ∈ sample.graphCrossingRankSet graph H ↔
      (sample.graphSourceIntersectionAtRank graph r ≤ H ∧
          H < sample.graphTargetIntersectionAtRank graph r) ∨
        (sample.graphTargetIntersectionAtRank graph r ≤ H ∧
          H < sample.graphSourceIntersectionAtRank graph r) := by
  change r ∈ Finset.univ.filter (fun r =>
    sample.graphRankLeftEndpoint graph r ≤ H ∧
      H < sample.graphRankRightEndpoint graph r) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change min (sample.graphSourceIntersectionAtRank graph r)
      (sample.graphTargetIntersectionAtRank graph r) ≤ H ∧
        H < max (sample.graphSourceIntersectionAtRank graph r)
          (sample.graphTargetIntersectionAtRank graph r) ↔ _
  rw [min_le_iff, lt_max_iff]
  constructor
  · rintro ⟨hs | ht, hs' | ht'⟩
    · exfalso
      linarith
    · exact Or.inl ⟨hs, ht'⟩
    · exact Or.inr ⟨ht, hs'⟩
    · exfalso
      linarith
  · rintro (⟨hs, ht⟩ | ⟨ht, hs⟩)
    · exact ⟨Or.inl hs, Or.inr ht⟩
    · exact ⟨Or.inr ht, Or.inl hs⟩

theorem graphCrossingRankCount_eq_rankCountDiscrepancy {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) :
    sample.graphCrossingRankCount graph H =
      sample.graphRankCountDiscrepancy graph H := by
  classical
  let s := sample.graphSourceCutCount graph H
  let t := sample.graphTargetCutCount graph H
  have hsle : s ≤ n := by
    dsimp [s, graphSourceCutCount]
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i : Fin n => sample.sourceIntersection graph i ≤ H)
  have htle : t ≤ n := by
    dsimp [t, graphTargetCutCount]
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun j : Fin n => sample.targetIntersection graph j ≤ H)
  have hsource (r : Fin n) :
      sample.graphSourceIntersectionAtRank graph r ≤ H ↔ r.val < s := by
    simpa [s] using sample.graphSourceRank_le_cut_iff graph H r
  have htarget (r : Fin n) :
      sample.graphTargetIntersectionAtRank graph r ≤ H ↔ r.val < t := by
    simpa [t] using sample.graphTargetRank_le_cut_iff graph H r
  have hcross (r : Fin n) :
      r ∈ sample.graphCrossingRankSet graph H ↔
        (s ≤ r.val ∧ r.val < t) ∨ (t ≤ r.val ∧ r.val < s) := by
    rw [sample.graphCrossingRank_iff graph H r]
    constructor
    · rintro (⟨hsr, htr⟩ | ⟨htr, hsr⟩)
      · right
        have hsi : r.val < s := (hsource r).mp hsr
        have htnot : ¬r.val < t := by
          intro hri
          exact (not_le_of_gt htr) ((htarget r).mpr hri)
        exact ⟨Nat.le_of_not_gt htnot, hsi⟩
      · left
        have hti : r.val < t := (htarget r).mp htr
        have hsnot : ¬r.val < s := by
          intro hri
          exact (not_le_of_gt hsr) ((hsource r).mpr hri)
        exact ⟨Nat.le_of_not_gt hsnot, hti⟩
    · rintro (⟨hlo, hhi⟩ | ⟨hlo, hhi⟩)
      · right
        have htr : sample.graphTargetIntersectionAtRank graph r ≤ H :=
          (htarget r).mpr hhi
        have hsr : H < sample.graphSourceIntersectionAtRank graph r := by
          apply lt_of_not_ge
          intro hle
          have hsi : r.val < s := (hsource r).mp hle
          omega
        exact ⟨htr, hsr⟩
      · left
        have hsr : sample.graphSourceIntersectionAtRank graph r ≤ H :=
          (hsource r).mpr hhi
        have htr : H < sample.graphTargetIntersectionAtRank graph r := by
          apply lt_of_not_ge
          intro hle
          have hti : r.val < t := (htarget r).mp hle
          omega
        exact ⟨hsr, htr⟩
  by_cases hst : s ≤ t
  · have hset : sample.graphCrossingRankSet graph H =
        Finset.univ.filter fun r : Fin n => s ≤ r.val ∧ r.val < t := by
      ext r
      simp only [hcross, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [graphCrossingRankCount, hset, card_fin_filter_val_interval htle]
    unfold graphRankCountDiscrepancy
    have hnat : Int.natAbs ((s : ℤ) - (t : ℤ)) = t - s := by
      rw [natAbs_int_sub_natCast]
      by_cases hts : t ≤ s
      · have hEq : t = s := Nat.le_antisymm hts hst
        simp [hEq]
      · simp [hts]
    simpa [s, t] using hnat.symm
  · have hts : t ≤ s := Nat.le_of_lt (lt_of_not_ge hst)
    have hset : sample.graphCrossingRankSet graph H =
        Finset.univ.filter fun r : Fin n => t ≤ r.val ∧ r.val < s := by
      ext r
      simp only [hcross, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [graphCrossingRankCount, hset, card_fin_filter_val_interval hsle]
    unfold graphRankCountDiscrepancy
    have hnat : Int.natAbs ((s : ℤ) - (t : ℤ)) = s - t := by
      rw [natAbs_int_sub_natCast]
      simp [hts]
    simpa [s, t] using hnat.symm

/-! ## Backward windows and the left endpoint of crossing ranks -/

private theorem graphSourceCut_eq_below_add_window {lam : ℝ}
    (graph : FeedbackGraph lam) (H L : ℝ) (hL : 0 ≤ L) :
    sample.graphSourceCutCount graph H =
      sample.graphSourceBelowCount graph (H - L) +
        sample.graphSourceBackwardWindowCount graph H L := by
  let cut : Finset (Fin n) := Finset.univ.filter fun i =>
    sample.sourceIntersection graph i ≤ H
  let below : Finset (Fin n) := Finset.univ.filter fun i =>
    sample.sourceIntersection graph i < H - L
  let window : Finset (Fin n) := Finset.univ.filter fun i =>
    H - L ≤ sample.sourceIntersection graph i ∧
      sample.sourceIntersection graph i ≤ H
  have hpart : cut = below ∪ window := by
    apply Finset.ext
    intro i
    simp only [cut, below, window, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    by_cases hi : sample.sourceIntersection graph i < H - L
    · have hil : sample.sourceIntersection graph i ≤ H :=
        le_trans (le_of_lt hi) (by linarith)
      simp [hi, hil]
    · have hil : H - L ≤ sample.sourceIntersection graph i := le_of_not_gt hi
      constructor
      · intro hcut
        exact Or.inr (And.intro hil hcut)
      · intro h
        rcases h with hi | hw
        · exact False.elim ((not_lt_of_ge hil) hi)
        · exact hw.2
  have hdisj : Disjoint below window := by
    rw [Finset.disjoint_left]
    intro i hi hj
    have hi' : sample.sourceIntersection graph i < H - L := by
      simpa [below] using hi
    have hj' : H - L ≤ sample.sourceIntersection graph i ∧
        sample.sourceIntersection graph i ≤ H := by
      simpa [window] using hj
    exact (not_lt_of_ge hj'.1) hi'
  calc
    sample.graphSourceCutCount graph H = cut.card := rfl
    _ = (below ∪ window).card := by rw [← hpart]
    _ = below.card + window.card := Finset.card_union_of_disjoint hdisj
    _ = sample.graphSourceBelowCount graph (H - L) +
        sample.graphSourceBackwardWindowCount graph H L := by rfl

private theorem graphTargetCut_eq_below_add_window {lam : ℝ}
    (graph : FeedbackGraph lam) (H L : ℝ) (hL : 0 ≤ L) :
    sample.graphTargetCutCount graph H =
      sample.graphTargetBelowCount graph (H - L) +
        sample.graphTargetBackwardWindowCount graph H L := by
  let cut : Finset (Fin n) := Finset.univ.filter fun j =>
    sample.targetIntersection graph j ≤ H
  let below : Finset (Fin n) := Finset.univ.filter fun j =>
    sample.targetIntersection graph j < H - L
  let window : Finset (Fin n) := Finset.univ.filter fun j =>
    H - L ≤ sample.targetIntersection graph j ∧
      sample.targetIntersection graph j ≤ H
  have hpart : cut = below ∪ window := by
    apply Finset.ext
    intro j
    simp only [cut, below, window, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    by_cases hj : sample.targetIntersection graph j < H - L
    · have hjl : sample.targetIntersection graph j ≤ H :=
        le_trans (le_of_lt hj) (by linarith)
      simp [hj, hjl]
    · have hjl : H - L ≤ sample.targetIntersection graph j := le_of_not_gt hj
      constructor
      · intro hcut
        exact Or.inr (And.intro hjl hcut)
      · intro h
        rcases h with hj | hjw
        · exact False.elim ((not_lt_of_ge hjl) hj)
        · exact hjw.2
  have hdisj : Disjoint below window := by
    rw [Finset.disjoint_left]
    intro j hj hjw
    have hj' : sample.targetIntersection graph j < H - L := by
      simpa [below] using hj
    have hjw' : H - L ≤ sample.targetIntersection graph j ∧
        sample.targetIntersection graph j ≤ H := by
      simpa [window] using hjw
    exact (not_lt_of_ge hjw'.1) hj'
  calc
    sample.graphTargetCutCount graph H = cut.card := rfl
    _ = (below ∪ window).card := by rw [← hpart]
    _ = below.card + window.card := Finset.card_union_of_disjoint hdisj
    _ = sample.graphTargetBelowCount graph (H - L) +
        sample.graphTargetBackwardWindowCount graph H L := by rfl

theorem graphCrossingRank_leftEndpoint_ge_of_backward_windows {lam : ℝ}
    (graph : FeedbackGraph lam) (H L : ℝ)
    (hL : 0 ≤ L)
    (hsource : sample.graphCrossingRankCount graph H ≤
      sample.graphSourceBackwardWindowCount graph H L)
    (htarget : sample.graphCrossingRankCount graph H ≤
      sample.graphTargetBackwardWindowCount graph H L)
    (r : Fin n) (hr : r ∈ sample.graphCrossingRankSet graph H) :
    H - L ≤ sample.graphRankLeftEndpoint graph r := by
  let s := sample.graphSourceCutCount graph H
  let t := sample.graphTargetCutCount graph H
  let m := sample.graphCrossingRankCount graph H
  have hdisc := sample.graphCrossingRankCount_eq_rankCountDiscrepancy graph H
  have hsourcePart := sample.graphSourceCut_eq_below_add_window graph H L hL
  have htargetPart := sample.graphTargetCut_eq_below_add_window graph H L hL
  have hsourcePart' : s =
      sample.graphSourceBelowCount graph (H - L) +
        sample.graphSourceBackwardWindowCount graph H L := hsourcePart
  have htargetPart' : t =
      sample.graphTargetBelowCount graph (H - L) +
        sample.graphTargetBackwardWindowCount graph H L := htargetPart
  have hmSource : m ≤ sample.graphSourceBackwardWindowCount graph H L := hsource
  have hmTarget : m ≤ sample.graphTargetBackwardWindowCount graph H L := htarget
  have hsourceRank := sample.graphSourceRank_le_cut_iff graph H r
  have htargetRank := sample.graphTargetRank_le_cut_iff graph H r
  have hcross := sample.graphCrossingRank_iff graph H r |>.mp hr
  by_cases hst : s ≤ t
  · have hdiff : m = t - s := by
      have hnat : Int.natAbs ((s : ℤ) - (t : ℤ)) = t - s := by
        rw [natAbs_int_sub_natCast]
        by_cases hts : t ≤ s
        · have hEq : t = s := Nat.le_antisymm hts hst
          simp [hEq]
        · simp [hts]
      have hdiff' : sample.graphCrossingRankCount graph H = t - s := by
        calc
          sample.graphCrossingRankCount graph H =
              sample.graphRankCountDiscrepancy graph H := hdisc
          _ = Int.natAbs ((s : ℤ) - (t : ℤ)) := by
            rfl
          _ = t - s := hnat
      simpa [m] using hdiff'
    have hbelow :
        sample.graphTargetBelowCount graph (H - L) ≤ s := by
      omega
    have hidx : r.val ≥
        sample.graphTargetBelowCount graph (H - L) := by
      rcases hcross with ⟨hsr, htr⟩ | ⟨htr, hsr⟩
      · have hri : r.val < s := (hsourceRank).mp hsr
        have hnot : ¬r.val < t := by
          intro hri'
          exact (not_le_of_gt htr) ((htargetRank).mpr hri')
        omega
      · have hri : r.val < t := (htargetRank).mp htr
        have hnot : ¬r.val < s := by
          intro hri'
          exact (not_le_of_gt hsr) ((hsourceRank).mpr hri')
        omega
    have htargetLower := sample.graphTargetRank_ge_of_below_count_le
      graph (H - L) r hidx
    have hcrossDir :
        sample.graphTargetIntersectionAtRank graph r ≤ H ∧
          H < sample.graphSourceIntersectionAtRank graph r := by
      rcases (sample.graphCrossingRank_iff graph H r).mp hr with h | h
      · have hri : r.val < s := (hsourceRank).mp h.1
        have hri' : r.val < t := lt_of_lt_of_le hri hst
        exact False.elim ((not_le_of_gt h.2) ((htargetRank).mpr hri'))
      · exact h
    rw [graphRankLeftEndpoint, min_eq_right
      (hcrossDir.1.trans hcrossDir.2.le)]
    exact htargetLower
  · have hts : t ≤ s := Nat.le_of_lt (lt_of_not_ge hst)
    have hdiff : m = s - t := by
      have hnat : Int.natAbs ((s : ℤ) - (t : ℤ)) = s - t := by
        rw [natAbs_int_sub_natCast]
        simp [hts]
      have hdiff' : sample.graphCrossingRankCount graph H = s - t := by
        calc
          sample.graphCrossingRankCount graph H =
              sample.graphRankCountDiscrepancy graph H := hdisc
          _ = Int.natAbs ((s : ℤ) - (t : ℤ)) := by
            rfl
          _ = s - t := hnat
      simpa [m] using hdiff'
    have hbelow :
        sample.graphSourceBelowCount graph (H - L) ≤ t := by
      omega
    have hidx : r.val ≥
        sample.graphSourceBelowCount graph (H - L) := by
      rcases hcross with ⟨hsr, htr⟩ | ⟨htr, hsr⟩
      · have hri : r.val < s := (hsourceRank).mp hsr
        have hnot : ¬r.val < t := by
          intro hri'
          exact (not_le_of_gt htr) ((htargetRank).mpr hri')
        omega
      · have hri : r.val < t := (htargetRank).mp htr
        have hnot : ¬r.val < s := by
          intro hri'
          exact (not_le_of_gt hsr) ((hsourceRank).mpr hri')
        omega
    have hsourceLower := sample.graphSourceRank_ge_of_below_count_le
      graph (H - L) r hidx
    have hcrossDir :
        sample.graphSourceIntersectionAtRank graph r ≤ H ∧
          H < sample.graphTargetIntersectionAtRank graph r := by
      rcases (sample.graphCrossingRank_iff graph H r).mp hr with h | h
      · exact h
      · have hri : r.val < t := (htargetRank).mp h.1
        have hri' : r.val < s := lt_of_lt_of_le hri hts
        exact False.elim ((not_le_of_gt h.2) ((hsourceRank).mpr hri'))
    rw [graphRankLeftEndpoint, min_eq_left
      (hcrossDir.1.trans hcrossDir.2.le)]
    exact hsourceLower

/-! ## Terminal gap and energy bounds -/

/-- Absolute same-rank gap of a terminal rank. -/
noncomputable def graphTerminalRankGapAbs {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) : ℝ :=
  |sample.graphSameRankGap graph r|

/-- Maximum absolute gap among terminal ranks, with value zero when there are none. -/
noncomputable def graphTerminalMaxAbsGap {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℝ :=
  if h : (sample.graphTerminalRankSet graph H).Nonempty then
    (sample.graphTerminalRankSet graph H).sup' h
      (sample.graphTerminalRankGapAbs graph)
  else 0

/-- Squared terminal gap energy. -/
noncomputable def graphTerminalEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℝ :=
  ∑ r ∈ (sample.graphTerminalRankSet graph H),
    sample.graphSameRankGap graph r ^ 2

theorem graphTerminalMaxAbsGap_nonneg {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) :
    0 ≤ sample.graphTerminalMaxAbsGap graph H := by
  classical
  by_cases h : (sample.graphTerminalRankSet graph H).Nonempty
  · simp only [graphTerminalMaxAbsGap, dite_eq_left h]
    obtain ⟨r, hr⟩ := h
    exact (abs_nonneg _).trans
      (Finset.le_sup' (sample.graphTerminalRankGapAbs graph) hr)
  · simp [graphTerminalMaxAbsGap, h]

theorem graphTerminalEnergy_le_count_mul_maxGap_sq {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) :
    sample.graphTerminalEnergy graph H ≤
      (sample.graphTerminalRankCount graph H : ℝ) *
        sample.graphTerminalMaxAbsGap graph H ^ 2 := by
  classical
  let terminal := sample.graphTerminalRankSet graph H
  by_cases h : terminal.Nonempty
  · have hgap : ∀ r ∈ terminal,
        sample.graphSameRankGap graph r ^ 2 ≤
          sample.graphTerminalMaxAbsGap graph H ^ 2 := by
      intro r hr
      have hle : sample.graphTerminalRankGapAbs graph r ≤
          sample.graphTerminalMaxAbsGap graph H := by
        have h' : (sample.graphTerminalRankSet graph H).Nonempty := by
          simpa [terminal] using h
        have hr' : r ∈ sample.graphTerminalRankSet graph H := by
          simpa [terminal] using hr
        simp only [graphTerminalMaxAbsGap, dite_eq_left h']
        exact Finset.le_sup' (sample.graphTerminalRankGapAbs graph) hr'
      simpa [graphTerminalRankGapAbs, sq_abs] using
        ((sq_le_sq₀ (abs_nonneg _) (sample.graphTerminalMaxAbsGap_nonneg graph H)).mpr
          hle)
    have hsum := Finset.sum_le_card_nsmul terminal
      (fun r => sample.graphSameRankGap graph r ^ 2)
      (sample.graphTerminalMaxAbsGap graph H ^ 2) hgap
    simpa [graphTerminalEnergy, graphTerminalRankCount, terminal,
      nsmul_eq_mul] using hsum
  · have hempty : terminal = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [graphTerminalEnergy, graphTerminalRankCount, terminal, hempty]

theorem graphTerminalEnergy_le_of_count_le_of_maxGap_le
    {lam : ℝ} (graph : FeedbackGraph lam) (H L : ℝ) (M : ℕ)
    (hcount : sample.graphTerminalRankCount graph H ≤ M)
    (hmax : sample.graphTerminalMaxAbsGap graph H ≤ L)
    (hL : 0 ≤ L) :
    sample.graphTerminalEnergy graph H ≤ (M : ℝ) * L ^ 2 := by
  have hcountR : (sample.graphTerminalRankCount graph H : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hcount
  have hmax0 := sample.graphTerminalMaxAbsGap_nonneg graph H
  have hmaxSq : sample.graphTerminalMaxAbsGap graph H ^ 2 ≤ L ^ 2 := by
    exact (sq_le_sq₀ hmax0 hL).mpr hmax
  calc
    sample.graphTerminalEnergy graph H ≤
        (sample.graphTerminalRankCount graph H : ℝ) *
          sample.graphTerminalMaxAbsGap graph H ^ 2 :=
      sample.graphTerminalEnergy_le_count_mul_maxGap_sq graph H
    _ ≤ (M : ℝ) * L ^ 2 := by
      exact mul_le_mul hcountR hmaxSq (by positivity) (by positivity)

private theorem graphRankGapAbs_eq_right_sub_left {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) :
    sample.graphTerminalRankGapAbs graph r =
      sample.graphRankRightEndpoint graph r -
        sample.graphRankLeftEndpoint graph r := by
  unfold graphTerminalRankGapAbs graphSameRankGap graphRankRightEndpoint
    graphRankLeftEndpoint
  exact (max_sub_min_eq_abs _ _).symm

theorem graphTerminalCrossingRank_gap_le_of_bounds {lam : ℝ}
    (graph : FeedbackGraph lam) (H L U : ℝ) (r : Fin n)
    (_hr : r ∈ sample.graphCrossingRankSet graph H)
    (hleft : H - L ≤ sample.graphRankLeftEndpoint graph r)
    (hright : sample.graphRankRightEndpoint graph r ≤ U) :
    sample.graphTerminalRankGapAbs graph r ≤ U - H + L := by
  rw [graphRankGapAbs_eq_right_sub_left]
  linarith

theorem graphTerminalMaxAbsGap_le_of_right_endpoint_le_of_crossing_left_ge
    {lam : ℝ} (graph : FeedbackGraph lam) (H L U : ℝ)
    (hL : 0 ≤ L) (hHU : H ≤ U)
    (hright : ∀ r : Fin n,
      sample.graphRankRightEndpoint graph r ≤ U)
    (hleft : ∀ r ∈ sample.graphCrossingRankSet graph H,
      H - L ≤ sample.graphRankLeftEndpoint graph r) :
    sample.graphTerminalMaxAbsGap graph H ≤ U - H + L := by
  classical
  by_cases hne : (sample.graphTerminalRankSet graph H).Nonempty
  · simp only [graphTerminalMaxAbsGap, dite_eq_left hne]
    apply Finset.sup'_le hne
    intro r hr
    have hterm : H < sample.graphRankRightEndpoint graph r :=
      (sample.graphTerminalRank_iff graph H r).mp hr
    by_cases hcross : r ∈ sample.graphCrossingRankSet graph H
    · exact sample.graphTerminalCrossingRank_gap_le_of_bounds graph H L U r
        hcross (hleft r hcross) (hright r)
    · have hleftH : H < sample.graphRankLeftEndpoint graph r := by
        by_contra hnot
        have hle : sample.graphRankLeftEndpoint graph r ≤ H := le_of_not_gt hnot
        exact hcross (by
          simp only [graphCrossingRankSet, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact ⟨hle, hterm⟩)
      rw [graphRankGapAbs_eq_right_sub_left]
      linarith [hright r, hleftH, hL]
  · simp [graphTerminalMaxAbsGap, hne]
    linarith

theorem graphTerminalMaxAbsGap_le_of_crossing_windows_and_endpoint_bound
    {lam : ℝ} (graph : FeedbackGraph lam) (H L U : ℝ)
    (hL : 0 ≤ L) (hHU : H ≤ U)
    (hright : ∀ r : Fin n,
      sample.graphRankRightEndpoint graph r ≤ U)
    (hsource : sample.graphCrossingRankCount graph H ≤
      sample.graphSourceBackwardWindowCount graph H L)
    (htarget : sample.graphCrossingRankCount graph H ≤
      sample.graphTargetBackwardWindowCount graph H L) :
    sample.graphTerminalMaxAbsGap graph H ≤ U - H + L := by
  apply sample.graphTerminalMaxAbsGap_le_of_right_endpoint_le_of_crossing_left_ge
    graph H L U hL hHU hright
  intro r hr
  exact sample.graphCrossingRank_leftEndpoint_ge_of_backward_windows
    graph H L hL hsource htarget r hr

/-- Freezing the graph after `xR` puts every intersection at or before `n + 2 |q|`.
The bound follows from the original unit-interval coordinates and the two mark ranges. -/
theorem graphRankRightEndpoint_le_of_constant_tail
    {lam : ℝ} (graph : FeedbackGraph lam) (xR q : ℝ)
    (hconstant : ∀ x, xR ≤ x → graph.curve x = q)
    (hxR : xR ≤ (n : ℝ) + 2 * |q|) (r : Fin n) :
    sample.graphRankRightEndpoint graph r ≤ (n : ℝ) + 2 * |q| := by
  have hsource (i : Fin n) :
      sample.sourceIntersection graph i ≤ (n : ℝ) + 2 * |q| := by
    apply (sample.sourceIntersection_le_iff graph i _).mpr
    rw [hconstant _ hxR]
    have hheight : (n : ℝ) * (sample.sourceHeight i : ℝ) ≤ n := by
      simpa using mul_le_mul_of_nonneg_left (sample.sourceHeight i).property.2
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hslope := sample.sourceSlope_mem i
    have hmark : sample.sourceSlope i * q ≤ |q| := by
      calc
        sample.sourceSlope i * q ≤ sample.sourceSlope i * |q| :=
          mul_le_mul_of_nonneg_left (le_abs_self q) hslope.1
        _ ≤ 1 * |q| := mul_le_mul_of_nonneg_right hslope.2 (abs_nonneg q)
        _ = |q| := one_mul _
    unfold sourcePhase
    linarith [abs_nonneg q]
  have htarget (j : Fin n) :
      sample.targetIntersection graph j ≤ (n : ℝ) + 2 * |q| := by
    apply (sample.targetIntersection_le_iff graph j _).mpr
    rw [hconstant _ hxR]
    have hheight : (n : ℝ) * (sample.targetHeight j : ℝ) ≤ n := by
      simpa using mul_le_mul_of_nonneg_left (sample.targetHeight j).property.2
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hslope := sample.targetSlope_mem j
    have hmark : sample.targetSlope j * (-q) ≤ 2 * |q| := by
      calc
        sample.targetSlope j * (-q) ≤ sample.targetSlope j * |q| :=
          mul_le_mul_of_nonneg_left (neg_le_abs q) (zero_le_one.trans hslope.1)
        _ ≤ 2 * |q| := mul_le_mul_of_nonneg_right hslope.2 (abs_nonneg q)
    unfold targetPhase
    linarith
  exact max_le (hsource _) (htarget _)

/-- Deterministic terminal localization and energy from the two backward-window occupations.
Only the probabilistic count and occupation estimates remain to be supplied by the tail layer. -/
theorem graphTerminalEnergy_le_of_constant_tail_and_backward_windows
    {lam : ℝ} (graph : FeedbackGraph lam) (xR q H L : ℝ)
    (hconstant : ∀ x, xR ≤ x → graph.curve x = q)
    (hxR : xR ≤ (n : ℝ) + 2 * |q|) (hH : H ≤ (n : ℝ) + 2 * |q|)
    (hL : 0 ≤ L)
    (hsource : sample.graphCrossingRankCount graph H ≤
      sample.graphSourceBackwardWindowCount graph H L)
    (htarget : sample.graphCrossingRankCount graph H ≤
      sample.graphTargetBackwardWindowCount graph H L) :
    sample.graphTerminalEnergy graph H ≤
      ((sample.graphSourceRightEndpointCount graph H +
        sample.graphTargetRightEndpointCount graph H : ℕ) : ℝ) *
          ((n : ℝ) + 2 * |q| - H + L) ^ 2 := by
  apply sample.graphTerminalEnergy_le_of_count_le_of_maxGap_le
    graph H ((n : ℝ) + 2 * |q| - H + L)
    (sample.graphSourceRightEndpointCount graph H +
      sample.graphTargetRightEndpointCount graph H)
  · exact sample.graphTerminalRankCount_le_rightEndpointCounts graph H
  · exact sample.graphTerminalMaxAbsGap_le_of_crossing_windows_and_endpoint_bound
      graph H L ((n : ℝ) + 2 * |q|) hL hH
      (sample.graphRankRightEndpoint_le_of_constant_tail graph xR q hconstant hxR)
      hsource htarget
  · linarith

end FiniteSample

end OTSelector
