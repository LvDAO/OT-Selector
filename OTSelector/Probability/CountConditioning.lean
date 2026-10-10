import Mathlib.Data.Finset.Sort
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Conditioning iid samples by a membership pattern

Conditioning only on the total number of observations in a set does not leave the original labeled
coordinates independent.  The correct finite decomposition conditions first on the complete
membership pattern.  On each non-null pattern, the coordinates remain independent with their
one-coordinate conditional laws; selected coordinates can then be reindexed by `Fin k`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.CountConditioning

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Set prescribed for coordinate `i` by a membership pattern `J`. -/
def patternCoordinateSet {n : ℕ} (A : Set Ω) (J : Finset (Fin n)) (i : Fin n) : Set Ω :=
  if i ∈ J then A else Aᶜ

/-- Samples whose coordinates belong to `A` exactly at the indices in `J`. -/
def membershipPattern {n : ℕ} (A : Set Ω) (J : Finset (Fin n)) : Set (Fin n → Ω) :=
  Set.univ.pi (patternCoordinateSet A J)

/-- Number of sample coordinates lying in `A`. -/
noncomputable def sampleSetCount {n : ℕ} (A : Set Ω) (sample : Fin n → Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun i ↦ sample i ∈ A).card

theorem measurableSet_patternCoordinateSet {n : ℕ} {A : Set Ω} (hA : MeasurableSet A)
    (J : Finset (Fin n)) (i : Fin n) : MeasurableSet (patternCoordinateSet A J i) := by
  by_cases hi : i ∈ J <;> simp [patternCoordinateSet, hi, hA, hA.compl]

theorem measurableSet_membershipPattern {n : ℕ} {A : Set Ω} (hA : MeasurableSet A)
    (J : Finset (Fin n)) : MeasurableSet (membershipPattern A J) := by
  exact MeasurableSet.univ_pi fun i ↦ measurableSet_patternCoordinateSet hA J i

omit [MeasurableSpace Ω] in theorem mem_membershipPattern_iff {n : ℕ} {A : Set Ω}
    {J : Finset (Fin n)}
    {sample : Fin n → Ω} :
    sample ∈ membershipPattern A J ↔ ∀ i, (sample i ∈ A ↔ i ∈ J) := by
  constructor
  · intro hs i
    have hi := Set.mem_pi.mp hs i (Set.mem_univ i)
    by_cases hJ : i ∈ J
    · simp [patternCoordinateSet, hJ] at hi
      exact ⟨fun _ ↦ hJ, fun _ ↦ hi⟩
    · simp [patternCoordinateSet, hJ] at hi
      exact ⟨fun hA ↦ (hi hA).elim, fun h ↦ (hJ h).elim⟩
  · intro hs
    apply Set.mem_pi.mpr
    intro i _
    by_cases hJ : i ∈ J
    · simpa [patternCoordinateSet, hJ] using (hs i).mpr hJ
    · have hnot : sample i ∉ A := fun hA ↦ hJ ((hs i).mp hA)
      simpa [patternCoordinateSet, hJ] using hnot

omit [MeasurableSpace Ω] in theorem membershipPattern_eq_iInter {n : ℕ} (A : Set Ω)
    (J : Finset (Fin n)) :
    membershipPattern A J =
      ⋂ i, (fun sample : Fin n → Ω ↦ sample i) ⁻¹' patternCoordinateSet A J i := by
  ext sample
  simp [membershipPattern, Set.mem_pi]

omit [MeasurableSpace Ω] in theorem pairwiseDisjoint_membershipPattern {n : ℕ} (A : Set Ω) :
    Pairwise fun J K : Finset (Fin n) ↦
      Disjoint (membershipPattern A J) (membershipPattern A K) := by
  intro J K hJK
  rw [Set.disjoint_left]
  intro sample hJ hK
  have hJeq : J = K := by
    ext i
    exact (mem_membershipPattern_iff.mp hJ i).symm.trans
      (mem_membershipPattern_iff.mp hK i)
  exact hJK hJeq

omit [MeasurableSpace Ω] in theorem iUnion_membershipPattern_eq_univ {n : ℕ} (A : Set Ω) :
    ⋃ J : Finset (Fin n), membershipPattern A J = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro sample
  let J := Finset.univ.filter fun i ↦ sample i ∈ A
  exact Set.mem_iUnion.mpr ⟨J, mem_membershipPattern_iff.mpr fun i ↦ by simp [J]⟩

omit [MeasurableSpace Ω] in theorem sampleSetCount_eq_card_of_mem_membershipPattern
    {n : ℕ} {A : Set Ω}
    {J : Finset (Fin n)} {sample : Fin n → Ω} (hsample : sample ∈ membershipPattern A J) :
    sampleSetCount A sample = J.card := by
  classical
  have hset : Finset.univ.filter (fun i ↦ sample i ∈ A) = J := by
    ext i
    simp [mem_membershipPattern_iff.mp hsample i]
  rw [sampleSetCount, hset]

/-- Increasing reindexing of the coordinates selected by a pattern of cardinality `k`. -/
def selectedCoordinates {n k : ℕ} (J : Finset (Fin n)) (hJ : J.card = k)
    (sample : Fin n → Ω) (j : Fin k) : Ω :=
  sample (J.orderEmbOfFin hJ j)

theorem measurable_selectedCoordinate {n k : ℕ} (J : Finset (Fin n))
    (hJ : J.card = k) (j : Fin k) :
    Measurable (fun sample : Fin n → Ω ↦ selectedCoordinates J hJ sample j) := by
  exact measurable_pi_apply _

/-- The probability of a full membership pattern under the canonical iid product law. -/
theorem measure_membershipPattern {n : ℕ} (P : Measure Ω) [SigmaFinite P] (A : Set Ω)
    (J : Finset (Fin n)) :
    Measure.pi (fun _ : Fin n ↦ P) (membershipPattern A J) =
      ∏ i : Fin n, P (patternCoordinateSet A J i) := by
  rw [membershipPattern, Measure.pi_pi]

/-- A full pattern has positive probability when both sides of `A` have positive probability. -/
theorem measure_membershipPattern_ne_zero {n : ℕ} (P : Measure Ω) [SigmaFinite P] (A : Set Ω)
    (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) :
    Measure.pi (fun _ : Fin n ↦ P) (membershipPattern A J) ≠ 0 := by
  rw [measure_membershipPattern P A J, Finset.prod_ne_zero_iff]
  intro i _
  by_cases hi : i ∈ J <;> simp [patternCoordinateSet, hi, hA0, hAc0]

private theorem eval_preimage_patternCoordinateSet_ne_zero
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (i : Fin n) :
    Measure.pi (fun _ : Fin n ↦ P)
      ((fun sample : Fin n → Ω ↦ sample i) ⁻¹' patternCoordinateSet A J i) ≠ 0 := by
  have hset : MeasurableSet (patternCoordinateSet A J i) :=
    measurableSet_patternCoordinateSet hA J i
  rw [← Measure.map_apply (measurable_pi_apply i) hset,
    (measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq]
  by_cases hi : i ∈ J <;> simp [patternCoordinateSet, hi, hA0, hAc0]

private theorem measure_pi_eval_preimage
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (i : Fin n) (s : Set Ω) (hs : MeasurableSet s) :
    Measure.pi (fun _ : Fin n ↦ P) ((fun sample : Fin n → Ω ↦ sample i) ⁻¹' s) = P s := by
  rw [← Measure.map_apply (measurable_pi_apply i) hs,
    (measurePreserving_eval (fun _ : Fin n ↦ P) i).map_eq]

private theorem cond_pi_eval_preimage
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (i : Fin n) (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (Measure.pi (fun _ : Fin n ↦ P))[
        (fun sample : Fin n → Ω ↦ sample i) ⁻¹' s |
        (fun sample : Fin n → Ω ↦ sample i) ⁻¹' t] = P[s | t] := by
  rw [cond_apply (ht.preimage (measurable_pi_apply i)), cond_apply ht,
    measure_pi_eval_preimage P i t ht, ← Set.preimage_inter,
    measure_pi_eval_preimage P i (t ∩ s) (ht.inter hs)]

private theorem cond_eval_eq_cond_coordinate
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (i : Fin n) (s : Set Ω) (hs : MeasurableSet s) :
    (Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]
        ((fun sample : Fin n → Ω ↦ sample i) ⁻¹' s) =
      P[s | patternCoordinateSet A J i] := by
  let μ := Measure.pi (fun _ : Fin n ↦ P)
  let Y : Fin n → (Fin n → Ω) → Ω := fun i sample ↦ sample i
  have hY : ∀ i, Measurable (Y i) := fun i ↦ measurable_pi_apply i
  have hpair : iIndepFun (fun i sample ↦ (Y i sample, Y i sample)) μ := by
    exact (iIndepFun_pi fun _ ↦ measurable_id.aemeasurable).comp
      (fun _ z ↦ (z, z)) fun _ ↦ measurable_id.prodMk measurable_id
  have hcond := cond_iInter (μ := μ) (X := Y) (Y := Y)
    (f := fun j ↦ if j = i then Y j ⁻¹' s else Set.univ)
    (t := patternCoordinateSet A J) hY hpair (s := {i})
    (fun j hj ↦ by
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      rw [ite_eq_left rfl]
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨s, hs, rfl⟩)
    (fun j _ ↦ eval_preimage_patternCoordinateSet_ne_zero P A hA hA0 hAc0 J j)
    (fun j ↦ measurableSet_patternCoordinateSet hA J j)
  calc
    (Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]
        ((fun sample : Fin n → Ω ↦ sample i) ⁻¹' s) =
        μ[(fun sample ↦ sample i) ⁻¹' s |
          ⋂ j, Y j ⁻¹' patternCoordinateSet A J j] := by
            rw [membershipPattern_eq_iInter]
    _ = μ[(fun sample ↦ sample i) ⁻¹' s |
        (fun sample ↦ sample i) ⁻¹' patternCoordinateSet A J i] := by
      simpa [μ, Y] using hcond
    _ = P[s | patternCoordinateSet A J i] := by
      exact cond_pi_eval_preimage P i s (patternCoordinateSet A J i) hs
        (measurableSet_patternCoordinateSet hA J i)

/-- Under a non-null full pattern, all labeled coordinates remain independent. -/
theorem eval_iIndep_cond_membershipPattern
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) :
    iIndepFun (fun i (sample : Fin n → Ω) ↦ sample i)
      ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]) := by
  let μ := Measure.pi (fun _ : Fin n ↦ P)
  let Y : Fin n → (Fin n → Ω) → Ω := fun i sample ↦ sample i
  have hY : ∀ i, Measurable (Y i) := fun i ↦ measurable_pi_apply i
  have hpair : iIndepFun (fun i sample ↦ (Y i sample, Y i sample)) μ := by
    exact (iIndepFun_pi fun _ ↦ measurable_id.aemeasurable).comp
      (fun _ z ↦ (z, z)) fun _ ↦ measurable_id.prodMk measurable_id
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hcond := cond_iInter (μ := μ) (X := Y) (Y := Y)
    (f := fun i ↦ Y i ⁻¹' sets i) (t := patternCoordinateSet A J)
    hY hpair (s := S)
    (fun i hi ↦ by
      rw [MeasurableSpace.measurableSet_comap]
      exact ⟨sets i, hsets i hi, rfl⟩)
    (fun i _ ↦ eval_preimage_patternCoordinateSet_ne_zero P A hA hA0 hAc0 J i)
    (fun i ↦ measurableSet_patternCoordinateSet hA J i)
  calc
    (μ[|membershipPattern A J]) (⋂ i ∈ S, Y i ⁻¹' sets i) =
        μ[⋂ i ∈ S, Y i ⁻¹' sets i |
          ⋂ i, Y i ⁻¹' patternCoordinateSet A J i] := by
            rw [membershipPattern_eq_iInter]
    _ = ∏ i ∈ S, μ[Y i ⁻¹' sets i |
        Y i ⁻¹' patternCoordinateSet A J i] := hcond
    _ = ∏ i ∈ S, P[sets i | patternCoordinateSet A J i] := by
      apply Finset.prod_congr rfl
      intro i hi
      exact cond_pi_eval_preimage P i (sets i) (patternCoordinateSet A J i) (hsets i hi)
        (measurableSet_patternCoordinateSet hA J i)
    _ = ∏ i ∈ S, (μ[|membershipPattern A J]) (Y i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [cond_eval_eq_cond_coordinate P A hA hA0 hAc0 J i (sets i) (hsets i hi)]

/-- Marginal law of one coordinate under a full membership pattern. -/
theorem map_eval_cond_membershipPattern
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (i : Fin n) :
    ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
        (fun sample : Fin n → Ω ↦ sample i) = P[|patternCoordinateSet A J i] := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  exact cond_eval_eq_cond_coordinate P A hA hA0 hAc0 J i s hs

/-- Selected coordinates are iid with law `P[|A]` on a full pattern. -/
theorem selectedCoordinates_iIndep_cond_membershipPattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) :
    iIndepFun (fun j sample ↦ selectedCoordinates J hJ sample j)
      ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]) := by
  exact (eval_iIndep_cond_membershipPattern P A hA hA0 hAc0 J).precomp
    (J.orderEmbOfFin hJ).injective

/-- Every selected coordinate has the conditional law `P[|A]`. -/
theorem map_selectedCoordinate_cond_membershipPattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (j : Fin k) :
    ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
        (fun sample ↦ selectedCoordinates J hJ sample j) = P[|A] := by
  change ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
      (fun sample : Fin n → Ω ↦ sample (J.orderEmbOfFin hJ j)) = P[|A]
  have hmap := map_eval_cond_membershipPattern P A hA hA0 hAc0 J
    (J.orderEmbOfFin hJ j)
  simpa [patternCoordinateSet, Finset.orderEmbOfFin_mem] using hmap

/-- Assemble one event for each full membership pattern.  This is the correct finite mixture used
after applying an iid estimate to the selected coordinates on each pattern. -/
def patternwiseEvent {n : ℕ} (A : Set Ω)
    (event : Finset (Fin n) → Set (Fin n → Ω)) : Set (Fin n → Ω) :=
  ⋃ J, membershipPattern A J ∩ event J

/-- The probabilities of all full membership patterns sum to one. -/
theorem sum_measure_membershipPattern_eq_one
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) :
    ∑' J : Finset (Fin n), Measure.pi (fun _ : Fin n ↦ P) (membershipPattern A J) = 1 := by
  let μ := Measure.pi (fun _ : Fin n ↦ P)
  rw [← measure_iUnion (pairwiseDisjoint_membershipPattern A)
    (fun J ↦ measurableSet_membershipPattern hA J), iUnion_membershipPattern_eq_univ,
    measure_univ]

/-- A uniform conditional tail bound on every full pattern survives mixing over the patterns.
No independence assertion is made after conditioning only on the total count. -/
theorem measure_patternwiseEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (event : Finset (Fin n) → Set (Fin n → Ω)) (δ : ℝ≥0∞)
    (htail : ∀ J,
      (Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J] (event J) ≤ δ) :
    Measure.pi (fun _ : Fin n ↦ P) (patternwiseEvent A event) ≤ δ := by
  classical
  let μ := Measure.pi (fun _ : Fin n ↦ P)
  calc
    μ (patternwiseEvent A event) ≤ ∑' J, μ (membershipPattern A J ∩ event J) := by
      exact measure_iUnion_le _
    _ = ∑' J : Finset (Fin n),
        (μ[|membershipPattern A J]) (event J) * μ (membershipPattern A J) := by
      apply tsum_congr
      intro J
      exact (cond_mul_eq_inter (measurableSet_membershipPattern hA J) (event J) μ).symm
    _ ≤ ∑' J : Finset (Fin n), δ * μ (membershipPattern A J) := by
      exact ENNReal.tsum_le_tsum fun J ↦ by
        simpa [mul_comm] using
          (mul_right_mono (a := μ (membershipPattern A J)) (htail J))
    _ = δ * ∑' J : Finset (Fin n), μ (membershipPattern A J) :=
      ENNReal.tsum_mul_left
    _ = δ := by
      rw [sum_measure_membershipPattern_eq_one P A hA, mul_one]

end OTSelector.CountConditioning
