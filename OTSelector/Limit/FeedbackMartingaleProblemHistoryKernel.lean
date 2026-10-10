import OTSelector.Limit.FeedbackMartingaleProblemHistory
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# From conditional observed-history events to the full next-step kernel

The current takes countably many values. Conditional readout laws on fixed-current history
events determine the joint history/next-step law by a disjoint partition over the current.
-/

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped ENNReal

namespace OTSelector.Limit

/-- Fixed-current conditional laws on all measurable history events determine the entire
history-dependent transition kernel. This is an ordinary measure identity on rectangles. -/
theorem map_history_next_eq_compProd_of_cond_laws
    {Ω H E K : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace E]
    [MeasurableSpace K] [Countable K] [MeasurableSingletonClass K]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → H} {Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (current : H → K) (hc : Measurable current) (κ : Kernel K E) [IsMarkovKernel κ]
    (hcond : ∀ (A : Set H), MeasurableSet A → ∀ k,
      (∀ x ∈ A, current x = k) → μ (X ⁻¹' A) ≠ 0 →
      (μ[|X ⁻¹' A]).map Y = κ k) :
    μ.map (fun ω ↦ (X ω, Y ω)) = μ.map X ⊗ₘ κ.comap current hc := by
  classical
  apply Measure.ext_prod
  intro S B hS hB
  let Sk : K → Set H := fun k ↦ S ∩ current ⁻¹' {k}
  have hSk (k : K) : MeasurableSet (Sk k) := hS.inter (hc (measurableSet_singleton k))
  have hdis : Pairwise (fun k l ↦ Disjoint (Sk k) (Sk l)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hkl (hx.2.symm.trans hy.2)
  have hcover : (⋃ k, Sk k) = S := by
    ext x
    simp [Sk]
  have hpiece (k : K) :
      μ.map (fun ω ↦ (X ω, Y ω)) (Sk k ×ˢ B) =
        ∫⁻ x in Sk k, (κ.comap current hc) x B ∂μ.map X := by
    have hstate : ∀ x ∈ Sk k, current x = k := fun _ hx ↦ hx.2
    have hmass : μ (X ⁻¹' Sk k ∩ Y ⁻¹' B) = μ (X ⁻¹' Sk k) * κ k B := by
      by_cases hz : μ (X ⁻¹' Sk k) = 0
      · simp only [hz, zero_mul]
        exact measure_mono_null inter_subset_left hz
      · have hh := congrArg (fun m : Measure E ↦ m B) (hcond (Sk k) (hSk k) k hstate hz)
        rw [Measure.map_apply hY hB, cond_apply (hX (hSk k))] at hh
        calc
          _ = μ (X ⁻¹' Sk k) *
              ((μ (X ⁻¹' Sk k))⁻¹ * μ (X ⁻¹' Sk k ∩ Y ⁻¹' B)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hz (measure_ne_top _ _), one_mul]
          _ = _ := by rw [hh]
    rw [Measure.map_apply (hX.prodMk hY) ((hSk k).prod hB)]
    change μ (X ⁻¹' Sk k ∩ Y ⁻¹' B) = _
    rw [hmass]
    calc
      _ = ∫⁻ _x in Sk k, κ k B ∂μ.map X := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          univ_inter, Measure.map_apply hX (hSk k), mul_comm]
      _ = _ := lintegral_congr_ae (by
        filter_upwards [ae_restrict_mem (hSk k)] with x hx
        simp only [Kernel.comap_apply, hstate x hx])
  have hdisProd : Pairwise (fun k l ↦ Disjoint (Sk k ×ˢ B) (Sk l ×ˢ B)) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact Set.disjoint_left.mp (hdis hkl) hp.1 hq.1
  rw [Measure.compProd_apply_prod hS hB, ← hcover, iUnion_prod_const,
    measure_iUnion hdisProd (fun k ↦ (hSk k).prod hB),
    lintegral_iUnion hSk hdis]
  exact tsum_congr hpiece

/-- The joint finite-history transition identities determine the complete Ionescu--Tulcea
path law on an arbitrary original probability space. -/
theorem map_path_eq_trajMeasure_of_joint_history
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {W : Ω → ℕ → E} (hW : Measurable W)
    (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → E) E)
    [∀ n, IsMarkovKernel (κ n)]
    (hinit : μ.map (fun ω ↦ W ω 0) = ν₀)
    (hstep : ∀ n, μ.map (fun ω ↦ (frestrictLe n (W ω), W ω (n + 1))) =
      μ.map (fun ω ↦ frestrictLe n (W ω)) ⊗ₘ κ n) :
    μ.map W = Kernel.trajMeasure (X := fun _ ↦ E) ν₀ κ := by
  apply TrajectoryProjection.ext_prefix
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) hW]
  simp only [Function.comp_def]
  induction n with
  | zero =>
      have hzero : Measurable (fun ω ↦ W ω 0) := (measurable_pi_apply 0).comp hW
      rw [TrajectoryProjection.trajMeasure_prefix_zero, ← hinit,
        Measure.map_map (MeasurableEquiv.measurable _) hzero]
      congr 1
      funext ω i
      have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.2; omega
      simp [hi]
  | succ n ih =>
      have hpair : Measurable (fun ω ↦ (frestrictLe n (W ω), W ω (n + 1))) :=
        ((measurable_frestrictLe n).comp hW).prodMk ((measurable_pi_apply (n + 1)).comp hW)
      rw [TrajectoryProjection.trajMeasure_prefix_succ, ← ih, ← hstep n,
        Measure.map_map (TrajectoryProjection.measurable_snoc n) hpair]
      simp only [Function.comp_def, TrajectoryProjection.snoc_restrict]

end OTSelector.Limit
