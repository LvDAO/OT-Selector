import OTSelector.Limit.FeedbackRegeneration
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Joint exponential-holding and jump trajectories

At each current, the next waiting time and next current are sampled from the product of the actual
exponential waiting law and the feedback jump law. Ionescu--Tulcea then constructs the entire
sequence of waiting times and currents. Coordinate zero is the initial pair `(0, k)`;
coordinate `n + 1` records the wait at current `n` followed by the new current.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal ProbabilityTheory

namespace OTSelector.Limit

/-- One physical jump: first wait at the present current, then choose its neighboring current. -/
noncomputable def feedbackHoldingJumpKernel (lam : ℝ) : Kernel ℤ (ℝ × ℤ) where
  toFun k := (feedbackHoldingKernel lam k).prod (feedbackJumpKernel lam k)
  measurable' := measurable_of_countable _

theorem feedbackHoldingJumpKernel_isMarkov {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackHoldingJumpKernel lam) := by
  let := feedbackHoldingKernel_isMarkov hlam₀ hlam
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  constructor
  intro k
  change IsProbabilityMeasure ((feedbackHoldingKernel lam k).prod (feedbackJumpKernel lam k))
  infer_instance

/-- Rectangle probabilities express the actual independence of the wait and the jump direction. -/
theorem feedbackHoldingJumpKernel_rectangle {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (s : Set ℝ) (t : Set ℤ) :
    feedbackHoldingJumpKernel lam k (s ×ˢ t) =
      expMeasure (totalJumpRate lam k) s * feedbackJumpKernel lam k t := by
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  exact Measure.prod_prod _ _

theorem feedbackHoldingJumpKernel_indep {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    IndepFun Prod.fst Prod.snd (feedbackHoldingJumpKernel lam k) := by
  let := feedbackHoldingKernel_isMarkov hlam₀ hlam
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- The waiting coordinate has the exponential law with the correct state-dependent rate. -/
theorem feedbackHoldingJumpKernel_map_wait {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackHoldingJumpKernel lam k).map Prod.fst = expMeasure (totalJumpRate lam k) := by
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  change ((feedbackHoldingKernel lam k).prod (feedbackJumpKernel lam k)).map Prod.fst = _
  simp [feedbackHoldingKernel]

/-- The current coordinate has exactly the previously constructed jump kernel. -/
theorem feedbackHoldingJumpKernel_map_current {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackHoldingJumpKernel lam k).map Prod.snd = feedbackJumpKernel lam k := by
  let := feedbackHoldingKernel_isMarkov hlam₀ hlam
  change ((feedbackHoldingKernel lam k).prod (feedbackJumpKernel lam k)).map Prod.snd = _
  simp

/-- The holding law gives no mass to a zero or negative waiting time. -/
theorem feedbackHoldingKernel_nonpositive {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : feedbackHoldingKernel lam k (Set.Iic 0) = 0 := by
  let := isProbabilityMeasure_expMeasure (totalJumpRate_pos hlam₀ hlam k)
  change expMeasure (totalJumpRate lam k) (Set.Iic 0) = 0
  rw [← ofReal_cdf, cdf_expMeasure_eq (totalJumpRate_pos hlam₀ hlam k)]
  simp

/-- The constructed joint transition has a strictly positive physical waiting time almost surely. -/
theorem feedbackHoldingJumpKernel_positive_wait {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    feedbackHoldingJumpKernel lam k (Set.Ioi 0 ×ˢ Set.univ) = 1 := by
  let := feedbackHoldingKernel_isMarkov hlam₀ hlam
  let := feedbackJumpKernel_isMarkov hlam₀ hlam
  rw [feedbackHoldingJumpKernel_rectangle hlam₀ hlam, measure_univ, mul_one]
  change feedbackHoldingKernel lam k (Set.Ioi 0) = 1
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
    feedbackHoldingKernel_nonpositive hlam₀ hlam, tsub_zero]

/-- A history determines the next physical step through its current coordinate. -/
noncomputable def feedbackHoldingJumpHistoryKernel (lam : ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ℝ × ℤ) (ℝ × ℤ) :=
  (feedbackHoldingJumpKernel lam).comap
    (fun x ↦ (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2) (by fun_prop)

theorem feedbackHoldingJumpHistoryKernel_isMarkov {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) : IsMarkovKernel (feedbackHoldingJumpHistoryKernel lam n) := by
  let := feedbackHoldingJumpKernel_isMarkov hlam₀ hlam
  unfold feedbackHoldingJumpHistoryKernel
  infer_instance

/-- The joint infinite sequence of physical waiting times and visited currents, from current `k`. -/
noncomputable def feedbackHoldingJumpTrajectory (lam : ℝ) (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : Measure (ℕ → ℝ × ℤ) := by
  let := feedbackHoldingJumpHistoryKernel_isMarkov hlam₀ hlam
  exact Kernel.trajMeasure (X := fun _ ↦ ℝ × ℤ) (Measure.dirac (0, k))
    (feedbackHoldingJumpHistoryKernel lam)

instance feedbackHoldingJumpTrajectory_isProbability {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    IsProbabilityMeasure (feedbackHoldingJumpTrajectory lam hlam₀ hlam k) := by
  let := feedbackHoldingJumpHistoryKernel_isMarkov hlam₀ hlam
  unfold feedbackHoldingJumpTrajectory
  infer_instance

/-- At every finite time its conditional next-step law is the actual product law. -/
theorem feedbackHoldingJumpTrajectory_condDistrib {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    condDistrib (fun x : ℕ → ℝ × ℤ ↦ x (n + 1)) (frestrictLe n)
      (feedbackHoldingJumpTrajectory lam hlam₀ hlam k) =ᵐ[
        (feedbackHoldingJumpTrajectory lam hlam₀ hlam k).map (frestrictLe n)]
          feedbackHoldingJumpHistoryKernel lam n := by
  let := feedbackHoldingJumpHistoryKernel_isMarkov hlam₀ hlam
  exact Kernel.condDistrib_trajMeasure (X := fun _ ↦ ℝ × ℤ)

/-- The first physical step is distributed according to the current's explicit product law. -/
theorem feedbackHoldingJumpTrajectory_map_one {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackHoldingJumpTrajectory lam hlam₀ hlam k).map (fun x ↦ x 1) =
      feedbackHoldingJumpKernel lam k := by
  let := feedbackHoldingJumpHistoryKernel_isMarkov hlam₀ hlam
  unfold feedbackHoldingJumpTrajectory Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply _), Kernel.map_traj_succ_self,
    Measure.map_dirac' (by fun_prop), Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- From current zero, the first actual waiting time is exponential of rate two. -/
theorem feedbackHoldingJumpTrajectory_zero_wait {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackHoldingJumpTrajectory lam hlam₀ hlam 0).map (fun x ↦ (x 1).1) =
      expMeasure 2 := by
  rw [show (fun x : ℕ → ℝ × ℤ ↦ (x 1).1) = Prod.fst ∘ (fun x ↦ x 1) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    feedbackHoldingJumpTrajectory_map_one hlam₀ hlam,
    feedbackHoldingJumpKernel_map_wait hlam₀ hlam, totalJumpRate_zero]

end OTSelector.Limit
