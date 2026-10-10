import OTSelector.Limit.FeedbackMarkedHolding
import OTSelector.Limit.FeedbackRegenerationNonexplosion
import OTSelector.Limit.FeedbackRegenerationReturnPhysical

/-!
# Actual marked feedback trajectories and their physical projection

Ionescu--Tulcea constructs the marked process from the real holding/mark/current transition.
Its physical projection has exactly the existing holding/current trajectory law, so nonexplosion
and return statements transfer along this measurable projection.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal

namespace OTSelector.Limit

namespace TrajectoryProjection

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

/-- Coordinatewise maps commute with one step of a history-dependent transition. -/
theorem map_compProd (μ : Measure A) [SFinite μ] (κ : Kernel A B)
    [IsSFiniteKernel κ] (η : Kernel C D) [IsSFiniteKernel η]
    {f : A → C} {g : B → D} (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x, (κ x).map g = η (f x)) :
    (μ ⊗ₘ κ).map (Prod.map f g) = μ.map f ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs, Measure.compProd_apply ((hf.prodMap hg) hs),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro x
  rw [← h x, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

/-- Append a single coordinate to a finite history. -/
def snoc (n : ℕ) (p : ((i : Finset.Iic n) → A) × A) (i : Finset.Iic (n + 1)) : A :=
  if h : i.val ≤ n then p.1 ⟨i.val, Finset.mem_Iic.mpr h⟩ else p.2

@[fun_prop]
theorem measurable_snoc (n : ℕ) : Measurable (snoc (A := A) n) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i.val ≤ n <;> simp only [snoc, h, ↓reduceDIte] <;> fun_prop

omit [MeasurableSpace A] in
@[simp]
theorem snoc_restrict (n : ℕ) (x : ℕ → A) :
    snoc n (frestrictLe n x, x (n + 1)) = frestrictLe (n + 1) x := by
  funext i
  dsimp [snoc]
  split_ifs with h
  · rfl
  · have hi : i.val = n + 1 := by have := Finset.mem_Iic.mp i.2; omega
    simp [hi]

/-- A finite trajectory marginal grows by its actual next-step transition. -/
theorem trajMeasure_prefix_succ (μ : Measure A) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.trajMeasure (X := fun _ ↦ A) μ κ).map (frestrictLe (n + 1)) =
      (((Kernel.trajMeasure (X := fun _ ↦ A) μ κ).map (frestrictLe n)) ⊗ₘ κ n).map
        (snoc n) := by
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.map_map (measurable_snoc n) (by fun_prop)]
  simp only [Function.comp_def, snoc_restrict]

/-- The initial finite history is just the initial law, as a one-coordinate tuple. -/
theorem trajMeasure_prefix_zero (μ : Measure A)
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    [∀ n, IsMarkovKernel (κ n)] :
    (Kernel.trajMeasure (X := fun _ ↦ A) μ κ).map (frestrictLe 0) =
      μ.map (MeasurableEquiv.piUnique _).symm := by
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  simp [Kernel.id, Measure.deterministic_comp_eq_map]

/-- Equality on finite initial histories determines the entire trajectory law. -/
theorem ext_prefix {μ ν : Measure (ℕ → A)} [IsFiniteMeasure ν]
    (h : ∀ n, μ.map (frestrictLe n) = ν.map (frestrictLe n)) : μ = ν := by
  let P (I : Finset ℕ) := ν.map I.restrict
  have hν : IsProjectiveLimit ν P := fun _ ↦ rfl
  apply IsProjectiveLimit.unique (P := P) (hν := hν)
  intro I
  let N := I.sup id
  have hI : I ⊆ Finset.Iic N := I.subset_Iic_sup_id
  rw [← Finset.restrict₂_comp_restrict hI]
  change μ.map (Finset.restrict₂ hI ∘ frestrictLe N) = _
  rw [← Measure.map_map (Finset.measurable_restrict₂ hI) (measurable_frestrictLe N)]
  rw [h N, Measure.map_map (Finset.measurable_restrict₂ hI) (measurable_frestrictLe N)]
  change ν.map (Finset.restrict₂ hI ∘ (Finset.Iic N).restrict) = _
  rw [Finset.restrict₂_comp_restrict hI]

/-- An actual one-step kernel projection determines the projection of its entire trajectory. -/
theorem trajMeasure_map (μ : Measure A) [IsProbabilityMeasure μ]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (κ : (n : ℕ) → Kernel ((i : Finset.Iic n) → A) A)
    (η : (n : ℕ) → Kernel ((i : Finset.Iic n) → B) B)
    [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]
    {f : A → B} (hf : Measurable f) (hinit : μ.map f = ν)
    (hstep : ∀ n x, (κ n x).map f = η n (fun i ↦ f (x i))) :
    (Kernel.trajMeasure (X := fun _ ↦ A) μ κ).map (fun w n ↦ f (w n)) =
      Kernel.trajMeasure (X := fun _ ↦ B) ν η := by
  have hfN (n : ℕ) : Measurable (fun x : (i : Finset.Iic n) → A ↦ fun i ↦ f (x i)) := by
    fun_prop
  have hprefix (n : ℕ) :
      ((Kernel.trajMeasure (X := fun _ ↦ A) μ κ).map (frestrictLe n)).map
        (fun x i ↦ f (x i)) =
      (Kernel.trajMeasure (X := fun _ ↦ B) ν η).map (frestrictLe n) := by
    induction n with
    | zero =>
        rw [trajMeasure_prefix_zero, trajMeasure_prefix_zero,
          Measure.map_map (hfN 0) (MeasurableEquiv.measurable _), ← hinit,
          Measure.map_map (MeasurableEquiv.measurable _) hf]
        rfl
    | succ n ih =>
        rw [trajMeasure_prefix_succ, trajMeasure_prefix_succ,
          Measure.map_map (hfN (n + 1)) (measurable_snoc n)]
        have hcomm : (fun x : (i : Finset.Iic (n + 1)) → A ↦ fun i ↦ f (x i)) ∘ snoc n =
            snoc n ∘ Prod.map (fun x : (i : Finset.Iic n) → A ↦ fun i ↦ f (x i)) f := by
          funext p i
          dsimp [snoc]
          split_ifs <;> rfl
        rw [hcomm, ← Measure.map_map (measurable_snoc n) ((hfN n).prodMap hf),
          map_compProd _ (κ n) (η n) (hfN n) hf (hstep n), ih]
  apply ext_prefix
  intro n
  rw [Measure.map_map (measurable_frestrictLe n) (by fun_prop)]
  change (Kernel.trajMeasure (X := fun _ ↦ A) μ κ).map
    ((fun x : (i : Finset.Iic n) → A ↦ fun i ↦ f (x i)) ∘ frestrictLe (π := fun _ ↦ A) n) = _
  rw [← Measure.map_map (hfN n) (measurable_frestrictLe n)]
  exact hprefix n

end TrajectoryProjection

/-- Forget marks at every coordinate of an infinite physical path. -/
def feedbackMarkedTrajectoryProjection (w : ℕ → FeedbackMarkedStep) : ℕ → ℝ × ℤ :=
  fun n ↦ feedbackMarkedStepProjection (w n)

@[fun_prop]
theorem measurable_feedbackMarkedTrajectoryProjection :
    Measurable feedbackMarkedTrajectoryProjection := by
  unfold feedbackMarkedTrajectoryProjection
  fun_prop

/-- The marked next step depends on the current at the end of the revealed history. -/
noncomputable def feedbackMarkedHistoryKernel (lam : ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → FeedbackMarkedStep) FeedbackMarkedStep :=
  (feedbackMarkedHoldingKernel lam).comap
    (fun x ↦ (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2) (by fun_prop)

theorem feedbackMarkedHistoryKernel_isMarkov {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) : IsMarkovKernel (feedbackMarkedHistoryKernel lam n) := by
  let := feedbackMarkedHoldingKernel_isMarkov hlam0 hlam
  unfold feedbackMarkedHistoryKernel
  infer_instance

/-- Actual marked physical trajectory, with virtual initial wait and mark both zero. -/
noncomputable def feedbackMarkedTrajectory (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) : Measure (ℕ → FeedbackMarkedStep) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  exact Kernel.trajMeasure (X := fun _ ↦ FeedbackMarkedStep)
    (Measure.dirac (0, ⟨0, by simp⟩, k)) (feedbackMarkedHistoryKernel lam)

instance feedbackMarkedTrajectory_isProbability {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    IsProbabilityMeasure (feedbackMarkedTrajectory lam hlam0 hlam k) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  unfold feedbackMarkedTrajectory
  infer_instance

/-- The finite marked history determines the next step by the constructed physical kernel. -/
theorem feedbackMarkedTrajectory_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    condDistrib (fun w : ℕ → FeedbackMarkedStep ↦ w (n + 1)) (frestrictLe n)
      (feedbackMarkedTrajectory lam hlam0 hlam k) =ᵐ[
        (feedbackMarkedTrajectory lam hlam0 hlam k).map (frestrictLe n)]
          feedbackMarkedHistoryKernel lam n := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  exact Kernel.condDistrib_trajMeasure (X := fun _ ↦ FeedbackMarkedStep)

/-- The first real step has the stated holding/mark/current kernel; coordinate zero is virtual. -/
theorem feedbackMarkedTrajectory_map_one {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ w 1) =
      feedbackMarkedHoldingKernel lam k := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  unfold feedbackMarkedTrajectory Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply _), Kernel.map_traj_succ_self,
    Measure.map_dirac' (by fun_prop), Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- Forgetting all marks gives precisely the already constructed physical trajectory law. -/
theorem feedbackMarkedTrajectory_map {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    (feedbackMarkedTrajectory lam hlam0 hlam k).map feedbackMarkedTrajectoryProjection =
      feedbackHoldingJumpTrajectory lam hlam0 hlam k := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  let := feedbackHoldingJumpHistoryKernel_isMarkov hlam0 hlam
  unfold feedbackMarkedTrajectory feedbackHoldingJumpTrajectory feedbackMarkedTrajectoryProjection
  apply TrajectoryProjection.trajMeasure_map _ _ _ _ measurable_feedbackMarkedStepProjection
  · rw [Measure.map_dirac' measurable_feedbackMarkedStepProjection]
    rfl
  · intro n x
    exact feedbackMarkedHoldingKernel_map_step hlam0 hlam _

/-- Marks do not change the nonexplosion of the actual physical clock. -/
theorem feedbackMarkedTrajectory_nonexplosion {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam k,
      Tendsto (fun n ↦ feedbackJumpTime n (feedbackMarkedTrajectoryProjection w)) atTop atTop := by
  have h := feedbackHoldingJumpTrajectory_nonexplosion hlam0 hlam k
  rw [← feedbackMarkedTrajectory_map hlam0 hlam k] at h
  exact ae_of_ae_map measurable_feedbackMarkedTrajectoryProjection.aemeasurable h

/-- Every bounded physical window contains only finitely many marked jump indices. -/
theorem feedbackMarkedTrajectory_finite_jumps {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam k,
      ∀ T : ℝ, Set.Finite {n | feedbackJumpTime n (feedbackMarkedTrajectoryProjection w) ≤ T} := by
  have h := feedbackHoldingJumpTrajectory_finite_jumps hlam0 hlam k
  rw [← feedbackMarkedTrajectory_map hlam0 hlam k] at h
  exact ae_of_ae_map measurable_feedbackMarkedTrajectoryProjection.aemeasurable h

/-- The actual marked trajectory from zero returns to zero at a positive jump index. -/
theorem feedbackMarkedTrajectory_returns_zero {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0, ∃ n, 0 < n ∧ (w n).2.2 = 0 := by
  have h := feedbackHoldingJumpTrajectory_returns_zero hlam0 hlam
  rw [← feedbackMarkedTrajectory_map hlam0 hlam 0] at h
  exact ae_of_ae_map measurable_feedbackMarkedTrajectoryProjection.aemeasurable h

/-- The marked path inherits the actual geometric tail of its first positive return. -/
theorem feedbackMarkedTrajectory_positive_return_tail {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackMarkedTrajectory lam hlam0 hlam 0
      {w | feedbackAvoidsZero n (feedbackPostInitialCurrent (feedbackMarkedTrajectoryProjection w))} ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
  have h := feedbackHoldingJumpTrajectory_positive_return_tail hlam0 hlam n
  have hm : MeasurableSet {w : ℕ → ℝ × ℤ |
      feedbackAvoidsZero n (feedbackPostInitialCurrent w)} :=
    (measurableSet_feedbackAvoidsZero n).preimage measurable_feedbackPostInitialCurrent
  rw [← feedbackMarkedTrajectory_map hlam0 hlam 0,
    Measure.map_apply measurable_feedbackMarkedTrajectoryProjection hm] at h
  exact h

end OTSelector.Limit
