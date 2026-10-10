/-
Adapted from StatLean/Stat-Lean commit e1ef06bf52d2a8896439c5b59d982d9aad28a254,
`StatLean/ConcentrationInequalities/Symmetrization/Symmetrization.lean`.
Original source licensed under Apache-2.0.
-/

import OTSelector.Probability.Symmetrization.Rademacher
import OTSelector.Probability.Symmetrization.SignFlip
import OTSelector.Probability.Symmetrization.NormAddMeanZero
import OTSelector.Probability.Symmetrization.IndepTransport

/-!
# Symmetrization (HDP Lemma 6.3.2)

For independent mean-zero random vectors $X_1, \dots, X_N$ in a Banach space
and independent Rademacher signs $\varepsilon_1, \dots, \varepsilon_N$,
$$ \tfrac12\, \mathbb{E}\Bigl\|\sum_{i=1}^N \varepsilon_i X_i\Bigr\|
   \;\le\; \mathbb{E}\Bigl\|\sum_{i=1}^N X_i\Bigr\|
   \;\le\; 2\, \mathbb{E}\Bigl\|\sum_{i=1}^N \varepsilon_i X_i\Bigr\|, $$
stated as two one-sided inequalities with the book's factors `2` exactly. The
signs live on the canonical product extension `μ.prod (signVec N)` (the mixed
public form); the mathematics happens in a canonical core over laws
`ν : Fin N → Measure E` on `Measure.pi ν`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Lemma 6.3.2 (Symmetrization), pp. 180–181.

**Proof formalization notes.** The canonical **upper** bound is stated in
*centered* form with **no mean-zero hypothesis**:
`∫ ‖∑ (yᵢ − ∫ z ∂νᵢ)‖ ≤ 2 ∫ ‖∑ sᵢ • yᵢ‖` — the centering constant cancels in
`Xᵢ − Xᵢ'`, which is why the empirical RHS of Exercise 8.11 is uncentered;
Lemma 6.3.2 (mean-zero: the centering term vanishes) and Exercise 8.11 are
then one-line instantiations, and no mean-zero hypothesis is laundered where
none is needed. Mean zero **is** needed for the lower bound. Proof per book
pp. 180–181: Eq. (6.13) (`NormAddMeanZero`) with the independent copy realized
as a second `Measure.pi ν` factor, the sign flip (`SignFlip`) plus
a.e.-constancy averaging over `signVec`, then the triangle inequality and
marginalization along `measurePreserving_fst`/`snd`. Mixed public forms follow
by the `ForMathlib/IndepTransport` wrappers. Constants: `2` and `2`, exactly
as the book. Degenerate case: both mixed forms are true and provable at
`N = 0` (empty sums; no `NeZero` hypotheses). This migration includes the
upper direction used by Exercise 8.11.

**Bibliographic comments.** Symmetrization goes back to P. Lévy; the modern
two-sided Banach-space form is due to J.-P. Kahane and is often called the
Kahane symmetrization lemma (Kahane, *Some Random Series of Functions*, 1968;
Ledoux–Talagrand, *Probability in Banach Spaces*, 1991, Lemma 6.3).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OTSelector.Probability.Symmetrization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Private plumbing helpers -/

/-- Marginalize the second (probability) factor: an integral of a function of
the first coordinate over `μ.prod ν` equals the integral over `μ`. -/
private theorem integral_comp_fst {α β G' : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure ν]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [CompleteSpace G']
    {g : α → G'} (hg : AEStronglyMeasurable g μ) :
    ∫ w, g w.1 ∂(μ.prod ν) = ∫ x, g x ∂μ := by
  have hmap := (measurePreserving_fst (μ := μ) (ν := ν)).map_eq
  have h := integral_map (μ := μ.prod ν) (φ := (Prod.fst : α × β → α))
    measurable_fst.aemeasurable (f := g) (by rw [hmap]; exact hg)
  rw [hmap] at h
  exact h.symm

/-- Marginalize the first (probability) factor. -/
private theorem integral_comp_snd {α β G' : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ]
    [SFinite ν] [NormedAddCommGroup G'] [NormedSpace ℝ G'] [CompleteSpace G']
    {g : β → G'} (hg : AEStronglyMeasurable g ν) :
    ∫ w, g w.2 ∂(μ.prod ν) = ∫ y, g y ∂ν := by
  have hmap := (measurePreserving_snd (μ := μ) (ν := ν)).map_eq
  have h := integral_map (μ := μ.prod ν) (φ := (Prod.snd : α × β → β))
    measurable_snd.aemeasurable (f := g) (by rw [hmap]; exact hg)
  rw [hmap] at h
  exact h.symm

/-- Each coordinate is integrable under the product law. -/
private theorem integrable_pi_eval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} (ν : Fin N → Measure E)
    [∀ i, IsProbabilityMeasure (ν i)] (h_int : ∀ i, Integrable id (ν i))
    (i : Fin N) : Integrable (fun y : Fin N → E => y i) (Measure.pi ν) := by
  have h := ((measurePreserving_eval (μ := ν) i).integrable_comp
    (g := (id : E → E)) aestronglyMeasurable_id).mpr (h_int i)
  simpa [Function.comp, Function.eval] using h

/-- The coordinate mean under the product law is the marginal mean. -/
private theorem integral_pi_eval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} (ν : Fin N → Measure E)
    [∀ i, IsProbabilityMeasure (ν i)] (i : Fin N) :
    ∫ y : Fin N → E, y i ∂(Measure.pi ν) = ∫ z, z ∂(ν i) := by
  have hmap := (measurePreserving_eval (μ := ν) i).map_eq
  have h := integral_map (μ := Measure.pi ν) (φ := Function.eval i)
    (measurable_pi_apply i).aemeasurable (f := (id : E → E))
    (by rw [hmap]; exact aestronglyMeasurable_id)
  rw [hmap] at h
  simpa [Function.eval] using h.symm

/-- Domination principle: a sign-randomized sum of per-coordinate integrable
data has integrable norm on the canonical sign-product, because a.e. the signs
are `±1`, so the norm is dominated by the sum of coordinate norms. -/
private theorem integrable_norm_sign_prod {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} {D : Type*} [MeasurableSpace D]
    {Q : Measure D} [IsProbabilityMeasure Q] (a : D → Fin N → E)
    (ha_meas : ∀ i, Measurable (fun d => a d i))
    (ha_int : ∀ i, Integrable (fun d => ‖a d i‖) Q) :
    Integrable (fun p : D × (Fin N → ℝ) => ‖∑ i, p.2 i • a p.1 i‖)
      (Q.prod (signVec N)) := by
  have hsum : Integrable (fun d => ∑ i, ‖a d i‖) Q :=
    integrable_finsetSum _ (fun i _ => ha_int i)
  have hg : Integrable (fun p : D × (Fin N → ℝ) => ∑ i, ‖a p.1 i‖)
      (Q.prod (signVec N)) := by
    have h := ((measurePreserving_fst (μ := Q) (ν := signVec N)).integrable_comp
      (g := fun d => ∑ i, ‖a d i‖) hsum.aestronglyMeasurable).mpr hsum
    change Integrable ((fun d => ∑ i, ‖a d i‖) ∘ Prod.fst) (Q.prod (signVec N))
    exact h
  have hmeas0 : Measurable
      (fun p : D × (Fin N → ℝ) => ∑ i, p.2 i • a p.1 i) := by
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp measurable_snd).smul
      ((ha_meas i).comp measurable_fst)
  have hmeas : AEStronglyMeasurable
      (fun p : D × (Fin N → ℝ) => ∑ i, p.2 i • a p.1 i) (Q.prod (signVec N)) :=
    hmeas0.aestronglyMeasurable
  have hpm : ∀ᵐ p ∂(Q.prod (signVec N)), ∀ i, p.2 i = 1 ∨ p.2 i = -1 :=
    (measurePreserving_snd (μ := Q)
      (ν := signVec N)).quasiMeasurePreserving.tendsto_ae.eventually (signVec_ae_pm N)
  refine Integrable.mono' hg hmeas.norm ?_
  filter_upwards [hpm] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  rcases hp i with h | h <;> simp [h]

/-- **Flip averaging** (engine of Lemma 6.3.2): averaging the sign-randomized
difference-of-copies norm over the sign vector gives back the plain
difference-of-copies norm, because for each fixed `±1` sign pattern the two are
equidistributed (`integral_flip_diff`). -/
private theorem flip_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} (ν : Fin N → Measure E)
    [∀ i, IsProbabilityMeasure (ν i)] (h_int : ∀ i, Integrable id (ν i)) :
    ∫ q, ‖∑ i, q.2 i • (q.1.1 i - q.1.2 i)‖
        ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N))
      = ∫ w, ‖∑ i, (w.1 i - w.2 i)‖ ∂((Measure.pi ν).prod (Measure.pi ν)) := by
  have hyi := integrable_pi_eval ν h_int
  have hw1 : ∀ i, Integrable
      (fun w : (Fin N → E) × (Fin N → E) => w.1 i)
      ((Measure.pi ν).prod (Measure.pi ν)) := fun i => by
    have h := ((measurePreserving_fst (μ := Measure.pi ν)
      (ν := Measure.pi ν)).integrable_comp
      (g := fun y : Fin N → E => y i) (hyi i).aestronglyMeasurable).mpr (hyi i)
    change Integrable ((fun y : Fin N → E => y i) ∘ Prod.fst)
      ((Measure.pi ν).prod (Measure.pi ν))
    exact h
  have hw2 : ∀ i, Integrable
      (fun w : (Fin N → E) × (Fin N → E) => w.2 i)
      ((Measure.pi ν).prod (Measure.pi ν)) := fun i => by
    have h := ((measurePreserving_snd (μ := Measure.pi ν)
      (ν := Measure.pi ν)).integrable_comp
      (g := fun y : Fin N → E => y i) (hyi i).aestronglyMeasurable).mpr (hyi i)
    change Integrable ((fun y : Fin N → E => y i) ∘ Prod.snd)
      ((Measure.pi ν).prod (Measure.pi ν))
    exact h
  have hF_int : Integrable
      (fun q : ((Fin N → E) × (Fin N → E)) × (Fin N → ℝ) =>
        ‖∑ i, q.2 i • (q.1.1 i - q.1.2 i)‖)
      (((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) :=
    integrable_norm_sign_prod (D := (Fin N → E) × (Fin N → E))
      (Q := (Measure.pi ν).prod (Measure.pi ν)) (a := fun w i => w.1 i - w.2 i)
      (fun i => ((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd))
      (fun i => ((hw1 i).sub (hw2 i)).norm)
  have hinner :
      (fun s : Fin N → ℝ => ∫ w, ‖∑ i, s i • (w.1 i - w.2 i)‖
          ∂((Measure.pi ν).prod (Measure.pi ν)))
        =ᵐ[signVec N]
      (fun _ => ∫ w, ‖∑ i, (w.1 i - w.2 i)‖
          ∂((Measure.pi ν).prod (Measure.pi ν))) := by
    filter_upwards [signVec_ae_pm N] with s hs
    exact integral_flip_diff ν hs
  have e : ∫ q, ‖∑ i, q.2 i • (q.1.1 i - q.1.2 i)‖
        ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N))
      = ∫ s, (∫ w, ‖∑ i, s i • (w.1 i - w.2 i)‖
          ∂((Measure.pi ν).prod (Measure.pi ν))) ∂(signVec N) :=
    integral_prod_symm _ hF_int
  rw [e, integral_congr_ae hinner, integral_const, probReal_univ, one_smul]

/-- **Symmetrization, upper bound, canonical centered form** (HDP §6.3,
Lemma 6.3.2): over the product of the laws `νᵢ`, the expected norm of the
*centered* sum is at most twice the expected norm of the sign-randomized
(uncentered) sum. No mean-zero hypothesis — the centering constant cancels in
the difference of two independent copies. -/
theorem symmetrization_upper_pi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ}
    (ν : Fin N → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (h_int : ∀ i, Integrable id (ν i)) :
    ∫ y, ‖∑ i, (y i - ∫ z, z ∂(ν i))‖ ∂(Measure.pi ν)
      ≤ 2 * ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N)) := by
  have hyi := integrable_pi_eval ν h_int
  -- per-coordinate integrability on the doubled product
  have hw1 : ∀ i, Integrable
      (fun w : (Fin N → E) × (Fin N → E) => w.1 i)
      ((Measure.pi ν).prod (Measure.pi ν)) := fun i => by
    have h := ((measurePreserving_fst (μ := Measure.pi ν)
      (ν := Measure.pi ν)).integrable_comp
      (g := fun y : Fin N → E => y i) (hyi i).aestronglyMeasurable).mpr (hyi i)
    change Integrable ((fun y : Fin N → E => y i) ∘ Prod.fst)
      ((Measure.pi ν).prod (Measure.pi ν))
    exact h
  have hw2 : ∀ i, Integrable
      (fun w : (Fin N → E) × (Fin N → E) => w.2 i)
      ((Measure.pi ν).prod (Measure.pi ν)) := fun i => by
    have h := ((measurePreserving_snd (μ := Measure.pi ν)
      (ν := Measure.pi ν)).integrable_comp
      (g := fun y : Fin N → E => y i) (hyi i).aestronglyMeasurable).mpr (hyi i)
    change Integrable ((fun y : Fin N → E => y i) ∘ Prod.snd)
      ((Measure.pi ν).prod (Measure.pi ν))
    exact h
  -- E-valued centered sums on `Measure.pi ν`
  have hf : Integrable (fun y => ∑ i, (y i - ∫ z, z ∂(ν i))) (Measure.pi ν) :=
    integrable_finsetSum _ (fun i _ => (hyi i).sub (integrable_const _))
  have hg : Integrable (fun y => ∑ i, ((∫ z, z ∂(ν i)) - y i)) (Measure.pi ν) :=
    integrable_finsetSum _ (fun i _ => (integrable_const _).sub (hyi i))
  have hg0 : ∫ y, ∑ i, ((∫ z, z ∂(ν i)) - y i) ∂(Measure.pi ν) = 0 := by
    have hsplit : ∫ y, ∑ i, ((∫ z, z ∂(ν i)) - y i) ∂(Measure.pi ν)
        = ∑ i, ∫ y, ((∫ z, z ∂(ν i)) - y i) ∂(Measure.pi ν) :=
      integral_finsetSum _ (fun i _ => (integrable_const _).sub (hyi i))
    rw [hsplit]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_sub (integrable_const _) (hyi i), integral_pi_eval ν i, integral_const,
      probReal_univ, one_smul, sub_self]
  -- integrands used on the sign-product
  have hΦμS : Integrable
      (fun p : (Fin N → E) × (Fin N → ℝ) => ‖∑ i, p.2 i • p.1 i‖)
      ((Measure.pi ν).prod (signVec N)) :=
    integrable_norm_sign_prod (D := Fin N → E) (Q := Measure.pi ν)
      (a := fun y i => y i)
      (fun i => measurable_pi_apply i) (fun i => (hyi i).norm)
  have hG1_int : Integrable
      (fun q : ((Fin N → E) × (Fin N → E)) × (Fin N → ℝ) =>
        ‖∑ i, q.2 i • q.1.1 i‖)
      (((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) :=
    integrable_norm_sign_prod (D := (Fin N → E) × (Fin N → E))
      (Q := (Measure.pi ν).prod (Measure.pi ν)) (a := fun w i => w.1 i)
      (fun i => (measurable_pi_apply i).comp measurable_fst)
      (fun i => (hw1 i).norm)
  have hG2_int : Integrable
      (fun q : ((Fin N → E) × (Fin N → E)) × (Fin N → ℝ) =>
        ‖∑ i, q.2 i • q.1.2 i‖)
      (((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) :=
    integrable_norm_sign_prod (D := (Fin N → E) × (Fin N → E))
      (Q := (Measure.pi ν).prod (Measure.pi ν)) (a := fun w i => w.2 i)
      (fun i => (measurable_pi_apply i).comp measurable_snd)
      (fun i => (hw2 i).norm)
  have hF_int_upper : Integrable
      (fun q : ((Fin N → E) × (Fin N → E)) × (Fin N → ℝ) =>
        ‖∑ i, q.2 i • (q.1.1 i - q.1.2 i)‖)
      (((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) :=
    integrable_norm_sign_prod (D := (Fin N → E) × (Fin N → E))
      (Q := (Measure.pi ν).prod (Measure.pi ν)) (a := fun w i => w.1 i - w.2 i)
      (fun i => ((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd))
      (fun i => ((hw1 i).sub (hw2 i)).norm)
  -- partial-integral measurability for marginalization
  have hk_aesm : AEStronglyMeasurable
      (fun a => ∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) (Measure.pi ν) :=
    hΦμS.integral_prod_left.aestronglyMeasurable
  -- STEP A + B: introduce the independent copy (Eq. 6.13) and cancel centering
  have stepA := integral_norm_le_integral_norm_add_prod (Measure.pi ν) (Measure.pi ν)
    (f := fun y => ∑ i, (y i - ∫ z, z ∂(ν i)))
    (g := fun y => ∑ i, ((∫ z, z ∂(ν i)) - y i)) hf hg hg0
  have stepB : ∫ p, ‖(∑ i, (p.1 i - ∫ z, z ∂(ν i))) + (∑ i, ((∫ z, z ∂(ν i)) - p.2 i))‖
        ∂((Measure.pi ν).prod (Measure.pi ν))
      = ∫ w, ‖∑ i, (w.1 i - w.2 i)‖ ∂((Measure.pi ν).prod (Measure.pi ν)) := by
    apply integral_congr_ae
    filter_upwards with p
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    abel
  -- STEP C: the plain difference-of-copies norm equals its sign-averaged version
  have claim1 := (flip_average ν h_int).symm
  -- STEP D: `∫_P G1 = ∫_P G2 = RHS-integral`
  have hG1 : ∫ q, ‖∑ i, q.2 i • q.1.1 i‖
        ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N))
      = ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N)) := by
    have hG1a : ∫ q, ‖∑ i, q.2 i • q.1.1 i‖
          ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N))
        = ∫ w, (∫ s, ‖∑ i, s i • w.1 i‖ ∂(signVec N))
            ∂((Measure.pi ν).prod (Measure.pi ν)) := integral_prod _ hG1_int
    have hG1b : ∫ w, (∫ s, ‖∑ i, s i • w.1 i‖ ∂(signVec N))
            ∂((Measure.pi ν).prod (Measure.pi ν))
        = ∫ a, (∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) ∂(Measure.pi ν) :=
      integral_comp_fst (μ := Measure.pi ν) (ν := Measure.pi ν)
        (g := fun a => ∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) hk_aesm
    have hΦa : ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N))
        = ∫ a, (∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) ∂(Measure.pi ν) :=
      integral_prod _ hΦμS
    rw [hG1a, hG1b, hΦa]
  have hG2 : ∫ q, ‖∑ i, q.2 i • q.1.2 i‖
        ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N))
      = ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N)) := by
    have hG2a : ∫ q, ‖∑ i, q.2 i • q.1.2 i‖
          ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N))
        = ∫ w, (∫ s, ‖∑ i, s i • w.2 i‖ ∂(signVec N))
            ∂((Measure.pi ν).prod (Measure.pi ν)) := integral_prod _ hG2_int
    have hG2b : ∫ w, (∫ s, ‖∑ i, s i • w.2 i‖ ∂(signVec N))
            ∂((Measure.pi ν).prod (Measure.pi ν))
        = ∫ a, (∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) ∂(Measure.pi ν) :=
      integral_comp_snd (μ := Measure.pi ν) (ν := Measure.pi ν)
        (g := fun a => ∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) hk_aesm
    have hΦa : ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N))
        = ∫ a, (∫ s, ‖∑ i, s i • a i‖ ∂(signVec N)) ∂(Measure.pi ν) :=
      integral_prod _ hΦμS
    rw [hG2a, hG2b, hΦa]
  -- STEP E: triangle inequality
  have hpt : ∀ q : ((Fin N → E) × (Fin N → E)) × (Fin N → ℝ),
      ‖∑ i, q.2 i • (q.1.1 i - q.1.2 i)‖
        ≤ ‖∑ i, q.2 i • q.1.1 i‖ + ‖∑ i, q.2 i • q.1.2 i‖ := by
    intro q
    have h : ∑ i, q.2 i • (q.1.1 i - q.1.2 i)
        = (∑ i, q.2 i • q.1.1 i) - (∑ i, q.2 i • q.1.2 i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_sub]
    rw [h]
    exact norm_sub_le _ _
  calc ∫ y, ‖∑ i, (y i - ∫ z, z ∂(ν i))‖ ∂(Measure.pi ν)
      ≤ ∫ p, ‖(∑ i, (p.1 i - ∫ z, z ∂(ν i))) + (∑ i, ((∫ z, z ∂(ν i)) - p.2 i))‖
          ∂((Measure.pi ν).prod (Measure.pi ν)) := stepA
    _ = ∫ w, ‖∑ i, (w.1 i - w.2 i)‖ ∂((Measure.pi ν).prod (Measure.pi ν)) := stepB
    _ = ∫ q, ‖∑ i, q.2 i • (q.1.1 i - q.1.2 i)‖
          ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) := claim1
    _ ≤ ∫ q, (‖∑ i, q.2 i • q.1.1 i‖ + ‖∑ i, q.2 i • q.1.2 i‖)
          ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) :=
        integral_mono hF_int_upper (hG1_int.add hG2_int) hpt
    _ = (∫ q, ‖∑ i, q.2 i • q.1.1 i‖
            ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)))
          + ∫ q, ‖∑ i, q.2 i • q.1.2 i‖
            ∂(((Measure.pi ν).prod (Measure.pi ν)).prod (signVec N)) :=
        integral_add hG1_int hG2_int
    _ = 2 * ∫ p, ‖∑ i, p.2 i • p.1 i‖ ∂((Measure.pi ν).prod (signVec N)) := by
        rw [hG1, hG2]; ring

end OTSelector.Probability.Symmetrization
