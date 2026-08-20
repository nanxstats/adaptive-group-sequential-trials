import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Integration

/-!
# Adaptive unbiased estimation

This file formalizes Theorem 5 for finite sets of candidate sample sizes and trial stages.  The
paper cites Liu, Proschan, and Pledger (2002) for the fact that predictable sample-size selection
preserves unbiasedness.  Here that dependency is expressed by independence between each one-hot
selection decision and its candidate estimator.  This is the finite-choice form of the independent
cohort assumption used in the supplement.

For part (ii), `effectiveWeight i` is the paper's `w_i` before stopping and zero afterward.  Thus a
sum over all finite stages is definitionally the paper's stopped sum through `tau`.
-/

open Finset MeasureTheory ProbabilityTheory Set

namespace AdaptiveGroupSequentialTrials

variable {Omega : Type*} [MeasurableSpace Omega]

/-- An integrable estimator whose expectation equals the target parameter. -/
def Unbiased (mu : Measure Omega) (theta : Real) (estimator : Omega → Real) : Prop :=
  Integrable estimator mu ∧ ∫ omega, estimator omega ∂mu = theta

/-- A finite weighted estimator. -/
def weightedEstimator {I : Type*} [Fintype I] (weight estimate : I → Omega → Real)
    (omega : Omega) : Real :=
  ∑ i, weight i omega * estimate i omega

/-- The expectation calculation underlying Theorem 5(ii): predictable effective weights,
independent of their new-stage estimators and summing to one, preserve unbiasedness. -/
theorem weightedEstimator_unbiased {I : Type*} [Fintype I] (mu : Measure Omega)
    [IsProbabilityMeasure mu] (theta : Real) (weight estimate : I → Omega → Real)
    (weight_integrable : ∀ i, Integrable (weight i) mu)
    (estimate_unbiased : ∀ i, Unbiased mu theta (estimate i))
    (weight_independent : ∀ i, weight i ⟂ᵢ[mu] estimate i)
    (weights_sum_one : ∀ omega, ∑ i, weight i omega = 1) :
    Unbiased mu theta (weightedEstimator weight estimate) := by
  have product_integrable (i : I) : Integrable (fun omega ↦ weight i omega * estimate i omega) mu :=
    (weight_independent i).integrable_mul (weight_integrable i) (estimate_unbiased i).1
  refine ⟨?_, ?_⟩
  · change Integrable (fun omega ↦ ∑ i, weight i omega * estimate i omega) mu
    exact integrable_finsetSum Finset.univ fun i _ ↦ product_integrable i
  · simp only [weightedEstimator]
    rw [integral_finsetSum Finset.univ fun i _ ↦ product_integrable i]
    calc
      ∑ i, ∫ omega, weight i omega * estimate i omega ∂mu =
          ∑ i, (∫ omega, weight i omega ∂mu) * (∫ omega, estimate i omega ∂mu) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (weight_independent i).integral_mul_eq_mul_integral
          (weight_integrable i).aestronglyMeasurable (estimate_unbiased i).1.aestronglyMeasurable
      _ = ∑ i, (∫ omega, weight i omega ∂mu) * theta := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(estimate_unbiased i).2]
      _ = (∑ i, ∫ omega, weight i omega ∂mu) * theta := by rw [Finset.sum_mul]
      _ = (∫ omega, ∑ i, weight i omega ∂mu) * theta := by
        rw [integral_finsetSum Finset.univ fun i _ ↦ weight_integrable i]
      _ = theta := by simp_rw [weights_sum_one]; simp

/-- One-hot weight selecting candidate sample size `m`. -/
def selectionWeight {M : Type*} [DecidableEq M] (selection : Omega → M) (m : M)
    (omega : Omega) : Real :=
  if selection omega = m then 1 else 0

/-- The adaptively selected estimator, written as a finite one-hot weighted sum. -/
def adaptiveEstimator {M : Type*} [Fintype M] [DecidableEq M] (selection : Omega → M)
    (candidate : M → Omega → Real) : Omega → Real :=
  weightedEstimator (selectionWeight selection) candidate

/-- Theorem 5(i): predictable selection among finitely many unbiased candidate estimators remains
unbiased when each selection decision is independent of its corresponding candidate. -/
theorem theorem_five_i {M : Type*} [Fintype M] [DecidableEq M] [MeasurableSpace M]
    [MeasurableSingletonClass M] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (theta : Real) (selection : Omega → M) (candidate : M → Omega → Real)
    (selection_measurable : Measurable selection)
    (candidate_unbiased : ∀ m, Unbiased mu theta (candidate m))
    (selection_independent : ∀ m, selectionWeight selection m ⟂ᵢ[mu] candidate m) :
    Unbiased mu theta (adaptiveEstimator selection candidate) := by
  apply weightedEstimator_unbiased mu theta (selectionWeight selection) candidate
  · intro m
    have hset : MeasurableSet {omega | selection omega = m} :=
      (measurableSet_singleton m).preimage selection_measurable
    have hone : Integrable (fun _ : Omega ↦ (1 : Real)) mu := integrable_const 1
    have hindicator : Integrable
        ({omega | selection omega = m}.indicator fun _ ↦ (1 : Real)) mu := hone.indicator hset
    exact hindicator.congr (Filter.Eventually.of_forall fun omega ↦ by
      simp [selectionWeight, Set.indicator])
  · exact candidate_unbiased
  · exact selection_independent
  · intro omega
    simp [selectionWeight]

/-- Theorem 5(ii): the effective stopped weights yield an unbiased overall estimator. -/
theorem theorem_five_ii {K : Nat} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (theta : Real) (effectiveWeight stageEstimate : Fin K → Omega → Real)
    (weight_integrable : ∀ i, Integrable (effectiveWeight i) mu)
    (stage_unbiased : ∀ i, Unbiased mu theta (stageEstimate i))
    (predictable_independence : ∀ i, effectiveWeight i ⟂ᵢ[mu] stageEstimate i)
    (variance_spent : ∀ omega, ∑ i, effectiveWeight i omega = 1) :
    Unbiased mu theta (weightedEstimator effectiveWeight stageEstimate) := by
  exact weightedEstimator_unbiased mu theta effectiveWeight stageEstimate weight_integrable
    stage_unbiased predictable_independence variance_spent

end AdaptiveGroupSequentialTrials
