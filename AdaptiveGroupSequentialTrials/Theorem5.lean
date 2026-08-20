import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Integration

/-!
# Adaptive unbiased estimation

This file formalizes Theorem 5 for finite sets of candidate sample sizes and trial stages.  The
paper cites Liu, Proschan, and Pledger (2002) for the fact that predictable sample size selection
preserves unbiasedness.  Here that dependency is expressed by independence between each one-hot
selection decision and its candidate estimator.  This is the finite-choice form of the independent
cohort assumption used in the supplement.

For part (ii), `effectiveWeight i` is the paper's `w_i` before stopping and zero afterward.  Thus a
sum over all finite stages is definitionally the paper's stopped sum through `tau`.  The
independence hypothesis of part (ii) pairs the composite weight
`effectiveWeight i * selectionWeight (selection i) m` with the candidate estimator
`candidate i m`: in the paper's filtration both the weight and the sample size decision are
functions of past data while each candidate comes from the new, independent stage cohort, so this
composite independence is exactly what the model supplies.  Independence between the weight and the
*selected* estimator would be strictly stronger and generally fails under sample size adaptation,
because the selected estimator and the weight are correlated through the sample size choice.
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

/-- Theorem 5(ii): at the stopping time, the variance-spending weighted sum of the adaptively
selected stage estimators is unbiased.

The overall estimator is `∑ i, effectiveWeight i * adaptiveEstimator (selection i) (candidate i)`,
the paper's `∑_{k ≤ τ} w_k Δ̂_{k, ñ_k}`.  The proof reindexes it over stage-and-candidate pairs so
that each composite weight `effectiveWeight i * selectionWeight (selection i) m`, a function of
past data in the paper's filtration, faces its independent new-cohort candidate `candidate i m`. -/
theorem theorem_five_ii {K : Nat} {M : Type*} [Fintype M] [DecidableEq M] [MeasurableSpace M]
    [MeasurableSingletonClass M] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (theta : Real) (effectiveWeight : Fin K → Omega → Real)
    (selection : Fin K → Omega → M) (candidate : Fin K → M → Omega → Real)
    (weight_integrable : ∀ i, Integrable (effectiveWeight i) mu)
    (selection_measurable : ∀ i, Measurable (selection i))
    (candidate_unbiased : ∀ i m, Unbiased mu theta (candidate i m))
    (predictable_independence : ∀ i m,
      (fun omega ↦ effectiveWeight i omega * selectionWeight (selection i) m omega)
        ⟂ᵢ[mu] candidate i m)
    (variance_spent : ∀ omega, ∑ i, effectiveWeight i omega = 1) :
    Unbiased mu theta
      (weightedEstimator effectiveWeight
        (fun i ↦ adaptiveEstimator (selection i) (candidate i))) := by
  have composite_integrable (i : Fin K) (m : M) : Integrable
      (fun omega ↦ effectiveWeight i omega * selectionWeight (selection i) m omega) mu := by
    have hmeas : Measurable (selectionWeight (selection i) m) :=
      Measurable.ite ((measurableSet_singleton m).preimage (selection_measurable i))
        measurable_const measurable_const
    have hbound : ∀ omega, ‖selectionWeight (selection i) m omega‖ ≤ 1 := by
      intro omega
      simp only [selectionWeight]
      split <;> simp
    exact (weight_integrable i).mul_bdd hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have h := weightedEstimator_unbiased (I := Fin K × M) mu theta
    (fun p omega ↦ effectiveWeight p.1 omega * selectionWeight (selection p.1) p.2 omega)
    (fun p omega ↦ candidate p.1 p.2 omega)
    (fun p ↦ composite_integrable p.1 p.2)
    (fun p ↦ candidate_unbiased p.1 p.2)
    (fun p ↦ predictable_independence p.1 p.2)
    (fun omega ↦ by
      rw [Fintype.sum_prod_type]
      calc
        ∑ i, ∑ m, effectiveWeight i omega * selectionWeight (selection i) m omega =
            ∑ i, effectiveWeight i omega := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [selectionWeight, mul_ite, Finset.sum_ite_eq]
        _ = 1 := variance_spent omega)
  have hfun : weightedEstimator
      (fun (p : Fin K × M) omega ↦
        effectiveWeight p.1 omega * selectionWeight (selection p.1) p.2 omega)
      (fun p omega ↦ candidate p.1 p.2 omega) =
      weightedEstimator effectiveWeight
        (fun i ↦ adaptiveEstimator (selection i) (candidate i)) := by
    funext omega
    rw [weightedEstimator, weightedEstimator, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [adaptiveEstimator, weightedEstimator, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ ↦ mul_assoc _ _ _
  rwa [hfun] at h

end AdaptiveGroupSequentialTrials
