import AdaptiveGroupSequentialTrials.Theorem1
import Mathlib.Probability.IdentDistribIndep
import StatsMLlib.Probability.Gaussian.Basic

/-!
# Adaptive Gaussian extensions

This file formalizes Theorem 4.  The supplement derives the joint law of the adaptively selected
stage statistics by citing Theorems 1 and 2 of Liu, Proschan, and Pledger (2002).  That external
result is represented precisely by `adaptive_stage_joint_law`: the stage vector has the canonical
product standard-Gaussian law `GaussianMeasure.stdGaussianPi K`.

StatsMLlib is used here, and only here in this project, because it supplies that canonical product
measure together with its verified coordinate laws and independence theorem.
-/

open Finset MeasureTheory ProbabilityTheory Set

namespace AdaptiveGroupSequentialTrials

variable {Omega OmegaPlanned : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaPlanned]
variable {K : Nat}

/-- Deterministic cumulative statistics, corresponding to equation (12). Coefficients outside the
prefix through `k` are ignored. -/
def cumulativeStatistics (coefficient : Fin K → Fin K → Real)
    (stageStatistic : Fin K → Omega → Real) (k : Fin K) (omega : Omega) : Real :=
  ∑ i ∈ Finset.univ.filter fun i ↦ i ≤ k, coefficient i k * stageStatistic i omega

/-- The same cumulative construction as a deterministic map on vectors. -/
def cumulativeTransform (coefficient : Fin K → Fin K → Real)
    (x : Fin K → Real) (k : Fin K) : Real :=
  ∑ i ∈ Finset.univ.filter fun i ↦ i ≤ k, coefficient i k * x i

theorem measurable_cumulativeTransform (coefficient : Fin K → Fin K → Real) :
    Measurable (cumulativeTransform coefficient) := by
  apply measurable_pi_lambda
  intro k
  exact Finset.measurable_sum _ fun i _ ↦ measurable_const.mul (measurable_pi_apply i)

private theorem coordinate_hasStandardGaussianLaw (mu : Measure Omega)
    (stageStatistic : Fin K → Omega → Real)
    (joint_law : HasLaw (fun omega i ↦ stageStatistic i omega)
      (GaussianMeasure.stdGaussianPi K) mu) (i : Fin K) :
    HasLaw (stageStatistic i) (gaussianReal 0 1) mu := by
  have hcanonical : HasLaw (fun x : Fin K → Real ↦ x i) (gaussianReal 0 1)
      (GaussianMeasure.stdGaussianPi K) :=
    ⟨(measurable_pi_apply i).aemeasurable, GaussianMeasure.map_eval_stdGaussianPi i⟩
  simpa [Function.comp_def] using hcanonical.comp joint_law

/-- Theorem 4(i): the external adaptive-sampling joint-law result entails mutual independence of
the selected stagewise statistics. -/
theorem theorem_four_i (mu : Measure Omega) [IsProbabilityMeasure mu]
    (stageStatistic : Fin K → Omega → Real)
    (adaptive_stage_joint_law : HasLaw (fun omega i ↦ stageStatistic i omega)
      (GaussianMeasure.stdGaussianPi K) mu) :
    iIndepFun stageStatistic mu := by
  apply (iIndepFun_iff_hasLaw_pi_pi fun i ↦
    coordinate_hasStandardGaussianLaw mu stageStatistic adaptive_stage_joint_law i).mpr
  simpa [GaussianMeasure.stdGaussianPi] using adaptive_stage_joint_law

/-- Theorem 4(ii): applying the same deterministic cumulative-statistic map to two standard
Gaussian stage vectors gives identically distributed multivariate cumulative statistics. -/
theorem theorem_four_ii (mu : Measure Omega) (nu : Measure OmegaPlanned)
    (coefficient : Fin K → Fin K → Real)
    (adaptiveStage : Fin K → Omega → Real)
    (plannedStage : Fin K → OmegaPlanned → Real)
    (adaptive_stage_joint_law : HasLaw (fun omega i ↦ adaptiveStage i omega)
      (GaussianMeasure.stdGaussianPi K) mu)
    (planned_stage_joint_law : HasLaw (fun omega i ↦ plannedStage i omega)
      (GaussianMeasure.stdGaussianPi K) nu) :
    IdentDistrib (fun omega k ↦ cumulativeStatistics coefficient adaptiveStage k omega)
      (fun omega k ↦ cumulativeStatistics coefficient plannedStage k omega) mu nu := by
  have hstages : IdentDistrib (fun omega i ↦ adaptiveStage i omega)
      (fun omega i ↦ plannedStage i omega) mu nu :=
    adaptive_stage_joint_law.identDistrib planned_stage_joint_law
  change IdentDistrib
    (cumulativeTransform coefficient ∘ fun omega i ↦ adaptiveStage i omega)
    (cumulativeTransform coefficient ∘ fun omega i ↦ plannedStage i omega) mu nu
  exact hstages.comp (measurable_cumulativeTransform coefficient)

/-- Boundary-crossing vectors form a measurable subset of finite-dimensional Euclidean space. -/
theorem measurableSet_vectorCrossing (boundary : Fin K → Real) :
    MeasurableSet {z : Fin K → Real | ∃ i, boundary i ≤ z i} := by
  rw [show {z : Fin K → Real | ∃ i, boundary i ≤ z i} =
      ⋃ i, {z : Fin K → Real | boundary i ≤ z i} by ext z; simp]
  exact MeasurableSet.iUnion fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)

/-- Theorem 4(iii): adaptive cumulative statistics retain type I error control for every stopping
rule.  The proof transfers full-boundary calibration by identical distribution and then applies
Theorem 1; no joint-distribution assumption involving the stopping rule is needed. -/
theorem theorem_four_iii (mu : Measure Omega) (nu : Measure OmegaPlanned)
    (coefficient : Fin K → Fin K → Real)
    (adaptiveStage : Fin K → Omega → Real)
    (plannedStage : Fin K → OmegaPlanned → Real)
    (boundary : Fin K → Real) (tau : Omega → Fin K) (alpha : ENNReal)
    (adaptive_stage_joint_law : HasLaw (fun omega i ↦ adaptiveStage i omega)
      (GaussianMeasure.stdGaussianPi K) mu)
    (planned_stage_joint_law : HasLaw (fun omega i ↦ plannedStage i omega)
      (GaussianMeasure.stdGaussianPi K) nu)
    (planned_calibration :
      nu (fullCrossingEvent (cumulativeStatistics coefficient plannedStage) boundary) = alpha) :
    mu (extendedRejectionEvent (cumulativeStatistics coefficient adaptiveStage) boundary tau) ≤
      alpha := by
  have hident := theorem_four_ii mu nu coefficient adaptiveStage plannedStage
    adaptive_stage_joint_law planned_stage_joint_law
  have hmeasure := hident.measure_preimage_eq (measurableSet_vectorCrossing boundary)
  have hadaptiveCalibration :
      mu (fullCrossingEvent (cumulativeStatistics coefficient adaptiveStage) boundary) = alpha := by
    calc
      mu (fullCrossingEvent (cumulativeStatistics coefficient adaptiveStage) boundary) =
          nu (fullCrossingEvent (cumulativeStatistics coefficient plannedStage) boundary) := by
        simpa [fullCrossingEvent] using hmeasure
      _ = alpha := planned_calibration
  exact theorem_one mu alpha (cumulativeStatistics coefficient adaptiveStage) boundary tau
    hadaptiveCalibration

end AdaptiveGroupSequentialTrials
