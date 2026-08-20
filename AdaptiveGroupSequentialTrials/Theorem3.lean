import AdaptiveGroupSequentialTrials.FiniteHorizon
import AdaptiveGroupSequentialTrials.Theorem1
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.Linarith

/-!
# Sequential confidence bounds

This file formalizes the four parts of Theorem 3.  `sqrtInformation i` represents the paper's
positive quantity `ℐ_i¹⁄²`; taking positivity as an explicit hypothesis avoids hiding the division
condition used in equation (8).
-/

open MeasureTheory Set

namespace AdaptiveGroupSequentialTrials

variable {Omega : Type*} {K : Nat}

/-- The test statistic shifted to test the null value `delta`. -/
def shiftedStatistic (Z : Fin K → Omega → Real) (sqrtInformation : Fin K → Real)
    (delta : Real) (i : Fin K) (omega : Omega) : Real :=
  Z i omega - delta * sqrtInformation i

/-- Equation (8): the largest repeated lower confidence bound observed through analysis `k`. -/
noncomputable def lowerConfidenceBound (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) (k : Fin K) (omega : Omega) : Real :=
  cumulativeMax (fun i ↦ (Z i omega - boundary i) / sqrtInformation i) k

/-- The shifted boundary-crossing event through look `k`, used in equation (7). -/
def shiftedCrossingEvent (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) (delta : Real) (k : Fin K) : Set Omega :=
  {omega | ∃ i, i ≤ k ∧ boundary i ≤ shiftedStatistic Z sqrtInformation delta i omega}

theorem lowerConfidenceBound_ge_iff (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real) (sqrtInformation : Fin K → Real)
    (information_pos : ∀ i, 0 < sqrtInformation i) (delta : Real) (k : Fin K) (omega : Omega) :
    delta ≤ lowerConfidenceBound Z boundary sqrtInformation k omega ↔
      omega ∈ shiftedCrossingEvent Z boundary sqrtInformation delta k := by
  rw [lowerConfidenceBound, le_cumulativeMax_iff]
  simp only [shiftedCrossingEvent, shiftedStatistic, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, hratio⟩
    refine ⟨i, hi, ?_⟩
    have hmul := (le_div_iff₀ (information_pos i)).mp hratio
    linarith
  · rintro ⟨i, hi, hshift⟩
    refine ⟨i, hi, (le_div_iff₀ (information_pos i)).mpr ?_⟩
    linarith

/-- Theorem 3(i): a nonnegative lower bound is equivalent to a significance-boundary crossing. -/
theorem theorem_three_i (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) (information_pos : ∀ i, 0 < sqrtInformation i)
    (k : Fin K) (omega : Omega) :
    0 ≤ lowerConfidenceBound Z boundary sqrtInformation k omega ↔
      ∃ i, i ≤ k ∧ boundary i ≤ Z i omega := by
  simpa [shiftedCrossingEvent, shiftedStatistic] using
    lowerConfidenceBound_ge_iff Z boundary sqrtInformation information_pos 0 k omega

variable [MeasurableSpace Omega]

theorem measurableSet_shiftedCrossingEvent (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real) (sqrtInformation : Fin K → Real) (delta : Real) (k : Fin K)
    (hZ : ∀ i, Measurable (Z i)) :
    MeasurableSet (shiftedCrossingEvent Z boundary sqrtInformation delta k) := by
  rw [show shiftedCrossingEvent Z boundary sqrtInformation delta k =
      ⋃ i, if i ≤ k then
        {omega | boundary i ≤ shiftedStatistic Z sqrtInformation delta i omega} else ∅ by
    ext omega
    simp [shiftedCrossingEvent]]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ≤ k
  · simp only [hi, if_true]
    exact measurableSet_le measurable_const ((hZ i).sub measurable_const)
  · simp [hi]

/-- Theorem 3(ii): equation (7) implies exact fixed-look lower-bound coverage. -/
theorem theorem_three_ii (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) (information_pos : ∀ i, 0 < sqrtInformation i)
    (hZ : ∀ i, Measurable (Z i)) (delta : Real) (k : Fin K) (alphaK : ENNReal)
    (equation_seven : mu (shiftedCrossingEvent Z boundary sqrtInformation delta k) = alphaK) :
    mu {omega | lowerConfidenceBound Z boundary sqrtInformation k omega < delta} = 1 - alphaK := by
  have hevent : {omega | lowerConfidenceBound Z boundary sqrtInformation k omega < delta} =
      (shiftedCrossingEvent Z boundary sqrtInformation delta k)ᶜ := by
    ext omega
    constructor
    · intro hlt hcross
      exact (not_le_of_gt hlt) ((lowerConfidenceBound_ge_iff Z boundary sqrtInformation
        information_pos delta k omega).mpr hcross)
    · intro hnot
      exact lt_of_not_ge fun hge ↦ hnot ((lowerConfidenceBound_ge_iff Z boundary
        sqrtInformation information_pos delta k omega).mp hge)
  rw [hevent, measure_compl (measurableSet_shiftedCrossingEvent Z boundary sqrtInformation
    delta k hZ) (measure_ne_top mu _), measure_univ, equation_seven]

omit [MeasurableSpace Omega] in
/-- Theorem 3(iii): lower confidence bounds increase with the analysis index; hence once a lower
bound is nonnegative it remains nonnegative. -/
theorem theorem_three_iii (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) {k l : Fin K} (hkl : k ≤ l) (omega : Omega) :
    lowerConfidenceBound Z boundary sqrtInformation k omega ≤
        lowerConfidenceBound Z boundary sqrtInformation l omega ∧
      (0 ≤ lowerConfidenceBound Z boundary sqrtInformation k omega →
        0 ≤ lowerConfidenceBound Z boundary sqrtInformation l omega) := by
  have hmono : lowerConfidenceBound Z boundary sqrtInformation k omega ≤
      lowerConfidenceBound Z boundary sqrtInformation l omega := cumulativeMax_monotone hkl
  exact ⟨hmono, fun hnonneg ↦ hnonneg.trans hmono⟩

/-- Theorem 3(iv): at an arbitrary stopping rule, undercoverage and false rejection are controlled
by the full-design error level. -/
theorem theorem_three_iv (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) (information_pos : ∀ i, 0 < sqrtInformation i)
    (hZ : ∀ i, Measurable (Z i)) (tau : Omega → Fin K)
    (tau_fiber_measurable : ∀ k, MeasurableSet {omega | tau omega = k})
    (delta : Real) (alpha : ENNReal)
    (full_calibration :
      mu (fullCrossingEvent (shiftedStatistic Z sqrtInformation delta) boundary) = alpha) :
    mu {omega | delta ≤ lowerConfidenceBound Z boundary sqrtInformation (tau omega) omega} ≤ alpha ∧
      1 - alpha ≤
        mu {omega | lowerConfidenceBound Z boundary sqrtInformation (tau omega) omega < delta} := by
  have hevent : {omega | delta ≤ lowerConfidenceBound Z boundary sqrtInformation
      (tau omega) omega} =
      extendedRejectionEvent (shiftedStatistic Z sqrtInformation delta) boundary tau := by
    ext omega
    exact lowerConfidenceBound_ge_iff Z boundary sqrtInformation information_pos delta
      (tau omega) omega
  have hrejection : mu {omega | delta ≤ lowerConfidenceBound Z boundary sqrtInformation
      (tau omega) omega} ≤ alpha := by
    rw [hevent]
    exact theorem_one mu alpha (shiftedStatistic Z sqrtInformation delta) boundary tau full_calibration
  refine ⟨hrejection, ?_⟩
  have hmeas : MeasurableSet (extendedRejectionEvent
      (shiftedStatistic Z sqrtInformation delta) boundary tau) := by
    rw [show extendedRejectionEvent (shiftedStatistic Z sqrtInformation delta) boundary tau =
        ⋃ k, {omega | tau omega = k} ∩
          shiftedCrossingEvent Z boundary sqrtInformation delta k by
      ext omega
      simp [extendedRejectionEvent, shiftedCrossingEvent]]
    exact MeasurableSet.iUnion fun k ↦ (tau_fiber_measurable k).inter
      (measurableSet_shiftedCrossingEvent Z boundary sqrtInformation delta k hZ)
  have hcompl : {omega | lowerConfidenceBound Z boundary sqrtInformation (tau omega) omega < delta} =
      (extendedRejectionEvent (shiftedStatistic Z sqrtInformation delta) boundary tau)ᶜ := by
    ext omega
    rw [← hevent]
    simp
  rw [hcompl, measure_compl hmeas (measure_ne_top mu _), measure_univ]
  apply tsub_le_tsub_left (b := alpha) (c := 1)
  rw [← hevent]
  exact hrejection

/-- The false-rejection conclusion stated at the end of Theorem 3(iv), obtained by setting the true
effect to zero. -/
theorem theorem_three_iv_typeI (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Z : Fin K → Omega → Real) (boundary : Fin K → Real)
    (sqrtInformation : Fin K → Real) (information_pos : ∀ i, 0 < sqrtInformation i)
    (hZ : ∀ i, Measurable (Z i)) (tau : Omega → Fin K)
    (tau_fiber_measurable : ∀ k, MeasurableSet {omega | tau omega = k}) (alpha : ENNReal)
    (full_calibration : mu (fullCrossingEvent Z boundary) = alpha) :
    mu {omega | 0 ≤ lowerConfidenceBound Z boundary sqrtInformation (tau omega) omega} ≤
      alpha := by
  have hshifted : mu (fullCrossingEvent (shiftedStatistic Z sqrtInformation 0) boundary) =
      alpha := by
    have hfun : shiftedStatistic Z sqrtInformation 0 = Z := by
      funext i omega
      simp [shiftedStatistic]
    rw [hfun]
    exact full_calibration
  exact (theorem_three_iv mu Z boundary sqrtInformation information_pos hZ tau
    tau_fiber_measurable 0 alpha hshifted).1

end AdaptiveGroupSequentialTrials
