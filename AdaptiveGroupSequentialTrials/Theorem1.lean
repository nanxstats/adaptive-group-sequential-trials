import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Adaptive extensions of group sequential trials

This file formalizes Theorem 1 of Q. Liu and K. M. Anderson,
"On Adaptive Extensions of Group Sequential Trials for Clinical Investigations",
JASA 103(484), 2008.

The paper has `K` analysis times, test statistics `Z i`, significance boundaries `b i`,
and an arbitrary stopping rule `τ` taking values among the analysis times.  We use `Fin K`
for those times; Lean index `i` corresponds to analysis time `i + 1` in the paper.

The mathematical core is independent of the joint distribution of the statistics: crossing a
boundary at or before stopping implies crossing a boundary at some point in the full design.
Monotonicity of a measure then gives type-I-error control.  Consequently the result below is
slightly stronger than the paper's statement: neither Gaussian assumptions nor measurability of
the stopping rule is needed for the set containment and measure inequality.
-/

open MeasureTheory Set

namespace AdaptiveGroupSequentialTrials

variable {Omega : Type*}
variable {K : Nat}

/-- The event in equation (1): at least one significance boundary is crossed during the
full `K`-analysis design. -/
def fullCrossingEvent (Z : Fin K → Omega → Real) (b : Fin K → Real) : Set Omega :=
  {omega | ∃ i, b i ≤ Z i omega}

/-- The rejection event in equation (3): a significance boundary is crossed at or before the
analysis selected by the stopping rule `tau`. -/
def extendedRejectionEvent (Z : Fin K → Omega → Real) (b : Fin K → Real)
    (tau : Omega → Fin K) : Set Omega :=
  {omega | ∃ i, i ≤ tau omega ∧ b i ≤ Z i omega}

/-- Equation (1)'s event written in the paper's finite-union notation. -/
theorem fullCrossingEvent_eq_iUnion (Z : Fin K → Omega → Real) (b : Fin K → Real) :
    fullCrossingEvent Z b = ⋃ i, {omega | b i ≤ Z i omega} := by
  ext omega
  simp [fullCrossingEvent]

/-- Equation (3)'s event written literally as a union over possible stopping analyses, followed by
a union over the boundaries available at that analysis. -/
theorem extendedRejectionEvent_eq_iUnion (Z : Fin K → Omega → Real) (b : Fin K → Real)
    (tau : Omega → Fin K) :
    extendedRejectionEvent Z b tau =
      ⋃ k, {omega | tau omega = k} ∩ ⋃ i, ⋃ (_h : i ≤ k), {omega | b i ≤ Z i omega} := by
  ext omega
  simp only [extendedRejectionEvent, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨i, hi, hcross⟩
    exact ⟨tau omega, rfl, i, hi, hcross⟩
  · rintro ⟨k, htau, i, hi, hcross⟩
    subst k
    exact ⟨i, hi, hcross⟩

/-- The set-theoretic heart of Theorem 1. -/
theorem extendedRejectionEvent_subset_full (Z : Fin K → Omega → Real) (b : Fin K → Real)
    (tau : Omega → Fin K) :
    extendedRejectionEvent Z b tau ⊆ fullCrossingEvent Z b := by
  rintro omega ⟨i, _hi, hcross⟩
  exact ⟨i, hcross⟩

variable [MeasurableSpace Omega]

/-- The measure inequality in equation (3), before substituting equation (1). -/
theorem measure_extendedRejectionEvent_le_full (mu : Measure Omega)
    (Z : Fin K → Omega → Real) (b : Fin K → Real) (tau : Omega → Fin K) :
    mu (extendedRejectionEvent Z b tau) ≤ mu (fullCrossingEvent Z b) := by
  exact measure_mono (extendedRejectionEvent_subset_full Z b tau)

/-- Liu and Anderson (2008), Theorem 1.

If the full group-sequential boundary is calibrated to have null probability `alpha`, then an
extended test using any stopping rule has null rejection probability at most `alpha`.

The paper assumes `alpha ∈ (0, 1)` because it is a significance level.  The containment argument
proves the inequality for every `ENNReal` value, so that statistically motivated side condition is
not needed in the formal statement.
-/
theorem theorem_one (mu : Measure Omega) (alpha : ENNReal)
    (Z : Fin K → Omega → Real) (b : Fin K → Real) (tau : Omega → Fin K)
    (boundary_calibration : mu (fullCrossingEvent Z b) = alpha) :
    mu (extendedRejectionEvent Z b tau) ≤ alpha := by
  calc
    mu (extendedRejectionEvent Z b tau) ≤ mu (fullCrossingEvent Z b) :=
      measure_extendedRejectionEvent_le_full mu Z b tau
    _ = alpha := boundary_calibration

/-- A version of Theorem 1 with the paper's real-valued significance level. -/
theorem theorem_one_ofReal (mu : Measure Omega) (alpha : Real)
    (Z : Fin K → Omega → Real) (b : Fin K → Real) (tau : Omega → Fin K)
    (boundary_calibration : mu (fullCrossingEvent Z b) = ENNReal.ofReal alpha) :
    mu (extendedRejectionEvent Z b tau) ≤ ENNReal.ofReal alpha := by
  exact theorem_one mu (ENNReal.ofReal alpha) Z b tau boundary_calibration

end AdaptiveGroupSequentialTrials
