import AdaptiveGroupSequentialTrials.FiniteHorizon
import AdaptiveGroupSequentialTrials.Theorem1
import Mathlib.Tactic.Linarith

/-!
# Sequential and final p-values

This file formalizes all six parts of Theorem 2.  The paper defines a stagewise crossing level by
inverting a continuous, decreasing boundary.  `stageP` records that inverse, while
`stageP_inverts_boundary` is the exact order property supplied by the analytic `sup` construction.
Keeping that fact explicit separates the real-analysis question of boundary inversion from the
finite-horizon probability argument.
-/

open MeasureTheory Set

namespace AdaptiveGroupSequentialTrials

variable {Omega : Type*} [MeasurableSpace Omega] {K : Nat}

/-- The sequential p-value is the smallest stagewise crossing level observed through look `k`. -/
noncomputable def sequentialPValue (stageP : Fin K → Omega → Real) (k : Fin K)
    (omega : Omega) : Real :=
  cumulativeMin (fun i ↦ stageP i omega) k

/-- The p-value reported at the analysis selected by `tau`. -/
noncomputable def finalPValue (stageP : Fin K → Omega → Real) (tau : Omega → Fin K)
    (omega : Omega) : Real :=
  sequentialPValue stageP (tau omega) omega

/-- A boundary has been crossed by look `k` at significance level `level`. -/
def crossingBy (Z : Fin K → Omega → Real) (boundary : Fin K → Real → Real)
    (level : Real) (k : Fin K) : Set Omega :=
  {omega | ∃ i, i ≤ k ∧ boundary i level ≤ Z i omega}

/-- The spent type I error level at look `k`. -/
def spentLevel (mu : Measure Omega) (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real → Real) (level : Real) (k : Fin K) : ENNReal :=
  mu (crossingBy Z boundary level k)

omit [MeasurableSpace Omega] in
/-- Theorem 2(i): a sequential p-value is below `level` exactly when a corresponding boundary has
been crossed by that analysis. -/
theorem theorem_two_i (stageP : Fin K → Omega → Real) (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real → Real)
    (stageP_inverts_boundary : ∀ omega i level,
      stageP i omega ≤ level ↔ boundary i level ≤ Z i omega)
    (k : Fin K) (omega : Omega) (level : Real) :
    sequentialPValue stageP k omega ≤ level ↔ omega ∈ crossingBy Z boundary level k := by
  rw [sequentialPValue, cumulativeMin_le_iff]
  simp only [crossingBy, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, hp⟩
    exact ⟨i, hi, (stageP_inverts_boundary omega i level).mp hp⟩
  · rintro ⟨i, hi, hcross⟩
    exact ⟨i, hi, (stageP_inverts_boundary omega i level).mpr hcross⟩

omit [MeasurableSpace Omega] in
theorem crossingBy_subset_full (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real → Real) (level : Real) (k : Fin K) :
    crossingBy Z boundary level k ⊆ fullCrossingEvent Z (fun i ↦ boundary i level) := by
  rintro omega ⟨i, _hi, hcross⟩
  exact ⟨i, hcross⟩

/-- Theorem 2(ii): the p-value event has probability exactly equal to the spent level, and that
spent level is at most the full-design level.  The equality strengthens the paper's displayed first
inequality and agrees with its supplementary proof. -/
theorem theorem_two_ii (mu : Measure Omega) (stageP : Fin K → Omega → Real)
    (Z : Fin K → Omega → Real) (boundary : Fin K → Real → Real)
    (stageP_inverts_boundary : ∀ omega i level,
      stageP i omega ≤ level ↔ boundary i level ≤ Z i omega)
    (k : Fin K) (level : Real)
    (full_calibration : mu (fullCrossingEvent Z (fun i ↦ boundary i level)) =
      ENNReal.ofReal level) :
    mu {omega | sequentialPValue stageP k omega ≤ level} =
        spentLevel mu Z boundary level k ∧
      spentLevel mu Z boundary level k ≤ ENNReal.ofReal level := by
  constructor
  · congr 1
    ext omega
    exact theorem_two_i stageP Z boundary stageP_inverts_boundary k omega level
  · calc
      spentLevel mu Z boundary level k ≤
          mu (fullCrossingEvent Z (fun i ↦ boundary i level)) :=
        measure_mono (crossingBy_subset_full Z boundary level k)
      _ = ENNReal.ofReal level := full_calibration

omit [MeasurableSpace Omega] in
/-- Theorem 2(iii): sequential p-values cannot increase as analyses accumulate. -/
theorem theorem_two_iii (stageP : Fin K → Omega → Real) {k l : Fin K} (hkl : k ≤ l)
    (omega : Omega) :
    sequentialPValue stageP l omega ≤ sequentialPValue stageP k omega := by
  exact cumulativeMin_antitone hkl

omit [MeasurableSpace Omega] in
/-- Theorem 2(iv): the final p-value event is the extended rejection event at `level`. -/
theorem theorem_two_iv (stageP : Fin K → Omega → Real) (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real → Real) (tau : Omega → Fin K)
    (stageP_inverts_boundary : ∀ omega i level,
      stageP i omega ≤ level ↔ boundary i level ≤ Z i omega)
    (omega : Omega) (level : Real) :
    finalPValue stageP tau omega ≤ level ↔
      omega ∈ extendedRejectionEvent Z (fun i ↦ boundary i level) tau := by
  exact theorem_two_i stageP Z boundary stageP_inverts_boundary (tau omega) omega level

/-- Theorem 2(v): the p-value at any stopping rule remains valid. -/
theorem theorem_two_v (mu : Measure Omega) (stageP : Fin K → Omega → Real)
    (Z : Fin K → Omega → Real) (boundary : Fin K → Real → Real)
    (tau : Omega → Fin K)
    (stageP_inverts_boundary : ∀ omega i level,
      stageP i omega ≤ level ↔ boundary i level ≤ Z i omega)
    (level : Real)
    (full_calibration : mu (fullCrossingEvent Z (fun i ↦ boundary i level)) =
      ENNReal.ofReal level) :
    mu {omega | finalPValue stageP tau omega ≤ level} ≤ ENNReal.ofReal level := by
  calc
    mu {omega | finalPValue stageP tau omega ≤ level} =
        mu (extendedRejectionEvent Z (fun i ↦ boundary i level) tau) := by
      congr 1
      ext omega
      exact theorem_two_iv stageP Z boundary tau stageP_inverts_boundary omega level
    _ ≤ ENNReal.ofReal level :=
      theorem_one_ofReal mu level Z (fun i ↦ boundary i level) tau full_calibration

private theorem eq_of_Icc_of_sublevel_iff {x y : Real} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1)
    (hlevels : ∀ level ∈ Ioo (0 : Real) 1, (x ≤ level ↔ y ≤ level)) : x = y := by
  apply le_antisymm
  · by_contra hxy
    have hyx : y < x := lt_of_not_ge hxy
    let level := (x + y) / 2
    have hlevel : level ∈ Ioo (0 : Real) 1 := by
      constructor <;> dsimp [level] <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hy_le : y ≤ level := by dsimp [level]; linarith
    have hx_not_le : ¬x ≤ level := by dsimp [level]; linarith
    exact hx_not_le ((hlevels level hlevel).mpr hy_le)
  · by_contra hyx
    have hxy : x < y := lt_of_not_ge hyx
    let level := (x + y) / 2
    have hlevel : level ∈ Ioo (0 : Real) 1 := by
      constructor <;> dsimp [level] <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hx_le : x ≤ level := by dsimp [level]; linarith
    have hy_not_le : ¬y ≤ level := by dsimp [level]; linarith
    exact hy_not_le ((hlevels level hlevel).mp hx_le)

/-- Theorem 2(vi): any `[0,1]`-valued final p-value inducing exactly the same tests at every
interior level agrees almost surely with the sequentially defined final p-value. -/
theorem theorem_two_vi (mu : Measure Omega) (stageP : Fin K → Omega → Real)
    (Z : Fin K → Omega → Real)
    (boundary : Fin K → Real → Real) (tau : Omega → Fin K) (pPrime : Omega → Real)
    (stageP_inverts_boundary : ∀ omega i level,
      stageP i omega ≤ level ↔ boundary i level ≤ Z i omega)
    (hfinal : ∀ᵐ omega ∂mu, finalPValue stageP tau omega ∈ Icc 0 1)
    (hprime : ∀ᵐ omega ∂mu, pPrime omega ∈ Icc 0 1)
    (hsame_tests : ∀ᵐ omega ∂mu, ∀ level ∈ Ioo (0 : Real) 1,
      (pPrime omega ≤ level ↔
        omega ∈ extendedRejectionEvent Z (fun i ↦ boundary i level) tau)) :
    pPrime =ᵐ[mu] finalPValue stageP tau := by
  filter_upwards [hfinal, hprime, hsame_tests] with omega hfinalOmega hprimeOmega htests
  apply eq_of_Icc_of_sublevel_iff hprimeOmega hfinalOmega
  intro level hlevel
  exact (htests level hlevel).trans
    (theorem_two_iv stageP Z boundary tau stageP_inverts_boundary omega level).symm

end AdaptiveGroupSequentialTrials
