import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

/-!
# Finite-horizon extrema

The paper repeatedly takes a minimum or maximum over analyses up to a given look.  These helpers
package those nonempty finite extrema and their elementary order properties.
-/

namespace AdaptiveGroupSequentialTrials

open Finset

variable {K : Nat} {R : Type*} [LinearOrder R]

/-- Values of `x` at analysis indices no later than `k`. -/
def prefixValues (x : Fin K → R) (k : Fin K) : Finset R :=
  (Finset.univ.filter fun i ↦ i ≤ k).image x

theorem prefixValues_nonempty (x : Fin K → R) (k : Fin K) : (prefixValues x k).Nonempty := by
  refine image_nonempty.mpr ⟨k, ?_⟩
  simp

/-- The cumulative minimum through analysis `k`. -/
def cumulativeMin (x : Fin K → R) (k : Fin K) : R :=
  (prefixValues x k).min' (prefixValues_nonempty x k)

/-- The cumulative maximum through analysis `k`. -/
def cumulativeMax (x : Fin K → R) (k : Fin K) : R :=
  (prefixValues x k).max' (prefixValues_nonempty x k)

theorem cumulativeMin_le_iff {x : Fin K → R} {k : Fin K} {a : R} :
    cumulativeMin x k ≤ a ↔ ∃ i, i ≤ k ∧ x i ≤ a := by
  constructor
  · intro h
    obtain ⟨i, hi, hvalue⟩ := mem_image.mp
      (min'_mem (prefixValues x k) (prefixValues_nonempty x k))
    exact ⟨i, (mem_filter.mp hi).2, hvalue ▸ h⟩
  · rintro ⟨i, hi, hvalue⟩
    apply (min'_le (prefixValues x k) (x i) ?_).trans hvalue
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩, rfl⟩

theorem le_cumulativeMax_iff {x : Fin K → R} {k : Fin K} {a : R} :
    a ≤ cumulativeMax x k ↔ ∃ i, i ≤ k ∧ a ≤ x i := by
  constructor
  · intro h
    obtain ⟨i, hi, hvalue⟩ := mem_image.mp
      (max'_mem (prefixValues x k) (prefixValues_nonempty x k))
    exact ⟨i, (mem_filter.mp hi).2, h.trans_eq hvalue.symm⟩
  · rintro ⟨i, hi, hvalue⟩
    exact hvalue.trans (le_max' (prefixValues x k) (x i)
      (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩, rfl⟩))

theorem cumulativeMin_antitone {x : Fin K → R} {k l : Fin K} (hkl : k ≤ l) :
    cumulativeMin x l ≤ cumulativeMin x k := by
  obtain ⟨i, hi, hvalue⟩ := (cumulativeMin_le_iff (x := x) (k := k)
    (a := cumulativeMin x k)).mp le_rfl
  exact (cumulativeMin_le_iff (x := x) (k := l)).mpr ⟨i, hi.trans hkl, hvalue⟩

theorem cumulativeMax_monotone {x : Fin K → R} {k l : Fin K} (hkl : k ≤ l) :
    cumulativeMax x k ≤ cumulativeMax x l := by
  obtain ⟨i, hi, hvalue⟩ := (le_cumulativeMax_iff (x := x) (k := k)
    (a := cumulativeMax x k)).mp le_rfl
  exact (le_cumulativeMax_iff (x := x) (k := l)).mpr ⟨i, hi.trans hkl, hvalue⟩

end AdaptiveGroupSequentialTrials
