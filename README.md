# AdaptiveGroupSequentialTrials

This project explores machine-checked mathematics for the core result in:

> Qing Liu and Keaven M. Anderson (2008), On Adaptive Extensions of
> Group Sequential Trials for Clinical Investigations,
> _Journal of the American Statistical Association_ 103(484), 1621--1630.

The OCR'd source article is in `paper/paper.tex`;
its supplementary proof is in `supplement/supplement.tex`.

## Formalized results

The aggregate module [`AdaptiveGroupSequentialTrials.lean`](AdaptiveGroupSequentialTrials.lean)
imports the formalizations of all five numbered theorems in the paper and supplement.

| Result | Lean module | Coverage |
| --- | --- | --- |
| Theorem 1 | [`Theorem1.lean`](AdaptiveGroupSequentialTrials/Theorem1.lean) | The extended rejection event is contained in the full crossing event, giving type I error control for every stopping rule. |
| Theorem 2(i)--(vi) | [`Theorem2.lean`](AdaptiveGroupSequentialTrials/Theorem2.lean) | Boundary inversion, spent-level calibration, monotonic sequential p-values, stopped p-value validity, and almost-sure uniqueness. |
| Theorem 3(i)--(iv) | [`Theorem3.lean`](AdaptiveGroupSequentialTrials/Theorem3.lean) | Test inversion, fixed-look coverage, monotonic lower bounds, stopped coverage, and the null false-rejection corollary. |
| Theorem 4(i)--(iii) | [`Theorem4.lean`](AdaptiveGroupSequentialTrials/Theorem4.lean) | Independence and identical distribution of adaptive Gaussian statistics, followed by stopped type I error control. |
| Theorem 5(i)--(ii) | [`Theorem5.lean`](AdaptiveGroupSequentialTrials/Theorem5.lean) | Unbiasedness under finite adaptive selection and predictable variance-spending weights. |

[`FiniteHorizon.lean`](AdaptiveGroupSequentialTrials/FiniteHorizon.lean) contains the reusable
cumulative-minimum and cumulative-maximum lemmas used by Theorems 2 and 3.

The development contains no `sorry`, `admit`, or project-defined axioms.

## Assumption boundaries

The Lean statements make dependencies that are implicit or external in the article explicit:

- Theorem 2 isolates the analytic inversion of the paper's `sup` definition as
  `stageP_inverts_boundary`, stated for significance levels in the open interval `(0, 1)` exactly
  as in the paper. The restriction matters: a well-ordered boundary diverges as the level tends to
  zero, so for statistics that are unbounded above no real-valued boundary can satisfy the
  inversion at nonpositive levels. All six finite-horizon and probability conclusions are then
  derived from that exact order equivalence.
- Theorem 3 assumes positive square-root information levels and equation (7), just as the paper
  does. Measurability of the test statistics and stopping fibers is stated where complements are
  assigned probabilities.
- The supplement proves Theorem 4(i) by citing Liu, Proschan, and Pledger (2002). The formal
  interface to that external result is `adaptive_stage_joint_law`, stating that the selected stage
  vector has the finite product standard-Gaussian law. Parts (i)--(iii) are proved from it.
- Theorem 5(i) uses a finite-choice version of the independent-cohort argument: each one-hot sample
  size decision is independent of its candidate estimator. In part (ii), `effectiveWeight` means
  the paper's predictable weight before stopping and zero afterward, and the overall estimator is
  the stopped weighted sum of the adaptively selected stage estimators. Independence is assumed
  between each composite weight (effective weight times one-hot sample size decision) and its
  new-cohort candidate estimator, which is the pairing the paper's filtration supplies; the
  selected estimator itself is generally correlated with the weight under sample size adaptation,
  so no independence involving it is assumed.

These interfaces avoid claiming that results from papers outside the supplied source and
supplement have themselves been formalized here.

## Dependency policy

StatsMLlib is used only in Theorem 4, via `StatsMLlib.Probability.Gaussian.Basic`.
That module provides `stdGaussianPi`, the canonical finite product of
independent standard Gaussians needed to state the adaptive joint-law interface.
The other four theorem files use Mathlib alone.

## Toolchain and build

The project downloads the `v4.33.0` release of
[StatsMLlib](https://github.com/Lean-MoDS/StatsMLlib), which pins Mathlib and the Lean toolchain to
the same release. With Homebrew's `elan-init` installed:

```console
elan show
lake update
lake exe cache get
lake build
```

`lake exe cache get` is optional but avoids rebuilding Mathlib from source.

To check only the public aggregate module:

```console
lake build AdaptiveGroupSequentialTrials
```
