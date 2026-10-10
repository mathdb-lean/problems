import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: SmoothObstruction
- collection: openai-math
- question_id: openai-math:152
- source: openai-math
- source_locator: lean/ComparatorChallenges/SmoothObstruction.lean#OAI.SmoothObstruction.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a zero-entropy ergodic invertible transformation of a standard nonatomic probability space that is not measurably conjugate to any C∞ diffeomorphism preserving a strictly positive smooth probability density on a compact finite-dimensional manifold. One example rules out every finite dimension. ([Lean](lean/docs/152.md)) We construct an ergodic invertible transformation of a standard nonatomic probability space with zero Kolmogorov–Sinai entropy that has no smooth positive-volume model. More precisely, it is not measurably conjugate to any C∞ diffeomorphism preserving a strictly positive smooth probability density on a compact finite-dimensional manifold. A single example excludes every finite dimension, including models on nonorientable manifolds and manifolds with smooth boundary.
- notes: OpenAI math result family 152, Zero entropy does not guarantee a smooth positive-volume model -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/152.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.SmoothObstruction.main
- source_theorem_count: 1
- source_solution_module: OAI.Dynamics.SmoothObstruction.Main
- source_papers: preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf
- source_scope_note: lean/docs/152.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI


open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction

/-- Shannon entropy in bits; the value at mass zero is zero. -/
noncomputable def entropyTerm (p : ℝ) : ℝ := -(p * Real.log p) / Real.log 2

/-- The entropy of the length-`n` join of the partition with labels in `Fin q`. -/
noncomputable def blockEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {q : ℕ} (P : X → Fin q) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin q,
    entropyTerm ((μ {x | ∀ j : Fin n, P ((T^[j.val]) x) = w j}).toReal)

/-- All finite-partition entropy rates exist and have one finite real upper
bound. This spells out `sup_P lim_n H(join_{j<n} T^{-j}P)/n < ∞` without
choosing a value for limits of nonconvergent sequences. Empty atoms are allowed. -/
def FiniteKSEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) (P : X → Fin (q + 1)), Measurable P →
    ∃ h : ℝ, h ≤ C ∧
      Tendsto (fun n : ℕ => blockEntropy μ T P n / (n : ℝ)) atTop (𝓝 h)

/-- Measure-space isomorphism after removing measurable null sets. -/
def ConullIsomorphic {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y))

/-- Standard nonatomic in the source's explicit modulo-null-set sense. -/
def StandardNonatomic {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ConullIsomorphic μ
    (volume.comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))

/-- Measurable conjugacy on invariant conull measurable subsets, not a
continuous conjugacy and not merely a factor map. -/
def ConullConjugate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → X) (ν : Measure Y) (S : Y → Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ T ⁻¹' A = A ∧ S ⁻¹' B = B ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y)) ∧
      ∀ (x y : A), T x = y → (e y : Y) = S (e x)

/-- Positive smooth local coordinate densities. In a half-space chart,
`ContDiffOn` includes smoothness up to the boundary. Absolute Lebesgue density
is used; no orientation or volume form is part of the data. -/
def SmoothPositiveDensity {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (ν : Measure M) : Prop :=
  ∀ x : M, ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffOn ℝ ∞ f (extChartAt I x).target ∧
    (∀ y ∈ (extChartAt I x).target, 0 < f y) ∧
    Measure.map (extChartAt I x) (ν.restrict (extChartAt I x).source) =
      (volume.withDensity (fun y => ENNReal.ofReal (f y))).restrict
        (extChartAt I x).target

/-- A smooth positive-volume model with a specified Euclidean or half-space
manifold model. All model dimensions will be quantified below. -/
def HasModelWith {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {d : ℕ} {H : Type} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : MeasurableSpace M)
      (_ : BorelSpace M) (_ : T2Space M) (_ : SecondCountableTopology M)
      (_ : CompactSpace M) (_ : ChartedSpace H M) (_ : IsManifold I ∞ M)
      (ν : Measure M) (_ : IsProbabilityMeasure ν)
      (S : Diffeomorph I I M M ∞),
    SmoothPositiveDensity I ν ∧ MeasurePreserving S ν ν ∧
      ConullConjugate μ T ν S

/-- Closed manifolds of all dimensions (including zero), and smooth manifolds
with boundary of every positive finite dimension. Nonorientable manifolds
are included: no orientability hypothesis occurs. -/
def HasSmoothPositiveVolumeModel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  (∃ d : ℕ, HasModelWith μ T (𝓡 d)) ∨
    (∃ d : ℕ, ∃ _ : NeZero d, HasModelWith μ T (𝓡∂ d))

/-- A finite-entropy standard nonatomic ergodic system with no smooth positive-volume model. -/
def main_statement : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (_ : IsProbabilityMeasure μ) (T : X ≃ᵐ X),
      StandardNonatomic μ ∧ Ergodic T μ ∧ FiniteKSEntropy μ T ∧
        ¬ HasSmoothPositiveVolumeModel μ T

end SmoothObstruction

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.SmoothObstruction.main_statement

end Problem

/- Formalization scope, from lean/docs/152.md: The paper asks whether a measure-preserving system can be represented by a smooth diffeomorphism preserving positive smooth volume. The formalized supporting result constructs an ergodic invertible transformation of a standard nonatomic probability space with finite Kolmogorov–Sinai entropy that has no such model on any compact finite-dimensional manifold, including manifolds with smooth boundary. The comparison is measurable conjugacy after discarding null sets. The linked statement gives finite entropy; the paper's stronger zero-entropy conclusion is outside this statement. -/
