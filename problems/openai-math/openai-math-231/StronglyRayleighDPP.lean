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

- problem_id: StronglyRayleighDPP
- collection: openai-math
- question_id: openai-math:231
- source: openai-math
- source_locator: lean/ComparatorChallenges/StronglyRayleighDPP.lean#OAI.Problem336AdditiveD139.finite_strongly_rayleigh_response
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: On every infinite connected locally finite simple unweighted graph, the free uniform spanning forest is a factor of independent vertex labels, by one isomorphism-equivariant rule using no root. Translation-invariant strongly Rayleigh binary processes on every countable group, including invariant determinantal processes with Hermitian positive-contraction kernels, are also factors of IID. ([Lean](lean/docs/231.md)) We prove that the free uniform spanning forest is a factor of IID on every infinite connected locally finite simple unweighted graph. One Borel rule works for all such graphs and uses no root, answering affirmatively the general factor question for unimodular random graphs. We also show that every translation-invariant strongly Rayleigh process indexed by a countable group is a factor of IID, including invariant determinantal processes with Hermitian positive-contraction kernels. This group-action conclusion requires no amenability.
- notes: OpenAI math result family 231, The free uniform spanning forest is a factor of IID -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/231.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem336AdditiveD139.finite_strongly_rayleigh_response OAI.Problem336AdditiveD139.strongly_rayleigh_group_factor OAI.Problem336AdditiveD139.finite_positive_contraction_dpp_is_strongly_rayleigh OAI.Problem336AdditiveD139.countable_positive_contraction_dpp_exists_unique OAI.Problem336AdditiveD139.invariant_positive_contraction_dpp_factor OAI.Problem336AdditiveD139.translation_invariant_kernel_dpp_factor
- source_theorem_count: 6
- source_solution_module: OAI.Probability.StrongRayleigh.Main
- source_papers: preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf
- source_scope_note: lean/docs/231.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

abbrev UnitLabel := Set.Icc (0 : ℝ) 1

def leftTranslate {Γ : Type u_1} {α : Type u_2} [Group Γ] (g : Γ) (a : Γ → α) : Γ → α :=
  fun h => a (g⁻¹ * h)

def iidUnitLabels (Γ : Type u_3) [MeasurableSpace Γ] : Measure (Γ → UnitLabel) :=
  Measure.infinitePi (fun _ : Γ => (volume : Measure UnitLabel))

def InvariantBinaryLaw {Γ : Type u_4} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) : Prop :=
  ∀ g : Γ,
    Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
      (μ : Measure (Γ → Bool))

def HasEquivariantIIDFactor {Γ : Type u_5} [Group Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) : Prop :=
  ∃ Phi : (Γ → UnitLabel) → (Γ → Bool),
    Measurable Phi ∧
    (∀ (g : Γ) (u : Γ → UnitLabel),
      Phi (leftTranslate g u) = leftTranslate g (Phi u)) ∧
    Measure.map Phi (iidUnitLabels Γ) = (μ : Measure (Γ → Bool))

def finiteGeneratingValue {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (z : F → ℂ) : ℂ := by
  classical
  exact ∑ x : F → Bool,
    (((μ : Measure (F → Bool)) {x}).toReal : ℂ) *
      ∏ i : F, if x i = true then z i else 1

def StronglyRayleighFinite {F : Type u_7} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) : Prop :=
  ∀ z : F → ℂ, (∀ i : F, 0 < (z i).im) → finiteGeneratingValue μ z ≠ 0

def marginalMass {I : Type u_8} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (x : S → Bool) : ℝ :=
  ((μ : Measure (I → Bool)) {a | ∀ i : S, a i.1 = x i}).toReal

def marginalGeneratingValue {I : Type u_9} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (z : S → ℂ) : ℂ := by
  classical
  exact ∑ x : S → Bool,
    (marginalMass μ S x : ℂ) *
      ∏ i : S, if x i = true then z i else 1

def StronglyRayleighCountable {I : Type u_10}
    (μ : ProbabilityMeasure (I → Bool)) : Prop :=
  ∀ S : Finset I, ∀ z : S → ℂ,
    (∀ i : S, 0 < (z i).im) → marginalGeneratingValue μ S z ≠ 0

def boolReal (b : Bool) : ℝ := if b = true then 1 else 0

def tiltPartition {F : Type u_11} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) : ℝ := by
  classical
  exact ∑ x : F → Bool,
    Real.exp (∑ j : F, h j * boolReal (x j)) *
      ((μ : Measure (F → Bool)) {x}).toReal

def tiltMean {F : Type u_12} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) : ℝ := by
  classical
  exact (∑ x : F → Bool,
      Real.exp (∑ j : F, h j * boolReal (x j)) *
        ((μ : Measure (F → Bool)) {x}).toReal * boolReal (x i)) /
    tiltPartition μ h

def tiltSecondMoment {F : Type u_13} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) : ℝ := by
  classical
  exact (∑ x : F → Bool,
      Real.exp (∑ k : F, h k * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal *
        boolReal (x i) * boolReal (x j)) /
    tiltPartition μ h

def tiltCovariance {F : Type u_14} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) : ℝ :=
  tiltSecondMoment μ h i j - tiltMean μ h i * tiltMean μ h j

def coordinatePerturb {F : Type u_15} (h : F → ℝ) (j : F) (r : ℝ) : F → ℝ := by
  classical
  exact fun k => h k + if k = j then r else 0

def PositiveContractionFinite {F : Type u_16} [Fintype F]
    (K : F → F → ℂ) : Prop :=
  (∀ i j, K i j = conj (K j i)) ∧
  ∀ c : F → ℂ,
    0 ≤ (∑ i : F, ∑ j : F, conj (c i) * K i j * c j).re ∧
    (∑ i : F, ∑ j : F, conj (c i) * K i j * c j).re ≤
      ∑ i : F, Complex.normSq (c i)

def IsFiniteDeterminantalLaw {F : Type u_17} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ) : Prop := by
  classical
  exact ∀ A : Finset F,
    (((μ : Measure (F → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
      Matrix.det (fun i j : A => K i.1 j.1)

def PositiveContractionKernel {I : Type u_18}
    (K : I → I → ℂ) : Prop :=
  (∀ i j, K i j = conj (K j i)) ∧
  ∀ (S : Finset I) (c : S → ℂ),
    0 ≤ (∑ i : S, ∑ j : S, conj (c i) * K i.1 j.1 * c j).re ∧
    (∑ i : S, ∑ j : S, conj (c i) * K i.1 j.1 * c j).re ≤
      ∑ i : S, Complex.normSq (c i)

def IsDeterminantalLaw {I : Type u_19}
    (μ : ProbabilityMeasure (I → Bool)) (K : I → I → ℂ) : Prop := by
  classical
  exact ∀ A : Finset I,
    (((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
      Matrix.det (fun i j : A => K i.1 j.1)

def TranslationInvariantKernel {Γ : Type u_20} [Group Γ]
    (K : Γ → Γ → ℂ) : Prop :=
  ∀ g h k : Γ, K (g * h) (g * k) = K h k

def finite_strongly_rayleigh_response_statement : Prop :=
  ∀ (F : Type u_1) [Fintype F] [Nonempty F] (μ : ProbabilityMeasure (F → Bool)),
      StronglyRayleighFinite μ →
        (∀ (i j : F) (h : F → ℝ),
          HasDerivAt (fun r : ℝ => tiltMean μ (coordinatePerturb h j r) i)
            (tiltCovariance μ h i j) 0) ∧
        (∀ (i : F) (h : F → ℝ),
          (∑ j : F, |tiltCovariance μ h i j|) ≤
              2 * tiltMean μ h i * (1 - tiltMean μ h i) ∧
            2 * tiltMean μ h i * (1 - tiltMean μ h i) ≤ (1 : ℝ) / 2) ∧
        (∀ (i : F) (h h' : F → ℝ) (D : ℝ),
          0 ≤ D → (∀ j : F, |h j - h' j| ≤ D) →
            |tiltMean μ h i - tiltMean μ h' i| ≤ D / 2)

def strongly_rayleigh_group_factor_statement : Prop :=
  ∀ (Γ : Type u_2) [Group Γ] [Countable Γ] [MeasurableSpace Γ],
      ∀ μ : ProbabilityMeasure (Γ → Bool),
        StronglyRayleighCountable μ → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ

def finite_positive_contraction_dpp_is_strongly_rayleigh_statement : Prop :=
  ∀ (F : Type u_3) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        (∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K) ∧
          ∀ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K →
            StronglyRayleighFinite μ

def countable_positive_contraction_dpp_exists_unique_statement : Prop :=
  ∀ (I : Type u_4) [Countable I] (K : I → I → ℂ),
      PositiveContractionKernel K →
        ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K

def invariant_positive_contraction_dpp_factor_statement : Prop :=
  ∀ (Γ : Type u_5) [Group Γ] [Countable Γ] [MeasurableSpace Γ]
      (K : Γ → Γ → ℂ) (μ : ProbabilityMeasure (Γ → Bool)),
      PositiveContractionKernel K → IsDeterminantalLaw μ K →
        InvariantBinaryLaw μ → HasEquivariantIIDFactor μ

def translation_invariant_kernel_dpp_factor_statement : Prop :=
  ∀ (Γ : Type u_6) [Group Γ] [Countable Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ),
      PositiveContractionKernel K → TranslationInvariantKernel K →
        ∃ μ : ProbabilityMeasure (Γ → Bool),
          IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ

end Problem336AdditiveD139

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1, u_2, u_3, u_4, u_5, u_6} : Prop :=
  _root_.OAI.Problem336AdditiveD139.finite_strongly_rayleigh_response_statement.{u_1} ∧
  _root_.OAI.Problem336AdditiveD139.strongly_rayleigh_group_factor_statement.{u_2} ∧
  _root_.OAI.Problem336AdditiveD139.finite_positive_contraction_dpp_is_strongly_rayleigh_statement.{u_3} ∧
  _root_.OAI.Problem336AdditiveD139.countable_positive_contraction_dpp_exists_unique_statement.{u_4} ∧
  _root_.OAI.Problem336AdditiveD139.invariant_positive_contraction_dpp_factor_statement.{u_5} ∧
  _root_.OAI.Problem336AdditiveD139.translation_invariant_kernel_dpp_factor_statement.{u_6}

end Problem

/- Formalization scope, from lean/docs/231.md: The formalization proves that the free uniform spanning forest is a factor of independent identically distributed vertex labels on every infinite connected locally finite simple unweighted graph. One Borel equivariant rule works for all such graphs and uses no distinguished root. The linked supplements also give equivariant IID sampling for invariant strongly Rayleigh laws on countable groups and existence, uniqueness, and IID-factor results for determinantal laws with Hermitian positive-contraction kernels on countable index sets. These group results require neither amenability nor finite generation, and the kernels need not be trace class. -/
