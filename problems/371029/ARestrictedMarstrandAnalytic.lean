/-
Copyright 2026 The mathdb-lean Authors.

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

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Restricted Marstrand projection conjecture for analytic families (MathDB 371029).
Authored directly from the mathematical source.

- problem_id: ARestrictedMarstrandAnalytic
- collection: authored
- question_id: authored:RestrictedMarstrandAnalytic
- source: mathdb-lean
- source_locator: problems/371029/ARestrictedMarstrandAnalytic.lean#Problem.Target
- prose: For an analytic one-parameter family of linear maps from R^n to R^m, n >= m, if each linear subspace has maximal possible image dimension except at finitely many parameters in [0,1], every Borel set has maximal possible Hausdorff image dimension for almost every parameter in [0,1].
- notes: https://mathdb.com/p/371029/restricted-marstrand-projection-conjecture-for-analytic-fami
- track: open
- answer_shape: proof

Reference: Jiahan Du, Restricted Marstrand projection theorem for general families of linear subspaces, arXiv:2510.16671v2, Conjecture 1.5. https://arxiv.org/html/2510.16671v2

AnalyticOnNhd on the compact parameter interval expresses real analyticity near each parameter, equivalent to coordinatewise analyticity in these finite-dimensional spaces. The finite exceptional set may depend on the subspace; the null exceptional set may depend on the Borel set. The maps are arbitrary linear maps, not assumed orthogonal projections. ContinuousLinearMap imposes no extra restriction in finite dimensions.
-/

open MeasureTheory

namespace Problem

/-- Every linear subspace has maximal possible image dimension outside a finite set of parameters. -/
def MaximalSubspaceRanks {n m : ℕ}
    (P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
    {t : ℝ | t ∈ Set.Icc 0 1 ∧
      Module.finrank ℝ (V.map (P t).toLinearMap) ≠ min (Module.finrank ℝ V) m}.Finite

/-- Conjecture 1.5, with Lebesgue almost-everywhere quantification on `[0,1]`. -/
abbrev Target : Prop :=
  ∀ n m : ℕ, m ≤ n →
    ∀ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m),
      AnalyticOnNhd ℝ P (Set.Icc 0 1) → MaximalSubspaceRanks P →
        ∀ A : Set (EuclideanSpace ℝ (Fin n)), @MeasurableSet _ (borel _) A →
          ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
            dimH ((P t) '' A) = min (dimH A) (m : ENNReal)

end Problem
