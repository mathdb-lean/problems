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

- problem_id: CoveringDensity
- collection: openai-math
- question_id: openai-math:092
- source: openai-math
- source_locator: lean/ComparatorChallenges/CoveringDensity.lean#OAI.CoveringOrder.optimal_order
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines the optimal worst-case covering density as $`\Theta(n\log n)`$, for both lattice and unrestricted translative coverings. Every convex body in ℝn, n ≥ 2, admits a lattice covering of density at most $`Cn\log n`$; centrally symmetric examples in every sufficiently large dimension require at least $`cn\log n`$ even without the lattice restriction, for absolute $`c,C\gt 0`$. ([Lean](lean/docs/092.md)) Every convex body in ℝn, n ≥ 2, admits a covering by translates along one full-rank lattice with density at most $`Cn\log n`$, for an absolute constant C. No symmetry or boundary regularity is assumed. For every sufficiently large dimension n, we construct a centrally symmetric convex body whose translative covering density exceeds $`c n\log n`$, where c &gt; 0 is absolute. This disproves the existence of a universal linear upper bound and matches the order of Rogers' upper bound.
- notes: OpenAI math result family 092, The optimal order of convex-body covering density -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/092.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CoveringOrder.optimal_order
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.CoveringDensity.Main
- source_papers: preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf
- source_scope_note: lean/docs/092.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Actual discrete full-rank lattice coverings; no assumed density theorem. -/
structure LatticeCover {n : ℕ} (K : Set (Space n)) where
  lattice : Submodule ℤ (Space n)
  discrete : DiscreteTopology lattice
  fullrank : IsZLattice ℝ lattice
  covers : ∀ y, ∃ l : lattice, y - l.val ∈ K

noncomputable def euclideanVolume (n : ℕ) :
    @Measure (EuclideanSpace ℝ (Fin n))
      (@WithLp.measurableSpace 2 (Fin n → ℝ)
        (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace))) :=
  @Measure.map (Fin n → ℝ) (EuclideanSpace ℝ (Fin n))
    (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace))
    (@WithLp.measurableSpace 2 (Fin n → ℝ)
      (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace)))
    (@WithLp.toLp 2 (Fin n → ℝ))
    (Measure.pi (fun _ : Fin n => @volume ℝ Real.measureSpace))

noncomputable def euclideanCovolume {n : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  addCovolume lattice (EuclideanSpace ℝ (Fin n)) (euclideanVolume n)

noncomputable def latticeDensity {n : ℕ} {K : Set (Space n)}
    (cover : LatticeCover K) : ℝ≥0∞ :=
  euclideanVolume n K / euclideanCovolume cover.lattice

noncomputable def thetaL {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ cover : LatticeCover K, latticeDensity cover

end CoveringOrder

namespace TranslativeCovering

open Set Filter MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (R : ℝ) : Set (Space n) :=
  {x | ∀ i, -R ≤ x i ∧ x i ≤ R}

def LocallyFiniteCenters {n : ℕ} (X : Set (Space n)) : Prop :=
  ∀ B : Set (Space n), Bornology.IsBounded B → (X ∩ B).Finite

def Covers {n : ℕ} (K X : Set (Space n)) : Prop :=
  ∀ y, ∃ x ∈ X, y - x ∈ K

def ConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def CentrallySymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ z, ∀ x, x ∈ K ↔ (2 : ℝ) • z - x ∈ K

noncomputable def upperCenterIntensity {n : ℕ} (X : Set (Space n)) : ℝ≥0∞ :=
  Filter.limsup (fun R : ℝ =>
    (↑(X ∩ cube n R).ncard : ℝ≥0∞) / ENNReal.ofReal ((2 * R) ^ n)) atTop

noncomputable def thetaT {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X},
    volume K * upperCenterIntensity X.val

end TranslativeCovering

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

abbrev Body (n : ℕ) := {K : Set (Space n) // TranslativeCovering.ConvexBody K}
abbrev SymmetricBody (n : ℕ) :=
  {K : Body n // TranslativeCovering.CentrallySymmetric K.val}

noncomputable def translativeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : Body n, TranslativeCovering.thetaT K.val

noncomputable def symmetricTranslativeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : SymmetricBody n, TranslativeCovering.thetaT K.val.val

noncomputable def latticeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : Body n, thetaL K.val

noncomputable def symmetricLatticeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : SymmetricBody n, thetaL K.val.val

/-- The finite real comparison scale, viewed in extended nonnegative reals. -/
def orderBounds (c C : ℝ) (n : ℕ) (a : ℝ≥0∞) : Prop :=
  ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ a ∧
    a ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ))

/-- All four extremal quantities have common
absolute positive comparison constants. ENNReal bounds imply finiteness rather
than mapping a potentially infinite density to zero through `toReal`. -/
def OptimalOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    orderBounds c C n (translativeSup n) ∧
    orderBounds c C n (symmetricTranslativeSup n) ∧
    orderBounds c C n (latticeSup n) ∧
    orderBounds c C n (symmetricLatticeSup n)

end CoveringOrder

/-- Translative and lattice covering densities over all convex bodies and over
centrally symmetric convex bodies have the same asymptotic order. -/
def CoveringOrder.optimal_order_statement : Prop :=
  CoveringOrder.OptimalOrder

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CoveringOrder.optimal_order_statement

end Problem

/- Formalization scope, from lean/docs/092.md: The formalized result gives an absolute constant $C>0$ such that every convex body $K\subset\mathbb R^n$, $n\ge2$, admits a covering by translates along one full-rank lattice $L$ with density $|K|/\mathrm{covol}(L)\le Cn\log n$. The covering is exact, and no symmetry, boundary regularity, or volume normalization is assumed. The formalization determines the order of the largest covering density in dimension $n$. For all sufficiently large $n$, the suprema of translative covering density and lattice covering density are each bounded above and below by absolute positive multiples of $n\log n$, both over all convex bodies and over centrally symmetric convex bodies. -/
