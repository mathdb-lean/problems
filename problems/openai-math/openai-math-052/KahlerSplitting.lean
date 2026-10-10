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

- problem_id: KahlerSplitting
- collection: openai-math
- question_id: openai-math:052
- source: openai-math
- source_locator: lean/ComparatorChallenges/KahlerSplitting.lean#OAI.UniversalCoverSplitting.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: A splitting of the tangent bundle of a compact Kähler manifold into two integrable holomorphic subbundles induces a compatible product decomposition of its universal cover, proving the two-summand form of Beauville's splitting conjecture. On smooth rationally connected projective manifolds, both summands are automatically integrable, establishing Höring's conjecture and the corresponding product decomposition. ([Lean](lean/docs/052.md)) We prove the two-summand form of Beauville's compatible splitting conjecture. If the tangent bundle of a compact connected Kähler manifold decomposes into two integrable holomorphic subbundles of positive rank, then its ordinary universal cover admits a product decomposition whose factor tangent bundles are the lifted specified summands. We prove that both summands of every specified holomorphic splitting of the tangent bundle of a smooth rationally connected projective complex manifold into two positive-rank subbundles are integrable. This proves Höring's conjecture on rationally connected projective manifolds. Höring's product theorem then gives a product decomposition compatible with the specified splitting.
- notes: OpenAI math result family 052, Tangent splittings and product decompositions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/052.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.UniversalCoverSplitting.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.KahlerSplitting.Main
- source_main_result: OAI.UniversalCoverSplitting.main
- source_papers: preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf
- source_scope_note: lean/docs/052.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped Manifold ContDiff
open Set

namespace UniversalCoverSplitting

universe u v

abbrev Model (n : ℕ) := Fin n → ℂ
abbrev model (n : ℕ) := 𝓘(ℂ, Model n)

structure ComplexManifold (n : ℕ) where
  Carrier : Type u
  [topology : TopologicalSpace Carrier]
  [charted : ChartedSpace (Model n) Carrier]
  [hausdorff : T2Space Carrier]
  [secondCountable : SecondCountableTopology Carrier]
  [complexSmooth : IsManifold (model n) ∞ Carrier]

attribute [instance] ComplexManifold.topology ComplexManifold.charted
  ComplexManifold.hausdorff ComplexManifold.secondCountable ComplexManifold.complexSmooth

variable {n r₁ r₂ : ℕ}

abbrev Tangent (X : ComplexManifold.{u} n) (x : X.Carrier) := TangentSpace (model n) x
abbrev RealMetricField (X : ComplexManifold.{u} n) :=
  ∀ x : X.Carrier, Tangent X x →ₗ[ℝ] Tangent X x →ₗ[ℝ] ℝ

def metricInChart {X : ComplexManifold.{u} n} (g : RealMetricField X)
    (c : X.Carrier) (z u v : Model n) : ℝ :=
  let e := extChartAt (model n) c
  let q := mfderiv (model n) (model n) e.symm z
  g (e.symm z) (q u) (q v)

def fundamentalInChart {X : ComplexManifold.{u} n} (g : RealMetricField X)
    (c : X.Carrier) (z u v : Model n) : ℝ :=
  metricInChart g c z (Complex.I • u) v

structure KahlerMetric (X : ComplexManifold.{u} n) where
  metric : RealMetricField X
  symmetric : ∀ x u v, metric x u v = metric x v u
  positive : ∀ x u, u ≠ 0 → 0 < metric x u u
  hermitian : ∀ x u v, metric x (Complex.I • u) (Complex.I • v) = metric x u v
  smooth : ∀ c u v, ContDiffOn ℝ ∞ (fun z ↦ metricInChart metric c z u v)
    (extChartAt (model n) c).target
  closed : ∀ c z, z ∈ (extChartAt (model n) c).target → ∀ u v w : Model n,
    fderiv ℝ (fun y ↦ fundamentalInChart metric c y v w) z u +
    fderiv ℝ (fun y ↦ fundamentalInChart metric c y w u) z v +
    fderiv ℝ (fun y ↦ fundamentalInChart metric c y u v) z w = 0

abbrev ProjectionField (X : ComplexManifold.{u} n) :=
  ∀ x : X.Carrier, Tangent X x →L[ℂ] Tangent X x

def projectionInChart {X : ComplexManifold.{u} n} (P : ProjectionField X)
    (c : X.Carrier) (z : Model n) : Model n →L[ℂ] Model n :=
  let e := extChartAt (model n) c
  (mfderiv (model n) (model n) e (e.symm z)).comp
    ((P (e.symm z)).comp (mfderiv (model n) (model n) e.symm z))

def HolomorphicProjection {X : ComplexManifold.{u} n} (P : ProjectionField X) : Prop :=
  ∀ c, DifferentiableOn ℂ (projectionInChart P c) (extChartAt (model n) c).target

def Integrable {X : ComplexManifold.{u} n} (P : ProjectionField X) : Prop :=
  ∀ c U, IsOpen U → U ⊆ (extChartAt (model n) c).target →
    ∀ V W : Model n → Model n,
      DifferentiableOn ℂ V U → DifferentiableOn ℂ W U →
      (∀ z ∈ U, projectionInChart P c z (V z) = V z) →
      (∀ z ∈ U, projectionInChart P c z (W z) = W z) →
      ∀ z ∈ U, projectionInChart P c z (VectorField.lieBracket ℂ V W z) =
        VectorField.lieBracket ℂ V W z

structure HolomorphicSplitting (X : ComplexManifold.{u} n) (r₁ r₂ : ℕ) where
  projection : ProjectionField X
  idempotent : ∀ x v, projection x (projection x v) = projection x v
  holomorphic : HolomorphicProjection projection
  first_rank : ∀ x, Module.finrank ℂ (LinearMap.range (projection x).toLinearMap) = r₁
  second_rank : ∀ x, Module.finrank ℂ (LinearMap.ker (projection x).toLinearMap) = r₂

def complementaryProjection {X : ComplexManifold.{u} n}
    (S : HolomorphicSplitting X r₁ r₂) : ProjectionField X :=
  fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x) - S.projection x

def LocalBiholomorphism {X : ComplexManifold.{u} n} {Z : ComplexManifold.{v} n}
    (π : Z.Carrier → X.Carrier) : Prop :=
  ∀ z, ∃ e : OpenPartialHomeomorph Z.Carrier X.Carrier,
    z ∈ e.source ∧ (∀ w ∈ e.source, e w = π w) ∧
      MDifferentiableOn (model n) (model n) e e.source ∧
      MDifferentiableOn (model n) (model n) e.symm e.target

structure OrdinaryUniversalCover (X : ComplexManifold.{u} n)
    (Z : ComplexManifold.{v} n) where
  projection : Z.Carrier → X.Carrier
  covering : IsCoveringMap projection
  [connected : ConnectedSpace Z.Carrier]
  [simplyConnected : SimplyConnectedSpace Z.Carrier]
  liftedComplexStructure : LocalBiholomorphism projection

def CompatibleProduct {X : ComplexManifold.{u} n} {Z : ComplexManifold.{v} n}
    (S : HolomorphicSplitting X r₁ r₂) (π : OrdinaryUniversalCover X Z)
    (Y₁ : ComplexManifold.{v} r₁) (Y₂ : ComplexManifold.{v} r₂) : Prop :=
  ∃ Φ : Z.Carrier ≃ₜ (Y₁.Carrier × Y₂.Carrier),
    MDifferentiable (model n) ((model r₁).prod (model r₂)) Φ ∧
    MDifferentiable ((model r₁).prod (model r₂)) (model n) Φ.symm ∧
    (∀ z, Submodule.map
      (mfderiv (model n) ((model r₁).prod (model r₂)) Φ z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.range (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.snd ℂ (Model r₁) (Model r₂)).toLinearMap) ∧
    (∀ z, Submodule.map
      (mfderiv (model n) ((model r₁).prod (model r₂)) Φ z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.ker (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.fst ℂ (Model r₁) (Model r₂)).toLinearMap)

open Set
open scoped Manifold ContDiff
variable {n r₁ r₂ : ℕ}

def main_statement : Prop :=
  ∀ {n r₁ r₂ : ℕ} {n r₁ r₂ : ℕ} (X : ComplexManifold.{u} n) [CompactSpace X.Carrier] [ConnectedSpace X.Carrier] (hn : 2 ≤ n) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (g : KahlerMetric X) (S : HolomorphicSplitting X r₁ r₂) (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) (Z : ComplexManifold.{v} n) (π : OrdinaryUniversalCover X Z),
    ∃ (Y₁ : ComplexManifold.{v} r₁) (Y₂ : ComplexManifold.{v} r₂),
      ConnectedSpace Y₁.Carrier ∧ ConnectedSpace Y₂.Carrier ∧
      SimplyConnectedSpace Y₁.Carrier ∧ SimplyConnectedSpace Y₂.Carrier ∧
      CompatibleProduct S π Y₁ Y₂

end UniversalCoverSplitting

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v} : Prop :=
  _root_.OAI.UniversalCoverSplitting.main_statement.{u, v}

end Problem

/- Formalization scope, from lean/docs/052.md: The splitting question asks whether a holomorphic decomposition of the tangent bundle comes from a product decomposition of the universal cover. The formalized result gives an affirmative answer for a compact connected Kähler manifold whose tangent bundle splits into two positive-rank, integrable holomorphic subbundles. The universal cover is a product of connected simply connected complex manifolds of the prescribed dimensions, and the differential identifies the two tangent factors with the original summands. Both integrability assumptions are required. Automatic integrability and the paper's additional corollaries are not included. The formalization proves integrability of both summands in a holomorphic splitting of the tangent bundle of a rationally connected projective manifold. More precisely, for a compact connected complex manifold of dimension at least two with a projective embedding witnessing rational connectedness, each positive-rank summand of a holomorphic tangent-bundle splitting is integrable. The paper's compatible product decomposition is a separate consequence, outside this selected statement. -/
