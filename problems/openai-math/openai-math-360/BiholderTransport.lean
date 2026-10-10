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

- problem_id: BiholderTransport
- collection: openai-math
- question_id: openai-math:360
- source: openai-math
- source_locator: lean/ComparatorChallenges/BiholderTransport.lean#OAI.WeakMTWTransport.uniform_biHolder_transport
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: On every closed connected Riemannian manifold of dimension at least two satisfying weak Ma–Trudinger–Wang curvature, all tangent injectivity domains are convex, resolving Villani’s conjecture in this setting. For squared-distance transport between measurable probability densities bounded above and away from zero, the optimal map and its inverse are Hölder continuous. ([Lean](lean/docs/360.md)) We prove that weak Ma–Trudinger–Wang curvature on a smooth, connected, compact Riemannian manifold of dimension at least two without boundary implies convexity of every tangent injectivity domain, resolving Villani's conjecture in this setting. Conjugate cut points are allowed. More generally, every ordinary subgradient of a squared-distance cost potential is a minimizing velocity with a global supporting mountain. No density hypothesis is used. We prove that the weak Ma–Trudinger–Wang condition on a fixed smooth connected compact boundaryless Riemannian manifold of dimension at least two implies a common Hölder estimate for optimal transport maps and their inverses over the entire class of probability densities with fixed positive upper and lower bounds. The maps have homeomorphic representatives, conjugate cut points are allowed, and no density regularity is assumed.
- notes: OpenAI math result family 360, Weak MTW curvature gives convexity and regular optimal transport -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/360.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.WeakMTWTransport.uniform_biHolder_transport
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.BiholderTransport.Main
- source_main_result: OAI.WeakMTWTransport.uniform_biHolder_transport
- source_papers: preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf
- source_scope_note: lean/docs/360.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

section MetricDefinitions

variable {M : Type*} [MetricSpace M]

/-- Squared-distance cost with factor one half. -/
def cost (x y : M) : ℝ := dist x y ^ 2 / 2

/-- Calibration of Hausdorff measure to Euclidean volume. -/
def euclideanVolumeFactor (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.ball (0 : Model n) 1) /
    (Measure.hausdorffMeasure (n : ℝ) : Measure (Model n))
      (Metric.ball (0 : Model n) 1)

variable [MeasurableSpace M]

/-- Riemannian volume calibrated to Lebesgue measure in Euclidean space. -/
def metricVolume [BorelSpace M] (n : ℕ) : Measure M :=
  euclideanVolumeFactor n • Measure.hausdorffMeasure (n : ℝ)

/-- Almost-everywhere measurable probability densities between fixed bounds. -/
def AdmissibleDensity (vol : Measure M) (lam cap : ℝ) (rho : M → ℝ) : Prop :=
  AEMeasurable rho vol ∧ Integrable rho vol ∧
  (∫ x, rho x ∂vol) = 1 ∧ (∀ᵐ x ∂vol, lam ≤ rho x ∧ rho x ≤ cap)

/-- Multiplication by a density, ignoring exceptional negative values on null sets. -/
def densityMeasure (vol : Measure M) (rho : M → ℝ) : Measure M :=
  vol.withDensity (fun x => ENNReal.ofReal (rho x))

/-- Optimality for the Monge minimization problem. -/
def IsOptimalMap (vol : Measure M) (rho0 rho1 : M → ℝ) (T : M → M) : Prop :=
  Measurable T ∧ Measure.map T (densityMeasure vol rho0) = densityMeasure vol rho1 ∧
  ∀ S : M → M, Measurable S →
    Measure.map S (densityMeasure vol rho0) = densityMeasure vol rho1 →
    (∫ x, cost x (T x) * rho0 x ∂vol) ≤
      (∫ x, cost x (S x) * rho0 x ∂vol)

/-- The two global estimates have the very same exponent and constant. -/
def BiHolderEstimate (alpha C : ℝ) (T : M ≃ₜ M) : Prop :=
  (∀ x x', dist (T x) (T x') ≤ C * (dist x x') ^ alpha) ∧
  (∀ y y', dist (T.symm y) (T.symm y') ≤ C * (dist y y') ^ alpha)

end MetricDefinitions

section RiemannianDefinitions

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold 𝓘(ℝ, Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]

/-- Complete affinely parametrized geodesic with prescribed initial tangent.
Local metric minimization is an intrinsic definition of Riemannian geodesics. -/
def IsGeodesicWithInitialData (x : M) (v : TangentSpace 𝓘(ℝ, Model n) x)
    (gamma : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n) ∞ gamma ∧
  (⟨gamma 0, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n) gamma 0 (1 : ℝ)⟩ :
    TangentBundle 𝓘(ℝ, Model n) M) = ⟨x, v⟩ ∧
  ∀ t : ℝ, ∃ eps : ℝ, 0 < eps ∧
    ∀ s u : ℝ, |s - t| < eps → |u - t| < eps →
      dist (gamma s) (gamma u) = |s - u| * ‖v‖

/-- Evaluation at time one of the geodesic determined by initial data. -/
def riemannianExp (x : M) (v : TangentSpace 𝓘(ℝ, Model n) x) : M := by
  classical
  exact if h : ∃ gamma, IsGeodesicWithInitialData x v gamma then (Classical.choose h) 1 else x

/-- The open injectivity domain, defined by extendible minimizing vectors. -/
def injectivityDomain (x : M) : Set (TangentSpace 𝓘(ℝ, Model n) x) :=
  {p | ∃ a : ℝ, 1 < a ∧ dist x (riemannianExp x (a • p)) = a * ‖p‖}

/-- The Ma–Trudinger–Wang fourth derivative with factor -3/2. -/
def mtw (x : M) (p xi eta : TangentSpace 𝓘(ℝ, Model n) x) : ℝ :=
  -(3 / 2 : ℝ) *
    iteratedDeriv 2 (fun s : ℝ =>
      iteratedDeriv 2 (fun t : ℝ =>
        cost (riemannianExp x (t • xi)) (riemannianExp x (p + s • eta))) 0) 0

/-- Weak MTW only at interior velocities and only for orthogonal test vectors. -/
def WeakMTW : Prop :=
  ∀ (x : M) (p : TangentSpace 𝓘(ℝ, Model n) x), p ∈ injectivityDomain x →
    ∀ xi eta : TangentSpace 𝓘(ℝ, Model n) x,
      inner ℝ xi eta = 0 → 0 ≤ mtw x p xi eta

end RiemannianDefinitions

/-- Uniform bi-Hölder optimal transport for all densities between fixed bounds
on a compact connected smooth Riemannian manifold satisfying weak MTW. -/
def uniform_biHolder_transport_statement : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) {M : Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M] [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ, Model n) ∞ M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)] [IsContMDiffRiemannianBundle 𝓘(ℝ, Model n) ∞ (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)] [IsRiemannianManifold 𝓘(ℝ, Model n) M] [MeasurableSpace M] [BorelSpace M] (hmtw : WeakMTW (n := n) (M := M)) (lam cap : ℝ) (hlam : 0 < lam) (hcap : lam ≤ cap) (hclass : ∃ rho : M → ℝ, AdmissibleDensity (metricVolume n) lam cap rho),
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T

end WeakMTWTransport

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.WeakMTWTransport.uniform_biHolder_transport_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/360.md: On a compact connected smooth Riemannian manifold of dimension at least two, the formalized result proves that weak MTW curvature implies convexity of every open tangent injectivity domain. Prior convexity or nonfocality is not assumed. Additional formalized results give global support at ordinary subgradients, compact convex lifted gap sections with the stated diameter bound, and scale and local-injectivity estimates for finite target families. The latter finite-family result does not cover the paper's arbitrary-potential local-injectivity assertion. The formalized result gives uniform bi-Hölder optimal transport for squared-distance cost on each fixed compact connected smooth Riemannian manifold of dimension at least two satisfying weak MTW. For probability densities between fixed positive lower and finite upper bounds, one exponent and constant work for every pair of densities. The optimal map is a homeomorphism, is unique almost everywhere, and both it and its inverse satisfy the global Hölder bound. The constants are uniform over the density class on the fixed manifold, not over varying metrics. -/
