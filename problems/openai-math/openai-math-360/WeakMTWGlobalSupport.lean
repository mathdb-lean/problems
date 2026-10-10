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

- problem_id: WeakMTWGlobalSupport
- collection: openai-math
- question_id: openai-math:360
- source: openai-math
- source_locator: lean/ComparatorChallenges/WeakMTWGlobalSupport.lean#OAI.WeakMTWGlobalSupport.current_main_convexity
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: On every closed connected Riemannian manifold of dimension at least two satisfying weak Ma–Trudinger–Wang curvature, all tangent injectivity domains are convex, resolving Villani’s conjecture in this setting. For squared-distance transport between measurable probability densities bounded above and away from zero, the optimal map and its inverse are Hölder continuous. ([Lean](lean/docs/360.md)) We prove that weak Ma–Trudinger–Wang curvature on a smooth, connected, compact Riemannian manifold of dimension at least two without boundary implies convexity of every tangent injectivity domain, resolving Villani's conjecture in this setting. Conjugate cut points are allowed. More generally, every ordinary subgradient of a squared-distance cost potential is a minimizing velocity with a global supporting mountain. No density hypothesis is used. We prove that the weak Ma–Trudinger–Wang condition on a fixed smooth connected compact boundaryless Riemannian manifold of dimension at least two implies a common Hölder estimate for optimal transport maps and their inverses over the entire class of probability densities with fixed positive upper and lower bounds. The maps have homeomorphic representatives, conjugate cut points are allowed, and no density regularity is assumed.
- notes: OpenAI math result family 360, Weak MTW curvature gives convexity and regular optimal transport -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/360.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.WeakMTWGlobalSupport.current_main_convexity
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.WeakMTW.Main
- source_main_result: OAI.WeakMTWGlobalSupport.current_main_convexity
- source_papers: preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf preprints/Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/paper.pdf
- source_scope_note: lean/docs/360.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace WeakMTWGlobalSupport

open scoped Manifold ContDiff Topology
open Set Filter Manifold Bundle

namespace WeakMTW

noncomputable section

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev model (n : ℕ) := 𝓘(ℝ, Model n)

variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n)
    (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

def CompleteGeodesicWithInitialData (x : M) (v : TangentSpace (model n) x)
    (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) (model n) ∞ γ ∧
  ∃ h : γ 0 = x,
    (h ▸ mfderiv 𝓘(ℝ, ℝ) (model n) γ 0 (1 : ℝ)) = v ∧
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s ∈ Metric.ball t ε, ∀ r ∈ Metric.ball t ε,
        dist (γ s) (γ r) = ‖v‖ * |s - r|

def ExpEndpoint (x : M) (v : TangentSpace (model n) x) (y : M) : Prop :=
  ∃ γ : ℝ → M, CompleteGeodesicWithInitialData x v γ ∧ γ 1 = y

noncomputable def exp (x : M) (v : TangentSpace (model n) x) : M :=
  by
    classical
    exact if h : ∃ y, ExpEndpoint x v y then Classical.choose h else x

def injectivityDomain (x : M) : Set (TangentSpace (model n) x) :=
  {v | ∃ a : ℝ, 1 < a ∧ dist x (exp x (a • v)) = a * ‖v‖}

def cost (x y : M) : ℝ := dist x y ^ 2 / 2

noncomputable def mtw (x : M) (v ξ η : TangentSpace (model n) x) : ℝ :=
  -(3 / 2 : ℝ) * deriv (fun s : ℝ =>
    deriv (fun s' : ℝ => deriv (fun t : ℝ =>
      deriv (fun t' : ℝ => cost (exp x (t' • ξ)) (exp x (v + s' • η))) t) 0) s) 0

def HasWeakMTW : Prop :=
  ∀ (x : M) (v : TangentSpace (model n) x), v ∈ injectivityDomain x →
    ∀ ξ η : TangentSpace (model n) x, inner ℝ ξ η = 0 → 0 ≤ mtw x v ξ η

def MainConvexity : Prop :=
  ∀ x : M, Convex ℝ (injectivityDomain (n := n) x)

end

end WeakMTW

/-- Weak MTW implies linear convexity of every open tangent injectivity domain. -/
def current_main_convexity_statement : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) {M : Type*} [MetricSpace M] [ChartedSpace (WeakMTW.Model n) M] [IsManifold (WeakMTW.model n) ∞ M] [CompactSpace M] [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace (WeakMTW.model n) x)] [IsContMDiffRiemannianBundle (WeakMTW.model n) ∞ (WeakMTW.Model n)
      (fun x : M => TangentSpace (WeakMTW.model n) x)] [IsRiemannianManifold (WeakMTW.model n) M] (hmtw : WeakMTW.HasWeakMTW (n := n) (M := M)),
    WeakMTW.MainConvexity (n := n) (M := M)

end WeakMTWGlobalSupport

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.WeakMTWGlobalSupport.current_main_convexity_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/360.md: On a compact connected smooth Riemannian manifold of dimension at least two, the formalized result proves that weak MTW curvature implies convexity of every open tangent injectivity domain. Prior convexity or nonfocality is not assumed. Additional formalized results give global support at ordinary subgradients, compact convex lifted gap sections with the stated diameter bound, and scale and local-injectivity estimates for finite target families. The latter finite-family result does not cover the paper's arbitrary-potential local-injectivity assertion. The formalized result gives uniform bi-Hölder optimal transport for squared-distance cost on each fixed compact connected smooth Riemannian manifold of dimension at least two satisfying weak MTW. For probability densities between fixed positive lower and finite upper bounds, one exponent and constant work for every pair of densities. The optimal map is a homeomorphism, is unique almost everywhere, and both it and its inverse satisfy the global Hölder bound. The constants are uniform over the density class on the fixed manifold, not over varying metrics. -/
/- A supporting-result comparison, not the paper's main theorem (lean/ComparatorChallenges/README.md). -/
