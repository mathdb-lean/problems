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

- problem_id: AffineBernstein
- collection: openai-math
- question_id: openai-math:353
- source: openai-math
- source_locator: lean/ComparatorChallenges/AffineBernstein.lean#OAI.AffineBernstein.affine_bernstein
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every smooth locally uniformly convex affine-maximal graph of dimension three through nine, complete for its induced Euclidean metric, is an elliptic paraboloid. A smooth entire nonquadratic example in dimension ten makes this range sharp. In dimensions three through nine, the paraboloid classification also holds for connected open locally uniformly convex affine-maximal hypersurfaces complete for the affine Berwald–Blaschke metric. ([Lean](lean/docs/353.md)) We prove the Euclidean-complete affine Bernstein conjecture in dimensions three through nine: a smooth locally uniformly convex affine maximal graph is an elliptic paraboloid whenever its induced Euclidean metric is complete. The same conclusion holds, without an initial graph assumption, for connected smooth open (noncompact and without boundary) affine-complete locally uniformly convex immersed hypersurfaces that are classically affine maximal in these dimensions.
- notes: OpenAI math result family 353, Affine Bernstein rigidity through dimension nine and a smooth dimension-ten counterexample -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/353.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AffineBernstein.affine_bernstein
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.AffineBernstein.Main
- source_papers: preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf
- source_scope_note: lean/docs/353.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace AffineBernstein

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coordinateVector (n : ℕ) (i : Fin n) : Space n :=
  EuclideanSpace.single i 1

/-- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
def hessian {n : ℕ} (u : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector n j)) x
    (coordinateVector n i)

/-- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
def cofactorHessian {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hessian u x).det • (hessian u x)⁻¹

/-- The classical determinant weight; in particular, this is not a generalized exponent. -/
def affineWeight {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.rpow (hessian u x).det (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))

def AffineMaximalOn {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∀ x ∈ Ω, ∑ i : Fin n, ∑ j : Fin n,
    cofactorHessian u x i j * hessian (affineWeight u) x i j = 0

/-- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
def graphPathLength {n : ℕ} (u : Space n → ℝ) (γ : ℝ → Space n) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (‖derivWithin γ (Icc (0 : ℝ) 1) t‖ ^ 2 +
       (fderiv ℝ u (γ t) (derivWithin γ (Icc (0 : ℝ) 1) t)) ^ 2))

/-- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
def graphEDist {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Space n)
    (_ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1))
    (_ : MapsTo γ (Icc (0 : ℝ) 1) Ω)
    (_ : γ 0 = x) (_ : γ 1 = y), graphPathLength u γ

/-- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
def EuclideanGraphComplete {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∀ x : ℕ → Space n, (∀ i, x i ∈ Ω) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε) →
    ∃ a ∈ Ω, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      graphEDist Ω u (x i) a < ENNReal.ofReal ε

/-- The graph, regarded as an affine subset of R^{n+1}. -/
def graph {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Set (Space n × ℝ) :=
  {p | p.1 ∈ Ω ∧ p.2 = u p.1}

def standardParaboloid (n : ℕ) : Set (Space n × ℝ) :=
  {p | p.2 = ∑ i : Fin n, (p.1 i) ^ 2}

/-- Literal main theorem, with its stated affine-image consequence. -/
def affine_bernstein_statement : Prop :=
  ∀ (n : ℕ) (hn₃ : 3 ≤ n) (hn₉ : n ≤ 9) (Ω : Set (Space n)) (hΩne : Ω.Nonempty) (hΩopen : IsOpen Ω) (hΩconvex : Convex ℝ Ω) (u : Space n → ℝ) (hu : ContDiffOn ℝ ∞ u Ω) (hpos : ∀ x ∈ Ω, (hessian u x).PosDef) (hmax : AffineMaximalOn Ω u) (hcomplete : EuclideanGraphComplete Ω u),
    Ω = univ ∧
      (∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (c : ℝ),
        A.IsSymm ∧ A.PosDef ∧
        ∀ x, u x = (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)
          + (∑ i : Fin n, b i * x i) + c) ∧
      (∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
        e '' standardParaboloid n = graph Ω u)

end AffineBernstein

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AffineBernstein.affine_bernstein_statement

end Problem

/- Formalization scope, from lean/docs/353.md: The formalization proves the Euclidean-complete affine Bernstein theorem for graph dimensions $3\le n\le9$. If a smooth function on a nonempty open convex domain has positive-definite Hessian, satisfies the affine maximal equation, and its graph is complete in the induced Euclidean metric, then the domain is all of $\mathbb R^n$ and the function is a positive-definite quadratic polynomial plus an affine term. Its graph is therefore an elliptic paraboloid. The paper's extension to immersed hypersurfaces without an initial graph assumption is outside this selected statement. -/
