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

- problem_id: QuadricBundles
- collection: openai-math
- question_id: openai-math:050
- source: openai-math
- source_locator: lean/ComparatorChallenges/QuadricBundles.lean#OAI.QuadricCounterexample.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs ample rank-two bundles on $`\mathbb P^1\times\mathbb P^1`$ with no smooth Hermitian metric of strictly Griffiths-positive curvature, disproving Griffiths' positivity conjecture already on the quadric surface. ([Lean](lean/docs/050.md)) We give counterexamples to Griffiths' conjecture in rank two on the quadric surface $`\mathbb P^1\times\mathbb P^1`$. We construct an explicit bundle G whose coordinatewise power pullbacks, tensored with $`\mathcal O(1,1)`$, are ample for every positive power, but admit no smooth strictly Griffiths-positive Hermitian metric for all sufficiently large powers.
- notes: OpenAI math result family 050, A counterexample to Griffiths’ positivity conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/050.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.QuadricCounterexample.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.QuadricBundles.Main
- source_main_result: OAI.QuadricCounterexample.main_theorem
- source_papers: preprints/ample-rank-two-bundles-on-the-quadric-surface-without-griffiths-positive-metrics-September-24-2026/paper.pdf
- source_scope_note: lean/docs/050.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace QuadricCounterexample

open Set Filter Topology Metric OnePoint

open scoped Matrix.Norms.Elementwise ComplexOrder

abbrev ProjectiveLine := OnePoint ℂ
abbrev QuadricSurface := ProjectiveLine × ProjectiveLine

def reciprocalP1 (x : ProjectiveLine) : ProjectiveLine :=
  x.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

def affineP1 (i : Fin 2) (z : ℂ) : ProjectiveLine :=
  if i = 0 then reciprocalP1 z else (z : ProjectiveLine)

def affineQuadric (i : Fin 2 × Fin 2) (z : ℂ × ℂ) : QuadricSurface :=
  (affineP1 i.1 z.1, affineP1 i.2 z.2)

def coordP1 (i : Fin 2) (x : ProjectiveLine) : ℂ :=
  (if i=0 then reciprocalP1 x else x).elim 0 id
def coordQuadric (i : Fin 2 × Fin 2) (x : QuadricSurface) : ℂ × ℂ :=
  (coordP1 i.1 x.1,coordP1 i.2 x.2)

def powerP1 (m : ℕ) (x : ProjectiveLine) : ProjectiveLine :=
  x.elim ∞ (fun z ↦ ((z^m : ℂ) : ProjectiveLine))
def powerQuadric (m : ℕ) (x : QuadricSurface) : QuadricSurface :=
  (powerP1 m x.1,powerP1 m x.2)

abbrev BaseCoordinates := ℂ × ℂ
abbrev FiberCoordinates := Fin 2 → ℂ
abbrev TwoMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev BasePolynomial := MvPolynomial (Fin 2) ℂ
def baseEval (p : BasePolynomial) (z : BaseCoordinates) : ℂ :=
  MvPolynomial.eval ![z.1,z.2] p

def AlgebraicallyRegularOn (U : Set BaseCoordinates) (f : BaseCoordinates → ℂ) : Prop :=
  ∀ z ∈ U, ∃ p q : BasePolynomial, baseEval q z ≠ 0 ∧
    ∀ w ∈ U, baseEval q w ≠ 0 → f w=baseEval p w/baseEval q w

def principalChart (i : Fin 2 × Fin 2) (p : BasePolynomial) : Set QuadricSurface :=
  {x | x ∈ range (affineQuadric i) ∧ baseEval p (coordQuadric i x) ≠ 0}

structure AlgebraicRankTwoBundle where
  numberOfCharts : ℕ
  chart : ℕ → Fin 2 × Fin 2
  equation : ℕ → BasePolynomial
  finiteCover : ∀ i, numberOfCharts ≤ i → equation i=0
  covers : ∀ x : QuadricSurface, ∃ i, x ∈ principalChart (chart i) (equation i)
  transition : ℕ → ℕ → QuadricSurface → TwoMatrix
  transition_self : ∀ i x, x ∈ principalChart (chart i) (equation i) →
    transition i i x=1
  transition_mul : ∀ i j k x,
    x ∈ principalChart (chart i) (equation i) →
    x ∈ principalChart (chart j) (equation j) →
    x ∈ principalChart (chart k) (equation k) →
    transition i j x * transition j k x=transition i k x
  transition_regular : ∀ i j a b, AlgebraicallyRegularOn
    {z | baseEval (equation i) z ≠ 0 ∧
      affineQuadric (chart i) z ∈ principalChart (chart j) (equation j)}
    (fun z ↦ transition i j (affineQuadric (chart i) z) a b)

namespace AlgebraicRankTwoBundle

def domain (V : AlgebraicRankTwoBundle) (i : ℕ) : Set QuadricSurface :=
  principalChart (V.chart i) (V.equation i)
def coordinateDomain (V : AlgebraicRankTwoBundle) (i : ℕ) : Set BaseCoordinates :=
  {z | baseEval (V.equation i) z ≠ 0}

def dualTransition (V : AlgebraicRankTwoBundle) (i j : ℕ) (x : QuadricSurface) : TwoMatrix :=
  (V.transition j i x).transpose

end AlgebraicRankTwoBundle

def hyperplaneTransition (i j : Fin 2) (x : ProjectiveLine) : ℂ :=
  if i=j then 1 else coordP1 i x
def polarizationTransition (i j : Fin 2 × Fin 2) (x : QuadricSurface) : ℂ :=
  hyperplaneTransition i.1 j.1 x.1 * hyperplaneTransition i.2 j.2 x.2

def IsPowerPullbackTwist (G : AlgebraicRankTwoBundle) (m : ℕ)
    (E : AlgebraicRankTwoBundle) : Prop :=
  E.numberOfCharts=G.numberOfCharts ∧ E.chart=G.chart ∧
  (∀ i, E.equation i = (MvPolynomial.bind₁ fun j ↦ MvPolynomial.X j ^ m) (G.equation i)) ∧
  ∀ i j x, x ∈ E.domain i → x ∈ E.domain j →
    E.transition i j x = polarizationTransition (G.chart i) (G.chart j) x •
      G.transition i j (powerQuadric m x)

structure SymmetricSection (V : AlgebraicRankTwoBundle) (n : ℕ) where
  coefficient : ℕ → Fin (n+1) → BaseCoordinates → ℂ
  regular : ∀ i k, AlgebraicallyRegularOn (V.coordinateDomain i) (coefficient i k)
  compatible : ∀ i j x, x ∈ V.domain i → x ∈ V.domain j → ∀ v : FiberCoordinates,
    (∑ k : Fin (n+1), coefficient i k (coordQuadric (V.chart i) x) *
      ((V.dualTransition i j x).mulVec v 0)^k.val *
      ((V.dualTransition i j x).mulVec v 1)^(n-k.val)) =
    ∑ k : Fin (n+1), coefficient j k (coordQuadric (V.chart j) x) * v 0^k.val * v 1^(n-k.val)

def SymmetricSection.value {V : AlgebraicRankTwoBundle} {n : ℕ}
    (s : SymmetricSection V n) (i : ℕ) (x : QuadricSurface) (v : FiberCoordinates) : ℂ :=
  ∑ k : Fin (n+1), s.coefficient i k (coordQuadric (V.chart i) x) * v 0^k.val * v 1^(n-k.val)

def ProjectiveAlgebraicCone {N : ℕ} (C : Set (Fin N → ℂ)) : Prop :=
  ∃ equations : Set (MvPolynomial (Fin N) ℂ),
    (∀ p ∈ equations, ∃ d : ℕ, p.IsHomogeneous d) ∧
    C = {y | ∀ p ∈ equations, MvPolynomial.eval y p=0}

def sectionVector {V : AlgebraicRankTwoBundle} {n N : ℕ}
    (s : Fin N → SymmetricSection V n) (i : ℕ) (x : QuadricSurface)
    (v : FiberCoordinates) : Fin N → ℂ := fun j ↦ (s j).value i x v

def GivesClosedProjectiveEmbedding {V : AlgebraicRankTwoBundle} {n N : ℕ}
    (s : Fin N → SymmetricSection V n) : Prop :=
  (∀ i x, x ∈ V.domain i → ∀ v : FiberCoordinates, v ≠ 0 → sectionVector s i x v ≠ 0) ∧
  (∀ i j x y, x ∈ V.domain i → y ∈ V.domain j → ∀ v w : FiberCoordinates,
    v ≠ 0 → w ≠ 0 → (∃ c : ℂ, c ≠ 0 ∧ sectionVector s i x v = c • sectionVector s j y w) →
    x=y ∧ ∃ c : ℂ, c ≠ 0 ∧ v=c • ((V.dualTransition i j x).mulVec w)) ∧
  ProjectiveAlgebraicCone ({0} ∪ {a | ∃ i x, x ∈ V.domain i ∧
    ∃ v : FiberCoordinates, v ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ a=c • sectionVector s i x v}) ∧
  ∀ i x, x ∈ V.domain i → ∀ v : FiberCoordinates, v ≠ 0 →
    ∃ j : Fin N, ∃ b : Fin 2, v b ≠ 0 ∧ sectionVector s i x v j ≠ 0 ∧
    ∃ p q : Fin 3 → MvPolynomial (Fin N) ℂ,
      (∀ k, MvPolynomial.eval (fun l ↦ sectionVector s i x v l / sectionVector s i x v j) (q k) ≠ 0) ∧
      ∀ i' x', x' ∈ V.domain i' → ∀ v' : FiberCoordinates, v' ≠ 0 →
        sectionVector s i' x' v' j ≠ 0 →
        (∀ k, MvPolynomial.eval (fun l ↦ sectionVector s i' x' v' l / sectionVector s i' x' v' j) (q k) ≠ 0) →
        x' ∈ V.domain i ∧ ((V.dualTransition i i' x').mulVec v') b ≠ 0 ∧
        (∀ k : Fin 3,
          (![ (coordQuadric (V.chart i) x').1, (coordQuadric (V.chart i) x').2,
             ((V.dualTransition i i' x').mulVec v') (1-b) /
               ((V.dualTransition i i' x').mulVec v') b ] : Fin 3 → ℂ) k =
          MvPolynomial.eval (fun l ↦ sectionVector s i' x' v' l / sectionVector s i' x' v' j) (p k) /
          MvPolynomial.eval (fun l ↦ sectionVector s i' x' v' l / sectionVector s i' x' v' j) (q k))

def IsAmple (V : AlgebraicRankTwoBundle) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ N : ℕ, ∃ s : Fin N → SymmetricSection V n,
    GivesClosedProjectiveEmbedding s

def holomorphicMetricDerivative (H : BaseCoordinates → TwoMatrix)
    (z u : BaseCoordinates) : TwoMatrix :=
  (1/2 : ℂ) • (fderiv ℝ H z u - Complex.I • fderiv ℝ H z (Complex.I • u))

def metricMixedHessian (H : BaseCoordinates → TwoMatrix)
    (z u : BaseCoordinates) : TwoMatrix :=
  (1/4 : ℂ) • ((fderiv ℝ (fun y ↦ fderiv ℝ H y) z u) u +
    (fderiv ℝ (fun y ↦ fderiv ℝ H y) z (Complex.I • u)) (Complex.I • u))

structure SmoothHermitianMetric (V : AlgebraicRankTwoBundle) where
  dualMatrix : ℕ → BaseCoordinates → TwoMatrix
  smooth : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dualMatrix i) (V.coordinateDomain i)
  positive : ∀ i z, z ∈ V.coordinateDomain i → (dualMatrix i z).PosDef
  compatible : ∀ i j x, x ∈ V.domain i → x ∈ V.domain j →
    dualMatrix j (coordQuadric (V.chart j) x) =
      (V.dualTransition i j x).conjTranspose * dualMatrix i (coordQuadric (V.chart i) x) *
        V.dualTransition i j x

def SmoothHermitianMetric.StrictlyGriffithsPositive {V : AlgebraicRankTwoBundle}
    (h : SmoothHermitianMetric V) : Prop :=
  ∀ i z, z ∈ V.coordinateDomain i → ∀ u : BaseCoordinates, u ≠ 0 →
    (metricMixedHessian (h.dualMatrix i) z u -
      (holomorphicMetricDerivative (h.dualMatrix i) z u).conjTranspose *
        (h.dualMatrix i z)⁻¹ * holomorphicMetricDerivative (h.dualMatrix i) z u).PosDef

def SourceMainTheorem : Prop :=
  ∃ G : AlgebraicRankTwoBundle, ∃ E : ℕ → AlgebraicRankTwoBundle,
    (∀ m, 0 < m → IsPowerPullbackTwist G m (E m)) ∧
    (∀ m, 0 < m → IsAmple (E m)) ∧
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m, m₀ ≤ m →
      ¬ ∃ h : SmoothHermitianMetric (E m), h.StrictlyGriffithsPositive

def main_theorem_statement : Prop :=
  SourceMainTheorem

end QuadricCounterexample

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.QuadricCounterexample.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/050.md: Griffiths' positivity conjecture predicts that every ample holomorphic vector bundle on a smooth complex projective variety admits a smooth Hermitian metric with strictly Griffiths-positive curvature. The formalized counterexample starts with a rank-two algebraic bundle $G$ on $\mathbb P^1\times\mathbb P^1$. Its coordinatewise power pullbacks, tensored with $\mathcal O(1,1)$, are ample for every positive power but admit no such metric for all sufficiently large powers. The separate very-ampleness result for all admissible even exponents is not included. -/
