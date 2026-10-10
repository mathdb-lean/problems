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

- problem_id: DaugavetModuli
- collection: openai-math
- question_id: openai-math:331
- source: openai-math
- source_locator: lean/ComparatorChallenges/DaugavetModuli.lean#OAI.ExactModuli.exact_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a real reflexive Banach space with an asymptotically midpoint uniformly convex norm but no equivalent asymptotically uniformly convex norm, extending Baudier's separation to reflexive spaces. In the same space, depth-k countably branching diamonds require distortion at least $`\sqrt{1+k/12}`$, so midpoint uniform convexity does not force uniformly bounded diamond distortion even under reflexivity. ([Lean](lean/docs/331.md)) We construct a separable reflexive real Banach space whose given norm is asymptotically midpoint uniformly convex but which admits no asymptotically uniformly convex equivalent norm. Its averaged midpoint modulus is at least $`\sqrt{1+t^2/12}-1`$, and the countably branching diamond of depth k has distortion at least $`\sqrt{1+k/12}`$ in this space. This gives a negative answer to the reflexive diamond converse for asymptotic uniform convexifiability. For a real segment-forest dual with unbounded finite component heights and the real infinite-height coordinate predual, we bound the tail of an arbitrary displacement in a symmetric lens by $`2\sqrt{R^2-\|x\|^2}`$, where R is the lens radius and x is its finitely supported center. Both given norms are asymptotically midpoint uniformly convex, although neither space admits an equivalent asymptotically uniformly convex norm. The finite-height forest dual is reflexive. We derive quantitative distortion bounds for countably branching diamond graphs from midpoint estimates and direct tree energies. In the dual of a finite-height segment forest, every distortion-D embedding of the depth-k diamond satisfies $`D^2\ge1+k/4`$. The same bound holds in the infinite-height coordinate predual. We also obtain power-type distortion bounds for path-cost and recursive tree norms. For an infinite-dimensional real subspace of L1 whose unit ball is totally bounded in measure and whose norm has the Daugavet property, we compute the averaged midpoint and one-sided asymptotic moduli at every unit center. They are $`\max\{t/2,t-1\}`$ and $`\max\{0,t-2\}`$, respectively. The same weak-neighborhood geometry excludes every equivalent asymptotically uniformly convex norm. A quantitative realization of the Kadets–Werner construction supplies a space with both hypotheses. Four real Banach spaces defined by bounded tree potentials satisfy the averaged asymptotic midpoint bound $`\widehat\delta(t)\ge\sqrt{1+t^2/4}-1`$ for $`0\lt t\lt 1`$, while none admits an asymptotically uniformly convex (AUC) renorming. On finite-height trees, the globally constrained norm equals the least additive cost of a Hilbert vector and root paths. The quadratic path and segment-start outer Hilbert sums are reflexive and asymptotically midpoint uniformly convex, and admit no equivalent AUC norm. For a countably branching tree, the closed real L1 spans of products of independent exponential or Gaussian-square multipliers along its paths have positive averaged asymptotic midpoint moduli and admit no equivalent asymptotically uniformly convex norm. The renorming obstruction holds for every positive nonconstant mean-one multiplier with finite second moment. We study tree norms computed by two least nonnegative fields whose difference is the vector. For Euclidean child aggregation, two root-sum spaces have an averaged asymptotic midpoint modulus of at least $`t^3/128`$ for $`0\lt t\lt 1`$, including a reflexive joining-root space. A reflexive construction with a fixed zero root also satisfies a homogeneous cubic estimate. These spaces admit no equivalent asymptotically uniformly convex norm. We also obtain sixth-power and cubic estimates when the aggregation exponent depends on the height of a finite component.
- notes: OpenAI math result family 331, Reflexive midpoint convexity and diamond distortion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/331.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ExactModuli.exact_main OAI.ExactModuli.kadets_werner_existence OAI.ExactModuli.exact_example
- source_theorem_count: 3
- source_solution_module: OAI.Analysis.Daugavet.Main
- source_main_result: OAI.ExactModuli.exact_example
- source_papers: preprints/Asymptotic-midpoint-uniform-convexity-and-unbounded-diamond-distortion-in-a-reflexive-tree-space-September-27-2026/manuscript.pdf preprints/Midpoint-lenses-in-segment-spaces-September-27-2026/manuscript.pdf preprints/Diamond-distortion-from-midpoint-and-tree-energies-September-27-2026/manuscript.pdf preprints/Exact-asymptotic-moduli-in-a-Daugavet-subspace-of-L1-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-bounded-tree-potentials-and-path-costs-September-27-2026/manuscript.pdf preprints/Independent-products-in-real-L1-asymptotic-midpoint-convexity-without-AUC-renormings-September-27-2026/manuscript.pdf preprints/Midpoint-convexity-from-two-recursive-potentials-September-27-2026/manuscript.pdf
- source_scope_note: lean/docs/331.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Closed linear subspaces of finite codimension. -/
def Cofinite (F : Submodule ℝ X) : Prop :=
  IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)

/-- Averaged increment for directions of norm at least one. -/
def averagedIncrement (N : Seminorm ℝ X) (x : X) (t : ℝ) (y : X) : ℝ :=
  (N (x + t • y) + N (x - t • y)) / 2 - 1

def H (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, 1 ≤ N y ∧ a = averagedIncrement N x t y}}

def D (N : Seminorm ℝ X) (x : X) (t : ℝ) : ℝ :=
  sSup {r | ∃ F : Submodule ℝ X, Cofinite F ∧
    r = sInf {a | ∃ y ∈ F, N y = 1 ∧ a = N (x + t • y) - 1}}

def averagedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = H N x t}

def oneSidedModulus (N : Seminorm ℝ X) (t : ℝ) : ℝ :=
  sInf {r | ∃ x, N x = 1 ∧ r = D N x t}

/-- Two-sided comparison makes this seminorm a genuine norm equivalent to the original. -/
def EquivalentNorm (N : Seminorm ℝ X) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x, a * ‖x‖ ≤ N x ∧ N x ≤ b * ‖x‖

def AUC (N : Seminorm ℝ X) : Prop :=
  ∀ t : ℝ, 0 < t → 0 < oneSidedModulus N t

/-- Every rank-one operator has the form `ell.smulRight v`. -/
def Daugavet (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (ell : X →L[ℝ] ℝ) (v : X),
    ‖ContinuousLinearMap.id ℝ X + ell.smulRight v‖ = 1 + ‖ell.smulRight v‖

variable {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Convergence-in-measure distance on L1 equivalence classes. -/
def measureDistance (f g : Lp ℝ 1 μ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ μ.real {ω | a < |f ω - g ω|} < a}

/-- Finite covers of the entire unit ball in convergence-in-measure distance. -/
def MeasurePrecompactBall (E : Submodule ℝ (Lp ℝ 1 μ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Finset (Lp ℝ 1 μ),
    ∀ y : E, ‖y‖ ≤ 1 → ∃ b ∈ s, measureDistance μ (y : Lp ℝ 1 μ) b < ε

/-- Every nonempty unit-ball slice contains an almost antipodal unit vector. -/
def UnitSliceProperty (X : Type uX) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (w : X), ‖w‖ = 1 → ∀ (ell : X →L[ℝ] ℝ) (α : ℝ),
    (∃ u : X, ‖u‖ ≤ 1 ∧ α < ell u) →
    ∀ ρ : ℝ, 0 < ρ → ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖

/-- The countable product of unit intervals. -/
abbrev KWOmega := ℕ → unitInterval

def kwMeasure : Measure KWOmega := Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

def exact_main_statement : Prop :=
  ∀ {Ω : Type u_1} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Submodule ℝ (Lp ℝ 1 μ)) (_hclosed : IsClosed (E : Set (Lp ℝ 1 μ))) (hdim : ¬ FiniteDimensional ℝ E) (hprecompact : MeasurePrecompactBall μ E) (hdaugavet : Daugavet E),
    (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
      H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
      D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
    (∀ t : ℝ, 0 < t →
      averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
      oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
    (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N)

def kadets_werner_existence_statement : Prop :=
  ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E

def exact_example_statement : Prop :=
  ∃ E : Submodule ℝ (Lp ℝ 1 kwMeasure),
      IsClosed (E : Set (Lp ℝ 1 kwMeasure)) ∧ (¬ FiniteDimensional ℝ E) ∧
      MeasurePrecompactBall kwMeasure E ∧ UnitSliceProperty E ∧ Daugavet E ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 < t →
        H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
        D (normSeminorm ℝ E) x t = max 0 (t - 2)) ∧
      (∀ t : ℝ, 0 < t →
        averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
        oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2)) ∧
      (∀ N : Seminorm ℝ E, EquivalentNorm N → ¬ AUC N)

end ExactModuli

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.ExactModuli.exact_main_statement.{u_1} ∧
  _root_.OAI.ExactModuli.kadets_werner_existence_statement ∧
  _root_.OAI.ExactModuli.exact_example_statement

end Problem

/- Formalization scope, from lean/docs/331.md: The paper constructs a Banach space whose midpoint geometry is asymptotically uniformly convex even though no equivalent norm is asymptotically uniformly convex in the usual one-sided sense. The formalization proves that the full dual of the specified segment-norm completion is infinite-dimensional, separable, and reflexive; its averaged midpoint modulus is at least $\sqrt{1+t^2/12}-1$ for every $t>0$, while every equivalent norm fails asymptotic uniform convexity. It also proves that an embedding of a depth-$k$ countably branching diamond has distortion at least $\sqrt{1+k/12}$. The general-forest and word-forest results use the closed span of the coordinate functionals. Their conclusions retain the finite-ancestor and equivalent-norm hypotheses, including the scale $\alpha/(2\beta)$ when $0<\alpha\le\beta$ and the new norm lies between $\alpha$ and $\beta$ times the original norm; they do not identify that span with the full dual or assert reflexivity for every forest. The paper controls midpoint lenses in Banach spaces defined by tree-segment norms. The formalization proves the following estimate in both the full dual of the finite-height forest space and the coordinate predual of the infinite-tree space. If $x$ is supported on a finite ancestral set $H$, $R\ge0$, and $\|x+y\|,\|x-y\|\le R$, then the part of $y$ outside $H$ has norm at most $2\sqrt{R^2-\|x\|^2}$. The formalization also covers selected consequences for averaged midpoint moduli and separated families of vectors, together with reflexivity and renorming obstructions. This scope concerns the segment-space results; the companion results on diamond energies remain separate. The paper studies embeddings of countably branching diamond graphs into Banach spaces built from tree segments. The formalization proves that every embedding of the depth-$k$ diamond with distortion $D$, at any positive scale, satisfies $1+k/4\le D^2$ in either of two spaces: the full dual of the completed finite-height forest space and the closed coordinate span in the dual of the infinite-tree space. The bound applies to all pairs of vertices and is unconditional. The formalization also contains selected graph deductions under explicit companion assumptions. Twenty-two of those companion inputs are assumed in these deductions; the diamond distortion bound above does not require them. The paper exhibits a real $L_1$ subspace with positive averaged midpoint convexity but no equivalent asymptotically uniformly convex norm. For every closed infinite-dimensional subspace whose unit ball is precompact in measure and which has the Daugavet property, the formalization computes the moduli at every unit vector: the averaged midpoint modulus is $\max(t/2,t-1)$ and the usual one-sided asymptotic modulus is $\max(0,t-2)$ for every $t>0$. The same formulas hold after taking the infimum over unit vectors, and every equivalent norm fails asymptotic uniform convexity. The formalization also constructs such a subspace on a countable product of unit intervals and proves that it has the stated measure-precompactness and Daugavet properties, so the modulus formulas apply to an actual example. The paper constructs Banach spaces from bounded tree potentials and path costs to separate averaged midpoint convexity from asymptotic uniform convexity. For the specified tree-potential completions, the formalization proves completeness, separability, infinite dimension, and an averaged midpoint modulus of at least $\sqrt{1+t^2/4}-1$ for $0<t<1$. No space linearly isomorphic to one of these completions is asymptotically uniformly convex. The formalization also covers selected path-cost duality and comparison results, clipping and energy estimates, and further renorming obstructions. These retain their stated support, head, and tail hypotheses; the remaining auxiliary assertions of the paper are outside this scope. The paper forms a real $L_1$ space from the closed span of products of independent multipliers along tree paths. For a positive, nonconstant multiplier of mean one and finite second moment, the formalization proves that this space is infinite-dimensional and has no equivalent asymptotically uniformly convex norm. For every $t>0$, the averaged midpoint modulus nevertheless has explicit positive lower bounds. If $G$ is a standard real Gaussian, the exponential-multiplier bound is $\frac{7t}{480}\mathbb E[(|G|-20/t)_+]$, where $u_+=\max(u,0)$. For squared-Gaussian multipliers, the bounds are $\frac18\Pr(|G|\ge4\sqrt2(2+\sqrt2)/t)$ and $\frac14\Pr(|G|\ge8\sqrt6/t)$. The paper constructs three Banach spaces from recursive tree potentials: a root-sum space, a zero-root space, and a joined space. The formalization proves that all three are infinite-dimensional and have no equivalent asymptotically uniformly convex norm. The root-sum and joined spaces have averaged midpoint modulus at least $t^3/128$ for $0<t<1$, and the root-sum modulus is positive for every $t>0$. The zero-root estimate retains its finite ancestral support and tail hypotheses, and the zero-root and joined spaces are reflexive. The formalization also covers a separated-midpoint result for the joined space and a variable-exponent model with its recursive norm, duality, projections, renorming obstruction, and sixth- and third-order stability estimates. The separation, sequence, support, and head assumptions in these results are essential parts of their statements. -/
