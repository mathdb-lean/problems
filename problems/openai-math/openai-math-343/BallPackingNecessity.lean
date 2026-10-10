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

- problem_id: BallPackingNecessity
- collection: openai-math
- question_id: openai-math:343
- source: openai-math
- source_locator: lean/ComparatorChallenges/BallPackingNecessity.lean#OAI.HigherDimensionalBallPacking.packing_necessity
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the Siegel–Yao conjecture for arbitrary capacities in every dimension $`2n\ge6`$. Finitely many closed symplectic balls of capacities $`R_1,\ldots,R_k`$ embed disjointly into an open ball of capacity R exactly when $`\sum_iR_i^n\lt R^n`$ and $`R_i+R_j\lt R`$ for every distinct pair i, j. ([Lean](lean/docs/343.md)) We prove that, for all integers n ≥ 3 and k ≥ 1 and all positive real capacities $`R_1,\ldots,R_k`$, the closed standard symplectic $`2n`$-balls of these capacities embed disjointly into the interior of a ball of capacity R &gt; 0 if and only if
- notes: OpenAI math result family 343, Symplectic ball packing in higher dimensions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/343.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.HigherDimensionalBallPacking.packing_necessity
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.BallPacking.Necessity.Main
- source_papers: preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf
- source_scope_note: lean/docs/343.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

abbrev Phase (n : ℕ) := Fin n → ℂ

noncomputable def capacity {n : ℕ} (z : Phase n) : ℝ :=
  Real.pi * ∑ j, Complex.normSq (z j)

def closedBall (n : ℕ) (r : ℝ) : Set (Phase n) := {z | capacity z ≤ r}

def openBall (n : ℕ) (r : ℝ) : Set (Phase n) := {z | capacity z < r}

noncomputable def standardForm {n : ℕ} (u v : Phase n) : ℝ :=
  ∑ j, ((u j).re * (v j).im - (u j).im * (v j).re)

 
def SymplecticOn {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ ∞ f U ∧
    Topology.IsEmbedding (fun x : U => f x) ∧
    ∀ x ∈ U, ∀ u v : Phase n,
      standardForm (fderiv ℝ f x u) (fderiv ℝ f x v) = standardForm u v

 
def HasPacking (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  ∃ (U : Fin k → Set (Phase n)) (f : Fin k → Phase n → Phase n),
    (∀ i, closedBall n (r i) ⊆ U i ∧ SymplecticOn (U i) (f i) ∧
      Set.MapsTo (f i) (closedBall n (r i)) (openBall n R)) ∧
    (∀ i j, i ≠ j →
      Disjoint (f i '' closedBall n (r i)) (f j '' closedBall n (r j)))

def PackingInequalities (n k : ℕ) (R : ℝ) (r : Fin k → ℝ) : Prop :=
  (∑ i, r i ^ n) < R ^ n ∧ ∀ i j, i ≠ j → r i + r j < R

def packing_necessity_statement : Prop :=
  ∀ (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) (R : ℝ) (r : Fin k → ℝ) (hR : 0 < R) (hr : ∀ i, 0 < r i) (hp : HasPacking n k R r),
    PackingInequalities n k R r

end HigherDimensionalBallPacking

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.HigherDimensionalBallPacking.packing_necessity_statement

end Problem

/- Formalization scope, from lean/docs/343.md: The formalization proves Siegel and Yao's ball-packing criterion in every symplectic dimension $2n$ with $n\ge3$. For $k\ge1$ closed standard balls of positive capacities $R_1,\ldots,R_k$, disjoint symplectic embeddings into the interior of a ball of capacity $R$ exist exactly when $\sum_i R_i^n<R^n$ and $R_i+R_j<R$ for all $i\ne j$. Capacity is $\pi$ times squared Euclidean radius, and each embedding is defined on a neighborhood of its closed source ball. The linked statements include both the full equivalence and the necessity direction. -/
