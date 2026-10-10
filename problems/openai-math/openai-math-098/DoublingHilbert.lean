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

- problem_id: DoublingHilbert
- collection: openai-math
- question_id: openai-math:098
- source: openai-math
- source_locator: lean/ComparatorChallenges/DoublingHilbert.lean#OAI.DoublingHilbert.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every infinite-dimensional real Banach space contains a compact doubling set that admits no bi-Lipschitz embedding into any finite-dimensional normed space. The doubling constant is universal. This answers the Lang–Plaut problem negatively, even for compact subsets of Hilbert space. ([Lean](lean/docs/098.md)) Every infinite-dimensional real Banach space contains a compact doubling subset that admits no bi-Lipschitz embedding into any finite-dimensional real normed space. The doubling constant has a universal bound, independent of the ambient Banach space. This answers the Lang–Plaut problem negatively, even for compact subsets of Hilbert space.
- notes: OpenAI math result family 098, Compact counterexamples to bi-Lipschitz dimension reduction -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/098.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.DoublingHilbert.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.DoublingHilbert.Main
- source_main_result: OAI.DoublingHilbert.main
- source_papers: preprints/A-doubling-Hilbert-subset-with-no-finite-dimensional-bi-Lipschitz-embedding-September-25-2026/main.pdf
- source_scope_note: lean/docs/098.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace DoublingHilbert

abbrev RealL2 := lp (fun _ : ℕ => ℝ) 2

/-- Intrinsic open-ball doubling with a specified integer bound and centers in the subset. -/
def DoublingAtMost (S : Set RealL2) (bound : ℕ) : Prop :=
  ∀ x : S, ∀ r : ℝ, 0 < r →
    ∃ centers : Finset S, centers.card ≤ bound ∧
      ∀ y : S, dist y x < r → ∃ c ∈ centers, dist y c < r / 2

/-- Finite distortion includes an arbitrary positive change of scale. -/
def AdmitsBiLipschitzEmbedding (S : Set RealL2) (k : ℕ) : Prop :=
  ∃ f : S → EuclideanSpace ℝ (Fin k),
    ∃ a : ℝ, 0 < a ∧ ∃ D : ℝ, 1 ≤ D ∧
      ∀ x y : S, a * dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ D * a * dist x y

/-- A single fixed subset, independent of dimension and distortion. -/
def main_statement : Prop :=
  ∃ S : Set RealL2,
    DoublingAtMost S 76800 ∧
      ∀ k : ℕ, 0 < k → ¬ AdmitsBiLipschitzEmbedding S k

end DoublingHilbert

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.DoublingHilbert.main_statement

end Problem

/- Formalization scope, from lean/docs/098.md: The formalized result gives a doubling subset of real $\ell_2$, with doubling constant at most $76800$, that admits no bi-Lipschitz embedding into any finite-dimensional Euclidean space at any finite distortion. A companion gives one universal doubling constant such that every infinite-dimensional real Banach space contains a compact doubling subset with no bi-Lipschitz embedding into any finite-dimensional normed space. -/
