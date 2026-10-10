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

- problem_id: LogBrunnMinkowski
- collection: openai-math
- question_id: openai-math:091
- source: openai-math
- source_locator: lean/ComparatorChallenges/LogBrunnMinkowski.lean#OAI.LogBrunnMinkowski.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the logarithmic Brunn–Minkowski inequality for origin-symmetric convex bodies in every dimension, and the scalar-dilation B-conjecture for all even log-concave Radon measures. For Lebesgue volume it also proves the additive Lp Brunn–Minkowski inequality for full-dimensional origin-symmetric convex bodies throughout $`0\lt p\lt 1`$. ([Lean](lean/docs/091.md)) We prove the logarithmic Brunn–Minkowski conjecture for arbitrary origin-symmetric convex bodies in every dimension. The theorem also gives the symmetric Lp Brunn–Minkowski inequality for every $`0\lt p\lt 1`$. Combined with Saroglou's transfer theorem and a support-subspace reduction, it yields the logarithmic inequality for every even log-concave Radon measure and the scalar-dilation $`(B)`$-conjecture.
- notes: OpenAI math result family 091, Logarithmic and <i>L</i><sub><i>p</i></sub> Brunn–Minkowski inequalities and the B-conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/091.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.LogBrunnMinkowski.main
- source_theorem_count: 1
- source_solution_module: OAI.Geometry.LogVolume.BrunnMinkowski
- source_main_result: OAI.LogBrunnMinkowski.main
- source_papers: preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf
- source_scope_note: lean/docs/091.md
- source_field: Geometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LogBrunnMinkowski

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def OriginSymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x : Space n => ⟪x, u⟫_ℝ) '' K)

def wulff {n : ℕ} (f : Space n → ℝ) : Set (Space n) :=
  {x | ∀ u, ‖u‖ = 1 → ⟪x, u⟫_ℝ ≤ f u}

def logCombination {n : ℕ} (K L : Set (Space n)) (t : ℝ) :
    Set (Space n) :=
  wulff (fun u => (support K u) ^ (1 - t) * (support L u) ^ t)

def main_statement : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (K L : Set (Space n)) (hK : IsConvexBody K) (hL : IsConvexBody L) (hsK : OriginSymmetric K) (hsL : OriginSymmetric L) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
    (volume K) ^ (1 - t) * (volume L) ^ t ≤ volume (logCombination K L t)

end LogBrunnMinkowski

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.LogBrunnMinkowski.main_statement

end Problem

/- Formalization scope, from lean/docs/091.md: The logarithmic Brunn–Minkowski conjecture asserts that logarithmic interpolation of origin-symmetric convex bodies preserves the geometric-mean lower bound for volume. The formalized result proves, for every dimension $n\ge1$, such bodies $K,L\subset\mathbb R^n$, and $0\le t\le1$, that their logarithmic Wulff combination has volume at least $|K|^{1-t}|L|^t$. It assumes neither boundary smoothness nor coordinatewise unconditionality. -/
