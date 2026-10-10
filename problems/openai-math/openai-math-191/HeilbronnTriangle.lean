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

- problem_id: HeilbronnTriangle
- collection: openai-math
- question_id: openai-math:191
- source: openai-math
- source_locator: lean/ComparatorChallenges/HeilbronnTriangle.lean#OAI.Problem355.heilbronn_power_lower_bound
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every sufficiently large n, constructs n points in the unit square such that every triangle has area at least $`n^{-2+c}`$ for one absolute c &gt; 0. This disproves the conjectured almost-n−2 upper bound in Heilbronn's triangle problem, which asks how large the smallest determined triangle can be. ([Lean](lean/docs/191.md)) There are absolute constants $`\eta,c_1\gt 0`$ such that, for every sufficiently large integer n, one can choose n points in the unit square so that every triangle they determine has area at least $`c_1n^{-2+\eta}`$. Thus the almost n−2 upper-bound formulation of Heilbronn's triangle problem is false. The exponent η is fixed but extremely small.
- notes: OpenAI math result family 191, A power improvement in the Heilbronn triangle lower bound -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/191.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem355.heilbronn_power_lower_bound OAI.Problem355.almost_n_minus_two_refuted
- source_theorem_count: 2
- source_solution_module: OAI.Geometry.HeilbronnTriangle.Main
- source_papers: preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026/main.pdf
- source_scope_note: lean/docs/191.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace Problem355

abbrev Point := ℝ × ℝ

def triangleArea (p q r : Point) : ℝ :=
  abs ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) / 2

def pointInUnitSquare (p : Point) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1

def pointsInUnitSquare (P : Finset Point) : Prop := by
  classical
  exact ∀ p, p ∈ P → pointInUnitSquare p

def triangleAreasAtLeast (P : Finset Point) (a : ℝ) : Prop := by
  classical
  exact ∀ p, p ∈ P → ∀ q, q ∈ P → ∀ r, r ∈ P →
    p ≠ q → p ≠ r → q ≠ r → a ≤ triangleArea p q r

def hasTriangleAreaAtMost (P : Finset Point) (a : ℝ) : Prop := by
  classical
  exact ∃ p, p ∈ P ∧ ∃ q, q ∈ P ∧ ∃ r, r ∈ P ∧
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r ≤ a

def heilbronnD : ℕ := 41

def heilbronnM : ℕ := Nat.choose (4 * heilbronnD - 1) heilbronnD

def heilbronnT : ℕ := Nat.choose heilbronnM 3

def heilbronnK : ℕ := heilbronnT ^ 2 + 1

def heilbronnExponent : ℝ :=
  1 / (100000 * (heilbronnK : ℝ))

def eventualAlmostUpperBound (epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → 3 ≤ n →
    ∀ P : Finset Point, P.card = n → pointsInUnitSquare P →
      hasTriangleAreaAtMost P
        (C * Real.rpow (n : ℝ) (-2 + epsilon))

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

def heilbronn_power_lower_bound_statement : Prop :=
  0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
      Filter.Tendsto n Filter.atTop Filter.atTop ∧ ∀ j : ℕ,
        3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
        triangleAreasAtLeast (P j)
          (Real.rpow (n j : ℝ) (-2 + heilbronnExponent))

def almost_n_minus_two_refuted_statement : Prop :=
  0 < heilbronnExponent / 2 ∧
      ¬ eventualAlmostUpperBound (heilbronnExponent / 2)

end Problem355

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem355.heilbronn_power_lower_bound_statement ∧
  _root_.OAI.Problem355.almost_n_minus_two_refuted_statement

end Problem

/- Formalization scope, from lean/docs/191.md: Heilbronn's triangle problem asks how large the smallest triangle determined by $n$ points in the unit square can be. The formalization constructs an unbounded sequence of sizes $n$ and point sets for which every triangle has area at least $n^{-2+\eta}$, for one fixed $\eta>0$. It consequently refutes the proposed upper bound of order $n^{-2+\varepsilon}$ for every $\varepsilon>0$. The linked construction is for an unbounded sequence of sizes; the paper's statement for every sufficiently large $n$ is broader. -/
