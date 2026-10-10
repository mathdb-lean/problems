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

- problem_id: EgyptianFractions
- collection: openai-math
- question_id: openai-math:025
- source: openai-math
- source_locator: lean/ComparatorChallenges/EgyptianFractions.lean#OAI.Problem337.egyptian_length_is_minimum
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Every rational $`a/b`$ with $`1\le a\lt b`$ is a sum of $`O(\log\log b)`$ distinct positive unit fractions. The worst-case minimum number of terms has the same order, resolving Erdős’s conjecture on short Egyptian fractions. ([Lean](lean/docs/025.md)) We prove a conjecture of Erdős: for every sufficiently large integer b, every rational number $`a/b`$ with $`1\le a\lt b`$ is a sum of $`O(\log\log b)`$ distinct positive unit fractions, with an absolute implied constant. This order is best possible when the numerator varies. We also show that both the number of expansions of 1 with exactly k distinct terms and the least integer at least 2 that never occurs as a denominator in such an expansion grow doubly exponentially in k: their double logarithms have order k.
- notes: OpenAI math result family 025, Short Egyptian fractions -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/025.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem337.egyptian_length_is_minimum OAI.Problem337.main_double_log_order OAI.Problem337.one_expansions_finite_and_bounded OAI.Problem337.counting_double_log_order OAI.Problem337.exact_marker_padding OAI.Problem337.every_exact_marker_occurs OAI.Problem337.quantitative_marked_length OAI.Problem337.missing_denominator_semantics OAI.Problem337.prescribed_denominator_corollary
- source_theorem_count: 9
- source_solution_module: OAI.NumberTheory.EgyptianFractions.Main
- source_main_result: OAI.Problem337.prescribed_denominator_corollary
- source_papers: preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf
- source_scope_note: lean/docs/025.md
- source_field: NumberTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem337

def IsEgyptianExpansion {k : ℕ} (x : ℚ) (n : Fin k → ℕ) : Prop :=
  (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
    (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x

def egyptianLengths (a b : ℕ) : Set ℕ :=
  {k | ∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n}

def egyptianLength (a b : ℕ) : ℕ :=
  sInf (egyptianLengths a b)

def maxEgyptianLength (b : ℕ) : ℕ :=
  (Finset.range b).sup (fun a => if 1 ≤ a then egyptianLength a b else 0)

def IsOneExpansion {k : ℕ} (n : Fin k → ℕ) : Prop :=
  (∀ i, 1 ≤ n i) ∧ StrictMono n ∧
    (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = 1

def OneExpansions (k : ℕ) : Set (Fin k → ℕ) :=
  {n | IsOneExpansion n}

def F (k : ℕ) : ℕ :=
  (OneExpansions k).ncard

def D (k : ℕ) : Set ℕ :=
  {m | 2 ≤ m ∧ ∃ n : Fin k → ℕ,
    IsOneExpansion n ∧ ∃ i : Fin k, n i = m}

def missingDenominators (k : ℕ) : Set ℕ :=
  {m : ℕ | 2 ≤ m} \ D k

def v (k : ℕ) : ℕ :=
  sInf (missingDenominators k)

def prescribedSlope (k : ℕ) : ℝ :=
  Real.log (Real.log (v k : ℝ)) / (k : ℝ)

def egyptian_length_is_minimum_statement : Prop :=
  ∀ a b : ℕ, 1 ≤ a → a < b →
  (∃ n : Fin (egyptianLength a b) → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) ∧
  (∀ k : ℕ, (∃ n : Fin k → ℕ,
    IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) →
    egyptianLength a b ≤ k)

def main_double_log_order_statement : Prop :=
  ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∃ b0 : ℕ,
  ∀ b : ℕ, b0 ≤ b →
    c1 * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) ∧
    (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ))

def one_expansions_finite_and_bounded_statement : Prop :=
  (∀ k : ℕ, Set.Finite (OneExpansions k) ∧
    F k ≤ k ^ (2 ^ k - 1)) ∧
  (∀ k : ℕ, ∀ n : Fin k → ℕ, IsOneExpansion n →
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val))

def counting_double_log_order_statement : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
  ∀ k : ℕ, k0 ≤ k →
    c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
    Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ)

def exact_marker_padding_statement : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
  ∀ m : ℕ, (∃ i : Fin r, n i = m) →
    ∃ n' : Fin (r + 1) → ℕ,
      IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m

def every_exact_marker_occurs_statement : Prop :=
  ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k

def quantitative_marked_length_statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mε : ℕ, 2 ≤ mε ∧
  ∀ m : ℕ, mε ≤ m →
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧
      (∃ i : Fin k, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ))

def missing_denominator_semantics_statement : Prop :=
  ∀ k : ℕ,
  Set.Finite (D k) ∧
  (∃ m : ℕ, m ∈ missingDenominators k) ∧
  2 ≤ v k ∧ v k ∉ D k ∧
  (∀ m : ℕ, 2 ≤ m → m < v k → m ∈ D k) ∧
  (1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1)))

def prescribed_denominator_corollary_statement : Prop :=
  (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
    v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
  (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
    Filter.liminf prescribedSlope Filter.atTop ≤
      Filter.limsup prescribedSlope Filter.atTop ∧
    Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
  (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
    ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ))

end Problem337

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem337.egyptian_length_is_minimum_statement ∧
  _root_.OAI.Problem337.main_double_log_order_statement ∧
  _root_.OAI.Problem337.one_expansions_finite_and_bounded_statement ∧
  _root_.OAI.Problem337.counting_double_log_order_statement ∧
  _root_.OAI.Problem337.exact_marker_padding_statement ∧
  _root_.OAI.Problem337.every_exact_marker_occurs_statement ∧
  _root_.OAI.Problem337.quantitative_marked_length_statement ∧
  _root_.OAI.Problem337.missing_denominator_semantics_statement ∧
  _root_.OAI.Problem337.prescribed_denominator_corollary_statement

end Problem

/- Formalization scope, from lean/docs/025.md: An Egyptian-fraction expansion writes a rational number as a sum of distinct unit fractions. The formalization proves that every $a/b$ with $1\le a<b$ has such an expansion and that the largest minimum length at denominator $b$ is $\Theta(\log\log b)$. If $F(k)$ counts exact $k$-term expansions of $1$, it also proves $\log\log F(k)=\Theta(k)$ and bounds every denominator in such an expansion. Every integer $m\ge2$ occurs as a denominator in an expansion of $1$, with length eventually at most $(257/\log2+\varepsilon)\log\log m$ for every $\varepsilon>0$; padding can preserve that denominator. If $v(k)$ is the least integer at least $2$ absent from all exact $k$-term expansions of $1$, then eventually $e^{e^{k/600}}\le v(k)\le1+k^{2^{k-1}}$, and $\liminf_{k\to\infty}\log\log v(k)/k\ge\log2/257$. -/
