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

- problem_id: PrimeGaps
- collection: openai-math
- question_id: openai-math:026
- source: openai-math
- source_locator: lean/ComparatorChallenges/PrimeGaps.lean#OAI.Problem344.large_gaps_and_ratio_density
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: For every fixed C &gt; 0, a positive proportion of consecutive prime gaps exceed $`C\log p_n`$, throughout every sufficiently large initial segment of the primes. The proportion may depend on C. Consequently, the indices where $`p_n/n`$ increases have positive lower density, answering Erdős and Prachar. ([Lean](lean/docs/026.md)) For every fixed C &gt; 0, we prove that a positive proportion of consecutive prime gaps exceed $`C\log p`$, where p is the smaller prime. The proportion is bounded below for every sufficiently large initial segment of the prime sequence, with a constant depending on C. It follows that the indices at which $`p_n/n`$ increases have positive lower asymptotic density, answering a question of Erdős and Prachar.
- notes: OpenAI math result family 026, Positive lower density of large prime gaps -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/026.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Problem344.large_gaps_and_ratio_density
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.PrimeGaps.RatioCorollary
- source_papers: preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/main.pdf
- source_scope_note: lean/docs/026.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace LargePrimeGaps

noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def largeGapIndices (C : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    C * Real.log (prime n : ℝ) < (prime (n + 1) : ℝ) - (prime n : ℝ)

end LargePrimeGaps

noncomputable section

namespace Problem344

def primeAt (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

def initialCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

def lowerAsymptoticDensity (A : Set ℕ) : ℝ :=
  sSup {d : ℝ | ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    d ≤ (initialCount A N : ℝ) / (N : ℝ)}

def ratioIncreaseIndices : Set ℕ :=
  {n | 1 ≤ n ∧
    (primeAt n : ℝ) / (n : ℝ) <
      (primeAt (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ)}

def large_gaps_and_ratio_density_statement : Prop :=
  (∀ C : ℝ, 0 < C →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * (N : ℝ) ≤ ((LargePrimeGaps.largeGapIndices C N).card : ℝ)) ∧
    0 < lowerAsymptoticDensity ratioIncreaseIndices

end Problem344

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem344.large_gaps_and_ratio_density_statement

end Problem

/- Formalization scope, from lean/docs/026.md: The formalized supplement proves that the indices $n$ for which $p_n/n<p_{n+1}/(n+1)$ have positive lower asymptotic density, where $p_n$ is the $n$th prime. Thus the normalized prime sequence has a positive-density set of increases. This is the prime-ratio corollary associated with the paper's theorem on a positive lower density of large prime gaps. -/
