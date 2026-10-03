/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The mathdb-lean Authors.

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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E839_parts_ii_prove
- collection: erdos
- question_id: erdos:839
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/839.lean#erdos_839.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Erdős Problem 839 (Part 2, stronger) [Er78f][Er92c]: Let $1 \leq a_1 < a_2 < \cdots$ be a strictly increasing sequence of positive integers such that no $a_i$ is the sum of consecutive $a_j$ for $j < i$. Is it true that $\lim_{x \to \infty} \frac{1}{\log x} \sum_{a_n < x} \frac{1}{a_n} = 0$? This is equivalent to asking whether the range $\{a_1,a_2,\ldots\}$ has logarithmic density zero (see `Set.HasLogDensity`).
- notes: Erdos Problem 839 -- https://www.erdosproblems.com/839
- track: open
- answer_shape: prove
- pair_id: E839_parts_ii
- pair_role: prove
- source_stem: 839
- mathdb_ref: erdos:839
- source_namespace: Erdos839
- source_theorem: erdos_839.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real Finset
open scoped ENNReal

namespace Problem

/-- A sequence $a : \mathbb{N} \to \mathbb{N}$ is "sum-of-consecutive-free" if no term equals
the sum of a contiguous block of earlier terms. That is, for all $i$,
$a_i \neq a_j + a_{j+1} + \cdots + a_k$ for any $j \leq k < i$. -/
def SumOfConsecutiveFree (a : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, ∀ j k : ℕ, j ≤ k → k < i →
    a i ≠ ∑ l ∈ Finset.Icc j k, a l

abbrev Target : Prop :=
    ∀ (a : ℕ → ℕ), (∀ n, 1 ≤ a n) → StrictMono a → SumOfConsecutiveFree a →
        Set.HasLogDensity (Set.range a) 0

end Problem
