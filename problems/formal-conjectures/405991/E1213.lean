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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E1213
- collection: erdos
- question_id: erdos:1213
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1213.lean#erdos_1213
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a,K\geq 1$. Does there exist $f(a,K)$ such that if $a=a_1<\cdots <a_s$ is a sequence of integers with $a_s> f(a,K)$ and with bounded gaps $a_{i+1}-a_i\leq K$ then there are two distinct intervals $I$ and $J$ such that $$\sum_{i\in I}a_i=\sum_{j\in J}a_j?$$ Hegyvári [He86] has proved the answer is yes, and gives an explicit bound of the shape $f(a,K) \ll ae^{O(K)}$. Hegyvári believes that the exponential dependence on $K$ here is not best possible.
- notes: Erdos Problem 1213 -- https://www.erdosproblems.com/1213
- track: solved
- answer_shape: decide
- source_stem: 1213
- mathdb_ref: erdos:1213
- source_namespace: Erdos1213
- source_theorem: erdos_1213
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/--
A finite sequence `A 0, …, A (s - 1)` has two distinct (nonempty) index intervals
`[u, v)` and `[x, y)` with the same sum.
-/
def HasEqualIntervalSums (A : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ u v x y : ℕ, u < v ∧ v ≤ s ∧ x < y ∧ y ≤ s ∧ (u, v) ≠ (x, y) ∧
    ∑ i ∈ Finset.Ico u v, A i = ∑ i ∈ Finset.Ico x y, A i

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ a K : ℕ, 1 ≤ a → 1 ≤ K → ∃ f : ℕ,
        ∀ (s : ℕ) (A : ℕ → ℕ), 0 < s → A 0 = a → StrictMonoOn A (Set.Iio s) →
          (∀ i, i + 1 < s → A (i + 1) - A i ≤ K) → f < A (s - 1) → HasEqualIntervalSums A s

end Problem
