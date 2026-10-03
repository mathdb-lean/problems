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

- problem_id: E309
- collection: erdos
- question_id: erdos:309
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/309.lean#erdos_309
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $N\geq 1$. How many integers can be written as the sum of distinct unit fractions with denominators from $\{1,\ldots,N\}$? Are there $o(\log N)$ such integers? If the number of such integers is $N(n)$ then it is trivial that $N(n)\leq \log n+O(1)$. Yokota [Yo97] proved that $N(n)\geq \log n-O(\log\log n)$. Croot [Cr99] proved that every integer at most $$\leq \sum_{n\leq N}\frac{1}{n}-(\tfrac{9}{2}+o(1))\frac{(\log\log N)^2}{\log N}$$ can be so represented. If $F(N)$ counts the number of integers which can be represented in this fashion, then the current best lower bound known is $$F(N) \geq \log N+\gamma -\left(\frac{\pi^2}{3}+o(1)\right)\frac{(\log\log N)^2}{\log N}$$ due to Yokota [Yo02]. The answer to the question is no: $F(N) \sim \log N$. Here $0$ (the empty sum) is counted.
- notes: Erdos Problem 309 -- https://www.erdosproblems.com/309
- track: solved
- answer_shape: decide
- source_stem: 309
- mathdb_ref: erdos:309
- source_namespace: Erdos309
- source_theorem: erdos_309
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics Topology

namespace Problem

/-- The number of integers which can be written as the sum of distinct unit fractions with
denominators from $\{1,\ldots,N\}$. -/
noncomputable def F (N : ℕ) : ℕ :=
  {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ ∑ n ∈ A, (1 / n : ℚ) = m}.ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        (fun N : ℕ => (F N : ℝ)) =o[atTop] fun N : ℕ => Real.log N

end Problem
