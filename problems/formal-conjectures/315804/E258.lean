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

- problem_id: E258
- collection: erdos
- question_id: erdos:258
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/258.lean#erdos_258
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_n \to \infty$ be a sequence of non-zero natural numbers. Is $\sum_n \frac{d(n)}{(a_1 ... a_n)}$ irrational, where $d(n)$ is the number of divisors of $n$? This was proved affirmatively by Chojecki and GPT-5.4 Pro [Ch26], and formalised in Lean by ster-oc [St26].
- notes: Erdos Problem 258 -- https://www.erdosproblems.com/258
- track: solved
- answer_shape: decide
- source_stem: 258
- mathdb_ref: erdos:258
- source_namespace: Erdos258
- source_theorem: erdos_258
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (a : ℕ → ℕ), (∀ n, 2 ≤ a n) →
        Filter.Tendsto a Filter.atTop Filter.atTop →
        Irrational (∑' (n : ℕ), ((n + 1).divisors.card / ∏ i ∈ Finset.Icc 1 (n + 1), a i))

end Problem
