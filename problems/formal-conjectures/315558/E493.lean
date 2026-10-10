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

- problem_id: E493
- collection: erdos
- question_id: erdos:493
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/493.lean#erdos_493
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist a $k$ such that every sufficiently large integer can be written in the form $$\prod_{i=1}^k a_i - \sum_{i=1}^k a_i$$ for some integers $a_i\geq 2$? Erdős attributes this question to Schinzel. Eli Seamans has observed that the answer is yes (with $k=2$) for a very simple reason: $n = 2(n+2)-(2+(n+2))$. There may well have been some additional constraint in the problem as Schinzel posed it, but [Er61] does not record what this is.
- notes: Erdos Problem 493 -- https://www.erdosproblems.com/493
- track: solved
- answer_shape: decide
- source_stem: 493
- mathdb_ref: erdos:493
- source_namespace: Erdos493
- source_theorem: erdos_493
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
          ∃ a : Fin k → ℤ,
            (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
            (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n

end Problem
