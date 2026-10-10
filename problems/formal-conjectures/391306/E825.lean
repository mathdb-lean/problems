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

- problem_id: E825
- collection: erdos
- question_id: erdos:825
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/825.lean#erdos_825
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there an absolute constant $C > 0$ such that every integer $n$ with $\sigma(n) > Cn$ is the distinct sum of proper divisors of $n$? This has been solved in the affirmative by Larsen - in fact, for any $\epsilon>0$ there exists $L$ such that if $n$ has only prime divisors $>L$ and $\sigma(n)>(2+\epsilon)n$ then $n$ is the distinct sum of proper divisors of $n$.
- notes: Erdos Problem 825 -- https://www.erdosproblems.com/825
- track: solved
- answer_shape: decide
- source_stem: 825
- mathdb_ref: erdos:825
- source_namespace: Erdos825
- source_theorem: erdos_825
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped ArithmeticFunction.sigma

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ (C : ℝ) (_ : C > 0),
      ∀ (n) (_ : σ 1 n > C * n),
        ∃ s ⊆ n.properDivisors, n = s.sum id

end Problem
