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

- problem_id: E419
- collection: erdos
- question_id: erdos:419
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/419.lean#erdos_419
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $\tau(n)$ counts the number of divisors of $n$, then what is the set of limit points of $$ \frac{\tau((n+1)!)}{\tau(n!)}? $$ The limit points are exactly $\{1\} \cup \{1+1/k : k \geq 1\}$.
- notes: Erdos Problem 419 -- https://www.erdosproblems.com/419
- track: solved
- answer_shape: proof
- source_stem: 419
- mathdb_ref: erdos:419
- source_namespace: Erdos419
- source_theorem: erdos_419
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped ArithmeticFunction.sigma

namespace Problem

/-- The ratio $\sigma_0((n+1)!)/\sigma_0(n!)$, where $\sigma_0$ is the divisor-counting function. -/
noncomputable def factorialDivisorRatio (n : ℕ) : ℝ :=
  (σ 0 (n + 1).factorial : ℝ) / (σ 0 n.factorial : ℝ)

/-- The set $\{1\} \cup \{1+1/k : k \geq 1\}$. -/
def limitPointSet : Set ℝ :=
  {1} ∪ {x | ∃ k : ℕ, 1 ≤ k ∧ x = 1 + 1 / (k : ℝ)}

abbrev Target : Prop :=
    {x : ℝ | MapClusterPt x atTop factorialDivisorRatio} = limitPointSet

end Problem
