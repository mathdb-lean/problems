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

- problem_id: E1214
- collection: erdos
- question_id: erdos:1214
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1214.lean#erdos_1214
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x,y\geq 1$ be integers such that, for all $n\geq 1$, the set of primes dividing $x^{n}-1$ is equal to the set of primes dividing $y^n-1$. Must $x=y$? Erdős asked this at a 1988 number theory conference in Banff. A positive answer was given by Corrales-Rodrigáñez and Schoof [CoSc97].
- notes: Erdos Problem 1214 -- https://www.erdosproblems.com/1214
- track: solved
- answer_shape: decide
- source_stem: 1214
- mathdb_ref: erdos:1214
- source_namespace: Erdos1214
- source_theorem: erdos_1214
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ x y : ℕ, x ≥ 1 → y ≥ 1 →
      (∀ n : ℕ, n ≥ 1 → { p : ℕ | p.Prime ∧ p ∣ x ^ n - 1 } = { p : ℕ | p.Prime ∧ p ∣ y ^ n - 1 }) →
      x = y

end Problem
