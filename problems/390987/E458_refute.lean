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

- problem_id: E458_refute
- collection: erdos
- question_id: erdos:458
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/458.lean#erdos_458
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\operatorname{lcm}(1, \dots, n)$ denote the least common multiple of $\{1, \dots, n\}$. Let $p_k$ be the $k$-th prime. Is it true that for all $k \geq 1$, $\operatorname{lcm}(1, \dots, p_{k+1}-1) < p_k \cdot \operatorname{lcm}(1, \dots, p_k)$?
- notes: Erdos Problem 458 -- https://www.erdosproblems.com/458
- track: open
- answer_shape: refute
- pair_id: E458
- pair_role: refute
- source_stem: 458
- mathdb_ref: erdos:458
- source_namespace: Erdos458
- source_theorem: erdos_458
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The least common multiple of the integers in the set $\{1, \dots, n\}$.
-/
def lcm_upto (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

abbrev Target : Prop :=
    ¬ (
      ∀ k : ℕ, lcm_upto ((k + 1).nth Prime - 1)
       < k.nth Prime * lcm_upto (k.nth Prime)
    )

end Problem
