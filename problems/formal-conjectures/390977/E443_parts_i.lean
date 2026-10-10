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

- problem_id: E443_parts_i
- collection: erdos
- question_id: erdos:443
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/443.lean#erdos_443.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $m,n\geq 1$. What is $$\# \{ k(m-k) : 1\leq k\leq m/2\} \cap \{ l(n-l) : 1\leq l\leq n/2\}?$$ Can it be arbitrarily large? This was solved independently by Hegyvári [He25] and Cambie (unpublished), who show that if $m>n$ then the set in question has size $$\leq m^{O(1/\log\log m)},$$ and that for any integer $s$ there exist infinitely many pairs $(m,n)$ such that the set in question has size $s$.
- notes: Erdos Problem 443 -- https://www.erdosproblems.com/443
- track: solved
- answer_shape: decide
- source_stem: 443
- mathdb_ref: erdos:443
- source_namespace: Erdos443
- source_theorem: erdos_443.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/--
The set $\{k(m-k) : 1\leq k\leq m/2\}$, where `m / 2` is `ℕ` floor division.
-/
def A (m : ℕ) : Finset ℕ := (Finset.Icc 1 (m / 2)).image fun k => k * (m - k)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ s : ℕ, ∃ m n : ℕ, n < m ∧ s ≤ (A n ∩ A m).card

end Problem
