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

- problem_id: E322_prove
- collection: erdos
- question_id: erdos:322
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/322.lean#erdos_322
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 3$ and $A\subset \mathbb{N}$ be the set of $k$th powers. What is the order of growth of $1_A^{(k)}(n)$, i.e. the number of representations of $n$ as the sum of $k$ many $k$th powers? Does there exist some $c>0$ and infinitely many $n$ such that $$1_A^{(k)}(n) >n^c?$$
- notes: Erdos Problem 322 -- https://www.erdosproblems.com/322
- track: open
- answer_shape: prove
- pair_id: E322
- pair_role: prove
- source_stem: 322
- mathdb_ref: erdos:322
- source_namespace: Erdos322
- source_theorem: erdos_322
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- For `k ≥ 3`, the number of ordered representations of `n` as a sum of `k` many `k`th
powers of positive integers. The bases can be restricted to the interval from `1` to `n`,
since `x ≤ x ^ k` for positive `x`. -/
def representationCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
    (fun a ↦ (∀ i, 0 < (a i : ℕ)) ∧ ∑ i, (a i : ℕ) ^ k = n)).card

abbrev Target : Prop :=
    ∀ k : ℕ, 3 ≤ k → ∃ c > (0 : ℝ),
          {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite

end Problem
