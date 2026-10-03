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

- problem_id: E287_prove
- collection: erdos
- question_id: erdos:287
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/287.lean#erdos_287
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq2$. Is it true that, for any distinct integers $1 < n_1 < \cdots < n_k$ such that $\sum_{i=1}^k \frac{1}{n_i} = 1$, we must have $\max(n_{i+1} - n_i) \geq 3$?
- notes: Erdos Problem 287 -- https://www.erdosproblems.com/287
- track: open
- answer_shape: prove
- pair_id: E287
- pair_role: prove
- source_stem: 287
- mathdb_ref: erdos:287
- source_namespace: Erdos287
- source_theorem: erdos_287
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The maximum gap between consecutive terms of a finite sequence `s : Fin k → ℕ`,
i.e., $\max_{0 \le i < k-1} (s(i+1) - s(i))$. -/
def max_gap (k : ℕ) (s : Fin k → ℕ ) : ℕ  :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s  ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

abbrev Target : Prop :=
    ∀ (k : ℕ) (hk : 2 ≤ k) (s : Fin k → ℕ),
        StrictMono s → 1 < s ⟨0, by omega⟩ →
        ∑ i : Fin k, 1/ (s i : ℝ) = 1 →
        3 ≤ max_gap k s

end Problem
