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

- problem_id: E672_refute
- collection: erdos
- question_id: erdos:672
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/672.lean#erdos_672
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Can the product of an arithmetic progression of positive integers $n, n + d, ..., n + (k - 1)d$ of length $k ≥ 4$, with $(n, d) = 1$, be a perfect power? Erdős believed not, i.e. that `Erdos672With k l` holds for all $k ≥ 4$ and $l > 1$.
- notes: Erdos Problem 672 -- https://www.erdosproblems.com/672
- track: open
- answer_shape: refute
- pair_id: E672
- pair_role: refute
- source_stem: 672
- mathdb_ref: erdos:672
- source_namespace: Erdos672
- source_theorem: erdos_672
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Erdős problem 672 conjectures that the below holds for any $k ≥ 4$ and $l > 1$. -/
def Erdos672With (k l : ℕ) : Prop :=
  ∀ (s : Finset ℕ), s.card = k → ∀ᵉ (n > 0) (d > 0), n.gcd d = 1 →
    Set.IsAPOfLengthWith s k n d → ∀ q, ∏ i ∈ s, i ≠ q ^ l

abbrev Target : Prop :=
    ¬ (
      ∃ᵉ (k ≥ 4) (l > 1), ¬ Erdos672With k l
    )

end Problem
