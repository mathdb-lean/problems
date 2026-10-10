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

- problem_id: E681_refute
- collection: erdos
- question_id: erdos:681
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/681.lean#erdos_681
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős problem 681.** Is it true that for all large $n$ there exists $k$ such that $n + k$ is composite and $p(n+k) > k^2$, where $p(m)$ is the least prime factor of $m$ ?
- notes: Erdos Problem 681 -- https://www.erdosproblems.com/681
- track: open
- answer_shape: refute
- pair_id: E681
- pair_role: refute
- source_stem: 681
- mathdb_ref: erdos:681
- source_namespace: Erdos681
- source_theorem: erdos_681
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- `IsLPF p m` says that `p` is the least prime factor of `m`. -/
def IsLPF (p m : ℕ) : Prop := p.Prime ∧ p ∣ m ∧ ∀ q, q.Prime ∧ q ∣ m → p ≤ q

abbrev Target : Prop :=
    ¬ (
      ∀ᶠ n in .atTop, ∃ k > 0, (n + k).Composite ∧ ∀ p, IsLPF p (n + k) → p > k ^ 2
    )

end Problem
