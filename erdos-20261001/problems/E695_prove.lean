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

- problem_id: E695_prove
- collection: erdos
- question_id: erdos:695
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/695.lean#erdos_695
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $q_1 < q_2 < \cdots$ be a sequence of primes such that $q_{i + 1} \equiv 1 \pmod{q_i}$. Is it true that $$ \lim_{k \to \infty} q_k^{1/k} = \infty? $$
- notes: Erdos Problem 695 -- https://www.erdosproblems.com/695
- track: open
- answer_shape: prove
- pair_id: E695
- pair_role: prove
- source_stem: 695
- mathdb_ref: erdos:695
- source_namespace: Erdos695
- source_theorem: erdos_695
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset Real

namespace Problem

abbrev Target : Prop :=
    ∀ {q : ℕ → ℕ},
          StrictMono q →
          (∀ i, (q i).Prime) →
          (∀ i, q (i + 1) % q i = 1) →
          Tendsto (fun k => (q k : ℝ) ^ (1 / k : ℝ)) atTop atTop

end Problem
