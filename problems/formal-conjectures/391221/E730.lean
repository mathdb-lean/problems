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

- problem_id: E730
- collection: erdos
- question_id: erdos:730
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/730.lean#erdos_730
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many pairs of integers $n < m$ such that $\binom{2n}{n}$ and $\binom{2m}{m}$ have the same set of prime divisors? Yes: there are infinitely many consecutive pairs $(n, n+1)$. The formal proof registered as [PALOMAR-2026-08-22-000001] proves `S.Infinite` for this `S`.
- notes: Erdos Problem 730 -- https://www.erdosproblems.com/730
- track: solved
- answer_shape: decide
- source_stem: 730
- mathdb_ref: erdos:730
- source_namespace: Erdos730
- source_theorem: erdos_730
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev S :=
  {(n, m) : ℕ × ℕ | n < m ∧ n.centralBinom.primeFactors = m.centralBinom.primeFactors}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ S.Infinite

end Problem
