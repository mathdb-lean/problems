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

- problem_id: E473
- collection: erdos
- question_id: erdos:473
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/473.lean#erdos_473
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a permutation $a_1, a_2, \ldots$ of the positive integers such that $a_k + a_{k+1}$ is always prime? A question of Segal [ErGr80, p.94]. The answer is yes, as shown by Odlyzko. The linked formal proof (Codex and GPT-5.6 Sol) builds the permutation as a spanning one-way ray of the graph on the positive integers in which two numbers are adjacent when their sum is prime.
- notes: Erdos Problem 473 -- https://www.erdosproblems.com/473
- track: solved
- answer_shape: decide
- source_stem: 473
- mathdb_ref: erdos:473
- source_namespace: Erdos473
- source_theorem: erdos_473
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ a : ℕ ≃ ℕ+, ∀ n : ℕ, ((a n : ℕ) + (a (n + 1) : ℕ)).Prime

end Problem
