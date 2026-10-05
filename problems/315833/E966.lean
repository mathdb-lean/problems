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

- problem_id: E966
- collection: erdos
- question_id: erdos:966
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/966.lean#erdos_966
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k,r\geq 2$. Does there exist a set $A\subseteq \mathbb{N}$ that contains no non-trivial arithmetic progression of length $k+1$, yet in any $r$-colouring of $A$ there must exist a monochromatic non-trivial arithmetic progression of length $k$? Erdős [Er75b] reported that 'Spencer has recently shown that such a sequence exists', but gives no reference.
- notes: Erdos Problem 966 -- https://www.erdosproblems.com/966
- track: solved
- answer_shape: decide
- source_stem: 966
- mathdb_ref: erdos:966
- source_namespace: Erdos966
- source_theorem: erdos_966
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k r : ℕ, 2 ≤ k → 2 ≤ r → ∃ A : Set ℕ, A.IsAPOfLengthFree (k + 1) ∧
          ∀ coloring : A → Fin r, ContainsMonoAPofLength coloring k

end Problem
