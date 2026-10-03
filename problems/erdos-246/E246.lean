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

- problem_id: E246
- collection: erdos
- question_id: erdos:246
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/246.lean#erdos_246
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $(a,b)=1$. The set $\{a^kb^l: k,l\geq 0\}$ is complete - that is, every large integer is the sum of distinct integers of the form $a^kb^l$ with $k,l\geq 0$. We state the nontrivial case $a,b\geq 2$, proved by Birch [Bi59].
- notes: Erdos Problem 246 -- https://www.erdosproblems.com/246
- track: solved
- answer_shape: proof
- source_stem: 246
- mathdb_ref: erdos:246
- source_namespace: Erdos246
- source_theorem: erdos_246
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The set $\{a^k b^l : k,l \geq 0\}$. -/
def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a ^ k * b ^ l}

abbrev Target : Prop :=
    ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b),
      IsAddComplete (Gamma a b)

end Problem
