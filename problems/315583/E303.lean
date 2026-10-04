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

- problem_id: E303
- collection: erdos
- question_id: erdos:303
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/303.lean#erdos_303
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that in any finite colouring of the integers there exists a monochromatic solution to $\frac 1 a = \frac 1 b + \frac 1 c$ with distinct $a, b, c$? This is true, as proved by Brown and Rödl [BrRo91]. This was formalized in Lean by Yuan using Seed-Prover.
- notes: Erdos Problem 303 -- https://www.erdosproblems.com/303
- track: solved
- answer_shape: decide
- source_stem: 303
- mathdb_ref: erdos:303
- source_namespace: Erdos303
- source_theorem: erdos_303
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
    -- For any finite colouring of the integers
    ∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
      -- There exists integers `a, b, c`
      ∃ (a b c : ℤ),
      -- that are non-zero and distinct.
      [a, b, c, 0].Nodup ∧
      -- `a, b, c` satisfy the equation
      (1/a : ℝ) = 1/b + 1/c ∧
      -- `a, b, c` have the same color
      (𝓒 '' {a, b, c}).Subsingleton

end Problem
