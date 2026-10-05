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

- problem_id: E965
- collection: erdos
- question_id: erdos:965
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/965.lean#erdos_965
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Erdős asks in [Er75b] if for every 2-coloring of ℝ, there is an uncountable set $A ⊆ ℝ$ such that all sums $a + b$ for $a, b ∈ A, a ≠ b$ have the same colour. In [Ko16] Péter Komjáth constructed a counterexample. The same result was proven independently in [SWCol] by Sokoup and Weiss.
- notes: Erdos Problem 965 -- https://www.erdosproblems.com/965
- track: solved
- answer_shape: decide
- source_stem: 965
- mathdb_ref: erdos:965
- source_namespace: Erdos965
- source_theorem: erdos_965
- source_category: research solved
- source_ams: 3 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ f : ℝ → Fin 2, ∃ A : Set ℝ, ¬ A.Countable ∧
      ∀ᵉ (a ∈ A) (b ∈ A) (c ∈ A) (d ∈ A), a ≠ b → c ≠ d → f (a + b) = f (c + d)

end Problem
