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

- problem_id: E532
- collection: erdos
- question_id: erdos:532
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/532.lean#erdos_532
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $\mathbb{N}$ is 2-coloured then is there some infinite set $A\subseteq \mathbb{N}$ such that all finite subset sums$$ \sum_{n\in S}n$$(as $S$ ranges over all non-empty finite subsets of $A$) are monochromatic? Asked by Graham and Rothschild. Proved by Hindman [Hi74] (for any number of colours).
- notes: Erdos Problem 532 -- https://www.erdosproblems.com/532
- track: solved
- answer_shape: decide
- source_stem: 532
- mathdb_ref: erdos:532
- source_namespace: Erdos532
- source_theorem: erdos_532
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (c : ℕ → Fin 2),
      ∃ A : Set ℕ, A.Infinite ∧
        ∃ color : Fin 2,
          ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A →
            c (∑ n ∈ S, n) = color

end Problem
