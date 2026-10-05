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

- problem_id: G12_refute
- collection: green
- question_id: green:12
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/12.lean#green_12
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be an abelian group of size $N$, and suppose that $A \subset G$ has density $\alpha$. Are there at least $\alpha^{15} N^{10}$ tuples $(x_1, \dots, x_5, y_1, \dots, y_5) \in G^{10}$ such that $x_i + y_j \in A$ whenever $j \in \{i, i+1, i+2\}$? Note: We interpret indices modulo 5.
- notes: Green, open problem 12
- track: open
- answer_shape: refute
- pair_id: G12
- pair_role: refute
- source_stem: 12
- source_namespace: Green12
- source_theorem: green_12
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Finset

abbrev Target : Prop :=
    ¬ (
      ∀ {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G],
          ∀ (A : Finset G),
          let N := Fintype.card G
          let α := (A.card : ℝ) / N
          let valid_tuples : Finset ((Fin 5 → G) × (Fin 5 → G)) := Finset.univ.filter (fun t =>
            ∀ i : Fin 5, ∀ j ∈ ({i, i + 1, i + 2} : Finset (Fin 5)), t.1 i + t.2 j ∈ A)
          (valid_tuples.card : ℝ) ≥ α ^ 15 * (N : ℝ) ^ 10
    )

end Problem
