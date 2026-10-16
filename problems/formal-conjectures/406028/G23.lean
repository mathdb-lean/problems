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

- problem_id: G23
- collection: green
- question_id: green:23
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/23.lean#green_23
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $\mathbb{N}$ is finitely coloured. Are there $x,y$ of the same colour such that $x^2 + y^2$ is a square? Solved in [FrKlMo25].
- notes: Green, open problem 23 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.23
- track: solved
- answer_shape: decide
- source_stem: 23
- source_namespace: Green23
- source_theorem: green_23
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
      -- For every finite colouring of the natural numbers
      ∀ (k : ℕ) (c : ℕ → Fin k),
      -- there exist two numbers of the same colour whose squares sum to a square
      ∃ x y : ℕ,
        0 < x ∧ 0 < y ∧  -- Exclude trivial x^2 + 0^2 = x^2 solution
        c x = c y ∧      -- Same colour
        IsSquare (x^2 + y^2)

end Problem
