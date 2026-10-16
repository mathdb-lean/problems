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

- problem_id: G62_prove
- collection: green
- question_id: green:62
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/62.lean#green_62
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p$ be a large prime, and let $A$ be the set of all primes less than $p$. Is every $x \in \{1, \ldots, p-1\}$ congruent to some product $a_1 a_2$ where $a_1, a_2 \in A$?
- notes: Green, open problem 62 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.62
- track: open
- answer_shape: prove
- pair_id: G62
- pair_role: prove
- source_stem: 62
- source_namespace: Green62
- source_theorem: green_62
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ᶠ p in atTop, p.Prime →
        let A := (Finset.range p).filter Nat.Prime
        ∀ x : ℕ, 1 ≤ x ∧ x < p →
          ∃ a₁ ∈ A, ∃ a₂ ∈ A, (x : ZMod p) = (a₁ * a₂ : ZMod p)

end Problem
