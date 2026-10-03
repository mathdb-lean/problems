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

- problem_id: E488_refute
- collection: erdos
- question_id: erdos:488
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/488.lean#erdos_488
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A$ be a finite set and $$B=\{ n \geq 1 : a\mid n\textrm{ for some }a\in A\}.$$ Is it true that, for every $m>n\geq \max(A)$, $$\frac{\lvert B\cap [1,m]\rvert }{m}< 2\frac{\lvert B\cap [1,n]\rvert}{n}?$$
- notes: Erdos Problem 488 -- https://www.erdosproblems.com/488
- track: open
- answer_shape: refute
- pair_id: E488
- pair_role: refute
- source_stem: 488
- mathdb_ref: erdos:488
- source_namespace: Erdos488
- source_theorem: erdos_488
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ (A : Finset ℕ), A.Nonempty →
          -- These are needed for the reasons outlined here: https://github.com/google-deepmind/formal-conjectures/pull/256
          0 ∉ A → 1 ∉ A →
          letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
          ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
            ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
              2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n
    )

end Problem
