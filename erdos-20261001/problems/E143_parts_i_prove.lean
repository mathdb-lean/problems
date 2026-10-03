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

- problem_id: E143_parts_i_prove
- collection: erdos
- question_id: erdos:143
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/143.lean#erdos_143.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does this imply that $$ \liminf \frac{|A \cap [1,x]|}{x} = 0? $$
- notes: Erdos Problem 143 -- https://www.erdosproblems.com/143
- track: open
- answer_shape: prove
- pair_id: E143_parts_i
- pair_role: prove
- source_stem: 143
- mathdb_ref: erdos:143
- source_namespace: Erdos143
- source_theorem: erdos_143.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset
open scoped Topology

namespace Problem

/--
Let $A \subseteq (1, \infty)$ be a countably infinite set such that for all $x\neq y\in A$ and
integers $k \geq 1$ we have $|kx - y| \geq 1$.
-/
def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

abbrev Target : Prop :=
    ∀ (A : Set ℝ), WellSeparatedSet A →
        liminf (fun x => (A ∩ (Set.Icc 1 x)).ncard / x) atTop = 0

end Problem
