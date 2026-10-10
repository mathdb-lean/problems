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

- problem_id: E359_parts_ii
- collection: erdos
- question_id: erdos:359
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/359.lean#erdos_359.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a_1< a_2 < ⋯ $ be an infinite sequence of integers such that $a_1=1$ and $a_{i+1}$ is the least integer which is not a sum of consecutive earlier $a_j$s. Show that $a_k / k ^ {1 + c} \to 0$ for any $c > 0$.
- notes: Erdos Problem 359 -- https://www.erdosproblems.com/359
- track: open
- answer_shape: proof
- source_stem: 359
- mathdb_ref: erdos:359
- source_namespace: Erdos359
- source_theorem: erdos_359.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Asymptotics

/-- The predicate that `A` is monotone, `A 0 = n` and for all `j`, `A (j + 1)` is the smallest natural number that
cannot be written as a sum of consecutive terms of `A 0, ..., A j` -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)

abbrev Target : Prop :=
    ∀ (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c),
      atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0)

end Problem
