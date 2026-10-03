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

- problem_id: E318_parts_ii
- collection: erdos
- question_id: erdos:318
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/318.lean#erdos_318.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does the set of squares excluding 1 have property `P₁`? Larsen [La26] proved that this set does have property `P₁`.
- notes: Erdos Problem 318 -- https://www.erdosproblems.com/318
- track: solved
- answer_shape: decide
- source_stem: 318
- mathdb_ref: erdos:318
- source_namespace: Erdos318
- source_theorem: erdos_318.parts.ii
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set Real

namespace Problem

/-- A set `A : Set ℕ` is said to have property `P₁` if for any nonconstant sequence
`f : A → {-1, 1}`, one can always select a finite, nonempty subset `S ⊆ A \ {0}` such that
`∑ n ∈ S, fₙ / n = 0`. This is defined in [Sa82b]. -/
def P₁ (A : Set ℕ) : Prop := ∀ (f : ℕ → ℝ),
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => 1) →
  f ∘ (Subtype.val : (A \ {0} : Set ℕ) → ℕ) ≠ (fun _ => - 1) →
  Set.range f ⊆ {1, -1} →
  ∃ S : Finset ℕ, S.Nonempty ∧ ↑S ⊆ A \ {0} ∧ ∑ n ∈ S, f n / n = 0

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔  P₁ ({n | IsSquare n} \ {1})

end Problem
