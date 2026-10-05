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

- problem_id: E1196
- collection: erdos
- question_id: erdos:1196
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1196.lean#erdos_1196
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for any $x$, if $A\subset [x,\infty)$ is a primitive set of integers (so that no distinct elements of $A$ divide each other) then$$\sum_{a\in A}\frac{1}{a\log a}&#60; 1+o(1),$$where the $o(1)$ term $\to 0$ as $x\to \infty$? -
- notes: Erdos Problem 1196 -- https://www.erdosproblems.com/1196
- track: solved
- answer_shape: decide
- source_stem: 1196
- mathdb_ref: erdos:1196
- source_namespace: Erdos1196
- source_theorem: erdos_1196
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open scoped Asymptotics

-- TODO(Paul-Lez): add this to ForMathlib. I suspect this is the right generalisation from the natural number case?
/-- A set is primitive if no non-associated elements of the set divide each other. -/
def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧ ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
       ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x

end Problem
