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

- problem_id: E264_parts_ii_refute
- collection: erdos
- question_id: erdos:264
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/264.lean#erdos_264.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is $n!$ an example of an irrationality sequence?
- notes: Erdos Problem 264 -- https://www.erdosproblems.com/264
- track: open
- answer_shape: refute
- pair_id: E264_parts_ii
- pair_role: refute
- source_stem: 264
- mathdb_ref: erdos:264
- source_namespace: Erdos264
- source_theorem: erdos_264.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

open scoped ENNReal Asymptotics

/--
A sequence $a_n$ of integers is called an irrationality sequence if for every bounded sequence of integers $b_n$ with $a_n + b_n \neq 0$ and
$b_n \neq 0$ for all $n$, the sum
$$
  \sum \frac{1}{a_n + b_n}
$$
is irrational.

Note: there are other possible definitions of this concept. See
FormalConjectures/ErdosProblems/263.lean for another possible definition.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop := ∀ b : ℕ → ℤ,
  BddAbove (Set.range b) → BddBelow (Set.range b) →
  0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) → 0 ∉ Set.range b →
  Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))

abbrev Target : Prop :=
    ¬ (
      IsIrrationalitySequence Nat.factorial
    )

end Problem
