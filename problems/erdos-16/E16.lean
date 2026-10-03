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

- problem_id: E16
- collection: erdos
- question_id: erdos:16
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/16.lean#erdos_16
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is the set of odd integers not of the form $2^k+p$ the union of an infinite arithmetic progression and a set of density $0$? Erdős called this conjecture "rather silly". Chen [Ch23] has proved the answer is no. This was formalized in Lean by Chin using Aristotle.
- notes: Erdos Problem 16 -- https://www.erdosproblems.com/16
- track: solved
- answer_shape: decide
- source_stem: 16
- mathdb_ref: erdos:16
- source_namespace: Erdos16
- source_theorem: erdos_16
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat Filter Set
open scoped Topology

namespace Problem

/--
The set of odd integers not of the form $2^k+p$.
-/
def Erdos16Set : Set ℕ :=
  { n | Odd n ∧ ¬ ∃ k p : ℕ, p.Prime ∧ n = 2 ^ k + p }

/--
A set of natural numbers has density 0.
-/
def density_zero (S : Set ℕ) : Prop :=
  open scoped Classical in
  Tendsto (fun x : ℕ ↦ (count (· ∈ S) x : ℝ) / (x : ℝ)) atTop (𝓝 0)

/--
A set of natural numbers has positive lower density.
-/
def positive_lower_density (S : Set ℕ) : Prop :=
  open scoped Classical in
  0 < atTop.liminf (fun n : ℕ ↦ ((count (· ∈ S) n : ℝ) / (n : ℝ) : EReal))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∃ A B : Set ℕ, Erdos16Set = A ∪ B ∧
        (∃ a d : ℕ, d > 0 ∧ A = { x | ∃ m : ℕ, x = a + m * d }) ∧
        density_zero B

end Problem
