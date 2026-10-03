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

- problem_id: E193
- collection: erdos
- question_id: erdos:193
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/193.lean#erdos_193
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $S \subseteq \mathbb{Z}^3$ be a finite set and let $A = \lbrace a_1, a_2, \ldots \rbrace$ be an infinite $S$-walk, so that $a_{i+1} - a_i \in S$ for all $i$. Must $A$ contain three collinear points? Cambie and Kalviainen [CaKa26] answered this question in the negative by constructing an infinite walk in $\mathbb{Z}^3$ with a finite set of steps and no three collinear points.
- notes: Erdos Problem 193 -- https://www.erdosproblems.com/193
- track: solved
- answer_shape: decide
- source_stem: 193
- mathdb_ref: erdos:193
- source_namespace: Erdos193
- source_theorem: erdos_193
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Set

namespace Problem

/-- An $S$-walk is a sequence where every difference is in $S$. -/
def IsSWalk {V : Type*} [AddCommGroup V] (S : Set V) (a : ℕ → V) : Prop :=
  ∀ n, a (n + 1) - a n ∈ S

/-- True if set $A$ contains 3 distinct collinear points over $R$. -/
def HasCollinearTriple (R) {V : Type*} [DivisionRing R] [AddCommGroup V] [Module R V] (A : Set V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Collinear R ({x, y, z} : Set V)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ S : Set (Fin 3 → ℤ), S.Finite →
      /- The statement's $A = \lbrace a_1, a_2, \ldots \rbrace$ is an infinite set.

      If the sequence only takes finitely many values, one value has to repeat infinitely many
      times, which would yield a trivial collinear triple (x, x, x). In this case, the conjecture
      would hold for degenerate S-walks. Another case is constant S-walks, which would render the
      conjecture trivially false (finite loop ranges have no 3 distinct points).

      Assuming the authors intend to stay away from these degenerate cases, we formalize this by
      requiring an infinite range (and require distinct points). -/
      ∀ a : ℕ → Fin 3 → ℤ, IsSWalk S a → (range a).Infinite →
      HasCollinearTriple ℚ (range (fun n ↦ (↑) ∘ a n : ℕ → Fin 3 → ℚ))

end Problem
