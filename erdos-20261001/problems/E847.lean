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

- problem_id: E847
- collection: erdos
- question_id: erdos:847
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/847.lean#erdos_847
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A \subset \mathbb{N}$ be an infinite set for which there exists some $\epsilon > 0$ such that in any subset of $A$ of size $n$ there is a subset of size at least $\epsilon n$ which contains no three-term arithmetic progression. Is it true that $A$ is the union of a finite number of sets which contain no three-term arithmetic progression? A negative answer was given by Reiher, Rödl, and Sales [RRS24], who proved that, for any $0<\mu<1/2$, there exists $A\subseteq \mathbb{N}$ such that every finite colouring of $A$ contains a three-term arithmetic progression, and yet every subset of $A$ of size $n$ contains a subset of size $\geq \mu n$ without a three-term arithmetic progression.
- notes: Erdos Problem 847 -- https://www.erdosproblems.com/847
- track: solved
- answer_shape: decide
- source_stem: 847
- mathdb_ref: erdos:847
- source_namespace: Erdos847
- source_theorem: erdos_847
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/--
`HasFew3APs A` means that $A \subset \mathbb{N}$ is a set for which there exists some $\epsilon > 0$ such that
in any subset of $A$ of size $n$ there is a subset of size at least $\epsilon n$ which contains no
three-term arithmetic progression.
-/
def HasFew3APs (A : Set ℕ) := ∃ (ε : ℝ), ε > 0 ∧ ∀ (B : Set ℕ), B ⊆ A → Finite B →
  ∃ (C : Set ℕ), C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (A : Set ℕ), Infinite A → HasFew3APs A →
        ∃ n, ∃ (S : Fin n → Set ℕ), (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i

end Problem
