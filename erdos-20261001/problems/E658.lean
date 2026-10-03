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

- problem_id: E658
- collection: erdos
- question_id: erdos:658
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/658.lean#erdos_658
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\delta>0$ and $N$ be sufficiently large depending on $\delta$. Is it true that if $A\subseteq \{1,\ldots,N\}^2$ has $\lvert A\rvert \geq \delta N^2$ then $A$ must contain the vertices of a square? A problem of Graham, if the square is restricted to be axis-aligned. (It is unclear whether in [Er97e] had this restriction in mind.) This qualitative statement follows from the density Hales-Jewett theorem proved by Furstenberg and Katznelson [FuKa91]. A quantitative proof (yet with very poor bounds) was given by Solymosi [So04]. The square is taken to be axis-aligned (Graham's version), which implies the version allowing arbitrary squares.
- notes: Erdos Problem 658 -- https://www.erdosproblems.com/658
- track: solved
- answer_shape: decide
- source_stem: 658
- mathdb_ref: erdos:658
- source_namespace: Erdos658
- source_theorem: erdos_658
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset (ℕ × ℕ), A ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N → δ * N ^ 2 ≤ A.card →
          ∃ a b d : ℕ, 0 < d ∧ (a, b) ∈ A ∧ (a + d, b) ∈ A ∧ (a, b + d) ∈ A ∧ (a + d, b + d) ∈ A

end Problem
