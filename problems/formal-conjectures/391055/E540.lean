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

- problem_id: E540
- collection: erdos
- question_id: erdos:540
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/540.lean#erdos_540
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that if $A\subseteq \mathbb{Z}/N\mathbb{Z}$ has size $\gg N^{1/2}$ then there exists some non-empty $S\subseteq A$ such that $\sum_{n\in S}n\equiv 0\pmod{N}$? Szemerédi proved the answer is yes, in fact for arbitrary finite abelian groups.
- notes: Erdos Problem 540 -- https://www.erdosproblems.com/540
- track: solved
- answer_shape: decide
- source_stem: 540
- mathdb_ref: erdos:540
- source_namespace: Erdos540
- source_theorem: erdos_540
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- A finite set has a non-empty subset whose sum is zero. -/
def HasZeroSubsetSum {G : Type*} [AddCommMonoid G] (A : Finset G) : Prop :=
  ∃ S : Finset G, S ⊆ A ∧ S.Nonempty ∧ S.sum id = 0

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℝ, 0 < C ∧
          ∀ (N : ℕ), 0 < N → ∀ A : Finset (ZMod N),
            C * Real.sqrt N ≤ A.card →
              HasZeroSubsetSum A

end Problem
