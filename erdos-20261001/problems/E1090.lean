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

- problem_id: E1090
- collection: erdos
- question_id: erdos:1090
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1090.lean#erdos_1090
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 3$. Does there exist a finite set $A\subset \mathbb{R}^2$ such that, in any $2$-colouring of $A$, there exists a line which contains at least $k$ points from $A$, and all the points of $A$ on the line have the same colour? Erdős [Er75f] says Graham and Selfridge proved the answer is yes when $k=3$. Hunter has observed that, for sufficiently large $n$, a generic projection of $[k]^n$ into $\mathbb{R}^2$ has this property, by the Hales-Jewett theorem.
- notes: Erdos Problem 1090 -- https://www.erdosproblems.com/1090
- track: solved
- answer_shape: decide
- source_stem: 1090
- mathdb_ref: erdos:1090
- source_namespace: Erdos1090
- source_theorem: erdos_1090
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (k : ℕ), ∀ (hk : 3 ≤ k),
        ∃ (A : Finset (Fin 2 → ℝ)), ∀ (C : A → Fin 2),
          ∃ (S : Finset (Fin 2 → ℝ)), ∃ (hSA : S ⊆ A),
            Collinear ℝ (S : Set (Fin 2 → ℝ)) ∧ S.card ≥ k ∧
              (∀ y ∈ A, y ∈ affineSpan ℝ (S : Set (Fin 2 → ℝ)) → y ∈ S) ∧
              ∃ c, ∀ x (hx : x ∈ S), C ⟨x, hSA hx⟩ = c

end Problem
