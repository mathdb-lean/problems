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

- problem_id: E512
- collection: erdos
- question_id: erdos:512
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/512.lean#erdos_512
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, if $A\subset \mathbb{Z}$ is a finite set of size $N$, then $$\int_0^1 \left\lvert \sum_{n\in A}e(n\theta)\right\rvert \mathrm{d}\theta \gg \log N,$$ where $e(x)=e^{2\pi ix }$? Littlewood's conjecture, proved independently by Konyagin [Ko81] and McGehee, Pigno, and Smith [MPS81].
- notes: Erdos Problem 512 -- https://www.erdosproblems.com/512
- track: solved
- answer_shape: decide
- source_stem: 512
- mathdb_ref: erdos:512
- source_namespace: Erdos512
- source_theorem: erdos_512
- source_category: research solved
- source_ams: 11 42
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped ExponentialSum

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℤ), A.card = N →
          c * Real.log N ≤ ∫ θ in (0 : ℝ)..1, ‖∑ n ∈ A, e (n * θ)‖

end Problem
