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

- problem_id: E171
- collection: erdos
- question_id: erdos:171
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/171.lean#erdos_171
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that for every $\epsilon>0$ and integer $t\geq 1$, if $N$ is sufficiently large and $A$ is a subset of $[t]^N$ of size at least $\epsilon t^N$ then $A$ must contain a combinatorial line $P$ (a set $P=\{p_1,\ldots,p_t\}$ where for each coordinate $1\leq j\leq t$ the $j$th coordinate of $p_i$ is either $i$ or constant). The 'density Hales-Jewett' problem. This was proved by Furstenberg and Katznelson [FuKa91]. A new elementary proof, which gives quantitative bounds, was proved by the Polymath project [Po12]. Combinatorial lines are Mathlib's `Combinatorics.Line (Fin t) (Fin N)` (which have at least one non-constant coordinate).
- notes: Erdos Problem 171 -- https://www.erdosproblems.com/171
- track: solved
- answer_shape: decide
- source_stem: 171
- mathdb_ref: erdos:171
- source_namespace: Erdos171
- source_theorem: erdos_171
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ ε : ℝ, 0 < ε → ∀ t : ℕ, 1 ≤ t → ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset (Fin N → Fin t), ε * t ^ N ≤ A.card →
          ∃ l : Combinatorics.Line (Fin t) (Fin N), ∀ i : Fin t, l i ∈ A

end Problem
