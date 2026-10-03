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

- problem_id: E1077
- collection: erdos
- question_id: erdos:1077
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1077.lean#erdos_1077
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: We call a graph $D$-balanced (or $D$-almost-regular) if the maximum degree is at most $D$ times the minimum degree. Let $ε, α > 0$ and $D$ and $n$ be sufficiently large. If $G$ is a graph on $n$ vertices with at least $n^{1+α}$ edges, then must $G$ contain a $D$-balanced subgraph on $m > n^{1-α}$ vertices with at least $εm^{1+α}$ edges?
- notes: Erdos Problem 1077 -- https://www.erdosproblems.com/1077
- track: solved
- answer_shape: decide
- source_stem: 1077
- mathdb_ref: erdos:1077
- source_namespace: Erdos1077
- source_theorem: erdos_1077
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Finset Filter SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 → ∀ᶠ D in atTop, ∀ᶠ n in atTop,
      ∀ G : SimpleGraph (Fin n), G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
        ∃ (H : Subgraph G),
          letI m := H.verts.ncard
          IsBalanced H.coe D ∧
          m > (n : ℝ) ^ (1 - α) ∧
          H.edgeSet.ncard > ε * m ^ (1 + α)

end Problem
