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

- problem_id: E615
- collection: erdos
- question_id: erdos:615
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/615.lean#erdos_615
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist some constant $c > 0$ such that for all sufficiently large $n$, if $G$ is a graph with $n$ vertices and at least $(1/8 - c)n^2$ edges then $G$ must contain either a $K_4$ or an independent set on at least $n/\log n$ vertices? The answer is no, as shown by Fox, Loh, and Zhao [FLZ15].
- notes: Erdos Problem 615 -- https://www.erdosproblems.com/615
- track: solved
- answer_shape: decide
- source_stem: 615
- mathdb_ref: erdos:615
- source_namespace: Erdos615
- source_theorem: erdos_615
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ (n : ℕ) in atTop,
          ∀ G : SimpleGraph (Fin n), (1 / 8 - c) * n ^ 2 ≤ G.edgeFinset.card →
            ¬ G.CliqueFree 4 ∨ (n : ℝ) / Real.log n ≤ G.indepNum

end Problem
