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

- problem_id: E1037
- collection: erdos
- question_id: erdos:1037
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1037.lean#erdos_1037
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a graph on $n$ vertices in which every degree occurs at most twice, and the number of distinct degrees is $>(\frac{1}{2}+\epsilon)n$. Must $G$ contain a trivial (empty or complete) subgraph of size 'much larger' than $\log n$? A question of Chen and Erdős. The answer is no - Cambie, Chan, and Hunter have in the comment section given a simple construction of a graph on $n$ vertices with at least $\frac{3}{4}n$ distinct degrees, every degree appears at most twice, and the largest trivial subgraph has size $O(\log n)$.
- notes: Erdos Problem 1037 -- https://www.erdosproblems.com/1037
- track: solved
- answer_shape: decide
- source_stem: 1037
- mathdb_ref: erdos:1037
- source_namespace: Erdos1037
- source_theorem: erdos_1037
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/--
A set `s` of vertices of a graph `G` is *trivial* if the subgraph it induces is empty or
complete, that is, if `s` is an independent set or a clique of `G`.
-/
def IsTrivialSet {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  G.IsIndepSet s ∨ G.IsClique s

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
          (∀ d : ℕ, {v : Fin n | (G.neighborSet v).ncard = d}.ncard ≤ 2) →
          ((1 / 2 + ε) * (n : ℝ) <
            ((Set.range fun v : Fin n => (G.neighborSet v).ncard).ncard : ℝ)) →
          ∃ s : Set (Fin n), IsTrivialSet G s ∧ (C * Real.log (n : ℝ) < (s.ncard : ℝ))

end Problem
