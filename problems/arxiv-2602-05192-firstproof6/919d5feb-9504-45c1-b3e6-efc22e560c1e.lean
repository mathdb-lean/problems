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

- problem_id: X2602_05192_FirstProof6_epsilon_light_subset_exists
- collection: arxiv
- question_id: arxiv:2602.05192/FirstProof6
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2602.05192/FirstProof6.lean#epsilon_light_subset_exists
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist a constant $c > 0$ so that for every graph $G$ and every $\epsilon$ between $0$ and $1$, $V$ contains an $\epsilon$-light subset $S$ of size at least $c \epsilon |V|$?
- notes: arXiv 2602.05192/FirstProof6 -- https://arxiv.org/abs/2602.05192v2
- track: solved
- answer_shape: decide
- source_stem: 2602.05192/FirstProof6
- source_namespace: Arxiv.«2602.05192»
- source_theorem: epsilon_light_subset_exists
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Matrix Polynomial SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
For a graph $G = (V, E)$, let $G_S = (V, E(S,S))$ denote the graph with the same vertex set,
but only the edges between vertices in $S$.
Let $L$ be the Laplacian matrix of $G$ and let $L_S$ be the Laplacian of $G_S$.

I say that a set of vertices $S$ is $\epsilon$-light if the matrix $\epsilon L - L_S$ is
positive semidefinite.
-/
def IsEpsilonLight (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  open scoped Classical in
  letI G_S := G.induce S |>.spanningCoe
  letI L := lapMatrix ℝ G
  letI L_S := lapMatrix ℝ (G_S)
  PosSemidef (ε • L - L_S)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ (c : ℝ), c > 0 ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : ℝ),
        0 < ε → ε < 1 →
        ∃ (S : Finset (Fin n)), IsEpsilonLight G ε S ∧ (S.card : ℝ) ≥ c * ε * n

end Problem
