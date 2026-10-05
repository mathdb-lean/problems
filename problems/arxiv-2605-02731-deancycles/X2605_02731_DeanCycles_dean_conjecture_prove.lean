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

- problem_id: X2605_02731_DeanCycles_dean_conjecture_prove
- collection: arxiv
- question_id: arxiv:2605.02731/DeanCycles
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2605.02731/DeanCycles.lean#dean_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Conjecture 1.1 (Dean, 1988).** For every integer $k \geq 3$, every finite simple graph with minimum degree at least $k$ contains a cycle whose length is divisible by $k$. A cycle has length at least `3`, so the divisor is never `0` and the statement is not satisfied for a trivial reason. `SimpleGraph.minDegree` is `0` on a graph with no vertices and on a graph with no edges, so the hypothesis excludes both.
- notes: arXiv 2605.02731/DeanCycles -- https://arxiv.org/abs/2605.02731
- track: open
- answer_shape: prove
- pair_id: X2605_02731_DeanCycles_dean_conjecture
- pair_role: prove
- source_stem: 2605.02731/DeanCycles
- source_namespace: Arxiv.«2605.02731»
- source_theorem: dean_conjecture
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: minDegree_bot_eq_zero minDegree_top_fin_four
- generator: adapters/formal_conjectures/adapter.py
-/

open SimpleGraph

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- A graph with no edges has minimum degree `0`, so the hypothesis of the conjecture rules it
out. This is a check that the hypothesis carries weight. -/
@[category test, AMS 5]
theorem minDegree_bot_eq_zero : (⊥ : SimpleGraph (Fin 5)).minDegree = 0 := by
  decide

/-- The complete graph on four vertices has minimum degree `3`, so it is one of the graphs the
case `k = 3` applies to. -/
@[category test, AMS 5]
theorem minDegree_top_fin_four : (⊤ : SimpleGraph (Fin 4)).minDegree = 3 := by
  decide

abbrev Target : Prop :=
    ∀ (k : ℕ), 3 ≤ k → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], k ≤ G.minDegree →
        ∃ m ∈ G.cycleLengths, k ∣ m

end Problem
