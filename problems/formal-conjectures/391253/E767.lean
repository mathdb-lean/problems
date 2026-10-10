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

- problem_id: E767
- collection: erdos
- question_id: erdos:767
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/767.lean#erdos_767
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $g_k(n)$ be the maximal number of edges possible on a graph with $n$ vertices which does not contain a cycle with $k$ chords incident to a vertex on the cycle. Is it true that $$g_k(n)=(k+1)n-(k+1)^2$$ for $n$ sufficiently large? The answer is yes: the conjectured equality was proved for $n\geq 3k+3$ by Jiang [Ji04].
- notes: Erdos Problem 767 -- https://www.erdosproblems.com/767
- track: solved
- answer_shape: decide
- source_stem: 767
- mathdb_ref: erdos:767
- source_namespace: Erdos767
- source_theorem: erdos_767
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open SimpleGraph

namespace Problem

/-- `G` contains a cycle with `k` chords incident to a vertex on the cycle. -/
def HasCycleWithIncidentChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

open scoped Classical in
/-- `g k n` is the maximal number of edges possible on a graph with `n` vertices which does not
contain a cycle with `k` chords incident to a vertex on the cycle. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {m | ∃ G : SimpleGraph (Fin n),
    ¬ HasCycleWithIncidentChords G k ∧ G.edgeFinset.card = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k ≥ 1, ∀ n ≥ 3 * k + 3, g k n = (k + 1) * n - (k + 1) ^ 2

end Problem
