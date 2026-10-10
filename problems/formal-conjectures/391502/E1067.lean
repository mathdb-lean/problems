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

- problem_id: E1067
- collection: erdos
- question_id: erdos:1067
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1067.lean#erdos_1067
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every graph with chromatic number $\aleph_1$ contain an infinitely connected subgraph with chromatic number $\aleph_1$? Komjáth [Ko13] proved that it is consistent that the answer is no. This was improved by Soukup [So15], who constructed a counterexample using no extra set-theoretical assumptions. A simpler elementary example was given by Bowler and Pitz [BoPi24]. This was formalized in Lean by Alexeev using Aristotle and Aleph Prover.
- notes: Erdos Problem 1067 -- https://www.erdosproblems.com/1067
- track: solved
- answer_shape: decide
- source_stem: 1067
- mathdb_ref: erdos:1067
- source_namespace: Erdos1067
- source_theorem: erdos_1067
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Cardinal SimpleGraph

namespace Problem

/--
A graph is infinitely edge-connected if to disconnect the graph requires deleting
infinitely many edges. In other words, removing any finite set of edges leaves
the graph connected.
-/
def InfinitelyEdgeConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃s : Set (Sym2 V)⦄, s.Finite → (G.deleteEdges s).Connected

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      ∃ (H : G.Subgraph), H.coe.chromaticCardinal = ℵ_ 1 ∧ InfinitelyConnected H.coe

end Problem
