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

- problem_id: E1080
- collection: erdos
- question_id: erdos:1080
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1080.lean#erdos_1080
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $G$ be a bipartite graph on $n$ vertices such that one part has $\lfloor n^{2/3}\rfloor$ vertices. Is there a constant $c>0$ such that if $G$ has at least $cn$ edges then $G$ must contain a $C_6$? The answer is no, as shown by De Caen and Székely [DeSz92], who in fact show a stronger result. Let $f(n,m)$ be the maximum number of edges of a bipartite graph between $n$ and $m$ vertices which does not contain either a $C_4$ or $C_6$. A positive answer to this question would then imply $f(n,\lfloor n^{2/3}\rfloor)\ll n$. De Caen and Székely prove $n^{10/9}\gg f(n,\lfloor n^{2/3}\rfloor) \gg n^{58/57+o(1)}$ for $m\sim n^{2/3}$. They also prove more generally that, for $n^{1/2}\leq m\leq n$, $f(n,m) \ll (nm)^{2/3},$ which was also proved by Faudree and Simonovits. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 1080 -- https://www.erdosproblems.com/1080
- track: solved
- answer_shape: decide
- source_stem: 1080
- mathdb_ref: erdos:1080
- source_namespace: Erdos1080
- source_theorem: erdos_1080
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open SimpleGraph

namespace Problem

/-- `IsBipartition G X Y` means that `X` and `Y` form a bipartition of the vertices of `G`. -/
def IsBipartition {V : Type*} (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
    ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) (X Y : Set V),
      IsBipartition G X Y → X.ncard = ⌊(Fintype.card V : ℝ) ^ (2/3 : ℝ)⌋₊ →
      G.edgeSet.ncard ≥ c * Fintype.card V →
        ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = 6

end Problem
