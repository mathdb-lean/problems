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

- problem_id: WGraphConjecture316_conjecture316
- collection: wotw
- question_id: wotw:GraphConjecture316
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture316.lean#conjecture316
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 316](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) Let `G` be a simple connected graph and let `P` denote the set of pendant vertices (vertices of degree 1). If `|P| ≥ deg_avg(Gᶜ)`, then `G` is well totally dominated, where `deg_avg(Gᶜ)` is the average degree of the complement of `G`. **Proof sketch.** In the trivial cases (`P = ∅`, or at most `2` vertices) `G` is complete, and complete graphs are well totally dominated. Otherwise the set `C` of non-pendant vertices satisfies `|C| ≤ 3` and is a clique of `G`, and a case split on the set `Q ⊆ C` of neighbours of pendant vertices shows that `G` is well totally dominated.
- notes: Written on the Wall II, problem GraphConjecture316 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture316
- source_namespace: WrittenOnTheWallII.GraphConjecture316
- source_theorem: conjecture316
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
        (h : (averageDegree Gᶜ : ℚ) ≤ (pendantVertices G).card),
      IsWellTotallyDominated G

end Problem
