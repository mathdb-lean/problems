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

- problem_id: WGraphConjecture31_conjecture31
- collection: wotw
- question_id: wotw:GraphConjecture31
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture31.lean#conjecture31
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 31](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj31) (Chung): For every simple connected graph $G$, $\mathrm{path}(G) \ge 2 \cdot \mathrm{rad}(G) - 1$, where $\mathrm{path}(G)$ is the maximum number of vertices in an induced path and $\mathrm{rad}(G)$ is the graph radius.
- notes: Written on the Wall II, problem GraphConjecture31
- track: solved
- answer_shape: proof
- source_stem: GraphConjecture31
- source_namespace: WrittenOnTheWallII.GraphConjecture31
- source_theorem: conjecture31
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

abbrev Target : Prop :=
    ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected),
      2 * (G.radius.toNat : ℤ) - 1 ≤ (path G : ℤ)

end Problem
