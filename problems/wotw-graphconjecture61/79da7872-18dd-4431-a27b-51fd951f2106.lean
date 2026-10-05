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

- problem_id: WGraphConjecture61_conjecture61
- collection: wotw
- question_id: wotw:GraphConjecture61
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture61.lean#conjecture61
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 61](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) For a simple connected graph $G$, the size $f(G)$ of a largest induced forest satisfies $f(G) \ge \mathrm{residue}(G) + \lceil \mathrm{diam}(G) / 3 \rceil$, where $\mathrm{residue}(G)$ is the Havel-Hakimi residue and $\mathrm{diam}(G)$ is the diameter of $G$. See: Favaron, Mahéo, Saclé (1991) for the residue; DeLaVina's Graffiti.pc for the conjecture.
- notes: Written on the Wall II, problem GraphConjecture61
- track: open
- answer_shape: proof
- source_stem: GraphConjecture61
- source_namespace: WrittenOnTheWallII.GraphConjecture61
- source_theorem: conjecture61
- source_category: research open
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
      (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ)

end Problem
