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

- problem_id: WGraphConjecture63_conjecture63
- collection: wotw
- question_id: wotw:GraphConjecture63
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture63.lean#conjecture63
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 63](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/) asked whether every simple connected graph $G$ satisfies $f(G) \geq \lceil(\min_v \operatorname{distEven}(v) + b(G) + 1)/3\rceil$. The answer is no, as witnessed by $C_5[K_4]$.
- notes: Written on the Wall II, problem GraphConjecture63 -- http://cms.dt.uh.edu/faculty/delavinae/research/wowII/
- track: solved
- answer_shape: decide
- source_stem: GraphConjecture63
- source_namespace: WrittenOnTheWallII.GraphConjecture63
- source_theorem: conjecture63
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open SimpleGraph

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (α : Type) [Fintype α] [DecidableEq α] [Nontrivial α]
          (G : SimpleGraph α) (_h : G.Connected),
          let minDistEven := (Finset.univ.image (G.distEven ·)).min' (by simp)
          ⌈((minDistEven : ℝ) + G.b + 1) / 3⌉ ≤ (G.largestInducedForestSize : ℝ)

end Problem
