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

- problem_id: WGraphConjecture100_conjecture100
- collection: wotw
- question_id: wotw:GraphConjecture100
- source: formal-conjectures
- source_locator: FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean#conjecture100
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: WOWII [Conjecture 100](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj100) (status O): For a simple connected graph `G`, `α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉` where `α(G) = G.indepNum` is the independence number, `max_v l(v)` is the maximum over all vertices of the independence number of the neighbourhood (in `G`), and `degreeL2Norm(Gᶜ)` is the square root of the sum of the squares of the degrees in the complement `Gᶜ`.
- notes: Written on the Wall II, problem GraphConjecture100
- track: open
- answer_shape: proof
- source_stem: GraphConjecture100
- source_namespace: WrittenOnTheWallII.GraphConjecture100
- source_theorem: conjecture100
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
      let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
      (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉

end Problem
