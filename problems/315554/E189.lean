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

- problem_id: E189
- collection: erdos
- question_id: erdos:189
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/189.lean#erdos_189
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $\mathbb{R}^2$ is finitely coloured then must there exist some colour class which contains the vertices of a rectangle of every area? Graham, "On Partitions of 𝔼ⁿ", Journal of Combinatorial Theory, Series A 28, 89-91 (1980). (See "Concluding Remarks" on page 96.) Solved (with answer `False`, as formalised below) in: Vjekoslav Kovač, "Coloring and density theorems for configurations of a given volume", 2023 https://arxiv.org/abs/2309.09973 In fact, Kovač's colouring is even Jordan measurable (the topological boundary of each monochromatic region is Lebesgue measurable and has measure zero). This was formalized in Lean by Alexeev and Kovac using Aristotle.
- notes: Erdos Problem 189 -- https://www.erdosproblems.com/189
- track: solved
- answer_shape: decide
- source_stem: 189
- mathdb_ref: erdos:189
- source_namespace: Erdos189
- source_theorem: erdos_189
- source_category: research solved
- source_ams: 5 51
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Affine EuclideanGeometry

namespace Problem

/-- Erdős problem 189 asked whether the below holds for all rectangles. -/
def Erdos189For (P : ℝ² → ℝ² → ℝ² → ℝ² → Prop) (A : ℝ² → ℝ² → ℝ² → ℝ² → ℝ) :=
    ∀ᵉ (n > 0) (colouring : ℝ² → Fin n), ∃ colour, ∀ area > (0 : ℝ), ∃ a b c d,
      {a, b, c, d} ⊆ colouring⁻¹' {colour} ∧
      IsCcwConvexPolygon ![a, b, c, d] ∧
      A a b c d = area ∧
      P a b c d

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Erdos189For
      (fun a b c d ↦
        line[ℝ, a, b].direction ⟂ line[ℝ, b, c].direction ∧
        line[ℝ, b, c].direction ⟂ line[ℝ, c, d].direction ∧
        line[ℝ, c, d].direction ⟂ line[ℝ, d, a].direction)
      (fun a b c d ↦ dist a b * dist b c)

end Problem
