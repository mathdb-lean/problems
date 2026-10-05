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

- problem_id: NBingBorsuk_bing_borsuk_conjecture
- collection: wikipedia
- question_id: wikipedia:BingBorsuk
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/BingBorsuk.lean#bing_borsuk_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The Bing-Borsuk Conjecture: every $n$-dimensional homogeneous absolute neighborhood retract is a topological $n$-manifold. A topological space $X$ is an $n$-dimensional manifold when `T2Space X ∧ Nonempty (ChartedSpace (Fin n → ℝ) X)`. The hypothesis `[MetrizableSpace X]` implies `T2Space X` so this does not appear in the conclusion.
- notes: Wikipedia: BingBorsuk -- https://en.wikipedia.org/wiki/Bing%E2%80%93Borsuk_conjecture
- track: open
- answer_shape: proof
- source_stem: BingBorsuk
- source_namespace: BingBorsuk
- source_theorem: bing_borsuk_conjecture
- source_category: research open
- source_ams: 54 57
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Manifold
open TopologicalSpace

abbrev Target : Prop :=
    ∀ n : ℕ, ∀ (X : Type) [TopologicalSpace X] [MetrizableSpace X] [HomogeneousSpace X] [IsAbsoluteNeighborhoodRetract X],
        HasLebesgueCoveringDimensionEq X n → Nonempty (ChartedSpace (Fin n → ℝ) X)

end Problem
