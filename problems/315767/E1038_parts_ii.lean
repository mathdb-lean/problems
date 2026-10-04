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

- problem_id: E1038_parts_ii
- collection: erdos
- question_id: erdos:1038
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1038.lean#erdos_1038.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The supremum of `|{x ∈ ℝ : |f x| < 1}|` over all monic polynomials `f` such that all of its roots are real and contained in `[-1,1]` is `2 * 2 ^ (1 / 2)`. This is proved in [Tao25].
- notes: Erdos Problem 1038 -- https://www.erdosproblems.com/1038
- track: solved
- answer_shape: proof
- source_stem: 1038
- mathdb_ref: erdos:1038
- source_namespace: Erdos1038
- source_theorem: erdos_1038.parts.ii
- source_category: research solved
- source_ams: 28
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Real ENNReal
open MeasureTheory

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ),
      2 * 2 ^ (1 / 2 : ℝ) =
          ⨆ f : {f : Polynomial ℝ // f.Monic ∧
          (f.roots.filter fun x => x ∈ Set.Icc (-1 : ℝ) 1).card = f.natDegree},
          volume {x | |f.1.eval x| < 1}

end Problem
