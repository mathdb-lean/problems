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

- problem_id: E14_parts_ii_refute
- collection: erdos
- question_id: erdos:14
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/14.lean#erdos_14.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it possible that $|\{1,\ldots,N\} \setminus B| = o(N^\frac{1}{2})$?
- notes: Erdos Problem 14 -- https://www.erdosproblems.com/14
- track: open
- answer_shape: refute
- pair_id: E14_parts_ii
- pair_role: refute
- source_stem: 14
- mathdb_ref: erdos:14
- source_namespace: Erdos14
- source_theorem: erdos_14.parts.ii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Asymptotics Filter

/--
The number of integers in $\{1,\ldots,N\}$ which are not representable in exactly one way
as the sum of two elements from $A$ (either because they are not representable at all, or
because they are representable in more than one way).
-/
noncomputable def nonUniqueSumCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Set.Icc 1 N) \ (allUniqueSums A)).ncard

noncomputable def almostSquareRoot (ε : ℝ) (N : ℕ) : ℝ :=
  N ^ (1/2 - ε)

noncomputable def squareRoot (N : ℕ) : ℝ :=
  Real.sqrt N

abbrev Target : Prop :=
    ¬ (
      ∃ (A : Set ℕ), IsLittleO atTop (nonUniqueSumCount A) squareRoot
    )

end Problem
