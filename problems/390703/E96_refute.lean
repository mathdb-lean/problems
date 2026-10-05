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

- problem_id: E96_refute
- collection: erdos
- question_id: erdos:96
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/96.lean#erdos_96
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If $n$ points in $\mathbb{R}^2$ form a convex polygon then there are $O(n)$ many pairs which are distance $1$ apart.
- notes: Erdos Problem 96 -- https://www.erdosproblems.com/96
- track: open
- answer_shape: refute
- pair_id: E96
- pair_role: refute
- source_stem: 96
- mathdb_ref: erdos:96
- source_namespace: Erdos96
- source_theorem: erdos_96
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: convexUnitDistanceCounts_bddAbove
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open EuclideanGeometry
open scoped EuclideanGeometry

namespace Problem

open Finset

/--
The set of all possible numbers of unit distances determined by the vertices of a convex
$n$-gon.
-/
noncomputable def convexUnitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset ℝ²) (_ : points.card = n) (_ : ConvexIndep points)}

/--
The **maximum number of unit distances** determined by the vertices of a convex $n$-gon.
This function is often denoted as $U_c(n)$ in combinatorics.
-/
noncomputable def maxConvexUnitDistances (n : ℕ) : ℕ :=
  sSup (convexUnitDistanceCounts n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
This lemma confirms that the set of possible unit-distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem convexUnitDistanceCounts_bddAbove (n : ℕ) : BddAbove <| convexUnitDistanceCounts n := by
  use n.choose 2
  rintro _ ⟨points, rfl, _, rfl⟩
  exact unitDistNum_le_choose_two points

abbrev Target : Prop :=
    ¬ (
      (fun n => (maxConvexUnitDistances n : ℝ)) =O[atTop] fun n => (n : ℝ)
    )

end Problem
