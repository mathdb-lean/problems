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

- problem_id: E90
- collection: erdos
- question_id: erdos:90
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/90.lean#erdos_90
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does every set of $n$ distinct points in $\mathbb{R}^2$ contain at most $n^{1+O(\frac{1}{\log\log n})}$ many pairs which are distance $1$ apart? This was [disproved](https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf) by an internal model at OpenAI, which constructed (for infinitely many $n$) a set $P$ of $n$ points in $\mathbb{R}^2$ such that the number of unit distance pairs in $P$ is at least $n^{1+c}$, where $c > 0$ is an absolute constant.
- notes: Erdos Problem 90 -- https://www.erdosproblems.com/90
- track: solved
- answer_shape: decide
- source_stem: 90
- mathdb_ref: erdos:90
- source_namespace: Erdos90
- source_theorem: erdos_90
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: unitDistanceCounts_BddAbove
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter EuclideanGeometry NumberField
open scoped EuclideanGeometry

namespace Problem

open Finset

/--
The set of all possible numbers of unit distances for a configuration of $n$ points.
-/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset ℝ²) (_ : points.card = n)}

/--
The **maximum number of unit distances** determined by any set of $n$ points in the plane.
This function is often denoted as $u(n)$ in combinatorics.
-/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
This lemma confirms that the set of possible unit distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem unitDistanceCounts_BddAbove (n : ℕ) : BddAbove <| unitDistanceCounts n := by
  use n.choose 2
  rintro _ ⟨points, rfl, rfl⟩
  exact unitDistNum_le_choose_two points

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ (O : ℕ → ℝ) (hO : O =O[atTop] (fun n => 1 / (n : ℝ).log.log)),
        (fun n => (maxUnitDistances n : ℝ)) =ᶠ[atTop] fun (n : ℕ) => (n : ℝ) ^ (1 + O n)

end Problem
