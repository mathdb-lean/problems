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

- problem_id: O60841_conjecture1
- collection: oeis
- question_id: oeis:60841
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/60841.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: "Conjecture: $1/\det(M)$ is an integer only for n: 1 to 34, 36 and 38." - _Robert G. Wilson v_, Aug 02 2015
- notes: OEIS A60841 -- https://oeis.org/A60841
- track: open
- answer_shape: proof
- source_stem: 60841
- source_namespace: OeisA60841
- source_theorem: conjecture1
- source_category: research open
- source_ams: 11 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The $n \times n$ matrix with entry $(i,j)$ equal to
$1/\operatorname{lcm}(i+1, j+1)$ over $\mathbb{Q}$. -/
def lcmMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j : Fin n ↦ 1 / ((Nat.lcm (i.val + 1) (j.val + 1) : ℚ))

/-- Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with
$M[i,j] = 1/\operatorname{lcm}(i+1,j+1)$. -/
def a (n : ℕ) : ℤ :=
  ((lcmMatrix n).det)⁻¹.num

/-- The exceptional values of $n$ where $1/\det(M)$ is conjectured to be an integer. -/
def integerDetN : Set ℕ :=
  Set.Icc 1 34 ∪ {36, 38}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11 15]
theorem a_1 : a 1 = 1 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_2 : a 2 = 4 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_3 : a 3 = 18 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_4 : a 4 = 144 := by
  decide +kernel

@[category test, AMS 11 15]
theorem a_5 : a 5 = 900 := by
  decide +kernel

abbrev Target : Prop :=
    ∀ n : ℕ, 1 ≤ n → (((lcmMatrix n).det)⁻¹.den = 1 ↔ n ∈ integerDetN)

end Problem
