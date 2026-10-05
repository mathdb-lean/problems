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

- problem_id: O5258_conjecture
- collection: oeis
- question_id: oeis:5258
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/5258.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For each $n = 1, 2, 3, \dots$ the polynomial $a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$ is irreducible over the field of rational numbers. - Zhi-Wei Sun, Mar 21 2013
- notes: OEIS A5258 -- https://oeis.org/A5258
- track: open
- answer_shape: proof
- source_stem: 5258
- source_namespace: OeisA5258
- source_theorem: conjecture
- source_category: research open
- source_ams: 11 12
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Apéry numbers: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k}$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose k

open Polynomial in
/-- The polynomial associated with the $n$-th Apéry number:
$a_n(x) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n+k}{k} x^k$. -/
noncomputable def aperyPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * X ^ k

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 19 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 147 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1251 := by rfl

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 1 ≤ n),
      Irreducible (aperyPoly n)

end Problem
