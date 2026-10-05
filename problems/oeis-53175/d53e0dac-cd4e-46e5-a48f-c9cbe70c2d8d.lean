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

- problem_id: O53175_conjecture
- collection: oeis
- question_id: oeis:53175
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/53175.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: let $P(n)$ be the $(n+1) \times (n+1)$ Hankel-type determinant with $(i,j)$-entry equal to $a(i+j)$ for all $i,j = 0, \ldots, n$. Then $P(n)/2^{n(n+3)}$ is a positive odd integer. - Zhi-Wei Sun, Aug 14 2013 Proved by [ZS18], Theorem 1.2: $2^{-n(n+3)} |P_{i+j}|_{0 \le i,j \le n}$ is a positive odd integer for every $n \in \mathbb{N}$, where $P_n$ are the Catalan-Larcombe-French numbers.
- notes: OEIS A53175 -- https://oeis.org/A53175
- track: solved
- answer_shape: proof
- source_stem: 53175
- source_namespace: OeisA53175
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Catalan-Larcombe-French sequence. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 8
  | n + 2 =>
    let n' := n + 2
    let an1 := a (n + 1)
    let an2 := a n
    let term1 := 8 * (3 * n' ^ 2 - 3 * n' + 1) * an1
    let term2 := 128 * (n' - 1) ^ 2 * an2
    (term1 - term2) / (n' ^ 2)

/-- The $(n+1) \times (n+1)$ Hankel-type matrix with $(i,j)$-entry $a(i+j)$. -/
def hankelMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦ (a (i.val + j.val) : ℤ)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 8 := by
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 80 := by
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 896 := by
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 10816 := by
  rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 137728 := by
  rfl

abbrev Target : Prop :=
    ∀ (n : ℕ),
      let detP := (hankelMatrix n).det
      let pow2 := (2 : ℤ) ^ (n * (n + 3))
      pow2 ∣ detP ∧ 0 < detP / pow2 ∧ (detP / pow2) % 2 = 1

end Problem
