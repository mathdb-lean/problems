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

- problem_id: O157225_conjecture
- collection: oeis
- question_id: oeis:157225
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/157225.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: On Feb. 24, 2009, Zhi-Wei Sun conjectured that $a(n) = 0$ if and only if $n < 11$ or $n \in \{13, 16, 992\}$; in other words, except for $25, 31, 1983$, any odd integer greater than $20$ can be written as the sum of a prime congruent to $5 \bmod 6$, a positive power of $2$ and seven times a positive power of $2$. Answer: false, for n = 716993899 we have a(n) = 0. See T. Adamczewski, OEIS Open: How many conjectures can language models turn into theorems?, [arxiv/2608.11941](https://arxiv.org/pdf/2608.11941).
- notes: OEIS A157225 -- https://oeis.org/A157225
- track: solved
- answer_shape: proof
- source_stem: 157225
- source_namespace: OeisA157225
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_11 a_12 a_13 a_14
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Number of representations of $2n - 1$ as $p + 2^x + 7 \cdot 2^y$ with $p \equiv 5 \pmod 6$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N := 2 * n - 1
    ∑ x ∈ Finset.Icc 1 N,
    ∑ y ∈ Finset.Icc 1 N,
      if 2 ^ x + 7 * 2 ^ y < N ∧
         (N - (2 ^ x + 7 * 2 ^ y)).Prime ∧
         (N - (2 ^ x + 7 * 2 ^ y)) % 6 = 5 then 1 else 0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by decide

/-- Value of the sequence `a` at 11. -/
@[category test, AMS 11]
theorem a_11 : a 11 = 1 := by decide

/-- Value of the sequence `a` at 12. -/
@[category test, AMS 11]
theorem a_12 : a 12 = 1 := by decide

/-- Value of the sequence `a` at 13. -/
@[category test, AMS 11]
theorem a_13 : a 13 = 0 := by decide

/-- Value of the sequence `a` at 14. -/
@[category test, AMS 11]
theorem a_14 : a 14 = 2 := by decide

abbrev Target : Prop :=
    ¬ ∀ n : ℕ, 0 < n → (a n = 0 ↔ n < 11 ∨ n = 13 ∨ n = 16 ∨ n = 992)

end Problem
