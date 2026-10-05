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

- problem_id: O157237_conjecture
- collection: oeis
- question_id: oeis:157237
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/157237.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: On Feb. 24, 2009, Zhi-Wei Sun conjectured that $a(n) = 0$ if and only if $n < 16$ or $n \in \{18, 21, 24, 51, 84, 1011, 59586\}$; in other words, except for $35, 41, 47, 101, 167, 2021, 119171$, any odd integer greater than $30$ can be written as the sum of a prime congruent to $1 \bmod 6$, a positive power of $2$ and eleven times a positive power of $2$.
- notes: OEIS A157237 -- https://oeis.org/A157237
- track: open
- answer_shape: proof
- source_stem: 157237
- source_namespace: OeisA157237
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_16 a_17 a_18 a_19
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Number of representations of $2n - 1$ as $p + 2^x + 11 \cdot 2^y$ with $p \equiv 1 \pmod 6$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N := 2 * n - 1
    ∑ x ∈ Finset.Icc 1 N,
    ∑ y ∈ Finset.Icc 1 N,
      if 2 ^ x + 11 * 2 ^ y < N ∧
         (N - (2 ^ x + 11 * 2 ^ y)).Prime ∧
         (N - (2 ^ x + 11 * 2 ^ y)) % 6 = 1 then 1 else 0

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

/-- Value of the sequence `a` at 16. -/
@[category test, AMS 11]
theorem a_16 : a 16 = 1 := by decide

/-- Value of the sequence `a` at 17. -/
@[category test, AMS 11]
theorem a_17 : a 17 = 1 := by decide

/-- Value of the sequence `a` at 18. -/
@[category test, AMS 11]
theorem a_18 : a 18 = 0 := by decide

/-- Value of the sequence `a` at 19. -/
@[category test, AMS 11]
theorem a_19 : a 19 = 2 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 0 < n),
      a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586

end Problem
