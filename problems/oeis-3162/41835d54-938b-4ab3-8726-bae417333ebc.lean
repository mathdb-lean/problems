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

- problem_id: O3162_conjecture
- collection: oeis
- question_id: oeis:3162
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/3162.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $b(n) = a(2n-1)$. Then the supercongruence $b(n p^k) \equiv b(n p^{k-1}) \pmod{p^{3k}}$ holds for positive integers $n$ and $k$ and all primes $p \ge 5$. - Zhi-Wei Sun, Nov 16 2019
- notes: OEIS A3162 -- https://oeis.org/A3162
- track: open
- answer_shape: proof
- source_stem: 3162
- source_namespace: OeisA3162
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A binomial coefficient summation: $a(n) = S(3, n) / S(1, n)$. -/
def a (n : ℕ) : ℚ :=
  let numerator : ℚ := ∑ k ∈ Finset.range (n / 2 + 1),
    let diff : ℚ := (n.choose k : ℚ) - (if k = 0 then 0 else (n.choose (k - 1) : ℚ))
    diff ^ 3
  let denominator : ℚ := (n.choose (n / 2) : ℚ)
  numerator / denominator

/-- Auxiliary sequence $b(n) = a(2n-1)$. -/
def b (n : ℕ) : ℚ :=
  a (2 * n - 1)

macro "eval_a" : tactic =>
  `(tactic| (dsimp [a]
             norm_num [Finset.sum_range_succ, Nat.choose_succ_succ, Nat.choose_zero_succ]))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by eval_a

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by eval_a

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by eval_a

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by eval_a

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by eval_a

abbrev Target : Prop :=
    ∀ (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p),
      (b (n * p ^ k)).num ≡ (b (n * p ^ (k - 1))).num [ZMOD (p : ℤ) ^ (3 * k)]

end Problem
