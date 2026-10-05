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

- problem_id: O46969_conjecture2
- collection: oeis
- question_id: oeis:46969
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/46969.lean#conjecture2
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture II: if $\frac{a(n)}{12}$ is prime, then $\frac{a(n-1)}{12} - (n-1)$, $\frac{a(n)}{12} - n$ and $\frac{a(n+2)}{12} - (n+2)$ are multiples of 6. - Lorenzo Sauras Altuzarra, Oct 13 2020 This is false for $n = 236791$.
- notes: OEIS A46969 -- https://oeis.org/A46969
- track: solved
- answer_shape: proof
- source_stem: 46969
- source_namespace: OeisA46969
- source_theorem: conjecture2
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 bernoulli'_six a_3 bernoulli'_eight a_4 bernoulli'_ten a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Denominators of coefficients in Stirling's expansion for $\log(\Gamma(z))$. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 12 := by
  dsimp [a]
  rw [bernoulli_two]
  norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 360 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
  norm_num

@[category API, AMS 11]
lemma bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have hchoose2 : Nat.choose 6 2 = 15 := by decide
  have hchoose3 : Nat.choose 6 3 = 20 := by decide
  have hchoose4 : Nat.choose 6 4 = 15 := by decide
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, h5, hchoose2, hchoose3, hchoose4]

@[category test, AMS 11]
theorem a_3 : a 3 = 1260 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]
  norm_num

@[category API, AMS 11]
lemma bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  have hchoose2 : Nat.choose 8 2 = 28 := by decide
  have hchoose3 : Nat.choose 8 3 = 56 := by decide
  have hchoose4 : Nat.choose 8 4 = 70 := by decide
  have hchoose5 : Nat.choose 8 5 = 56 := by decide
  have hchoose6 : Nat.choose 8 6 = 28 := by decide
  have h3 : bernoulli' 3 = 0 := bernoulli'_three
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_two, h3,
    bernoulli'_four, h5, bernoulli'_six, h7,
    hchoose2, hchoose3, hchoose4, hchoose5, hchoose6]

@[category test, AMS 11]
theorem a_4 : a 4 = 1680 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]
  norm_num

@[category API, AMS 11]
lemma bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  have hchoose2 : Nat.choose 10 2 = 45 := by decide
  have hchoose3 : Nat.choose 10 3 = 120 := by decide
  have hchoose4 : Nat.choose 10 4 = 210 := by decide
  have hchoose5 : Nat.choose 10 5 = 252 := by decide
  have hchoose6 : Nat.choose 10 6 = 210 := by decide
  have hchoose7 : Nat.choose 10 7 = 120 := by decide
  have hchoose8 : Nat.choose 10 8 = 45 := by decide
  have h3 : bernoulli' 3 = 0 := bernoulli'_three
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have h9 : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_two, h3,
    bernoulli'_four, h5, bernoulli'_six, h7, bernoulli'_eight, h9,
    hchoose2, hchoose3, hchoose4, hchoose5, hchoose6, hchoose7, hchoose8]

@[category test, AMS 11]
theorem a_5 : a 5 = 1188 := by
  dsimp [a]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_ten]
  norm_num

abbrev Target : Prop :=
    ¬ ∀ (n : ℕ), 2 ≤ n → 12 ∣ a n → Nat.Prime (a n / 12) →
      12 ∣ a (n - 1) → 12 ∣ a (n + 2) →
      6 ∣ ((a (n - 1) / 12 : ℤ) - (n - 1 : ℤ)) ∧
      6 ∣ ((a n / 12 : ℤ) - (n : ℤ)) ∧
      6 ∣ ((a (n + 2) / 12 : ℤ) - (n + 2 : ℤ))

end Problem
