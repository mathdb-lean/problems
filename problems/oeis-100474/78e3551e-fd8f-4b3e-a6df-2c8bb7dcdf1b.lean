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

- problem_id: O100474_conjecture_refute
- collection: oeis
- question_id: oeis:100474
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/100474.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: After $a(2) = 5$, is there another prime?
- notes: OEIS A100474 -- https://oeis.org/A100474
- track: open
- answer_shape: refute
- pair_id: O100474_conjecture
- pair_role: refute
- source_stem: 100474
- source_namespace: OeisA100474
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: nth_prime_five nth_prime_six nth_prime_seven nth_prime_eight nth_prime_nine nth_prime_ten nth_prime_eleven nth_prime_twelve nth_prime_thirteen a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The $n$-th triangular number. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The primary defining sequence `a`. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (Finset.Ico (triangular (n + 1) - 1) (triangular (n + 2) - 1)).prod (Nat.nth Nat.Prime) -
      a (n + 1)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : (13).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : (17).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : (19).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eight : Nat.nth Nat.Prime 8 = 23 := by
  have h1 : (23).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_nine : Nat.nth Nat.Prime 9 = 29 := by
  have h1 : (29).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_ten : Nat.nth Nat.Prime 10 = 31 := by
  have h1 : (31).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_eleven : Nat.nth Nat.Prime 11 = 37 := by
  have h1 : (37).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_twelve : Nat.nth Nat.Prime 12 = 41 := by
  have h1 : (41).Prime := by decide
  exact Nat.nth_count h1

@[category API, AMS 11]
lemma nth_prime_thirteen : Nat.nth Nat.Prime 13 = 43 := by
  have h1 : (43).Prime := by decide
  exact Nat.nth_count h1

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  change (Finset.Ico 0 2).prod (Nat.nth Nat.Prime) - a 1 = 5
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 380 := by
  change (Finset.Ico 2 5).prod (Nat.nth Nat.Prime) - a 2 = 380
  rw [a_2]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 96197 := by
  change (Finset.Ico 5 9).prod (Nat.nth Nat.Prime) - a 3 = 96197
  rw [a_3]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [nth_prime_five, nth_prime_six, nth_prime_seven, nth_prime_eight]
  rfl

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 58546472 := by
  change (Finset.Ico 9 14).prod (Nat.nth Nat.Prime) - a 4 = 58546472
  rw [a_4]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  rw [Finset.prod_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.prod_empty, one_mul]
  rw [nth_prime_nine, nth_prime_ten, nth_prime_eleven, nth_prime_twelve, nth_prime_thirteen]
  rfl

abbrev Target : Prop :=
    ¬ (
      ∃ n > 2, (a n).Prime
    )

end Problem
