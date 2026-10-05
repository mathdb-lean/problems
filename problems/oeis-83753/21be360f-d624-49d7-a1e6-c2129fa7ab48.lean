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

- problem_id: O83753_conjecture
- collection: oeis
- question_id: oeis:83753
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/83753.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There are no palindromic numbers greater than 1 which are the fifth or higher power of a natural number.
- notes: OEIS A83753 -- https://oeis.org/A83753
- track: open
- answer_shape: proof
- source_stem: 83753
- source_namespace: OeisA83753
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A natural number $m$ is a decimal palindrome if its base-$10$ digits read the same
forwards and backwards. -/
def IsDecimalPalindrome (m : ℕ) : Prop :=
  Nat.digits 10 m = (Nat.digits 10 m).reverse

instance (m : ℕ) : Decidable (IsDecimalPalindrome m) :=
  inferInstanceAs (Decidable (Nat.digits 10 m = (Nat.digits 10 m).reverse))

open Classical in
/-- Smallest positive palindrome with exactly $n$ divisors, or $0$ if no such number exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ m, 0 < m ∧ IsDecimalPalindrome m ∧ (Nat.divisors m).card = n then
    Nat.find h
  else
    0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨1, by decide⟩).elim

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨2, by decide⟩).elim

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨4, by decide⟩).elim

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 6 := by
  classical
  dsimp [a]
  split_ifs with h
  · rw [Nat.find_eq_iff]
    decide
  · exact (h ⟨6, by decide⟩).elim

abbrev Target : Prop :=
    ∀ (m k : ℕ) (hm : 1 < m) (hpal : IsDecimalPalindrome m) (hk : 5 ≤ k),
      ¬ ∃ x : ℕ, m = x ^ k

end Problem
