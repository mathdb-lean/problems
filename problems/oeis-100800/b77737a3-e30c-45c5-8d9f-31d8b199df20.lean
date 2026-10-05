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

- problem_id: O100800_conjecture
- collection: oeis
- question_id: oeis:100800
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/100800.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: A100800 Conjecture: No term is zero.
- notes: OEIS A100800 -- https://oeis.org/A100800
- track: open
- answer_shape: proof
- source_stem: 100800
- source_namespace: OeisA100800
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_of_dvd a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Function

/-- The sum of the decimal digits of a natural number. -/
def sumDigits (n : ℕ) : ℕ := ((10).digits n).sum

/-- The function $f(n) = n + \text{sum of the digits of } n$. -/
def f (n : ℕ) : ℕ := n + sumDigits n

open Classical in
/--
a n is the first iteration of $f(n) = n + \text{sum of the digits of } n$ that is a multiple of $n$.
$a(n) = 0$ if no such number exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- P(k) holds if the (k+1)-th iteration of f is a multiple of n.
  -- k=0 corresponds to the first iteration, f(n).
  let P (k : ℕ) : Prop := n ∣ Nat.iterate f (k + 1) n

  -- We use the noncomputable definition of finding the minimum index if it exists,
  -- or returning 0 otherwise, using the standard classical definition pattern.
  dite (∃ k, P k)
    (fun h_exists =>
      let k₀ : ℕ := Nat.find h_exists
      Nat.iterate f (k₀ + 1) n)
    (fun _ => 0)

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- If `n` already divides `f n`, the search stops immediately and `a n = f n`.  -/
@[category API, AMS 11]
lemma a_of_dvd {n : ℕ} (h : n ∣ f n) : a n = f n := by
  have hex : ∃ k, n ∣ f^[k + 1] n := ⟨0, by simpa using h⟩
  have hfind : Nat.find hex = 0 := (Nat.find_eq_zero hex).2 (by simpa using h)
  rw [a, dif_pos hex, hfind]
  simp

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by rw [a_of_dvd (by norm_num)]; norm_num [f, sumDigits]

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by rw [a_of_dvd (by norm_num [f, sumDigits])]; norm_num [f, sumDigits]

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := by rw [a_of_dvd (by norm_num [f, sumDigits])]; norm_num [f, sumDigits]

@[category test, AMS 11]
theorem a_4 : a 4 = 8 := by rw [a_of_dvd (by norm_num [f, sumDigits])]; norm_num [f, sumDigits]

@[category test, AMS 11]
theorem a_5 : a 5 = 10 := by rw [a_of_dvd (by norm_num [f, sumDigits])]; norm_num [f, sumDigits]

abbrev Target : Prop :=
    ∀ (n : ℕ), n ≠ 0 → a n ≠ 0

end Problem
