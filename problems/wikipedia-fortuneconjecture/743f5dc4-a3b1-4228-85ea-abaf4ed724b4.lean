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

- problem_id: NFortuneConjecture_fortune_conjecture_refute
- collection: wikipedia
- question_id: wikipedia:FortuneConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/FortuneConjecture.lean#fortune_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Fortune's Conjecture**: Every Fortunate number is prime.
- notes: Wikipedia: FortuneConjecture -- https://en.wikipedia.org/wiki/Fortunate_number
- track: open
- answer_shape: refute
- pair_id: NFortuneConjecture_fortune_conjecture
- pair_role: refute
- source_stem: FortuneConjecture
- source_namespace: FortuneConjecture
- source_theorem: fortune_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: exists_one_lt_prime_add fortunateNumber_spec fortunateNumber_le fortunateNumber_zero fortunateNumber_one fortunateNumber_two fortunateNumber_three
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat

/-- For any natural number `N` there is some `m > 1` with `N + m` prime; an
immediate consequence of the infinitude of primes. -/
@[category API, AMS 11]
lemma exists_one_lt_prime_add (N : ℕ) : ∃ m, 1 < m ∧ Nat.Prime (N + m) := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (N + 2)
  refine ⟨p - N, by omega, ?_⟩
  have hsum : N + (p - N) = p := by omega
  rw [hsum]; exact hp_prime

/-- The $n$-th *Fortunate number* (0-indexed): the smallest integer $m > 1$ such
that $p_{n+1}\\# + m$ is prime.

`Nat.nth Nat.Prime n` is the $(n+1)$-st prime (0-indexed), and `primorial p` is the
product of all primes $\le p$; when $p$ is the $(n+1)$-st prime this equals the
product of the first $n+1$ primes. Thus `fortunateNumber 0` corresponds to
$F_1 = 3$ in the OEIS A005235 indexing. -/
noncomputable def fortunateNumber (n : ℕ) : ℕ :=
  Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n)))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- `fortunateNumber n` is greater than $1$, and adding it to the primorial of
the $(n+1)$-st prime yields a prime. -/
@[category API, AMS 11]
lemma fortunateNumber_spec (n : ℕ) :
    1 < fortunateNumber n ∧
      Nat.Prime (primorial (Nat.nth Nat.Prime n) + fortunateNumber n) :=
  Nat.find_spec (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n)))

/-- Minimality of `fortunateNumber n`: no smaller integer $m > 1$ makes
`primorial (Nat.nth Nat.Prime n) + m` prime. -/
@[category API, AMS 11]
lemma fortunateNumber_le (n m : ℕ) (hm : 1 < m)
    (hp : Nat.Prime (primorial (Nat.nth Nat.Prime n) + m)) :
    fortunateNumber n ≤ m :=
  Nat.find_min' (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime n))) ⟨hm, hp⟩

-- The first four Fortunate numbers (OEIS A005235): 3, 5, 7, 13.

@[category API, AMS 11]
theorem fortunateNumber_zero : fortunateNumber 0 = 3 := by
  have hp : primorial (Nat.nth Nat.Prime 0) = 2 := by
    rw [Nat.nth_prime_zero_eq_two]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 0))) = 3
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 0) + 3)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m
    norm_num at hmp

@[category API, AMS 11]
theorem fortunateNumber_one : fortunateNumber 1 = 5 := by
  have hp : primorial (Nat.nth Nat.Prime 1) = 6 := by
    rw [Nat.nth_prime_one_eq_three]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 1))) = 5
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 1) + 5)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m <;> norm_num at hmp

@[category API, AMS 11]
theorem fortunateNumber_two : fortunateNumber 2 = 7 := by
  have hp : primorial (Nat.nth Nat.Prime 2) = 30 := by
    rw [Nat.nth_prime_two_eq_five]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 2))) = 7
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 2) + 7)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m <;> norm_num at hmp

@[category API, AMS 11]
theorem fortunateNumber_three : fortunateNumber 3 = 13 := by
  have hp : primorial (Nat.nth Nat.Prime 3) = 210 := by
    rw [Nat.nth_prime_three_eq_seven]; decide
  show Nat.find (exists_one_lt_prime_add (primorial (Nat.nth Nat.Prime 3))) = 13
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, ?_⟩, ?_⟩
  · show Nat.Prime (primorial (Nat.nth Nat.Prime 3) + 13)
    rw [hp]; norm_num
  · rintro m hm ⟨hm1, hmp⟩
    rw [hp] at hmp
    interval_cases m <;> norm_num at hmp

abbrev Target : Prop :=
    ¬ (
      (∀ n : ℕ, Nat.Prime (fortunateNumber n))
    )

end Problem
