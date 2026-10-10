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

- problem_id: E700_parts_iii_refute
- collection: erdos
- question_id: erdos:700
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/700.lean#erdos_700.parts.iii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n) = \min_{1 < k \le n/2} \gcd(n, \binom{n}{k})$. **(c)** Is it true that, for every composite $n$, $f(n) \ll_A n/(\log n)^A$ for every $A > 0$? Erdős–Szekeres [ErSz78] prove the weaker bound $f(n) \le (1 + o(1)) n/\log n$ (the case $A = 1$). Here $f(n) \ll_A n/(\log n)^A$ is spelled out as: for every `A > 0` there is a constant `C` (depending on `A`) with `f(n) ≤ C · n/(log n)^A` for every composite `n`.
- notes: Erdos Problem 700 -- https://www.erdosproblems.com/700
- track: open
- answer_shape: refute
- pair_id: E700_parts_iii
- pair_role: refute
- source_stem: 700
- mathdb_ref: erdos:700
- source_namespace: Erdos700
- source_theorem: erdos_700.parts.iii
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: f_eq f_mem f_le prime_dvd_of_not_dvd_choose
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Finset

/-- `f n = min_{1 < k ≤ n/2} gcd(n, C(n,k))`. (The infimum is `0` when the range is empty, i.e.
`n < 4`.) -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-- `P n` is the largest prime factor of `n` (and `0` if `n ≤ 1`). -/
noncomputable def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The set whose infimum defines `f`. -/
def fSet (n : ℕ) : Set ℕ := {m | ∃ k, 1 < k ∧ k ≤ n / 2 ∧ m = Nat.gcd n (n.choose k)}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- `f n` unfolds to the infimum of `fSet n`. -/
@[category API, AMS 11]
lemma f_eq (n : ℕ) : f n = sInf (fSet n) := rfl

/-- Each `gcd(n, C(n,k))` with `1 < k ≤ n/2` belongs to `fSet n`. -/
@[category API, AMS 11]
lemma f_mem (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    Nat.gcd n (n.choose k) ∈ fSet n := ⟨k, h1, h2, rfl⟩

/-- `f n` is a lower bound: `f n ≤ gcd(n, C(n,k))` for every `1 < k ≤ n/2`. -/
@[category API, AMS 11]
lemma f_le (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    f n ≤ Nat.gcd n (n.choose k) := Nat.sInf_le (f_mem n k h1 h2)

/- ## Proven partial results toward (a) -/

/-- Lucas (one step): for prime `P ∣ n`, if `P ∤ C(n,k)` then `P ∣ k`. -/
@[category API, AMS 11]
lemma prime_dvd_of_not_dvd_choose (P n k : ℕ) (hP : P.Prime) (hPn : P ∣ n)
    (h : ¬ P ∣ n.choose k) : P ∣ k := by
  have := Fact.mk hP
  by_contra hk
  apply h
  have hmod : n.choose k ≡ (n % P).choose (k % P) * (n / P).choose (k / P) [MOD P] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  have hn0 : n % P = 0 := by
    have h := (Nat.modEq_zero_iff_dvd).2 hPn; simpa [Nat.ModEq, Nat.zero_mod] using h
  have hkP : 0 < k % P := Nat.pos_of_ne_zero (fun hh => hk (Nat.dvd_of_mod_eq_zero hh))
  rw [hn0, Nat.choose_eq_zero_of_lt hkP, zero_mul] at hmod
  exact (Nat.modEq_zero_iff_dvd).1 hmod

abbrev Target : Prop :=
    ¬ (
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬ n.Prime → 1 < n →
        (f n : ℝ) ≤ C * (n : ℝ) / (Real.log n) ^ A)
    )

end Problem
