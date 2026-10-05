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

- problem_id: O84046_conjecture
- collection: oeis
- question_id: oeis:84046
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/84046.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: if a(k) = 0 then k is an even square. This is false for $k = 27$. Every candidate $x^{27} - 27$ factors as $(x^9 - 3)(x^{18} + 3x^9 + 9)$, so $a(27) = 0$, but $27$ is not an even square.
- notes: OEIS A84046 -- https://oeis.org/A84046
- track: solved
- answer_shape: proof
- source_stem: 84046
- source_namespace: OeisA84046
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ n = p + n}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  change sInf {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 0 = p + 0} = 0
  have h_empty : {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 0 = p + 0} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp ⟨k, hk⟩
    rw [pow_zero, add_zero] at hk
    subst hk
    exact Nat.not_prime_one hp
  rw [h_empty, Nat.sInf_empty]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h_least : IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 1 = p + 1} 2 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨Nat.prime_two, 3, by norm_num⟩
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      exact hp.1.two_le
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  have h_least : IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 2 = p + 2} 2 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨Nat.prime_two, 2, by norm_num⟩
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      exact hp.1.two_le
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  have h_least : IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 3 = p + 3} 5 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by norm_num, 2, by norm_num⟩
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      rcases hp with ⟨hp_prime, k, hk⟩
      by_contra! h
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · rcases (show k ≤ 1 ∨ 2 ≤ k by omega) with hk_le | hk_ge
        · interval_cases k <;> revert hk <;> decide
        · have : 8 ≤ k ^ 3 := by
            calc 8 = 2 ^ 3 := by decide
            _ ≤ k ^ 3 := Nat.pow_le_pow_left hk_ge 3
          omega
      · rcases (show k ≤ 1 ∨ 2 ≤ k by omega) with hk_le | hk_ge
        · interval_cases k <;> revert hk <;> decide
        · have : 8 ≤ k ^ 3 := by
            calc 8 = 2 ^ 3 := by decide
            _ ≤ k ^ 3 := Nat.pow_le_pow_left hk_ge 3
          omega
      · exact (by decide : ¬ Nat.Prime 4) hp_prime
  exact h_least.csInf_eq

abbrev Target : Prop :=
    ¬ ∀ k : ℕ, a k = 0 → ∃ m : ℕ, k = (2 * m) ^ 2

end Problem
