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

- problem_id: O159829_conjecture1
- collection: oeis
- question_id: oeis:159829
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/159829.lean#conjecture1
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture 1: For any $k \ge 3$, there are infinitely many primes of the form $n^k + m^k$ for $n, m \ge 1$. - _Ulrich Krug_, 2009 Answer: No. - _Kenta Kitamura_, 2026
- notes: OEIS A159829 -- https://oeis.org/A159829
- track: solved
- answer_shape: decide
- source_stem: 159829
- source_namespace: OeisA159829
- source_theorem: conjecture1
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Classical in
/-- $a(n)$ is the smallest natural number $m \ge 1$ such that $n^3 + m^3 + 1$ is prime,
or `none` if no such $m$ exists. -/
noncomputable def a (n : ℕ) : Option ℕ :=
  if ∃ m : ℕ, 1 ≤ m ∧ (n ^ 3 + m ^ 3 + 1).Prime then
    some (sInf {m : ℕ | 1 ≤ m ∧ (n ^ 3 + m ^ 3 + 1).Prime})
  else
    none

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = some 1 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (1 ^ 3 + m ^ 3 + 1).Prime} 1 :=
    ⟨⟨le_rfl, by decide⟩, fun m hm => hm.1⟩
  have h_ex : ∃ m : ℕ, 1 ≤ m ∧ (1 ^ 3 + m ^ 3 + 1).Prime := ⟨1, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = some 2 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (2 ^ 3 + m ^ 3 + 1).Prime} 2 :=
    ⟨⟨by decide, by decide⟩, fun m hm => by
      by_contra hc
      have hm1 : 1 ≤ m := hm.1
      have hm2 : m < 2 := not_le.mp hc
      obtain ⟨_, hprime⟩ := hm
      interval_cases m
      revert hprime
      decide⟩
  have h_ex : ∃ m : ℕ, 1 ≤ m ∧ (2 ^ 3 + m ^ 3 + 1).Prime := ⟨2, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = some 1 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (3 ^ 3 + m ^ 3 + 1).Prime} 1 :=
    ⟨⟨le_rfl, by decide⟩, fun m hm => hm.1⟩
  have h_ex : ∃ m : ℕ, 1 ≤ m ∧ (3 ^ 3 + m ^ 3 + 1).Prime := ⟨1, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = some 2 := by
  have h : IsLeast {m : ℕ | 1 ≤ m ∧ (4 ^ 3 + m ^ 3 + 1).Prime} 2 :=
    ⟨⟨by decide, by decide⟩, fun m hm => by
      by_contra hc
      have hm1 : 1 ≤ m := hm.1
      have hm2 : m < 2 := not_le.mp hc
      obtain ⟨_, hprime⟩ := hm
      interval_cases m
      revert hprime
      decide⟩
  have h_ex : ∃ m : ℕ, 1 ≤ m ∧ (4 ^ 3 + m ^ 3 + 1).Prime := ⟨2, h.1⟩
  rw [a, if_pos h_ex, h.csInf_eq]

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (k : ℕ), 3 ≤ k →
      Set.Infinite {p : ℕ | ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ p.Prime ∧
        p = n ^ k + m ^ k}

end Problem
