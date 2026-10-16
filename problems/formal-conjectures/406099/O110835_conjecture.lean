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

- problem_id: O110835_conjecture
- collection: oeis
- question_id: oeis:110835
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/110835.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Sierpinski's conjecture (1958) is precisely that $a(n) >= n$ for all $n$.
- notes: OEIS A110835 -- https://oeis.org/A110835
- track: open
- answer_shape: proof
- source_stem: 110835
- source_namespace: OeisA110835
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Set

/--
The primary defining sequence `a`.
$a(n)$ is the smallest $m > 0$ such that there are no primes between $n \cdot m$
and $n \cdot (m+1)$ inclusive.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let IsPrimeFreeInterval (m : ℕ) : Prop :=
    ∀ p : ℕ, p.Prime → ¬ (n * m ≤ p ∧ p ≤ n * (m + 1))
  let s : Set ℕ := {m : ℕ | m > 0 ∧ IsPrimeFreeInterval m}
  sInf s

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 8 := by
  dsimp [a]
  have hleast : IsLeast {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (1 * m ≤ p ∧ p ≤ 1 * (m + 1))} 8 := by
    constructor
    · simp only [mem_ofPred_eq, one_mul]
      refine ⟨by decide, ?_⟩
      intro p hp ⟨hge, hle⟩
      interval_cases p <;> revert hp <;> decide
    · rintro m ⟨hmpos, hfree⟩
      by_contra! hlt
      simp only [one_mul] at hfree
      interval_cases m
      · specialize hfree 2 (by decide); revert hfree; decide
      · specialize hfree 2 (by decide); revert hfree; decide
      · specialize hfree 3 (by decide); revert hfree; decide
      · specialize hfree 5 (by decide); revert hfree; decide
      · specialize hfree 5 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
  exact hleast.csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by
  dsimp [a]
  have hleast : IsLeast {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (2 * m ≤ p ∧ p ≤ 2 * (m + 1))} 4 := by
    constructor
    · simp only [mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      intro p hp ⟨hge, hle⟩
      interval_cases p <;> revert hp <;> decide
    · rintro m ⟨hmpos, hfree⟩
      by_contra! hlt
      interval_cases m
      · specialize hfree 2 (by decide); revert hfree; decide
      · specialize hfree 5 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
  exact hleast.csInf_eq

@[category test, AMS 11]
theorem a_3 : a 3 = 8 := by
  dsimp [a]
  have hleast : IsLeast {m : ℕ | m > 0 ∧ ∀ p : ℕ, p.Prime → ¬ (3 * m ≤ p ∧ p ≤ 3 * (m + 1))} 8 := by
    constructor
    · simp only [mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      intro p hp ⟨hge, hle⟩
      interval_cases p <;> revert hp <;> decide
    · rintro m ⟨hmpos, hfree⟩
      by_contra! hlt
      interval_cases m
      · specialize hfree 3 (by decide); revert hfree; decide
      · specialize hfree 7 (by decide); revert hfree; decide
      · specialize hfree 11 (by decide); revert hfree; decide
      · specialize hfree 13 (by decide); revert hfree; decide
      · specialize hfree 17 (by decide); revert hfree; decide
      · specialize hfree 19 (by decide); revert hfree; decide
      · specialize hfree 23 (by decide); revert hfree; decide
  exact hleast.csInf_eq

abbrev Target : Prop :=
    ∀ n > 0, a n ≥ n

end Problem
