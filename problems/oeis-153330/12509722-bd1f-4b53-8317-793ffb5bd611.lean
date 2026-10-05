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

- problem_id: O153330_conjecture3
- collection: oeis
- question_id: oeis:153330
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/153330.lean#conjecture3
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture 3 (Ya-Ping Lu, 2024): Except 1, 3 and 6, the absolute value of all terms can be written as $5x + 8y$ for $x, y \in \mathbb{N}$. (Note: in the OEIS comment, "x and y are integers" means $x$ and $y$ have the same sign, i.e., $|v| = 5x + 8y$ with $x, y \ge 0$, since every integer is a $\mathbb{Z}$-linear combination of 5 and 8).
- notes: OEIS A153330 -- https://oeis.org/A153330
- track: open
- answer_shape: proof
- source_stem: 153330
- source_namespace: OeisA153330
- source_theorem: conjecture3
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Single step of the Collatz mapping. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

open Classical in
/-- Number of iterations required to turn $n$ into 1 in the Collatz process,
or `none` if $n$ does not terminate. -/
noncomputable def collatzSteps (n : ℕ) : Option ℕ :=
  if n = 0 then none
  else if ∃ k : ℕ, (collatzStep^[k]) n = 1 then
    some (sInf {k : ℕ | (collatzStep^[k]) n = 1})
  else
    none

open Classical in
/-- The sequence $a(n) = \mathrm{A006577}(n+1) - \mathrm{A006577}(n)$ for $n > 0$,
or `none` if either $n$ or $n+1$ does not terminate. -/
noncomputable def a (n : ℕ) : Option ℤ :=
  if n = 0 then none
  else
    match collatzSteps (n + 1), collatzSteps n with
    | some s2, some s1 => some (s2 - s1)
    | _, _ => none

/-- The set of positive indices $n$ for which $a(n) = v$. -/
def indices (v : ℤ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ a n = some v}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = none := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = some 1 := by
  have h1 : IsLeast {k : ℕ | (collatzStep^[k]) 1 = 1} 0 := ⟨rfl, by simp [lowerBounds]⟩
  have h2 : IsLeast {k : ℕ | (collatzStep^[k]) 2 = 1} 1 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k; revert hk; decide
  have hs1 : collatzSteps 1 = some 0 := by
    have h : ∃ k, (collatzStep^[k]) 1 = 1 := ⟨0, h1.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h1.csInf_eq]
  have hs2 : collatzSteps 2 = some 1 := by
    have h : ∃ k, (collatzStep^[k]) 2 = 1 := ⟨1, h2.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h2.csInf_eq]
  rw [a, if_neg (by omega), hs2, hs1]; rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = some 6 := by
  have h2 : IsLeast {k : ℕ | (collatzStep^[k]) 2 = 1} 1 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k; revert hk; decide
  have h3 : IsLeast {k : ℕ | (collatzStep^[k]) 3 = 1} 7 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs2 : collatzSteps 2 = some 1 := by
    have h : ∃ k, (collatzStep^[k]) 2 = 1 := ⟨1, h2.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h2.csInf_eq]
  have hs3 : collatzSteps 3 = some 7 := by
    have h : ∃ k, (collatzStep^[k]) 3 = 1 := ⟨7, h3.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h3.csInf_eq]
  rw [a, if_neg (by omega), hs3, hs2]; rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = some (-5) := by
  have h3 : IsLeast {k : ℕ | (collatzStep^[k]) 3 = 1} 7 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h4 : IsLeast {k : ℕ | (collatzStep^[k]) 4 = 1} 2 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs3 : collatzSteps 3 = some 7 := by
    have h : ∃ k, (collatzStep^[k]) 3 = 1 := ⟨7, h3.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h3.csInf_eq]
  have hs4 : collatzSteps 4 = some 2 := by
    have h : ∃ k, (collatzStep^[k]) 4 = 1 := ⟨2, h4.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h4.csInf_eq]
  rw [a, if_neg (by omega), hs4, hs3]; rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = some 3 := by
  have h4 : IsLeast {k : ℕ | (collatzStep^[k]) 4 = 1} 2 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have h5 : IsLeast {k : ℕ | (collatzStep^[k]) 5 = 1} 5 := by
    constructor
    · rfl
    · intro k hk; by_contra! h; interval_cases k <;> revert hk <;> decide
  have hs4 : collatzSteps 4 = some 2 := by
    have h : ∃ k, (collatzStep^[k]) 4 = 1 := ⟨2, h4.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h4.csInf_eq]
  have hs5 : collatzSteps 5 = some 5 := by
    have h : ∃ k, (collatzStep^[k]) 5 = 1 := ⟨5, h5.1⟩
    rw [collatzSteps, if_neg (by omega), if_pos h, h5.csInf_eq]
  rw [a, if_neg (by omega), hs5, hs4]; rfl

abbrev Target : Prop :=
    ∀ (n : ℕ) (v : ℤ) (hn : 0 < n) (ha : a n = some v)
        (hv : v ≠ 1 ∧ v ≠ 3 ∧ v ≠ 6),
      ∃ x y : ℕ, v.natAbs = 5 * x + 8 * y

end Problem
