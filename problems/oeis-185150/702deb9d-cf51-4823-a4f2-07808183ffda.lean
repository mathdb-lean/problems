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

- problem_id: O185150_conjecture
- collection: oeis
- question_id: oeis:185150
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/185150.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $a(n) > 0$ for all $n > 0$. - _Zhi-Wei Sun_, Dec 29 2012
- notes: OEIS A185150 -- https://oeis.org/A185150
- track: open
- answer_shape: proof
- source_stem: 185150
- source_namespace: OeisA185150
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Number of odd primes $p \in (n^2, (n+1)^2)$ with $(n/p) = 1$. -/
def a (n : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2),
    if p.Prime ∧ p ≠ 2 ∧ jacobiSym (n : ℤ) p = 1 then 1 else 0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  change (if (2).Prime ∧ 2 ≠ 2 ∧ jacobiSym (1 : ℤ) 2 = 1 then 1 else 0) +
         ((if (3).Prime ∧ 3 ≠ 2 ∧ jacobiSym (1 : ℤ) 3 = 1 then 1 else 0) + 0) = 1
  norm_num

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  change (if (5).Prime ∧ 5 ≠ 2 ∧ jacobiSym (2 : ℤ) 5 = 1 then 1 else 0) +
         ((if (6).Prime ∧ 6 ≠ 2 ∧ jacobiSym (2 : ℤ) 6 = 1 then 1 else 0) +
         ((if (7).Prime ∧ 7 ≠ 2 ∧ jacobiSym (2 : ℤ) 7 = 1 then 1 else 0) +
         ((if (8).Prime ∧ 8 ≠ 2 ∧ jacobiSym (2 : ℤ) 8 = 1 then 1 else 0) + 0))) = 1
  norm_num

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +kernel

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by decide +kernel

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 0 < n),
      0 < a n

end Problem
