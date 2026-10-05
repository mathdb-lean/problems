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

- problem_id: O108211_conjecture
- collection: oeis
- question_id: oeis:108211
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/108211.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $$a(n) = \left\lfloor \frac{1}{\frac{1}{4n} - \log(2) + \frac{1}{n+1} + \frac{1}{n+2} + \dots + \frac{1}{2n}} \right\rfloor.$$ **Proof sketch** (certificate style; the kernel-checked development lives at the `formal_proof` permalink below). Write $T(n) = \log 2 - (H(2n) - H(n))$ for the harmonic tail defect. The proof sandwiches $T(n)$ between two explicit telescoping bounds — $h(n)$ from below and $h(n) + 60/(4n+1)^7$ from above, where $h$ telescopes a degree-7 rational certificate. The two resulting inequalities reduce to polynomial coefficient-nonnegativity facts discharged by elementary tactics, after which the reciprocal lands in $[16n^2 + 1,\, 16n^2 + 2)$ and the floor evaluates exactly.
- notes: OEIS A108211 -- https://oeis.org/A108211
- track: solved
- answer_shape: proof
- source_stem: 108211
- source_namespace: OeisA108211
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The primary defining sequence `a`.
`a n` is defined as $16n^2 + 1$.
-/
def a (n : ℕ) : ℕ := 16 * n ^ 2 + 1

open Real

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 17 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 65 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 145 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 257 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 401 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : n > 0),
      (a n : ℝ) =
        (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ)

end Problem
