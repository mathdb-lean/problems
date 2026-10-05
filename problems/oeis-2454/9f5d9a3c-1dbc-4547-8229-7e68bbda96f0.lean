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

- problem_id: O2454_conjecture
- collection: oeis
- question_id: oeis:2454
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/2454.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\zeta$ be a primitive $(2n+1)$-th root of unity. Then the permanent of the $2n \times 2n$ matrix $[m(j,k)]_{j,k=1..2n}$ is $a(n)/(2n+1) = ((2n)!!)^2/(2n+1)$, where $m(j,k)$ is $1$ or $(1+\zeta^{j-k})/(1-\zeta^{j-k})$ according as $j = k$ or not. - Zhi-Wei Sun, Jun 26 2022 Proved by [SSX22], Theorem 1.3(ii): for odd $m > 1$ and $\zeta$ a primitive $m$-th root of unity, the permanent of $[c_{j,k}]_{1 \le j,k \le m-1}$ is $((m-1)!!)^2/m$. Take $m = 2n+1$; translating both matrix indices by one leaves $j - k$ unchanged. For $n = 0$ the matrix is empty and both sides are $1$.
- notes: OEIS A2454 -- https://oeis.org/A2454
- track: solved
- answer_shape: proof
- source_stem: 2454
- source_namespace: OeisA2454
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- Central factorial numbers: $a(n) = 4^n (n!)^2$. -/
def a (n : ℕ) : ℕ :=
  4 ^ n * n.factorial ^ 2

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 4 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 64 := by rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 2304 := by rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 147456 := by rfl

abbrev Target : Prop :=
    ∀ (n : ℕ),
      let N : ℕ := 2 * n
      let K : ℕ := N + 1
      ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
        Matrix.permanent (fun (j k : Fin N) =>
          if j = k then
            (1 : ℂ)
          else
            let pow : ℤ := (j : ℤ) - (k : ℤ)
            (1 + ζ ^ pow) / (1 - ζ ^ pow)
        ) = (a n : ℂ) / (K : ℂ)

end Problem
