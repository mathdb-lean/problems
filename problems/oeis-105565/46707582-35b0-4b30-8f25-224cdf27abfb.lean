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

- problem_id: O105565_conjecture
- collection: oeis
- question_id: oeis:105565
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/105565.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $\beta-2 < S(n)-\alpha n < \beta-1$. The constants $\alpha$ and $\beta$ are as defined in the formula section. Solved by OpenAI Codex, prompted by Adam Haig. A complete Lean 4 proof is linked by the `formal_proof` attribute below.
- notes: OEIS A105565 -- https://oeis.org/A105565
- track: solved
- answer_shape: proof
- source_stem: 105565
- source_namespace: OeisA105565
- source_theorem: conjecture
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_1 a_2 a_3 a_4 a_5
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Finset Real

/--
The primary defining sequence `a`.
$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
That is, $a(n) = 1$ if the number of indices $k \in \mathbb{N}$ such that
$10^{n-1} \le \mathrm{fib}(k) < 10^n$ is 5.
-/
def a (n : ℕ) : ℕ :=
  if n > 0 then
    -- $n$ is the number of digits, so $n \ge 1$.
    let lowerBound : ℕ := 10 ^ (n - 1)
    let upperBound : ℕ := 10 ^ n

    -- A safe upper bound for the index $k$.
    let maxK : ℕ := 5 * n + 10

    -- Count indices $k$ in range $[0, maxK)$ such that $\mathrm{fib}(k)$ has $n$ digits.
    let count : ℕ :=
      (filter (fun k => lowerBound ≤ Nat.fib k ∧ Nat.fib k < upperBound) (range maxK)).card

    if count = 5 then 1 else 0
  else
    0

/-- The golden ratio $\phi = (1 + \sqrt{5})/2$. -/
noncomputable def phi : Real := goldenRatio

/-- The constant $\alpha = \log(10)/\log(\phi) - 4$. -/
noncomputable def alphaConst : Real := Real.log 10 / Real.log phi - 4

/-- The constant $\beta = \log(5)/(2\log(\phi)) - 1$. -/
noncomputable def betaConst : Real := Real.log 5 / (2 * Real.log phi) - 1

/-- The partial sum $S(n) = \sum_{k=1}^n a(k)$. -/
noncomputable def s (n : ℕ) : Real :=
  (Finset.Icc 1 n).sum (fun k => (a k : Real))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by decide

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : 1 ≤ n),
      betaConst - 2 < s n - alphaConst * (n : Real) ∧
        s n - alphaConst * (n : Real) < betaConst - 1

end Problem
