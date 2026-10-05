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

- problem_id: O108866_conjecture
- collection: oeis
- question_id: oeis:108866
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/108866.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: for $n > 3$, $\textrm{numerator}(-2/n + \sum_{k=1}^{n} \frac{2^k}{k}) == 0 (\textrm{mod} n^2)$ if and only if n is prime.
- notes: OEIS A108866 -- https://oeis.org/A108866
- track: open
- answer_shape: proof
- source_stem: 108866
- source_namespace: OeisA108866
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1 a_2 a_3 a_4
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
The primary defining sequence `a`.
a n is the numerator of $\sum_{k=1}^n \frac{2^k}{k}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)).num.natAbs

local macro "eval_a" : tactic => `(tactic| (delta a; norm_num))

/--
The rational number inside the numerator function in the conjecture.
$$ -\frac{2}{n} + \sum_{k=1}^n \frac{2^k}{k} $$
-/
noncomputable def ratExpression (n : ℕ) : ℚ :=
  if n > 0 then
    (-2 : ℚ) / (n : ℚ) + ∑ i ∈ (Finset.range n), (2 : ℚ) ^ (i + 1) / ((i + 1) : ℚ)
  else
    0

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by eval_a

@[category test, AMS 11]
theorem a_2 : a 2 = 4 := by eval_a

@[category test, AMS 11]
theorem a_3 : a 3 = 20 := by eval_a

@[category test, AMS 11]
theorem a_4 : a 4 = 32 := by eval_a

abbrev Target : Prop :=
    ∀ {n : ℕ} (hn : n > 3),
      (ratExpression n).num ≡ 0 [ZMOD (n^2 : ℤ)] ↔ n.Prime

end Problem
