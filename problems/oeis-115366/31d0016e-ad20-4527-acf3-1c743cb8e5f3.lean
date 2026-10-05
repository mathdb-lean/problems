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

- problem_id: O115366_conjecture
- collection: oeis
- question_id: oeis:115366
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/115366.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Conjecture: $a(n)/A006880(n) \rightarrow 1.77...$ where A006880(n) is the number of primes $\le 10^n$.
- notes: OEIS A115366 -- https://oeis.org/A115366
- track: open
- answer_shape: proof
- source_stem: 115366
- source_namespace: OeisA115366
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: a_0 a_1
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Real Topology

/--
The primary defining sequence `a`.
$a(n) = \#\{k \in \mathbb{N} \mid 1 \le k \le 10^n \land (k^2 + 3k + 1) \text{ is prime} \}.$
-/
def a (n : ℕ) : ℕ :=
  Finset.card <|
    Finset.filter
      (fun k : ℕ => Nat.Prime (k ^ 2 + 3 * k + 1))
      (Finset.Icc 1 (10 ^ n))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 9 := by decide

abbrev Target : Prop :=
    ∃ L : ℝ,
      Tendsto (fun n : ℕ => (a n : ℝ) / (Nat.primeCounting' (10 ^ n) : ℝ)) atTop (nhds L) ∧
      1.77 ≤ L ∧ L ≤ 1.78

end Problem
