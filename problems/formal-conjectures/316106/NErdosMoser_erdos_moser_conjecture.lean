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

- problem_id: NErdosMoser_erdos_moser_conjecture
- collection: wikipedia
- question_id: wikipedia:ErdosMoser
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/ErdosMoser.lean#erdos_moser_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The only positive solution of $S_k(m)=m^k$ is $(k,m)=(1,3)$.
- notes: Wikipedia: ErdosMoser -- https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Moser_equation
- track: open
- answer_shape: proof
- source_stem: ErdosMoser
- source_namespace: ErdosMoser
- source_theorem: erdos_moser_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: powerSum_one_three powerSum_two_three powerSum_zero
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The power sum $S_k(m)=\sum_{i=1}^{m-1} i^k$. -/
def powerSum (k m : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico 1 m, i ^ k

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The pair $(1,3)$ is the trivial solution of the Erdős–Moser equation. -/
@[category test, AMS 11]
theorem powerSum_one_three : powerSum 1 3 = 3 ^ 1 := by
  decide

/-- For $k=2$ and $m=3$, the left side is $1^2+2^2=5$, not $3^2$. -/
@[category test, AMS 11]
theorem powerSum_two_three : powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2 := by
  decide

/-- Zero is a solution for every positive exponent, so the conjecture must require $m>0$. -/
@[category test, AMS 11]
theorem powerSum_zero (k : ℕ) (hk : 0 < k) : powerSum k 0 = 0 ^ k := by
  simp [powerSum, Nat.zero_pow hk]

abbrev Target : Prop :=
    ∀ k m : ℕ, 0 < k → 0 < m → powerSum k m = m ^ k → k = 1 ∧ m = 3

end Problem
