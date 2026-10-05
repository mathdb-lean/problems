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

- problem_id: O113609_conjecture_refute
- collection: oeis
- question_id: oeis:113609
- source: formal-conjectures
- source_locator: FormalConjectures/OEIS/113609.lean#conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: (25,27) is the smallest pair of prime powers (q,q+2) such that both q and q+2 are not primes, conjecture: there are more (but not < 10^6).
- notes: OEIS A113609 -- https://oeis.org/A113609
- track: open
- answer_shape: refute
- pair_id: O113609_conjecture
- pair_role: refute
- source_stem: 113609
- source_namespace: OeisA113609
- source_theorem: conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
A number $n$ is an "OEIS prime power" (for the context of A113609's definition)
if $n=1$ or $n$ is a standard prime power.
-/
def IsOeisPrimePower (n : ℕ) : Prop := n = 1 ∨ IsPrimePow n

instance DecidableIsOeisPrimePower (n : ℕ) : Decidable (IsOeisPrimePower n) := by
  simp only [IsOeisPrimePower]
  exact instDecidableOr

/--
The primary defining sequence `a`.
$a(n)$ is the number of prime powers $q<=n$ such that also $q+2$ is a prime power.
$$a(n) = \operatorname{card} \{q \in \mathbb{N} \mid 1 \le q \le n \land P(q) \land P(q+2) \}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.range (n + 1)).filter fun q =>
    IsOeisPrimePower q ∧ IsOeisPrimePower (q + 2) ∧ q ≥ 1

abbrev Target : Prop :=
    ¬ (
      ∃ q ≥ 1000000,
        IsOeisPrimePower q ∧ IsOeisPrimePower (q + 2) ∧
        ¬ q.Prime ∧ ¬ (q + 2).Prime
    )

end Problem
