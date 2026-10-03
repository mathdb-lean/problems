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

- problem_id: E422_refute
- collection: erdos
- question_id: erdos:422
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/422.lean#erdos_422
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(1) = f(2) = 1$ and for $n > 2$ $$ f(n) = f(n - f(n - 1)) + f(n - f(n - 2)). $$ Does $f(n)$ miss infinitely many integers?
- notes: Erdos Problem 422 -- https://www.erdosproblems.com/422
- track: open
- answer_shape: refute
- pair_id: E422
- pair_role: refute
- source_stem: 422
- mathdb_ref: erdos:422
- source_namespace: Erdos422
- source_theorem: erdos_422
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter
open scoped Topology

/--
`IsHofstadterQ f` means that $f$ is Hofstadter's $Q$-sequence (OEIS A005185): $f(1) = f(2) = 1$
and for $n > 2$
$$
f(n) = f(n - f(n - 1)) + f(n - f(n - 2)),
$$
where the recurrence requires $f(n - 1) < n$ and $f(n - 2) < n$, so that both arguments on the
right-hand side are positive integers. The sequence begins $1, 1, 2, 3, 3, 4, \ldots$.

At most one function satisfies this predicate. Some function satisfies it if and only if $f(n)$ is
well-defined for all $n$, which is not known.
-/
def IsHofstadterQ (f : ℕ+ → ℕ+) : Prop :=
  f 1 = 1 ∧ f 2 = 1 ∧
  ∀ n : ℕ+, 2 < n →
    f (n - 1) < n ∧ f (n - 2) < n ∧ f n = f (n - f (n - 1)) + f (n - f (n - 2))

abbrev Target : Prop :=
    ¬ (
      ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → Set.Infinite {n | ∀ x, f x ≠ n}
    )

end Problem
