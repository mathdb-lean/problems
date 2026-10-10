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

- problem_id: E342_parts_i_prove
- collection: erdos
- question_id: erdos:342
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/342.lean#erdos_342.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Do infinitely many pairs $(a, a+2)$ occur in Ulam's sequence?
- notes: Erdos Problem 342 -- https://www.erdosproblems.com/342
- track: open
- answer_shape: prove
- pair_id: E342_parts_i
- pair_role: prove
- source_stem: 342
- mathdb_ref: erdos:342
- source_namespace: Erdos342
- source_theorem: erdos_342.parts.i
- source_category: research open
- source_ams: 5 11 40
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Set Filter
open scoped Topology

namespace Problem

/-- `UniqueUlamSum a n m` means that $m$ has a unique representation as $a(i) + a(j)$
with $i < j < n$. -/
def UniqueUlamSum (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∃! p : ℕ × ℕ, p.1 < p.2 ∧ p.2 < n ∧ m = a p.1 + a p.2

/-- `IsUlamSequence a` means that $a$ is the Ulam sequence (OEIS A002858):
$a(0) = 1$, $a(1) = 2$, and for each $n \geq 2$, $a(n)$ is the least integer
greater than $a(n-1)$ that has a unique representation as $a(i) + a(j)$
with $i < j < n$. -/
def IsUlamSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    UniqueUlamSum a n (a n) ∧
    ∀ m, a (n - 1) < m → m < a n → ¬ UniqueUlamSum a n m

abbrev Target : Prop :=
    ∀ a : ℕ → ℕ, IsUlamSequence a →
        Set.Infinite {n : ℕ | ∃ m, a m = a n + 2}

end Problem
