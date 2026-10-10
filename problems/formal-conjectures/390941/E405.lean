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

- problem_id: E405
- collection: erdos
- question_id: erdos:405
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/405.lean#erdos_405
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p$ be an odd prime. Is it true that the equation $(p-1)!+a^{p-1}=p^k$ has only finitely many solutions? Originally proposed by Erdős and Graham [ErGr80]. Brindza and Erdős [BrEr91] proved that there are finitely many such solutions.
- notes: Erdos Problem 405 -- https://www.erdosproblems.com/405
- track: solved
- answer_shape: proof
- source_stem: 405
- mathdb_ref: erdos:405
- source_namespace: Erdos405
- source_theorem: erdos_405
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Nat

namespace Problem

abbrev Target : Prop :=
    Set.Finite { x : ℕ × ℕ × ℕ | let (a, k, p) := x; p.Prime ∧ Odd p ∧
      Nat.factorial (p - 1) + a ^ (p - 1) = p ^ k}

end Problem
