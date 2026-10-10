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

- problem_id: E477
- collection: erdos
- question_id: erdos:477
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/477.lean#erdos_477
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a polynomial $f:\mathbb{Z}\to \mathbb{Z}$ of degree at least $2$ and a set $A\subset \mathbb{Z}$ such that for any $n\in \mathbb{Z}$ there is exactly one $a\in A$ and $b\in \{ f(k) : k\in\mathbb{Z}\}$ such that $n=a+b$? The answer is yes, contrary to the expectation of Erdős and Graham: such an `A` exists whenever $f(n) = n^d$ for even $d \ge 6$. The linked formal proof (Codex, following Price's exposition) exhibits a complement of $\{k^6 : k \in \mathbb{Z}\}$; it states uniqueness as `∃! p : ℤ × ℤ, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n` and the degree condition as `2 ≤ f.natDegree`.
- notes: Erdos Problem 477 -- https://www.erdosproblems.com/477
- track: solved
- answer_shape: decide
- source_stem: 477
- mathdb_ref: erdos:477
- source_namespace: Erdos477
- source_theorem: erdos_477
- source_category: research solved
- source_ams: 12
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Polynomial Set

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ f : ℤ[X], 2 ≤ f.degree ∧ ∃ A : Set ℤ,
          ∀ z, ∃! ab ∈ A ×ˢ (Set.range f.eval), z = ab.1 + ab.2

end Problem
