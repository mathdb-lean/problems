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

- problem_id: E645
- collection: erdos
- question_id: erdos:645
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/645.lean#erdos_645
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: If ℕ is $2$-coloured then there must exist a monochromatic three-term arithmetic progression $x,x+d,x+2d$ such that $d>x$. This was first proved by Brown and Landman [BrLa99], who in fact show that this is always possible with $d>f(x)$ for any increasing function $f$. This was formalized in Lean by Alexeev using Aristotle and ChatGPT.
- notes: Erdos Problem 645 -- https://www.erdosproblems.com/645
- track: solved
- answer_shape: proof
- source_stem: 645
- mathdb_ref: erdos:645
- source_namespace: Erdos645
- source_theorem: erdos_645
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (c : ℕ → Bool),
      ∃ x d, 0 < x ∧ x < d ∧
          (∃ C, c x = C ∧ c (x + d) = C ∧ c (x + 2 * d) = C)

end Problem
