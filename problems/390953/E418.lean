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

- problem_id: E418
- collection: erdos
- question_id: erdos:418
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/418.lean#erdos_418
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many integers not of the form $n - \phi(n)$? Asked by Erdős and Sierpiński. Numbers not of the form we call non-cototients. Browkin and Schinzel [BrSc95] provided an affirmative answer to this question, proving that any integer of the shape $2^{k}\cdot 509203$ for $k\geq 1$ is a non-cototient. This is discussed in problem B36 of Guy's collection [Gu04]. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 418 -- https://www.erdosproblems.com/418
- track: solved
- answer_shape: decide
- source_stem: 418
- mathdb_ref: erdos:418
- source_namespace: Erdos418
- source_theorem: erdos_418
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open scoped ArithmeticFunction.sigma

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ { (n - n.totient : ℕ) | n }ᶜ.Infinite

end Problem
