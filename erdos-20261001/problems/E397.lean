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

- problem_id: E397
- collection: erdos
- question_id: erdos:397
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/397.lean#erdos_397
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there only finitely many solutions to $$ \prod_i \binom{2m_i}{m_i}=\prod_j \binom{2n_j}{n_j} $$ with the $m_i,n_j$ distinct? Somani, using ChatGPT, has given a negative answer. In fact, for any $a\geq 2$, if $c=8a^2+8a+1$, $\binom{2a}{a}\binom{4a+4}{2a+2}\binom{2c}{c}= \binom{2a+2}{a+1}\binom{4a}{2a}\binom{2c+2}{c+1}.$ Further families of solutions are given in the comments by SharkyKesa. This was earlier asked about in a [MathOverflow] question, in response to which Elkies also gave an alternative construction which produces solutions - at the moment it is not clear whether Elkies' argument gives infinitely many solutions (although Bloom believes that it can). This was formalized in Lean by Wu using Aristotle.
- notes: Erdos Problem 397 -- https://www.erdosproblems.com/397
- track: solved
- answer_shape: decide
- source_stem: 397
- mathdb_ref: erdos:397
- source_namespace: Erdos397
- source_theorem: erdos_397
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      {(M, N) : Finset ℕ × Finset ℕ | Disjoint M N ∧
      ∏ i ∈ M, centralBinom i = ∏ j ∈ N, centralBinom j}.Finite

end Problem
