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

- problem_id: E899
- collection: erdos
- question_id: erdos:899
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/899.lean#erdos_899
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq\mathbb{N}$ be an infinite set such that $|A\cap \{1, ..., N\}| = o(N)$. Is it true that $$ \limsup_{N\to\infty}\frac{|(A - A)\cap \{1, ..., N\}|}{|A \cap \{1, ..., N\}|} = \infty? $$ The answer is yes, proved by Ruzsa [Ru78]. [Ru78] Ruzsa, I. Z., _On the cardinality of {$A+A$}\ and {$A-A$}_. (1978), 933--938.
- notes: Erdos Problem 899 -- https://www.erdosproblems.com/899
- track: solved
- answer_shape: decide
- source_stem: 899
- mathdb_ref: erdos:899
- source_namespace: Erdos899
- source_theorem: erdos_899
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Set

open scoped Pointwise Topology

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (A : Set ℕ), A.Infinite →
        Tendsto (fun N => (A ∩ Icc 1 N |>.ncard : ℝ) / N) atTop (𝓝 0) →
        atTop.limsup (fun N => ((A - A : Set ℕ) ∩ Icc 1 N |>.ncard : EReal) /
          (A ∩ Icc 1 N).ncard) = ⊤

end Problem
