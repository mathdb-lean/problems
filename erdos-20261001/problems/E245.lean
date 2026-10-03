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

- problem_id: E245
- collection: erdos
- question_id: erdos:245
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/245.lean#erdos_245
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq\mathbb{N}$ be an infinite set such that $|A\cap \{1, ..., N\}| = o(N)$. Is it true that $$ \limsup_{N\to\infty}\frac{|(A + A)\cap \{1, ..., N\}|}{|A \cap \{1, ..., N\}|} \geq 3? $$ The answer is yes, proved by Freiman [Fr73]. [Fr73] Fre\u{\i}man, G. A., _Foundations of a structural theory of set addition_. (1973), vii+108.
- notes: Erdos Problem 245 -- https://www.erdosproblems.com/245
- track: solved
- answer_shape: decide
- source_stem: 245
- mathdb_ref: erdos:245
- source_namespace: Erdos245
- source_theorem: erdos_245
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter Set

open scoped Pointwise Topology

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (𝓝 0) →
      3 ≤ atTop.limsup
        fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal)
          / (A ∩ Icc 1 ⌊N⌋₊).ncard

end Problem
