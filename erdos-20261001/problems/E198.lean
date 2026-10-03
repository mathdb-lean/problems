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

- problem_id: E198
- collection: erdos
- question_id: erdos:198
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/198.lean#erdos_198
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The answer is no; Erdős and Graham report this was proved by Baumgartner, presumably referring to the paper [Ba75], which does not state this exactly, but the following simple construction is implicit in [Ba75]. Let $P_1,P_2,\ldots$ be an enumeration of all countably many infinite arithmetic progressions. We choose $a_1$ to be the minimal element of $P_1\cap \mathbb{N}$, and in general choose $a_n$ to be an element of $P_n\cap \mathbb{N}$ such that $a_n>2a_{n-1}$. By construction $A=\{a_1 < a_2 < \cdots\}$ contains at least one element from every infinite arithmetic progression, and is a lacunary set, so is certainly Sidon. AlphaProof has found the following explicit construction: $A = \{ (n+1)!+n : n\geq 0\}$. This is a Sidon set, and intersects every arithmetic progression, since for any $a,d\in \mathbb{N}$, $(a+d+1)!+(a+d)\in A$, and $d$ divides $(a+d+1)!+d$. This was formalized in Lean by Alexeev using Aristotle.
- notes: Erdos Problem 198 -- https://www.erdosproblems.com/198
- track: solved
- answer_shape: decide
- source_stem: 198
- mathdb_ref: erdos:198
- source_namespace: Erdos198
- source_theorem: erdos_198
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Function Set Nat

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    (∀ A : Set ℕ, IsSidon A → (∃ Y, IsAPOfLength Y ⊤ ∧ Y ⊆ Aᶜ)) ↔
        verdict

end Problem
