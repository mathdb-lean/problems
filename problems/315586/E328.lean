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

- problem_id: E328
- collection: erdos
- question_id: erdos:328
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/328.lean#erdos_328
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose $A\subseteq\mathbb{N}$ and $C>0$ is such that $1_A\ast 1_A(n)\leq C$ for all $n\in\mathbb{N}$. Can $A$ be partitioned into $t$ many subsets $A_1,\ldots,A_t$ (where $t=t(C)$ depends only on $C$) such that $1_{A_i}\ast 1_{A_i}(n)<C$ for all $1\leq i\leq t$ and $n\in \mathbb{N}$? The answer is no. Asked by Erdős and Newman. Nešetřil and Rödl [NeRo85] have shown the answer is no for all $C$ (even if $t$ is also allowed to depend on $A$). Erdős [Er80e] had previously shown the answer is no for $C=3,4$ and infinitely many other values of $C$. See also [774]. The linked proof writes the representation function as `Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}`, which counts the same ordered pairs as `sumRep`, and states the partition condition as a named definition with the same two conjuncts used below. Its `∃ t` additionally carries `1 ≤ t`, which costs nothing: `t = 0` forces `A = ∅`, and `A = {1}` has all representation counts at most `C` for `C ≥ 1`.
- notes: Erdos Problem 328 -- https://www.erdosproblems.com/328
- track: solved
- answer_shape: decide
- source_stem: 328
- mathdb_ref: erdos:328
- source_namespace: Erdos328
- source_theorem: erdos_328
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open AdditiveCombinatorics

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ C : ℕ, 0 < C →
          ∃ t : ℕ, ∀ A : Set ℕ, (∀ n, sumRep A n ≤ C) →
            ∃ P : Fin t → Set ℕ, (⋃ i, P i) = A ∧
              Set.univ.PairwiseDisjoint P ∧
              ∀ i, ∀ n, sumRep (P i) n < C

end Problem
