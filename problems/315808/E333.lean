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

- problem_id: E333
- collection: erdos
- question_id: erdos:333
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/333.lean#erdos_333
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ be a set of density zero. Does there exist a $B$ such that $A\subseteq B+B$ and $$\lvert B\cap \{1,\ldots,N\}\rvert =o(N^{1/2})$$ for all large $N$? The answer is no. Erdős and Newman [ErNe77] have proved this is true when $A$ is the set of squares. In fact, Theorem 2 of [ErNe77] already implies a negative answer to this problem, but this seems to have been overlooked by Erdős and Graham. See also [806].
- notes: Erdos Problem 333 -- https://www.erdosproblems.com/333
- track: solved
- answer_shape: decide
- source_stem: 333
- mathdb_ref: erdos:333
- source_namespace: Erdos333
- source_theorem: erdos_333
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Asymptotics

open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ A : Set ℕ, A.HasDensity 0 →
          ∃ B : Set ℕ, A ⊆ B + B ∧
            (fun N => ((B ∩ Set.Icc 1 N).ncard : ℝ)) =o[atTop]
              fun N => Real.sqrt N

end Problem
