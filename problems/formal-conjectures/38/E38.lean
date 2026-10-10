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

- problem_id: E38
- collection: erdos
- question_id: erdos:38
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/38.lean#erdos_38
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Does there exist $B \subset \mathbb{N}$ which is not an additive basis, but is such that for every set $A \subseteq \mathbb{N}$ of Schnirelmann density $\alpha$ and every $N$ there exists $b \in B$ such that $$ \lvert (A \cup (A+b)) \cap \{1, \ldots, N\} \rvert \geq (\alpha + f(\alpha)) N $$ where $f(\alpha) > 0$ for $0 < \alpha < 1$? Note: here Erdős seems to use a slightly weaker notion of an additive basis (see [Er56] at the top of page 135). In particular, for this problem, a set is an additive basis of order $k$ if every natural number can be written as a sum of _at most_ $k$ elements of the set, rather than as a sum of _precisely_ $k$ elements. A positive [solution](https://github.com/spicylemonade/erdos-38) was given by GPT 5.5 Pro (prompted by gebyjaff, cleanup by Liam Price); in fact a sparse random set $B$ has this property, with $f(\alpha)\gg \alpha (1-\alpha)^2$.
- notes: Erdos Problem 38 -- https://www.erdosproblems.com/38
- track: solved
- answer_shape: decide
- source_stem: 38
- mathdb_ref: erdos:38
- source_namespace: Erdos38
- source_theorem: erdos_38
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set Pointwise

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ B : Set ℕ, ¬ B.IsWeakAddBasis ∧ ∃ f : ℝ → ℝ, (∀ α, 0 < α → α < 1 → f α > 0) ∧
          ∀ (A : Set ℕ) (N : ℕ),
            let α := schnirelmannDensity A
            ∃ b ∈ B, (Ioc 0 N ∩ (A ∪ (A + {b}))).ncard ≥ (α + f α) * N

end Problem
