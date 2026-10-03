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

- problem_id: E72
- collection: erdos
- question_id: erdos:72
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/72.lean#erdos_72
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is there a set $A\subset \mathbb{N}$ of density $0$ and a constant $c>0$ such that every graph on sufficiently many vertices with average degree $\geq c$ contains a cycle whose length is in $A$? Bollobás [Bo77] proved that such a $c$ does exist if $A$ is an infinite arithmetic progression containing even numbers (see [71](https://www.erdosproblems.com/71)). Erdős was 'almost certain' that if $A$ is the set of powers of $2$ then no such $c$ exists (although he conjectured that $n$ vertices and average degree $\gg (\log n)^{C}$ suffices for some $C=O(1)$). If $A$ is the set of squares (or the set of $p\pm 1$ for $p$ prime) then he had no guess. Solved by Verstraëte [Ve05], who gave a non-constructive proof that such a set $A$ exists. Liu and Montgomery [LiMo20] proved that in fact this is true when $A$ is the set of powers of $2$ (more generally any set of even numbers which doesn't grow too quickly) - in particular this contradicts the previous belief of Erdős.
- notes: Erdos Problem 72 -- https://www.erdosproblems.com/72
- track: solved
- answer_shape: decide
- source_stem: 72
- mathdb_ref: erdos:72
- source_namespace: Erdos72
- source_theorem: erdos_72
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter SimpleGraph

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ A : Set ℕ, A.HasDensity 0 ∧ ∃ c : ℚ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), c ≤ G.averageDegree →
          ∃ (v : Fin n) (w : G.Walk v v), w.IsCycle ∧ w.length ∈ A

end Problem
