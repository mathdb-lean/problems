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

- problem_id: E655
- collection: erdos
- question_id: erdos:655
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/655.lean#erdos_655
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x_1,\ldots,x_n\in \mathbb{R}^2$ be such that no circle whose centre is one of the $x_i$ contains three other points. Are there at least $$(1+c)\frac{n}{2}$$ distinct distances determined between the $x_i$, for some constant $c>0$ and all $n$ sufficiently large? The answer is **no**: as Zach Hunter observed, the regular `n`-gon (`n` points equally spaced on a circle) is valid and determines only `⌊n/2⌋ < (1+c)n/2` distinct distances, for every `c > 0`. (In the spirit of related conjectures of Erdős and others, presumably some kind of assumption that the points are in general position was intended; see `erdos_655.variants.general_position`.) The disproof — the regular `n`-gon construction together with its supporting lemmas — is formalised at the linked commit.
- notes: Erdos Problem 655 -- https://www.erdosproblems.com/655
- track: solved
- answer_shape: decide
- source_stem: 655
- mathdb_ref: erdos:655
- source_namespace: Erdos655
- source_theorem: erdos_655
- source_category: research solved
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter Finset EuclideanGeometry

namespace Problem

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is _valid_ if
no circle whose centre is one of the $x_i$ contains three other points. -/
def IsValid (X : Finset ℝ²) : Prop :=
  ∀ᵉ (x ∈ X) (r > 0), ¬3 ≤ (Metric.sphere x r ∩ X).ncard

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c > (0 : ℝ), ∀ᶠ n in atTop, ∀ (X : Finset ℝ²), #X = n → IsValid X →
      (1 + c) * n / 2 ≤ distinctDistances X

end Problem
