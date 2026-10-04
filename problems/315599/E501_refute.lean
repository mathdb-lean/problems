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

- problem_id: E501_refute
- collection: erdos
- question_id: erdos:501
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/501.lean#erdos_501
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For every $x \in \mathbb{R}$ let $A_x \subset \mathbb{R}$ be a bounded set with outer measure $< 1$. Must there exist an infinite independent set, that is, some infinite $X \subseteq \mathbb{R}$ such that $x \notin A_y$ for all $x \neq y \in X$? If the sets $A_x$ are closed and have measure $< 1$, then must there exist an independent set of size $3$? Known results: Erdős–Hajnal [ErHa60] proved the existence of arbitrarily large finite independent sets. Hechler [He72] showed the answer is **no** assuming the continuum hypothesis.
- notes: Erdos Problem 501 -- https://www.erdosproblems.com/501
- track: open
- answer_shape: refute
- pair_id: E501
- pair_role: refute
- source_stem: 501
- mathdb_ref: erdos:501
- source_namespace: Erdos501
- source_theorem: erdos_501
- source_category: research open
- source_ams: 5 28
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Set MeasureTheory
open scoped Cardinal ENNReal

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ (A : ℝ → Set ℝ),
            (∀ x, Bornology.IsBounded (A x)) →
            (∀ x, volume.toOuterMeasure (A x) < 1) →
            ∃ X : Set ℝ, X.Infinite ∧ X.Pairwise (fun x y => x ∉ A y)
    )

end Problem
