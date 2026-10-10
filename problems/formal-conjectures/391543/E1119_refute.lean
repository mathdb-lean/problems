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

- problem_id: E1119_refute
- collection: erdos
- question_id: erdos:1119
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1119.lean#erdos_1119
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\mathfrak{m}$ be an infinite cardinal with $\aleph_0 < \mathfrak{m} < \mathfrak{c} = 2^{\aleph_0}$. Let $\{f_\alpha\}$ be a family of entire functions such that, for every $z_0 \in \mathbb{C}$, there are at most $\mathfrak{m}$ distinct values of $f_\alpha(z_0)$. Must $\{f_\alpha\}$ have cardinality at most $\mathfrak{m}$? This is Problem 2.46 in [Ha74], where it is attributed to Erdős. The question is **independent of ZFC**, so the headline statement carries `answer(sorry)`: it is neither provable nor refutable from the usual axioms of set theory. The answer is yes if $\mathfrak{m}^+ < \mathfrak{c}$ (see `erdos_1119.variants.easy_case`), so the question reduces to the case $\mathfrak{m}^+ = \mathfrak{c}$, where it is undecidable: Kumar and Shelah [KuSh17] produced a model of $\mathfrak{c} = \aleph_2$ in which the answer is yes (with $\mathfrak{m} = \aleph_1$), while Schilhan and Weinert [ScWe24] produced a different model of $\mathfrak{c} = \aleph_2$ in which the answer is no.
- notes: Erdos Problem 1119 -- https://www.erdosproblems.com/1119
- track: solved
- answer_shape: refute
- pair_id: E1119
- pair_role: refute
- source_stem: 1119
- mathdb_ref: erdos:1119
- source_namespace: Erdos1119
- source_theorem: erdos_1119
- source_category: research solved
- source_ams: 3 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Cardinal Order
open scoped Cardinal

namespace Problem

set_option linter.style.category_answer false in
abbrev Target : Prop :=
    ¬ (
      ∀ (m : Cardinal.{0}), ℵ₀ < m → m < 𝔠 →
          ∀ F : Set (ℂ → ℂ), (∀ f ∈ F, Differentiable ℂ f) →
            (∀ z₀ : ℂ, #{y : ℂ | ∃ f ∈ F, f z₀ = y} ≤ m) →
            #F ≤ m
    )

end Problem
