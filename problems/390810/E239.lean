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

- problem_id: E239
- collection: erdos
- question_id: erdos:239
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/239.lean#erdos_239
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f:\mathbb{N}\to \{-1,1\}$ be a multiplicative function. Is it true that $$ \lim_{N\to \infty}\frac{1}{N}\sum_{n\leq N}f(n)$$ always exists? The answer is yes, as proved by Wirsing [Wi67], and generalised by Halász [Ha68].
- notes: Erdos Problem 239 -- https://www.erdosproblems.com/239
- track: solved
- answer_shape: decide
- source_stem: 239
- mathdb_ref: erdos:239
- source_namespace: Erdos239
- source_theorem: erdos_239
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter
open scoped Topology

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ f : ℕ → ℝ,
    (∀ n ≥ 1, f n = 1 ∨ f n = -1) ∧
    (∀ m n, m.Coprime n → f (m * n) = f m * f n) ∧
    f 1 = 1 →
    ∃ L, Tendsto (fun N ↦ (∑ n ∈ Finset.Icc 1 N, f n) / N) atTop (𝓝 L)

end Problem
