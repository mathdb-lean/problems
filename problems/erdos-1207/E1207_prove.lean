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

- problem_id: E1207_prove
- collection: erdos
- question_id: erdos:1207
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1207.lean#erdos_1207
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $P_d(n)$ be such that in any set of $n$ points in $\mathbb{R}^d$ there exist at least $P_d(n)$ many points which do not contain an isosceles triangle. Estimate $P_d(n)$ - in particular, is it true that $$P_2(n)<n^{1-c}$$ for some constant $c>0$?
- notes: Erdos Problem 1207 -- https://www.erdosproblems.com/1207
- track: open
- answer_shape: prove
- pair_id: E1207
- pair_role: prove
- source_stem: 1207
- mathdb_ref: erdos:1207
- source_namespace: Erdos1207
- source_theorem: erdos_1207
- source_category: research open
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped EuclideanGeometry

namespace Problem

/--
`P d n` is the largest number $m$ such that every set of $n$ points in $\mathbb{R}^d$ has an
isosceles-free subset of size at least $m$.
-/
noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (ℝ^d), S.card = n ∧
    m = sSup {k : ℕ | ∃ A ⊆ S, (A : Set (ℝ^d)).IsIsoscelesFree ∧ A.card = k}}

abbrev Target : Prop :=
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c)

end Problem
