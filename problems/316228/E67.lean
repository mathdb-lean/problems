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

- problem_id: E67
- collection: erdos
- question_id: erdos:67
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/67.lean#erdos_67
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **The Erdős discrepancy problem** If $f\colon \mathbb N \rightarrow \{-1, +1\}$ then is it true that for every $C>0$ there exist $d, m \ge 1$ such that $$\left\lvert \sum_{1\leq k\leq m}f(kd)\right\rvert > C?$$ This is true, and was proved by Tao [Ta16]
- notes: Erdos Problem 67 -- https://www.erdosproblems.com/67
- track: solved
- answer_shape: proof
- source_stem: 67
- mathdb_ref: erdos:67
- source_namespace: Erdos67
- source_theorem: erdos_67
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

abbrev Target : Prop :=
    ∀ (f : ℕ → ({-1, 1} : Finset ℝ)) (C : ℝ) (hC : 0 < C),
      ∃ᵉ (d ≥ 1) (m ≥ 1),
          C < |∑ k ∈ Finset.Icc 1 m, (f (k * d)).1|

end Problem
