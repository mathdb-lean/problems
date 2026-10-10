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

- problem_id: E1089
- collection: erdos
- question_id: erdos:1089
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1089.lean#erdos_1089
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$ determines at least $n$ many distinct distances. Estimate $g_d(n)$. In particular, does $$\lim_{d \to \infty} \frac{g_d(n)}{d^{n-1}}$$ exist? A problem of Erdős [Er75f, p.105]. The answer is yes: for $n \ge 2$, $$\binom{d+1}{n-1} + 1 \le g_d(n) \le \binom{d+n-1}{n-1} + 1,$$ where the upper bound is due to Bannai, Bannai and Stanton [BBS83] and the lower bound to a construction of Aletheia (generalising constructions for Problem 502), so that $g_d(n) / d^{n-1} \to 1/(n-1)!$ as $d \to \infty$.
- notes: Erdos Problem 1089 -- https://www.erdosproblems.com/1089
- track: solved
- answer_shape: decide
- source_stem: 1089
- mathdb_ref: erdos:1089
- source_namespace: Erdos1089
- source_theorem: erdos_1089
- source_category: research solved
- source_ams: 51 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter
open scoped Topology

namespace Problem

/-- `g d n` is the least `m` such that every `m` points in `ℝ^d` determine at least `n` distinct
distances, i.e. the least `m` with `n ≤ minimalDistinctDistances (EuclideanSpace ℝ (Fin d)) m`. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ minimalDistinctDistances (EuclideanSpace ℝ (Fin d)) m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ n : ℕ, 2 ≤ n → ∃ L : ℝ,
          Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop (𝓝 L)

end Problem
