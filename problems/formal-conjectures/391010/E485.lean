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

- problem_id: E485
- collection: erdos
- question_id: erdos:485
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/485.lean#erdos_485
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(k)$ be the minimum number of terms in $P(x)^2$, where $P \in \mathbb{Q}[x]$ ranges over all polynomials with exactly $k$ non-zero terms. Is it true that $f(k) \to \infty$ as $k \to \infty$? A conjecture of Erdős and Rényi (this is Problem 4.4 in [Ha74], attributed to Erdős); the function was first investigated by Rényi and Rédei [Re47], and Erdős [Er49b] proved that $f(k) < k^{1-c}$ for some $c > 0$. The answer is yes: Schinzel [Sc87] proved $f(k) > \log \log k / \log 2$, and Schinzel and Zannier [ScZa09] improved this to $f(k) \gg \log k$.
- notes: Erdos Problem 485 -- https://www.erdosproblems.com/485
- track: solved
- answer_shape: decide
- source_stem: 485
- mathdb_ref: erdos:485
- source_namespace: Erdos485
- source_theorem: erdos_485
- source_category: research solved
- source_ams: 11 12
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Polynomial

namespace Problem

/-- The minimum number of terms of the square of a rational polynomial with exactly `k` nonzero
terms, where the number of terms of `P` is `P.support.card`. -/
noncomputable def f (k : ℕ) : ℕ :=
  sInf {m | ∃ P : ℚ[X], P.support.card = k ∧ (P ^ 2).support.card = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Tendsto f atTop atTop

end Problem
