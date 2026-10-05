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

- problem_id: E314
- collection: erdos
- question_id: erdos:314
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/314.lean#erdos_314
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n\geq 1$ and let $m$ be minimal such that $\sum_{n\leq k\leq m}\frac{1}{k}\geq 1$. We define $$\epsilon(n) = \sum_{n\leq k\leq m}\frac{1}{k}-1.$$ How small can $\epsilon(n)$ be? Is it true that $$\liminf n^2\epsilon(n)=0?$$ This is true, and shown by Lim and Steinerberger [LiSt24], who further proved that, for any $\delta>0$, there exist infinitely many $n$ and $m$ such that $$n^2\left\lvert \sum_{n\leq k\leq m}\frac{1}{k}-1\right\rvert\ll \frac{1}{(\log n)^{5/4-\delta}}.$$ Erdős and Graham (and also Lim and Steinerberger) believe that the exponent of $2$ is best possible here, in that $\liminf \epsilon(n) n^{2+\delta}=\infty$ for all $\delta>0$.
- notes: Erdos Problem 314 -- https://www.erdosproblems.com/314
- track: solved
- answer_shape: decide
- source_stem: 314
- mathdb_ref: erdos:314
- source_namespace: Erdos314
- source_theorem: erdos_314
- source_category: research solved
- source_ams: 11 40
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/-- `mMin n` is the minimal `m` such that $\sum_{n\leq k\leq m}\frac{1}{k}\geq 1$; such an `m`
exists for `n ≥ 1` since the harmonic series diverges. -/
noncomputable def mMin (n : ℕ) : ℕ := sInf {m | 1 ≤ harmonicBlock n m}

/-- $\epsilon(n) = \sum_{n\leq k\leq m}\frac{1}{k}-1$, the overshoot of the minimal block sum
reaching $1$. -/
noncomputable def epsilon (n : ℕ) : ℝ := (harmonicBlock n (mMin n) : ℝ) - 1

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        atTop.liminf (fun n : ℕ => (n : ℝ) ^ 2 * epsilon n) = 0

end Problem
