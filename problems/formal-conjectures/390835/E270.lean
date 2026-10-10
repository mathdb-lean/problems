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

- problem_id: E270
- collection: erdos
- question_id: erdos:270
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/270.lean#erdos_270
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)\to \infty$ as $n\to \infty$. Is it true that $$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$$ is irrational? Erdős and Graham [ErGr80] write 'the answer is almost surely in the affirmative if $f(n)$ is assumed to be nondecreasing'. Even the case $f(n)=n$ is unknown, although Hansen [Ha75] has shown that $$\sum_n \frac{1}{\binom{2n}{n}}=\sum_n \frac{n!}{(n+1)\cdots (n+n)}=\frac{1}{3}+\frac{2\pi}{3^{5/2}}$$ is transcendental. Crmarić and Kovač [CrKo25] have shown that the answer to this question is no in a strong sense: for any $\alpha \in (0,\infty)$ there exists a function $f:\mathbb{N}\to\mathbb{N}$ such that $f(n)\to \infty$ as $n\to\infty$ and $$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}=\alpha.$$
- notes: Erdos Problem 270 -- https://www.erdosproblems.com/270
- track: solved
- answer_shape: decide
- source_stem: 270
- mathdb_ref: erdos:270
- source_namespace: Erdos270
- source_theorem: erdos_270
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/-- The series $\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}$, indexed from $0$. -/
noncomputable def series (f : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ f : ℕ → ℕ, Tendsto f atTop atTop → Irrational (series f)

end Problem
