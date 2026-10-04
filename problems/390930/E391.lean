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

- problem_id: E391
- collection: erdos
- question_id: erdos:391
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/391.lean#erdos_391
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $t(n)$ be maximal such that there is a representation $$n!=a_1\cdots a_n$$ with $t(n)=a_1\leq \cdots \leq a_n$. Obtain good bounds for $t(n)/n$. In particular, is it true that $$\lim \frac{t(n)}{n}=\frac{1}{e}?$$ It is easy to see that $\lim \frac{t(n)}{n}\leq \frac{1}{e}$. Erdős [Er96b] wrote he, Selfridge, and Straus had proved a corresponding lower bound, so that $\lim \frac{t(n)}{n}=\frac{1}{e}$, and 'believed that Straus had written up our proof. Unfortunately Straus suddenly died and no trace was ever found of his notes. Furthermore, we never could reconstruct our proof, so our assertion now can be called only a conjecture.' Alladi and Grinstead [AlGr77] have obtained similar results when the $a_i$ are restricted to prime powers. Both questions were answered by Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr, and Ventullo [ACRSTUV25], who proved that $$\frac{t(n)}{n}= \frac{1}{e}-\frac{c_0}{\log n}+O\left(\frac{1}{(\log n)^{1+c}}\right),$$ where $c_0=0.3044\cdots$ is an explicit constant, for some $c>0$.
- notes: Erdos Problem 391 -- https://www.erdosproblems.com/391
- track: solved
- answer_shape: decide
- source_stem: 391
- mathdb_ref: erdos:391
- source_namespace: Erdos391
- source_theorem: erdos_391
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Topology

namespace Problem

/-- `t n` is the largest `t` such that `n!` is a product of `n` factors all at least `t`,
i.e. the maximal $a_1$ in a representation $n! = a_1 \cdots a_n$ with $a_1 \leq \cdots \leq a_n$. -/
noncomputable def t (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin n → ℕ, ∏ i, a i = n.factorial ∧ ∀ i, k ≤ a i}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        Tendsto (fun n : ℕ => (t n : ℝ) / n) atTop (𝓝 (1 / Real.exp 1))

end Problem
