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

- problem_id: E290
- collection: erdos
- question_id: erdos:290
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/290.lean#erdos_290
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $a\geq 1$. Must there exist some $b>a$ such that $$\sum_{a\leq n\leq b}\frac{1}{n}=\frac{r_1}{s_1}\textrm{ and } \sum_{a\leq n\leq b+1}\frac{1}{n}=\frac{r_2}{s_2},$$ with $(r_i,s_i)=1$ and $s_2<s_1$? If so, how does this $b(a)$ grow with $a$? This was resolved in the affirmative by van Doorn [vD24], who proved $b=b(a)$ always exists, and in fact $b(a) \ll a$. Indeed, if $a\in (3^k,3^{k+1}]$ then one can take $b=2\cdot 3^{k+1}-1$. van Doorn also proves that $b(a)>a+(1/2-o(1))\log a$, and considers various generalisations of the original problem.
- notes: Erdos Problem 290 -- https://www.erdosproblems.com/290
- track: solved
- answer_shape: decide
- source_stem: 290
- mathdb_ref: erdos:290
- source_namespace: Erdos290
- source_theorem: erdos_290
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

/-- The denominator (in lowest terms) of the partial harmonic sum
$\sum_{a \leq n \leq b}\frac{1}{n}$. -/
noncomputable def harmonicDen (a b : ℕ) : ℕ := (harmonicBlock a b).den

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        (∀ a : ℕ, 1 ≤ a → ∃ b : ℕ, a < b ∧ harmonicDen a (b + 1) < harmonicDen a b)

end Problem
