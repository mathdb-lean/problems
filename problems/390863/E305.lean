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

- problem_id: E305
- collection: erdos
- question_id: erdos:305
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/305.lean#erdos_305
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For integers $1\leq a<b$ let $D(a,b)$ be the minimal value of $n_k$ such that there exist integers $1\leq n_1<\cdots <n_k$ with $$\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}.$$ Estimate $D(b)=\max_{1\leq a<b}D(a,b)$. Is it true that $$D(b) \ll b(\log b)^{1+o(1)}?$$ Bleicher and Erdős [BlEr76] have shown that $D(b)\ll b(\log b)^2$. If $b=p$ is a prime then $D(p) \gg p\log p$. This was solved by Yokota [Yo88], who proved that $$D(b)\ll b(\log b)(\log\log b)^4(\log\log\log b)^2.$$ This was improved by Liu and Sawhney [LiSa24] to $$D(b)\ll b(\log b)(\log\log b)^3(\log\log\log b)^{O(1)}.$$
- notes: Erdos Problem 305 -- https://www.erdosproblems.com/305
- track: solved
- answer_shape: decide
- source_stem: 305
- mathdb_ref: erdos:305
- source_namespace: Erdos305
- source_theorem: erdos_305
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real

namespace Problem

/--
`D a b` is the minimal value of $n_k$ such that there exist integers $1\leq n_1<\cdots <n_k$ with
$\frac{a}{b}=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$.
-/
noncomputable def D (a b : ℕ) : ℕ :=
  sInf {B | ∃ E : Finset ℕ, 0 ∉ E ∧ (∀ n ∈ E, n ≤ B) ∧
    ∑ n ∈ E, (1 : ℚ) / n = a / b}

/-- $D(b)=\max_{1\leq a<b}D(a,b)$. -/
noncomputable def Dmax (b : ℕ) : ℕ := (Finset.Ico 1 b).sup fun a ↦ D a b

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ b : ℕ in atTop,
          (Dmax b : ℝ) ≤ C * b * (log b) ^ (1 + δ b)

end Problem
