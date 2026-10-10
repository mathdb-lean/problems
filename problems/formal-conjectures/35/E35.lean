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

- problem_id: E35
- collection: erdos
- question_id: erdos:35
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/35.lean#erdos_35
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $B\subseteq\mathbb{N}$ be an additive basis of order $k$ with $0\in B$. Is it true that for every $A\subseteq\mathbb{N}$ we have $$d_s(A+B)\geq \alpha+\frac{\alpha(1-\alpha)}{k},$$ where $\alpha=d_s(A)$ and $$d_s(A) = \inf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N}$$ is the Schnirelmann density? Erdős [Er36c] proved this is true with $k$ replaced by $2k$ in the denominator (in a stronger form that only considers $A\cup (A+b)$ for some $b\in B$, see [38](https://www.erdosproblems.com/38)). Ruzsa has observed that this follows immediately from the stronger fact proved by Plünnecke [Pl70] that (under the same assumptions, and for $\alpha>0$) $$d_S(A+B)\geq \alpha^{1-1/k}.$$
- notes: Erdos Problem 35 -- https://www.erdosproblems.com/35
- track: solved
- answer_shape: decide
- source_stem: 35
- mathdb_ref: erdos:35
- source_namespace: Erdos35
- source_theorem: erdos_35
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Set Pointwise

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (B : Set ℕ) (k : ℕ), 0 ∈ B → B.IsAddBasisOfOrder k →
        ∀ A : Set ℕ, schnirelmannDensity A +
          schnirelmannDensity A * (1 - schnirelmannDensity A) / k ≤ schnirelmannDensity (A + B)

end Problem
