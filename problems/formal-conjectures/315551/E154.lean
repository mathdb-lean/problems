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

- problem_id: E154
- collection: erdos
- question_id: erdos:154
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/154.lean#erdos_154
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subset \{1,\ldots,N\}$ be a Sidon set with $\lvert A\rvert\sim N^{1/2}$. Must $A+A$ be well-distributed over all small moduli? In particular, must about half the elements of $A+A$ be even and half odd? The answer is yes. Lindström [Li98] proved the analogous statement for $A$ itself (see `erdos_154.variants.lindstrom`), later strengthened by Kolountzakis [Ko99]; well-distribution of $A+A$ then follows using the Sidon property. We state the question for the sumset: for any sequence of Sidon sets $A_k\subseteq\{0,\ldots,N_k\}$ with $N_k\to\infty$ and $\lvert A_k\rvert\sim N_k^{1/2}$, and any modulus $m\geq 2$, the proportion of elements of $A_k+A_k$ congruent to $i\pmod m$ (i.e. the count divided by $\lvert A_k+A_k\rvert$) tends to $1/m$ for every residue $i<m$.
- notes: Erdos Problem 154 -- https://www.erdosproblems.com/154
- track: solved
- answer_shape: decide
- source_stem: 154
- mathdb_ref: erdos:154
- source_namespace: Erdos154
- source_theorem: erdos_154
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Finset

open scoped Pointwise

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (m : ℕ) (hm : 2 ≤ m) (N : ℕ → ℕ) (A : ℕ → Finset ℕ),
          Tendsto (fun k => (N k : ℝ)) atTop atTop →
          (∀ k, ∀ x ∈ A k, x ≤ N k) →
          (∀ k, IsSidon (A k : Set ℕ)) →
          Tendsto (fun k => ((A k).card : ℝ) / Real.sqrt (N k)) atTop (nhds 1) →
          ∀ i < m, Tendsto
            (fun k => (((A k + A k).filter (fun s => s % m = i)).card : ℝ) / ((A k + A k).card : ℝ))
            atTop (nhds (1 / m))

end Problem
