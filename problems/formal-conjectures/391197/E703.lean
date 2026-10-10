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

- problem_id: E703
- collection: erdos
- question_id: erdos:703
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/703.lean#erdos_703
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $r\geq 1$ and define $T(n,r)$ to be maximal such that there exists a family $\mathcal{F}$ of subsets of $\{1,\ldots,n\}$ of size $T(n,r)$ such that $\lvert A\cap B\rvert\neq r$ for all $A,B\in \mathcal{F}$. Estimate $T(n,r)$ for $r\geq 2$. In particular, is it true that for every $\epsilon>0$ there exists $\delta>0$ such that for all $\epsilon n<r<(1/2-\epsilon) n$ we have $$T(n,r)<(2-\delta)^n?$$ The answer is yes, proved by Frankl and Rödl [FrRo87].
- notes: Erdos Problem 703 -- https://www.erdosproblems.com/703
- track: solved
- answer_shape: decide
- source_stem: 703
- mathdb_ref: erdos:703
- source_namespace: Erdos703
- source_theorem: erdos_703
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Finset

namespace Problem

/-- `T n r` is maximal such that there exists a family $\mathcal{F}$ of subsets of
$\{1,\ldots,n\}$ of size `T n r` such that $\lvert A\cap B\rvert\neq r$ for all
$A,B\in \mathcal{F}$ (including $A=B$). -/
noncomputable def T (n r : ℕ) : ℕ :=
  sSup {k | ∃ 𝓕 : Finset (Finset (Fin n)),
    (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, (A ∩ B).card ≠ r) ∧ 𝓕.card = k}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ (n r : ℕ), ε * n < r → r < (1 / 2 - ε) * n → (T n r : ℝ) < (2 - δ) ^ n

end Problem
