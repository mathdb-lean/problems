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

- problem_id: E337
- collection: erdos
- question_id: erdos:337
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/337.lean#erdos_337
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ be an additive basis (of any finite order) such that $\lvert A\cap \{1,\ldots,N\}\rvert=o(N)$. Is it true that $$ \lim_{N\to \infty}\frac{\lvert (A+A)\cap \{1,\ldots,N\}\rvert} {\lvert A\cap \{1,\ldots,N\}\rvert}=\infty? $$ The answer is no, and a counterexample was provided by Turjányi [Tu84]. This was generalised (to the replacement of $A+A$ by the $h$-fold sumset $hA$ for any $h\geq 2$) by Ruzsa and Turjányi [RT85]. "Additive basis" is `Set.IsAsymptoticAddBasis`: some finite $h$ has $hA$ containing every sufficiently large integer. The exact notion `Set.IsAddBasis`, which asks that $hA$ be all of $\mathbb{N}$, would force $0, 1 \in A$ and is not the class these results are about. The linked file states the basis hypothesis as `∃ N₀, Set.Ici N₀ ⊆ iterated_sumset A k` and indexes both counting functions by a real $x$ through $\lfloor x\rfloor$, where the counting functions here are indexed by $N : \mathbb{N}$.
- notes: Erdos Problem 337 -- https://www.erdosproblems.com/337
- track: solved
- answer_shape: decide
- source_stem: 337
- mathdb_ref: erdos:337
- source_namespace: Erdos337
- source_theorem: erdos_337
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Filter Set Asymptotics

open scoped Pointwise

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
          (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
          Tendsto (fun N : ℕ ↦ (((A + A) ∩ Icc 1 N).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
            atTop atTop

end Problem
