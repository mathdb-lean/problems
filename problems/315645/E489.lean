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

- problem_id: E489
- collection: erdos
- question_id: erdos:489
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/489.lean#erdos_489
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A\subseteq \mathbb{N}$ be a set such that $\lvert A\cap [1,x]\rvert=o(x^{1/2})$. Let $B=\{ n\geq 1 : a\nmid n\textrm{ for all }a\in A\}$. If $B=\{b_1 < b_2 < \cdots\}$ then is it true that $$\lim_{x \to \infty} \frac{1}{x}\sum_{b_i < x}(b_{i+1}-b_i)^2$$ exists (and is finite)? For example, when $A=\{p^2: p\textrm{ prime}\}$ then $B$ is the set of squarefree numbers, and the existence of this limit was proved by Erdős. See also [208].
- notes: Erdos Problem 489 -- https://www.erdosproblems.com/489
- track: solved
- answer_shape: decide
- source_stem: 489
- mathdb_ref: erdos:489
- source_namespace: Erdos489
- source_theorem: erdos_489
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

namespace Problem

open Filter
open scoped Topology

/-- The set of positive integers not divisible by any element of `A`. -/
def sievedSet (A : Set ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∀ a ∈ A, ¬(a ∣ n)}

/-- The squared-gap sum `∑_{b_i < x} (b_{i+1} - b_i)²`, where `b_i` enumerates the positive
integers not divisible by any element of `A`. -/
noncomputable def GapSumSq (A : Set ℕ) (x : ℕ) : ℝ :=
  open scoped Classical in
  letI B := sievedSet A
  let b := Nat.nth (· ∈ B)
  ∑ i < Nat.count (· ∈ B) x, ((b (i + 1) : ℝ) - b i) ^ 2

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (A : Set ℕ),
          (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ)) =o[atTop]
            (fun x : ℕ => (x : ℝ).sqrt) →
          (sievedSet A).Infinite →
          ∃ L : ℝ, Tendsto (fun x : ℕ => GapSumSq A x / (x : ℝ)) atTop (𝓝 L)

end Problem
