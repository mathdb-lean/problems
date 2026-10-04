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

- problem_id: E785
- collection: erdos
- question_id: erdos:785
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/785.lean#erdos_785
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A,B\subseteq \mathbb{N}$ be infinite sets of positive integers such that $A+B$ contains all large integers. Let $A(x)=\lvert A\cap [1,x]\rvert$ and similarly for $B(x)$. Is it true that if $A(x)B(x)\sim x$ then $$A(x)B(x)-x\to \infty$$ as $x\to \infty$? A conjecture of Erdős and Danzer. The answer is yes, proved by Sárközy and Szemerédi [SaSz94], who actually proved that it is impossible for $$A(x)B(x)-x=o(A(x)).$$ This was formalized in Lean by van Doorn using Aristotle.
- notes: Erdos Problem 785 -- https://www.erdosproblems.com/785
- track: solved
- answer_shape: decide
- source_stem: 785
- mathdb_ref: erdos:785
- source_namespace: Erdos785
- source_theorem: erdos_785
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Pointwise
open scoped Topology

namespace Problem

/-- The counting function $A(x)=\lvert A\cap [1,x]\rvert$. -/
noncomputable def counting (A : Set ℕ) (x : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 x).ncard

/-- The largest element of $A$ in $[1,x]$, that is $a^*(x)=\max A\cap [1,x]$
(equal to $0$ when there is no such element). -/
noncomputable def aStar (A : Set ℕ) (x : ℕ) : ℕ :=
  sSup (A ∩ Set.Icc 1 x)

/-- Two sets $A, B\subseteq \mathbb{N}$ are *exact additive complements* if $A+B$ contains all
large integers and $A(x)B(x)\sim x$. -/
def IsExactAdditiveComplement (A B : Set ℕ) : Prop :=
  IsAdditiveComplement A B ∧
    Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) / (x : ℝ)) atTop (𝓝 1)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ A B : Set ℕ, A.Infinite → B.Infinite → 0 ∉ A → 0 ∉ B → IsExactAdditiveComplement A B →
          Tendsto (fun x : ℕ => (counting A x * counting B x : ℝ) - (x : ℝ)) atTop atTop

end Problem
