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

- problem_id: E331
- collection: erdos
- question_id: erdos:331
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/331.lean#erdos_331
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A,B\subseteq \mathbb{N}$ such that for all large $N$$$\lvert A\cap \{1,\ldots,N\}\rvert \gg N^{1/2}$$and$$\lvert B\cap \{1,\ldots,N\}\rvert \gg N^{1/2}.$$ Is it true that there are infinitely many solutions to $a_1-a_2=b_1-b_2\neq 0$ with $a_1,a_2\in A$ and $b_1,b_2\in B$? Ruzsa has observed that there is a simple counterexample: take $A$ to be the set of numbers whose binary representation has only non-zero digits in even places, and $B$ similarly but with non-zero digits only in odd places. It is easy to see $A$ and $B$ both grow like $\gg N^{1/2}$ and yet for any $n\geq 1$ there is exactly one solution to $n=a+b$ with $a\in A$ and $b\in B$. This was formalized in Lean by van Doorn using Aristotle.
- notes: Erdos Problem 331 -- https://www.erdosproblems.com/331
- track: solved
- answer_shape: decide
- source_stem: 331
- mathdb_ref: erdos:331
- source_namespace: Erdos331
- source_theorem: erdos_331
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat Filter
open scoped Asymptotics

namespace Problem

open scoped Classical in
abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∀ A B : Set ℕ,
      (fun (n : ℕ) ↦ (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop] (fun (n : ℕ) ↦ (count (· ∈ A) n : ℝ)) →
      (fun (n : ℕ) ↦ (n : ℝ) ^ (1 / 2 : ℝ)) =O[atTop] (fun (n : ℕ) ↦ (count (· ∈ B) n : ℝ)) →
      { s : ℕ × ℕ × ℕ × ℕ | let ⟨a₁, a₂, b₁, b₂⟩ := s
        a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
        a₁ ≠ a₂ ∧ a₁ + b₂ = a₂ + b₁ }.Infinite

end Problem
