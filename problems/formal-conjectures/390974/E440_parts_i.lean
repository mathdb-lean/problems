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

- problem_id: E440_parts_i
- collection: erdos
- question_id: erdos:440
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/440.lean#erdos_440.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A=\{a_1<a_2<\cdots\}\subseteq \mathbb{N}$ be infinite and let $A(x)$ count the number of indices for which $\mathrm{lcm}(a_i,a_{i+1})\leq x$. Is it true that $A(x) \ll x^{1/2}$? The answer is yes: Tao has given a simple proof, and Erdős and Szemerédi [ErSz80] proved the sharp bound $A(x)\leq (c+o(1))x^{1/2}$ (see `erdos_440.variants.erdos_szemeredi`).
- notes: Erdos Problem 440 -- https://www.erdosproblems.com/440
- track: solved
- answer_shape: decide
- source_stem: 440
- mathdb_ref: erdos:440
- source_namespace: Erdos440
- source_theorem: erdos_440.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real

namespace Problem

/-- For a strictly increasing sequence `a` of positive integers, `count a x` is the number of
indices `i` with `lcm(aᵢ, aᵢ₊₁) ≤ x`. -/
noncomputable def count (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  {i | Nat.lcm (a i) (a (i + 1)) ≤ x}.ncard

/-- The Erdős–Szemerédi constant $c=\sum_{n\geq 1}\frac{1}{n^{1/2}(n+1)}\approx 1.86$
(summed here over $n = m + 1$, $m \geq 0$). -/
noncomputable def erdosSzemerediConstant : ℝ := ∑' m : ℕ, 1 / (√(m + 1 : ℝ) * (m + 2))

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ a : ℕ → ℕ, StrictMono a → (∀ i, 0 < a i) →
          (fun x : ℕ ↦ (count a x : ℝ)) =O[atTop] fun x : ℕ ↦ √x

end Problem
