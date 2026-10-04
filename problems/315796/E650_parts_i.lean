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

- problem_id: E650_parts_i
- collection: erdos
- question_id: erdos:650
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/650.lean#erdos_650.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(m)$ be such that if $A\subseteq \{1,\ldots,N\}$ has $\lvert A\rvert=m$ then every interval in $[1,\infty)$ of length $2N$ contains $\geq f(m)$ many distinct integers $b_1,\ldots,b_r$ where each $b_i$ is divisible by some $a_i\in A$, where $a_1,\ldots,a_r$ are distinct. Estimate $f(m)$. GPT 5.4 Pro (prompted by He, Li, and Tang) proved $f(m)\leq \lceil 2\sqrt{m}\rceil$. A corresponding lower bound was given by GPT 5.4 Pro and Aristotle; it is now known (see the paper of van Doorn, Li, and Tang [VLT26]) that $$f(m) = \min(m, \lceil 2\sqrt{m}\rceil)$$ for all $m$. This was formalized in Lean by van Doorn using Aristotle.
- notes: Erdos Problem 650 -- https://www.erdosproblems.com/650
- track: solved
- answer_shape: proof
- source_stem: 650
- mathdb_ref: erdos:650
- source_namespace: Erdos650
- source_theorem: erdos_650.parts.i
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
`f m` is the largest `r` such that whenever `A ⊆ {1, …, N}` has `m` elements, every interval
in `[1, ∞)` of length `2 * N` contains `r` distinct integers `b 0, …, b (r - 1)`, each `b i`
being divisible by some `a i ∈ A`, where `a 0, …, a (r - 1)` are distinct. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {r : ℕ | ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, A.card = m → ∀ x : ℝ, 1 ≤ x →
    ∃ a b : Fin r → ℕ, (Function.Injective a) ∧ (Function.Injective b) ∧
      (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧ (∀ i, a i ∣ b i)}

abbrev Target : Prop :=
    ∀ (m : ℕ),
      f m = min m ⌈2 * Real.sqrt m⌉₊

end Problem
