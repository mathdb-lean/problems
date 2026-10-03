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

- problem_id: E145_refute
- collection: erdos
- question_id: erdos:145
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/145.lean#erdos_145
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. Is it true that, for any $\alpha\geq 0$, $$ \lim_{x\to\infty} \frac{1}{x}\sum_{s_n\leq x}(s_{n+1}-s_n)^\alpha $$ exists?
- notes: Erdos Problem 145 -- https://www.erdosproblems.com/145
- track: open
- answer_shape: refute
- pair_id: E145
- pair_role: refute
- source_stem: 145
- mathdb_ref: erdos:145
- source_namespace: Erdos145
- source_theorem: erdos_145
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter
open scoped Topology

/-- Let $s_1 < s_2 < \cdots$ be the sequence of squarefree numbers. -/
noncomputable abbrev s (n : ℕ) : ℕ := Nat.nth Squarefree n

/-- Let $A(x)$ denote the set of indices $n$ for which $s_n \leq x$. -/
noncomputable abbrev A (x : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊x⌋₊).preimage s (Nat.nth_injective Nat.squarefree_infinite).injOn

abbrev Target : Prop :=
    ¬ (
      ∀ α ≥ (0 : ℝ), ∃ β : ℝ,
        atTop.Tendsto (fun x : ℝ ↦ 1 / x * ∑ n ∈ A x, (s (n + 1) - s n : ℝ) ^ α) (𝓝 β)
    )

end Problem
