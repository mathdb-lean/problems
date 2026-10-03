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

- problem_id: E796
- collection: erdos
- question_id: erdos:796
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/796.lean#erdos_796
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $k\geq 2$ and let $g_k(n)$ be the largest possible size of $A\subseteq \{1,\ldots,n\}$ such that every $m$ has $<k$ solutions to $m=a_1a_2$ with $a_1<a_2\in A$. Is it true that $$g_3(n)=\frac{\log\log n}{\log n}n+(c+o(1))\frac{n}{\log n}$$ for some constant $c$? The answer is yes: the rescaled error `normalizedError` converges.
- notes: Erdos Problem 796 -- https://www.erdosproblems.com/796
- track: solved
- answer_shape: decide
- source_stem: 796
- mathdb_ref: erdos:796
- source_namespace: Erdos796
- source_theorem: erdos_796
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

/-- The number of unordered representations `m = a₁ * a₂` by two distinct
elements `a₁ < a₂` of `A`. -/
def repCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  ((A ×ˢ A).filter fun a => a.1 < a.2 ∧ a.1 * a.2 = m).card

/-- `A` has at most `k - 1` representations of every `m` (fewer than `k`). -/
def HasRepBound (k : ℕ) (A : Finset ℕ) : Prop := ∀ m : ℕ, repCount A m < k

open scoped Classical in
/-- `g k n = g_k(n)` is the largest size of a subset `A ⊆ {1, …, n}` in which
every `m` has fewer than `k` representations `m = a₁ a₂` with `a₁ < a₂ ∈ A`. -/
noncomputable def g (k n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (HasRepBound k)).sup Finset.card

/-- The proposed second-order rescaling of `g_3(n)`:
`(g_3(n) - (log log n / log n) · n) / (n / log n)`, whose limit is the constant
`c` in the problem. -/
noncomputable def normalizedError (n : ℕ) : ℝ :=
  ((g 3 n : ℝ) - (n : ℝ) * Real.log (Real.log n) / Real.log n) / ((n : ℝ) / Real.log n)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ c : ℝ, Tendsto normalizedError atTop (𝓝 c)

end Problem
