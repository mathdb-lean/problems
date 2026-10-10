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

- problem_id: E308_parts_i
- collection: erdos
- question_id: erdos:308
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/308.lean#erdos_308.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $N\geq 1$. What is the smallest integer not representable as the sum of distinct unit fractions with denominators from $\{1,\ldots,N\}$? This was essentially solved by Croot [Cr99] (see `erdos_308.variants.croot`); in particular, for all sufficiently large $N$, the smallest such integer is either $m_N$ or $m_N+1$, where $m_N=\lfloor \sum_{n\leq N}\frac{1}{n}\rfloor$.
- notes: Erdos Problem 308 -- https://www.erdosproblems.com/308
- track: solved
- answer_shape: proof
- source_stem: 308
- mathdb_ref: erdos:308
- source_namespace: Erdos308
- source_theorem: erdos_308.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

/-- `k` is representable as a sum of distinct unit fractions with denominators from
`{1, …, N}`. -/
def IsRepresentable (N k : ℕ) : Prop :=
  ∃ A ⊆ Finset.Icc 1 N, ∑ n ∈ A, (1 : ℚ) / n = k

/-- The set of positive integers representable as a sum of distinct unit fractions with
denominators from `{1, …, N}`. -/
def representable (N : ℕ) : Set ℕ := {k | 0 < k ∧ IsRepresentable N k}

/-- `f N` is the smallest positive integer which is not representable as a sum of distinct unit
fractions with denominators from `{1, …, N}`. -/
noncomputable def f (N : ℕ) : ℕ := sInf {k | 0 < k ∧ ¬ IsRepresentable N k}

/-- `m N = ⌊∑_{n ≤ N} 1/n⌋`. -/
def m (N : ℕ) : ℕ := ⌊harmonic N⌋₊

abbrev Target : Prop :=
    ∀ᶠ N : ℕ in atTop, f N = m N ∨ f N = m N + 1

end Problem
