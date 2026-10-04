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

- problem_id: E1028
- collection: erdos
- question_id: erdos:1028
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1028.lean#erdos_1028
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $$H(n)=\min_f \max_{X\subseteq \{1,\ldots,n\}} \left\lvert \sum_{x<y\in X} f(x,y)\right\rvert,$$ where $f$ ranges over all functions $f:\{1,\ldots,n\}^2\to \{-1,1\}$. Estimate $H(n)$. Erdős [Er63d] proved $$\frac{n}{4}\leq H(n) \ll n^{3/2}.$$ Erdős and Spencer [ErSp71] proved that $H(n)\gg n^{3/2}$.
- notes: Erdos Problem 1028 -- https://www.erdosproblems.com/1028
- track: solved
- answer_shape: proof
- source_stem: 1028
- mathdb_ref: erdos:1028
- source_namespace: Erdos1028
- source_theorem: erdos_1028
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics

namespace Problem

/-- The imbalance of a finite set `X` under a colouring `f`, that is,
$\left\lvert \sum_{x<y\in X} f(x,y)\right\rvert$. -/
def imbalance (f : ℕ → ℕ → ℤ) (X : Finset ℕ) : ℤ :=
  |∑ x ∈ X, ∑ y ∈ X.filter (fun y => x < y), f x y|

/-- `H n` is the minimum, over all colourings `f` of pairs from `{1, …, n}` with values in
`{-1, 1}`, of the largest imbalance of a subset `X ⊆ {1, …, n}`. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf {m | ∃ f : ℕ → ℕ → ℤ, (∀ x y, f x y = 1 ∨ f x y = -1) ∧
    ∀ X ⊆ Finset.Icc 1 n, imbalance f X ≤ (m : ℤ)}

abbrev Target : Prop :=
    (fun n => (H n : ℝ)) =Θ[atTop]
      fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)

end Problem
