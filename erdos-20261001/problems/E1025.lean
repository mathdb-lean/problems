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

- problem_id: E1025
- collection: erdos
- question_id: erdos:1025
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1025.lean#erdos_1025
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f$ be a function from all pairs of elements in $\{1,\ldots,n\}$ to $\{1,\ldots,n\}$ such that $f(x,y)\neq x$ and $\neq y$ for all $x,y$. We call $X\subseteq \{1,\ldots,n\}$ independent if whenever $x,y\in X$ we have $f(x,y)\not\in X$. Let $g(n)$ be such that, in every function $f$, there is an independent set of size at least $g(n)$. Estimate $g(n)$. A question of Erdős and Hajnal [ErHa58], who could prove $n^{1/3} \ll g(n) \ll (n\log n)^{1/2}$. Spencer [Sp72] proved $g(n)\gg n^{1/2}$. Conlon, Fox, and Sudakov [CFS16] proved $g(n)\ll n^{1/2}$.
- notes: Erdos Problem 1025 -- https://www.erdosproblems.com/1025
- track: solved
- answer_shape: proof
- source_stem: 1025
- mathdb_ref: erdos:1025
- source_namespace: Erdos1025
- source_theorem: erdos_1025
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics

namespace Problem

/-- `X` is independent for a set mapping `f` on pairs if `f s(x, y) ∉ X` whenever `x ≠ y` are in
`X`. -/
def IsIndependent {n : ℕ} (f : Sym2 (Fin n) → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f s(x, y) ∉ X

/-- `g n` is the largest `k` such that every set mapping `f` on the pairs of an `n`-element set
with `f(x, y) ∉ {x, y}` admits an independent set of size at least `k`. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | k ≤ n ∧ ∀ f : Sym2 (Fin n) → Fin n,
    (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
      ∃ X : Finset (Fin n), IsIndependent f X ∧ k ≤ X.card}

abbrev Target : Prop :=
    (fun n : ℕ => (g n : ℝ)) =Θ[atTop] fun n : ℕ => √n

end Problem
