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

- problem_id: E241_refute
- collection: erdos
- question_id: erdos:241
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/241.lean#erdos_241
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $f(N)\sim N^{1/3}$? Originally asked to Erdős by Bose. This is discussed in problem C11 of Guy's collection [Gu04].
- notes: Erdos Problem 241 -- https://www.erdosproblems.com/241
- track: open
- answer_shape: refute
- pair_id: E241
- pair_role: refute
- source_stem: 241
- mathdb_ref: erdos:241
- source_namespace: Erdos241
- source_theorem: erdos_241
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Finset
open scoped Asymptotics

namespace Problem

/--
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums $a+b+c$ with
$a,b,c\in A$ are all distinct (aside from the trivial coincidences).

Formalization note: this is generalized to allow for different $r$.
-/
noncomputable def f (N r : ℕ) : ℕ :=
  open scoped Classical in
  letI candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card

/--
The conjecture that the size of the set $A\subseteq \{1,\ldots,N\}$ is asymptotically $N^{1/r}$.
-/
def BoseChowlaConjecture (r : ℕ) : Prop :=
  (fun N ↦ (f N r : ℝ)) ~[atTop] (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / r))

abbrev Target : Prop :=
    ¬ (
      (fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))
    )

end Problem

/-
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums $a+b+c$ with
$a,b,c\in A$ are all distinct (aside from the trivial coincidences).

Formalization note: this is generalized to allow for different $r$.
-/
