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

- problem_id: E534
- collection: erdos
- question_id: erdos:534
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/534.lean#erdos_534
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: What is the largest possible subset $A\subseteq\{1,\ldots,N\}$ which contains $N$ such that $\mathrm{gcd}(a,b)>1$ for all $a\neq b\in A$? Erdős conjectured that if $N=q_1^{k_1}\cdots q_r^{k_r}$ (where $q_1<\cdots <q_r$ are distinct primes) then the maximum is achieved by, for some $1\leq j\leq r$, those integers in $[1,N]$ which are a multiple of at least one of $\{2q_1,\ldots,2q_j,q_1\cdots q_j\}$. This conjecture was proved by Ahlswede and Khachatrian [AhKh96].
- notes: Erdos Problem 534 -- https://www.erdosproblems.com/534
- track: solved
- answer_shape: proof
- source_stem: 534
- mathdb_ref: erdos:534
- source_namespace: Erdos534
- source_theorem: erdos_534
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- A set `A ⊆ {1, …, N}` is *admissible* if it contains `N` and any two distinct elements
of `A` have a common factor. -/
def IsAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ N ∈ A ∧ (A : Set ℕ).Pairwise fun a b ↦ 1 < Nat.gcd a b

/-- The largest size of an admissible subset of `{1, …, N}`. -/
noncomputable def maxCard (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℕ, IsAdmissible N A ∧ A.card = n}

/-- The prime factors `q₁ < ⋯ < qⱼ` of `N` which are at most `q`. -/
def primePrefix (N q : ℕ) : Finset ℕ := N.primeFactors.filter (· ≤ q)

/-- The Ahlswede–Khachatrian set associated to a prime factor `q` of `N`: those integers in
`[1, N]` which are a multiple of at least one of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ`, where
`q₁ < ⋯ < qⱼ = q` are the prime factors of `N` which are at most `q`. -/
def ahlswedeKhachatrian (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m ↦
    (∏ p ∈ primePrefix N q, p) ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

abbrev Target : Prop :=
    ∀ (N : ℕ) (hN : 2 ≤ N),
      ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
        maxCard N = (ahlswedeKhachatrian N q).card

end Problem
