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

- problem_id: E36
- collection: erdos
- question_id: erdos:36
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/36.lean#erdos_36
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Find the value of the limit of `MinOverlapQuotient`!
- notes: Erdos Problem 36 -- https://www.erdosproblems.com/36
- track: open
- answer_shape: value
- answer_type: ℝ
- answer_pinned: true
- answer_pinned_reason: limit_is_unique
- source_stem: 36
- mathdb_ref: erdos:36
- source_namespace: Erdos36
- source_theorem: erdos_36
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Topology
open Filter

namespace Problem

/--
The number of solutions to the equation $a - b = k$, for $a \in A$ and $b \in B$.
This represents the "overlap" between sets $A$ and $B$ for a given difference $k$.
-/
def Overlap (A B : Finset ℤ) (k : ℤ) : ℕ := ((A.product B).filter <| fun (a, b) => a - b = k).card

/--
The maximum overlap for a given pair of sets $A$ and $B$,
taken over all possible integer differences $k$.
-/
noncomputable def MaxOverlap (A B : Finset ℤ) : ℕ := iSup <| Overlap A B

/--
Let $A$ and $B$ be two complementary subsets, a splitting of the numbers $\{1, 2, \dots, 2n\}$,
such that both have the same cardinality $n$.
Define $M(n)$ to be the minimum `MaxOverlap` that can be achieved,
ranging over all such partitions $(A, B)$.
-/
noncomputable def M (n : ℕ) : ℕ :=
  sInf {MaxOverlap A B | (A : Finset ℤ) (B : Finset ℤ)
    (_disjoint : Disjoint A B)
    (_union : A ∪ B = Finset.Icc (1 : ℤ) (2 * n))
    (_same_card : A.card = B.card)}

/-- A computable stand-in for `MaxOverlap`. `Overlap` is already computable; the only obstacle
is the `iSup`, and `maxOverlap_eq_sup` says it agrees with this `Finset.sup`. -/
private def maxOverlapC (A B : Finset ℤ) : ℕ :=
  ((A ×ˢ B).image fun p => p.1 - p.2).sup (Overlap A B)

/-- The `n`-element subsets of `{1, …, 2n}`. -/
private def parts (n : ℕ) : Finset (Finset ℤ) :=
  letI : Preorder ℤ := Int.instLinearOrder.toPreorder
  (Finset.Icc (1 : ℤ) (2 * n)).powerset.filter fun A => A.card = n

/--
The quotient of the minimum maximum overlap $M(N)$ by $N$. The central question of the
minimum overlap problem is to determine the asymptotic behavior of this quotient as $N \to \infty$.
-/
noncomputable def MinOverlapQuotient (N : ℕ) := (M N : ℝ) / N

abbrev Target (value : ℝ) : Prop :=
    atTop.Tendsto MinOverlapQuotient (𝓝 value)

end Problem
