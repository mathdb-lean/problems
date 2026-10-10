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

- problem_id: E535
- collection: erdos
- question_id: erdos:535
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/535.lean#erdos_535
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $r \geq 3$, and let $f_r(N)$ denote the size of the largest subset of $\{1,\ldots,N\}$ such that no subset of size $r$ has the same pairwise greatest common divisor between all elements. Erdős [Er64] proved that $f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$, and conjectured this should also be an upper bound; here we state the conjectural upper bound for all $r \geq 3$. See also [536].
- notes: Erdos Problem 535 -- https://www.erdosproblems.com/535
- track: open
- answer_shape: proof
- source_stem: 535
- mathdb_ref: erdos:535
- source_namespace: Erdos535
- source_theorem: erdos_535
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open ArithmeticFunction
open Filter Real
open scoped omega Omega

namespace Problem

/-- No `r`-subset has constant pairwise GCD with coprime quotients. -/
def NoConstantPairwiseGcdCoprimeSubsets (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.card = r →
    ¬ (∃ d, 0 < d ∧ (S : Set ℕ).Pairwise (fun a b => Nat.gcd a b = d) ∧
      ∀ a ∈ S, ∃ b, a = d * b ∧ Nat.gcd b d = 1)

/--
All elements of `A` are positive and have exactly `k` prime factors,
counted with multiplicity.

Erdős [Er73] explains that Abbott pointed out the ordinary sunflower conjecture
does not seem to suffice for Problem 535; the corrected stronger auxiliary
statement uses $Ω$, not $ω$.
-/
def AllBigOmega (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ Ω a = k

/-- `f r N` is the maximum size of a subset `A ⊆ {1,…,N}` such that no `r`-element
subset of `A` has constant pairwise GCD. -/
noncomputable def f (r N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}

abbrev Target : Prop :=
    ∀ r ≥ 3, ∃ c > (0 : ℝ),
        ∀ᶠ (N : ℕ) in atTop,
          (f r N : ℝ) ≤ (N : ℝ) ^ (c / log (log (N : ℝ)))

end Problem
