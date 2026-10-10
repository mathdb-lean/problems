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

- problem_id: E690
- collection: erdos
- question_id: erdos:690
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/690.lean#erdos_690
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $d_k(p)$ be the density of those integers whose $k$th smallest prime factor is $p$ (i.e. if $p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$). For fixed $k\geq 1$ is $d_k(p)$ unimodular in $p$? That is, it first increases in $p$ until its maximum then decreases. The answer is no in general: Cambie [Ca25] has shown that $d_k(p)$ is unimodular for $1\leq k\leq 3$ and is not unimodular for $4\leq k\leq 20$. The densities $d_k(p)$ exist (see `erdos_690.variants.hasDensity`), so the statement quantifies over any function `d` recording them.
- notes: Erdos Problem 690 -- https://www.erdosproblems.com/690
- track: solved
- answer_shape: decide
- source_stem: 690
- mathdb_ref: erdos:690
- source_namespace: Erdos690
- source_theorem: erdos_690
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

/-- The set of positive integers whose `k`-th smallest prime factor is `p`: if
$p_1<p_2<\cdots$ are the primes dividing $n$ then $p_k=p$. -/
def kthPrimeFactorSet (k p : ℕ) : Set ℕ :=
  {n | 0 < n ∧ p ∈ n.primeFactors ∧ (n.primeFactors.filter (· < p)).card = k - 1}

/-- A function on the primes is *unimodular* if it first increases in $p$ until its maximum then
decreases. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ m, m.Prime ∧ (∀ p q, p.Prime → q.Prime → p ≤ q → q ≤ m → f p ≤ f q) ∧
    ∀ p q, p.Prime → q.Prime → m ≤ p → p ≤ q → f q ≤ f p

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k ≥ 1, ∀ d : ℕ → ℝ,
          (∀ p, p.Prime → (kthPrimeFactorSet k p).HasDensity (d p)) → IsUnimodalOnPrimes d

end Problem
