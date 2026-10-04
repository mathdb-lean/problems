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

- problem_id: E17_refute
- collection: erdos
- question_id: erdos:17
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/17.lean#erdos_17
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 17.** Are there infinitely many cluster primes?
- notes: Erdos Problem 17 -- https://www.erdosproblems.com/17
- track: open
- answer_shape: refute
- pair_id: E17
- pair_role: refute
- source_stem: 17
- mathdb_ref: erdos:17
- source_namespace: Erdos17
- source_theorem: erdos_17
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isClusterPrime_97_isLeast_non_cluster
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics Real

namespace Problem

/-- A prime $p$ is a cluster prime if every even natural number
$n \le p - 3$ can be written as a difference of two primes
$q_1 - q_2$ with $q_1, q_2 \le p$. -/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧
    ∀ {n : ℕ}, Even n → n ≤ (p - 3 : ℤ) →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ ≤ p ∧ q₂ ≤ p ∧ n = (q₁ - q₂ : ℤ)

/-- The counting function of cluster primes $\le n$. -/
noncomputable def clusterPrimeCount (n : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ n ∧ IsClusterPrime p}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- $97$ is the smallest prime that is not a cluster prime. -/
@[category test, AMS 11]
theorem isClusterPrime_97_isLeast_non_cluster : IsLeast {p : ℕ | p.Prime ∧ ¬ IsClusterPrime p} 97 := by
  -- For a prime `p`, being a cluster prime is equivalent to a fully bounded
  -- (hence decidable) statement over `ℕ`: every even `n ≤ p - 3` is `q₁ - q₂`
  -- for primes `q₁, q₂ ≤ p`, which (since `n ≥ 0`) amounts to a prime `q₂ ≤ p`
  -- with `q₂ + n` again prime and `≤ p`.
  have cluster_iff : ∀ p : ℕ, p.Prime →
      (IsClusterPrime p ↔
        (∀ n ∈ Finset.range (p - 2), Even n →
          ∃ q₂ ∈ Finset.range (p + 1), (Nat.Prime q₂) ∧ Nat.Prime (q₂ + n) ∧ q₂ + n ≤ p)) := by
    intro p hp
    constructor
    · rintro ⟨-, h⟩ n hn hev
      simp only [Finset.mem_range] at hn
      have hn3 : (n : ℤ) ≤ (p - 3 : ℤ) := by omega
      obtain ⟨q₁, q₂, hq1p, hq2p, hq1le, hq2le, heq⟩ := h hev hn3
      refine ⟨q₂, ?_, hq2p, ?_, ?_⟩
      · simp only [Finset.mem_range]; omega
      · have hq2n : q₂ + n = q₁ := by omega
        rw [hq2n]; exact hq1p
      · omega
    · intro h
      refine ⟨hp, ?_⟩
      intro n hev hn3
      have hnp : n ≤ p - 3 := by omega
      have hnrange : n ∈ Finset.range (p - 2) := by
        simp only [Finset.mem_range]; omega
      obtain ⟨q₂, hq2r, hq2p, hq1p, hle⟩ := h n hnrange hev
      refine ⟨q₂ + n, q₂, hq1p, hq2p, hle, ?_, ?_⟩
      · simp only [Finset.mem_range] at hq2r; omega
      · push_cast; ring
  constructor
  · -- `97` is prime but not a cluster prime: the even number `88 ≤ 94` is not a
    -- difference of two primes `≤ 97`.
    refine ⟨by norm_num, ?_⟩
    rw [cluster_iff 97 (by norm_num)]
    simp only [Nat.reduceSub, Finset.mem_range, Nat.reduceAdd, not_forall, not_exists, not_and,
      not_le]
    refine ⟨88, by norm_num, by norm_num, ?_⟩
    intro x xl hx xl
    suffices 9 < x by
      lia
    contrapose! xl
    interval_cases x <;> norm_num
    · contrapose hx
      exact Nat.not_prime_one
    · contrapose hx
      norm_num
  · -- `97` is a lower bound: every prime `< 97` is a cluster prime, so cannot lie
    -- in the set of non-cluster primes.
    rintro b ⟨hbp, hbnc⟩
    by_contra! hlt
    interval_cases b <;>
      first
        | exact absurd hbp (by decide)
        | exact hbnc ((cluster_iff _ (by norm_num)).mpr (by set_option maxRecDepth 8000 in decide))

abbrev Target : Prop :=
    ¬ (
      {p : ℕ | IsClusterPrime p}.Infinite
    )

end Problem
