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

- problem_id: E1209_parts_iii_b_prove
- collection: erdos
- question_id: erdos:1209
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1209.lean#erdos_1209.parts.iii.b
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there $n$ such that $n+2^{2^k}$ is always squarefree?
- notes: Erdos Problem 1209 -- https://www.erdosproblems.com/1209
- track: open
- answer_shape: prove
- pair_id: E1209_parts_iii_b
- pair_role: prove
- source_stem: 1209
- mathdb_ref: erdos:1209
- source_namespace: Erdos1209
- source_theorem: erdos_1209.parts.iii.b
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: exists_prime_gt_not_prime_add seq_zero_spec seq_succ_spec exists_prime_gt_not_squarefree_add seq'_succ_spec
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Set

namespace Problem

/-- For every `k ≥ 1` and bound `m`, there is a prime `p > m` such that `k + p` is composite:
take a prime `q > k` and, by Dirichlet, a prime `p > max m q` with `p ≡ -k (mod q)`. -/
@[category API, AMS 11]
theorem exists_prime_gt_not_prime_add (k m : ℕ) (hk : 1 ≤ k) :
    ∃ p, m < p ∧ p.Prime ∧ ¬ (k + p).Prime := by
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have : NeZero q := ⟨hq.ne_zero⟩
  have hunit : IsUnit (-(k : ZMod q)) := by
    refine IsUnit.neg ?_
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
  obtain ⟨p, hp, hpp, hpq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max m q)
  refine ⟨p, by omega, hpp, ?_⟩
  have hdvd : q ∣ k + p := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpq]
    ring
  exact Nat.not_prime_of_dvd_of_lt hdvd hq.two_le (by omega)

/-- The counterexample sequence: `a 0` is a prime at least `f 0`, and `a (k + 1)` is a prime
larger than `a k` and `f (k + 1)` with `(k + 1) + a (k + 1)` composite. -/
noncomputable def seq (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_infinite_primes (f 0))
  | k + 1 => Classical.choose (exists_prime_gt_not_prime_add (k + 1) (max (seq f k) (f (k + 1)))
      (by omega))

/-- For every `k ≥ 1` and bound `m`, there is a prime `p > m` such that `k + p` is not squarefree:
take a prime `q > k` and, by Dirichlet, a prime `p > m` with `p ≡ -k (mod q ^ 2)`. -/
@[category API, AMS 11]
theorem exists_prime_gt_not_squarefree_add (k m : ℕ) (hk : 1 ≤ k) :
    ∃ p, m < p ∧ p.Prime ∧ ¬ Squarefree (k + p) := by
  obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 1)
  have : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have hunit : IsUnit (-(k : ZMod (q ^ 2))) := by
    refine IsUnit.neg ?_
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))))
  obtain ⟨p, hp, hpp, hpq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit m
  refine ⟨p, hp, hpp, ?_⟩
  have hdvd : q ^ 2 ∣ k + p := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, hpq]
    ring
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨q, hq, by rwa [← sq]⟩

/-- The counterexample sequence for the squarefree variant. -/
noncomputable def seq' (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_infinite_primes (f 0))
  | k + 1 => Classical.choose (exists_prime_gt_not_squarefree_add (k + 1)
      (max (seq' f k) (f (k + 1))) (by omega))

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- The defining properties of `seq f 0`. -/
@[category API, AMS 11]
theorem seq_zero_spec (f : ℕ → ℕ) : f 0 ≤ seq f 0 ∧ (seq f 0).Prime :=
  Classical.choose_spec (Nat.exists_infinite_primes (f 0))

/-- The defining properties of `seq f (k + 1)`. -/
@[category API, AMS 11]
theorem seq_succ_spec (f : ℕ → ℕ) (k : ℕ) :
    max (seq f k) (f (k + 1)) < seq f (k + 1) ∧ (seq f (k + 1)).Prime ∧
      ¬ ((k + 1) + seq f (k + 1)).Prime :=
  Classical.choose_spec (exists_prime_gt_not_prime_add (k + 1) (max (seq f k) (f (k + 1)))
    (by omega))

/-- The defining properties of `seq' f (k + 1)`. -/
@[category API, AMS 11]
theorem seq'_succ_spec (f : ℕ → ℕ) (k : ℕ) :
    max (seq' f k) (f (k + 1)) < seq' f (k + 1) ∧ (seq' f (k + 1)).Prime ∧
      ¬ Squarefree ((k + 1) + seq' f (k + 1)) :=
  Classical.choose_spec (exists_prime_gt_not_squarefree_add (k + 1) (max (seq' f k) (f (k + 1)))
    (by omega))

abbrev Target : Prop :=
    ∃ n : ℕ, ∀ k : ℕ, Squarefree (n + 2 ^ (2 ^ k))

end Problem
