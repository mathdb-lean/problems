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

- problem_id: M434111_restricted_prime_number_theorem_prove
- collection: mathoverflow
- question_id: mathoverflow:434111
- source: formal-conjectures
- source_locator: FormalConjectures/Mathoverflow/434111.lean#restricted_prime_number_theorem
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The conjecture claims that $\pi_n\sim\frac n{2\ln(n)}$. In other words, primes are distributed among the much sparser sequence $(S_n)_n$ with essentially the same density as in the positive integers, up to a factor of $2$. [MathOverflow 434111](https://mathoverflow.net/questions/434111/are-prime-numbers-among-sums-of-prime-numbers-distributed-as-frac-n2-lnn). [Me18] Meštrović, R., *Curious Conjectures on the Distribution of Primes Among the Sums of the First `2n` Primes*, [arXiv:1804.04198](https://arxiv.org/abs/1804.04198) (2018).
- notes: MathOverflow 434111 -- https://mathoverflow.net/questions/434111/are-prime-numbers-among-sums-of-prime-numbers-distributed-as-frac-n2-lnn
- track: open
- answer_shape: prove
- pair_id: M434111_restricted_prime_number_theorem
- pair_role: prove
- source_stem: 434111
- source_namespace: MathOverflow434111
- source_theorem: restricted_prime_number_theorem
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Nat Filter Topology Asymptotics

/-- $S_n$ is the sum of the first `n` primes, i.e. $S_n=p_1+\dots+p_n$, $1$-indexed,
matching the MathOverflow question. -/
noncomputable def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, nth Nat.Prime k

/-- $\pi_n$ counts how many of $S_1,S_2,\dots,S_n$ are themselves prime,
i.e. $\pi_n$ as used on MathOverflow (compare to $\pi_n$ in [Me18, Conjecture 3.3],
which instead ranges over $S_2,S_4,\dots,S_{2n}$). -/
noncomputable def piRestricted (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => Nat.Prime (S k))).card

abbrev Target : Prop :=
    ((fun n : ℕ => (piRestricted n : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ) / (2 * Real.log n)))

end Problem
