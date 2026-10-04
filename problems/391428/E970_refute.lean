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

- problem_id: E970_refute
- collection: erdos
- question_id: erdos:970
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/970.lean#erdos_970
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $h(k)$ be Jacobsthal's function, defined to as the minimal $m$ such that, if $n$ has at most $k$ prime factors, then in any set of $m$ consecutive integers there exists an integer coprime to $n$. Determine the order of magnitude of $h(k)$. In particular, is it true that $$h(k) \ll k^2?$$
- notes: Erdos Problem 970 -- https://www.erdosproblems.com/970
- track: open
- answer_shape: refute
- pair_id: E970
- pair_role: refute
- source_stem: 970
- mathdb_ref: erdos:970
- source_namespace: Erdos970
- source_theorem: erdos_970
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
`IsJacobsthalBound k m` says that every interval of `m` consecutive integers contains an
integer coprime to every positive natural number having at most `k` distinct prime factors.
-/
def IsJacobsthalBound (k m : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n

/--
Jacobsthal's function, uniformly parametrized by the maximum number of distinct prime factors.
-/
noncomputable def jacobsthalFunction (k : ℕ) : ℕ :=
  sInf {m : ℕ | IsJacobsthalBound k m}

abbrev Target : Prop :=
    ¬ (
      ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C * k ^ 2
    )

end Problem
