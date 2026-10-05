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

- problem_id: E435
- collection: erdos
- question_id: erdos:435
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/435.lean#erdos_435
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $n\in\mathbb{N}$ with $n\neq p^k$ for any prime $p$ and $k\geq 0$. What is the largest integer not of the form $$\sum_{1\leq i<n}c_i\binom{n}{i}$$ where the $c_i\geq 0$ are integers? If $n=\prod p_k^{a_k}$ then the largest integer not of this form is $$\sum_k \left( \sum_{1\leq d\leq a_k}\binom{n}{p_k^d}\right)(p_k-1)-n.$$ This was first proved by Hwang and Song [HwSo24]. Independently this was found in the comment section by Peake and Cambie.
- notes: Erdos Problem 435 -- https://www.erdosproblems.com/435
- track: solved
- answer_shape: proof
- source_stem: 435
- mathdb_ref: erdos:435
- source_namespace: Erdos435
- source_theorem: erdos_435
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ) (hn : n ≠ 0)
        (hpk : ∀ p k : ℕ, p.Prime → n ≠ p ^ k),
      IsGreatest
        {m : ℤ | ¬ ∃ c : ℕ → ℕ, m = ∑ i ∈ Finset.Ico 1 n, (c i : ℤ) * (n.choose i : ℤ)}
        ((∑ p ∈ n.primeFactors,
          (∑ d ∈ Finset.Icc 1 (n.factorization p), (n.choose (p ^ d) : ℤ)) * ((p : ℤ) - 1)) - n)

end Problem
