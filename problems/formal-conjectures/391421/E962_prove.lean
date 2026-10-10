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

- problem_id: E962_prove
- collection: erdos
- question_id: erdos:962
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/962.lean#erdos_962
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Main conjecture: $\log k(n) \le (\log n)^{(1/2 + o(1))}$
- notes: Erdos Problem 962 -- https://www.erdosproblems.com/962
- track: open
- answer_shape: prove
- pair_id: E962
- pair_role: prove
- source_stem: 962
- mathdb_ref: erdos:962
- source_namespace: Erdos962
- source_theorem: erdos_962
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real

namespace Problem

/--
`Erdos962Prop n k` : there exists $m \le n$ such that each of
$m+1, \ldots, m+k$ has a prime divisor strictly larger than $k$.
-/
def Erdos962Prop (n k : ℕ) : Prop :=
  ∃ m ≤ n, ∀ i ∈ Set.Icc 1 k,
    ∃ p : ℕ, Nat.Prime p ∧ k < p ∧ p ∣ (m + i)

/--
Let $k(n)$ be the maximal $k$ such that there exists $m \le n$ with
$m+1, \ldots, m+k$ each divisible by a prime $> k$.
-/
noncomputable def k (n : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (fun k => Erdos962Prop n k) n

abbrev Target : Prop :=
    ∃ ε : ℕ → ℝ,
        (∀ δ > 0, ∀ᶠ n in atTop, |ε n| < δ) ∧
        ∀ᶠ n : ℕ in atTop,
          log (k n : ℝ)
            ≤ rpow (log n) ((1 : ℝ) / 2 + ε n)

end Problem
