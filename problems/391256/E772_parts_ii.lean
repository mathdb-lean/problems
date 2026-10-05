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

- problem_id: E772_parts_ii
- collection: erdos
- question_id: erdos:772
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/772.lean#erdos_772.parts.ii
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $H_k(n) > n^{1/2+c}$ for some constant $c>0$? The answer is yes, and in fact $H_k(n) \gg_k n^{2/3}$, proved by Alon and Erdős [AlEr85].
- notes: Erdos Problem 772 -- https://www.erdosproblems.com/772
- track: solved
- answer_shape: decide
- source_stem: 772
- mathdb_ref: erdos:772
- source_namespace: Erdos772
- source_theorem: erdos_772.parts.ii
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Real AdditiveCombinatorics

namespace Problem

/-- $H_k(n)$ is the maximal $r$ such that if $A\subset\mathbb{N}$ has $\lvert A\rvert=n$ and
$\| 1_A\ast 1_A\|_\infty \leq k$ then $A$ contains a Sidon set of size at least $r$.

Here $1_A\ast 1_A(m)$ counts the ordered pairs $(a,b)\in A^2$ with $a+b=m$. (The value is
truncated at $n$, which only matters when no such $A$ exists.) -/
noncomputable def H (k n : ℕ) : ℕ :=
  sSup {r | r ≤ n ∧ ∀ A : Finset ℕ, A.card = n → (∀ m, sumRep A m ≤ k) →
    ∃ S ⊆ A, IsSidon (S : Set ℕ) ∧ r ≤ S.card}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ k ≥ 1, ∃ c > 0, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 / 2 + c : ℝ) < H k n

end Problem
