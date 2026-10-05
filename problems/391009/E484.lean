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

- problem_id: E484
- collection: erdos
- question_id: erdos:484
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/484.lean#erdos_484
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Prove that there exists an absolute constant $c>0$ such that, whenever $\{1,\ldots,N\}$ is $k$-coloured (and $N$ is large enough depending on $k$) then there are at least $cN$ many integers in $\{1,\ldots,N\}$ which are representable as a monochromatic sum (that is, $a+b$ where $a,b\in \{1,\ldots,N\}$ are in the same colour class and $a\neq b$). A conjecture of Roth. Solved by Erdős, Sárközy, and Sós [ESS89], who in fact prove that there are at least $\frac{N}{2}-O(N^{1-1/2^{k+1}})$ many even numbers which are of this form.
- notes: Erdos Problem 484 -- https://www.erdosproblems.com/484
- track: solved
- answer_shape: proof
- source_stem: 484
- mathdb_ref: erdos:484
- source_namespace: Erdos484
- source_theorem: erdos_484
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open scoped Classical in
abbrev Target : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ℕ → Fin k,
      c * N ≤ (((Finset.Icc 1 N).filter fun n =>
        ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N,
          a ≠ b ∧ f a = f b ∧ a + b = n).card : ℝ)

end Problem
