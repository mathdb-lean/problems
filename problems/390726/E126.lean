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

- problem_id: E126
- collection: erdos
- question_id: erdos:126
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/126.lean#erdos_126
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $|A| = n$ then $\prod_{a\neq b\in A}(a + b)$ has at least $f(n)$ distinct prime factors. Is it true that $\frac{f(n)}{\log n} \to\infty$? The answer is yes, and a machine-checked proof is available.
- notes: Erdos Problem 126 -- https://www.erdosproblems.com/126
- track: solved
- answer_shape: decide
- source_stem: 126
- mathdb_ref: erdos:126
- source_namespace: Erdos126
- source_theorem: erdos_126
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
        Tendsto (fun n => f n / Real.log n) atTop atTop

end Problem
