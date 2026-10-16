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

- problem_id: G47
- collection: green
- question_id: green:47
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/47.lean#green_47
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that a large sieve process leaves a set of quadratic size. Is that set quadratic? The following very particular instance is probably the simplest [Gr24]: Suppose that $A \subset \mathbb{N}$ is a set with the property that $|A \pmod p| \leqslant \frac{1}{2}(p + 1)$ for all sufficiently large $p$. Is it true that either $|A \cap [X]| \ll X^{1/2} / \log^{100} X$, or $A$ is contained in the image of $\mathbb{Z}$ under a quadratic map $\phi : \mathbb{Q} \to \mathbb{Q}$?
- notes: Green, open problem 47 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.47
- track: solved
- answer_shape: decide
- source_stem: 47
- source_namespace: Green47
- source_theorem: green_47
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Filter

namespace Problem

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ A : Set ℕ,
      (∀ᶠ p in atTop, Nat.Prime p → Set.ncard (Set.image (fun a : ℕ => (a : ZMod p)) A) ≤ (p + 1) / 2) →
      ((fun X : ℕ => ((A ∩ Set.Iic X).ncard : ℝ)) ≪ (fun X : ℕ => Real.sqrt (X : ℝ) / (Real.log (X : ℝ)) ^ 100))
      ∨ (∃ P : Polynomial ℚ, P.degree = 2 ∧ ∀ a ∈ A, ∃ z : ℤ, (a : ℚ) = P.eval (z : ℚ))

end Problem
