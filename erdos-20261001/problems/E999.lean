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

- problem_id: E999
- collection: erdos
- question_id: erdos:999
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/999.lean#erdos_999
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For any function $f:\mathbb{N}\to \mathbb{R}_{\geq 0}$ the property that, for almost all $\alpha$ $$\left\lvert \alpha-\frac{p}{q}\right\rvert < \frac{f(q)}{q}$$ has infinitely many solutions with $(p,q)=1$, is equivalent to $$\sum_{q\geq 1}\phi(q)\frac{f(q)}{q}=\infty.$$ The Duffin–Schaeffer conjecture. It is easy to prove that the latter follows from the former. Erdős proved this in the special case when $f(q)q$ is bounded. The full conjecture was proved by Koukoulopoulos and Maynard [KoMa20].
- notes: Erdos Problem 999 -- https://www.erdosproblems.com/999
- track: solved
- answer_shape: decide
- source_stem: 999
- mathdb_ref: erdos:999
- source_namespace: Erdos999
- source_theorem: erdos_999
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open MeasureTheory

namespace Problem

/-- `x` is *approximable* with respect to `f` if
$$\left\lvert x-\frac{p}{q}\right\rvert < \frac{f(q)}{q}$$
has infinitely many solutions with $(p,q)=1$. -/
def IsApproximable (f : ℕ → ℝ) (x : ℝ) : Prop :=
  {q : ℕ | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q}.Infinite

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ f : ℕ → ℝ, (∀ q, 0 ≤ f q) →
        ((∀ᵐ x : ℝ, IsApproximable f x) ↔
          ¬ Summable fun q : ℕ ↦ (Nat.totient q : ℝ) * f q / q)

end Problem
