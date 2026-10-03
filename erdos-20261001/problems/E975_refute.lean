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

- problem_id: E975_refute
- collection: erdos
- question_id: erdos:975
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/975.lean#erdos_975
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: For an irreducible polynomial $f \in \mathbb{Z}[x]$ with $f(n) \ge 1$ for sufficiently large $n$, does there exists a constant $c = c(f) > 0$ such that $\sum_{n \le x} \tau(f(n)) \approx c \cdot x \log x$? Note that it is unclear whether the polynomial should have integer coefficients or merely be integer-valued. We assume the former.
- notes: Erdos Problem 975 -- https://www.erdosproblems.com/975
- track: open
- answer_shape: refute
- pair_id: E975
- pair_role: refute
- source_stem: 975
- mathdb_ref: erdos:975
- source_namespace: Erdos975
- source_theorem: erdos_975
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real Polynomial
open scoped ArithmeticFunction.sigma Topology

namespace Problem

/-- Sum of $\tau(f(n))$ from `0` to `⌊x⌋` for a polynomial $f \in \mathbb{Z}[X]$.

Here $\tau$ is the divisor counting function, which is `σ 0` in mathlib.
Also, for simplicity, we use `Nat.floor` to convert rational values to natural numbers, instead of
dealing with negative values. -/
noncomputable def Erdos975Sum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ≤ ⌊x⌋₊, σ 0 ⌊f.eval ↑n⌋₊

abbrev Target : Prop :=
    ¬ (
      ∀ f : ℤ[X], f.natDegree ≠ 0 → Irreducible f → (∀ᶠ n in atTop, 1 ≤ f.eval n) →
          ∃ c > (0 : ℝ), Tendsto (fun x ↦ Erdos975Sum f x / (x * log x)) atTop (𝓝 c)
    )

end Problem
