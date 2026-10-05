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

- problem_id: E990
- collection: erdos
- question_id: erdos:990
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/990.lean#erdos_990
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f=a_0+\cdots+a_dx^d\in \mathbb{C}[x]$ be a polynomial. Is it true that, if $f$ has roots $z_1,\ldots,z_d$ with corresponding arguments $\theta_1,\ldots,\theta_d\in [0,2\pi]$, then for all intervals $I\subseteq [0,2\pi]$ $$ \left\lvert (\# \theta_i \in I) - \frac{\lvert I\rvert}{2\pi}d\right\rvert \ll \left(n\log M\right)^{1/2}, $$ where $n$ is the number of non-zero coefficients of $f$ and $$ M=\frac{\lvert a_0\rvert+\cdots +\lvert a_d\rvert}{(\lvert a_0\rvert\lvert a_d\rvert)^{1/2}}. $$ An internal OpenAI model (see [APSSV26b]) has disproved the conjecture, constructing, for every $n\geq 1$, a polynomial $f$ with $n$ non-zero coefficients such that $M<3$ and with a positive real zero of multiplicity $n-1$, whence letting $I=[0,c/d]$ for a suitably small $c>0$, $$ \left\lvert (\# \theta_i \in I) - \frac{\lvert I\rvert}{2\pi}d\right\rvert \geq n-1. $$
- notes: Erdos Problem 990 -- https://www.erdosproblems.com/990
- track: solved
- answer_shape: decide
- source_stem: 990
- mathdb_ref: erdos:990
- source_namespace: Erdos990
- source_theorem: erdos_990
- source_category: research solved
- source_ams: 12 30
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Polynomial

open scoped Real

namespace Problem

open scoped Classical in
/--
The number of roots of `f`, counted with multiplicity, whose argument lies in `I`. The argument
is normalised to `[0, 2π)`.
-/
noncomputable def rootArgCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  f.roots.countP fun z =>
    (if Complex.arg z < 0 then Complex.arg z + 2 * π else Complex.arg z) ∈ I

/--
For $f = a_0 + \cdots + a_dx^d$, the quantity
$M=\frac{\lvert a_0\rvert+\cdots +\lvert a_d\rvert}{(\lvert a_0\rvert\lvert a_d\rvert)^{1/2}}$.
-/
noncomputable def M (f : ℂ[X]) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∃ C : ℝ, ∀ f : ℂ[X], f.coeff 0 ≠ 0 → ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ 2 * π →
          |(rootArgCount f (Set.Icc α β) : ℝ) - (β - α) / (2 * π) * (f.natDegree : ℝ)| ≤
            C * Real.sqrt ((f.support.card : ℝ) * Real.log (M f))

end Problem
