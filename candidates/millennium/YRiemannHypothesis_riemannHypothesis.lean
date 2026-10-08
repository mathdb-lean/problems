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

- problem_id: YRiemannHypothesis_riemannHypothesis
- collection: millennium
- question_id: millennium:RiemannHypothesis
- source: formal-conjectures
- source_locator: FormalConjectures/Millennium/RiemannHypothesis.lean#riemannHypothesis
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The **Riemann Hypothesis**: all non-trivial zeros of the Riemann zeta function have real part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivial zero $-2(n+1)$ for some $n \in \mathbb{N}$, then $\operatorname{Re}(s) = \frac{1}{2}$. This is the official Millennium Prize Problem as posed by the [Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf). This uses the `RiemannHypothesis` type from Mathlib, which is defined as `∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`.
- notes: Millennium Prize problem RiemannHypothesis -- https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf
- track: open
- answer_shape: proof
- source_stem: RiemannHypothesis
- source_namespace: RiemannHypothesis
- source_theorem: riemannHypothesis
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: tools/manual_millennium.py
-/

namespace Problem

abbrev Target : Prop :=
    RiemannHypothesis

end Problem
