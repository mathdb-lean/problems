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

- problem_id: E694
- collection: erdos
- question_id: erdos:694
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/694.lean#erdos_694
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f_\max(n)$ be the largest $m$ such that $\phi(m) = n$, and $f_\min(n)$ be the smallest such $m$, where $\phi$ is Euler's totient function. Investigate $$ \max_{n\leq x}\frac{f_\max(n)}{f_\min(n)}. $$ GPT-5.5 Pro (prompted by Price) has proved (see also the comments for a summary) that $$ \max_{n\leq x}\frac{f_{\max}(n)}{f_{\min}(n)}=(e^\gamma+o(1))\log\log x. $$ A Lean formalisation of the reduction exists, conditional on Mertens' product theorem and Linnik's theorem; see the [formal proof](https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P694/Proof.lean). The extrema are only required on nonempty fibres of the totient (values such as $3$ have no preimage), and the identity is asked for sufficiently large $x$: at $x = 1$ the maximum is $f_\max(1) / f_\min(1) = 2$ while $\log \log 1 = 0$.
- notes: Erdos Problem 694 -- https://www.erdosproblems.com/694
- track: solved
- answer_shape: proof
- source_stem: 694
- mathdb_ref: erdos:694
- source_namespace: Erdos694
- source_theorem: erdos_694
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Topology Real

abbrev Target : Prop :=
    ∀ᵉ (fmax : ℕ → ℕ) (fmin : ℕ → ℕ),
          (∀ n, (∃ m, Nat.totient m = n) → IsGreatest (Nat.totient ⁻¹' {n}) (fmax n)) →
          (∀ n, (∃ m, Nat.totient m = n) → IsLeast (Nat.totient ⁻¹' {n}) (fmin n)) →
          ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
            ∀ᶠ x : ℕ in atTop,
              sSup { (fmax n : ℝ) / fmin n | (n : ℕ) (_ : n ≤ x) (_ : ∃ m, Nat.totient m = n) } =
                (exp eulerMascheroniConstant + o x) * log (log (x : ℝ))

end Problem
