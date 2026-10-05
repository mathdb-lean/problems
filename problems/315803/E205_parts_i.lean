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

- problem_id: E205_parts_i
- collection: erdos
- question_id: erdos:205
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/205.lean#erdos_205.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that all sufficiently large $n$ can be written as $2^k+m$ for some $k\geq 0$, where $\Omega(m)<\log\log m$? (Here $\Omega(m)$ is the number of prime divisors of $m$ counted with multiplicity.) Barreto and Leeham, using ChatGPT and Aristotle, have proved a negative answer, which was quantified by Tao and Alexeev (see the comments): in fact there are infinitely many $n$ such that, for all $k$ with $2^k<n$, $n-2^k$ has at least $$\gg \left(\frac{\log n}{\log\log n}\right)^{1/2}$$ many prime factors.
- notes: Erdos Problem 205 -- https://www.erdosproblems.com/205
- track: solved
- answer_shape: decide
- source_stem: 205
- mathdb_ref: erdos:205
- source_namespace: Erdos205
- source_theorem: erdos_205.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Asymptotics Filter

open scoped ArithmeticFunction.Omega

namespace Problem

/--
`IsRepresentable f n` states that `n` can be written as `2 ^ k + m` for some `k ≥ 0` where the
number of prime divisors of `m`, counted with multiplicity, is less than `f m`.
-/
def IsRepresentable (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ k m : ℕ, n = 2 ^ k + m ∧ (Ω m : ℝ) < f m

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ᶠ n : ℕ in atTop, IsRepresentable (fun m => Real.log (Real.log m)) n

end Problem
