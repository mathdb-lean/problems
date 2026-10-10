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

- problem_id: E1026
- collection: erdos
- question_id: erdos:1026
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1026.lean#erdos_1026
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $x_1,\ldots,x_n$ be a sequence of distinct real numbers. Determine $$ \max\left(\sum x_{i_r}\right), $$ where the maximum is taken over all monotonic subsequences. This is as Erdős posed the problem in [Er71], which is rather ambiguous. Discussion between several users in the comments section has led to the following precise possible question, as posed by van Doorn: What is the largest constant $c$ such that, for all sequences of $n$ real numbers $x_1,\ldots,x_n$, $$ \max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i $$ (where again the maximum is taken over all monotonic subsequences)? Cambie makes the stronger conjecture that if $x_1,\ldots,x_{k^2}$ are distinct positive real numbers with $\sum x_i=1$ then there is always a monotonic subsequence with sum at least $1/k$. This stronger conjecture appears to have been first proved by Tidor, Wang, and Yang [TWY16], and is also implicit in work of Wagner [Wa17]. A proof was given and formalised by Aristotle (see the comments), with an alternative proof provided by Chan. In particular, this shows that $c=1$.
- notes: Erdos Problem 1026 -- https://www.erdosproblems.com/1026
- track: solved
- answer_shape: proof
- source_stem: 1026
- mathdb_ref: erdos:1026
- source_namespace: Erdos1026
- source_theorem: erdos_1026
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

/--
The set of sums $\sum x_{i_r}$, where $x_{i_1},\ldots,x_{i_r}$ ranges over the monotonic
subsequences of the sequence $x_1,\ldots,x_n$.
-/
def monotonicSubsequenceSums {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {S | ∃ I : Finset (Fin n), (MonotoneOn x ↑I ∨ AntitoneOn x ↑I) ∧ (∑ i ∈ I, x i) = S}

/--
The set of constants $c$ such that, for all sequences of $n$ distinct positive real numbers
$x_1,\ldots,x_n$,
$$
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
$$
(where the maximum is taken over all monotonic subsequences).

The source reduces to positive sequences. With signed sequences the condition is not a vanishing
error term: for $\varepsilon > |c|$ and $x_i = -i$ the right-hand side is positive while every
subsequence sum is nonpositive, so no constant would be admissible.
-/
def admissibleConstants : Set ℝ :=
  {c : ℝ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
    (∀ i, 0 < x i) →
    ∃ S ∈ monotonicSubsequenceSums x, (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) ≤ S}

abbrev Target : Prop :=
    IsGreatest admissibleConstants 1

end Problem
