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

- problem_id: E448
- collection: erdos
- question_id: erdos:448
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/448.lean#erdos_448
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $\tau(n)$ count the divisors of $n$ and $\tau^+(n)$ count the number of $k$ such that $n$ has a divisor in $[2^k, 2^{k+1})$. Is it true that, for all $\epsilon > 0$, $$ \tau^+(n) < \epsilon \cdot \tau(n) $$ for almost all $n$? This is false, and was disproved by Erdős and Tenenbaum [ErTe81], who showed that in fact the upper density of the set of such $n$ is $\asymp \epsilon^{1-o(1)}$ (where the $o(1)$ in the exponent $\to 0$ as $\epsilon \to 0$). A more precise result was proved by Hall and Tenenbaum [HaTe88] (see Section 4.6), who showed that the upper density is $\ll \epsilon \log(2/\epsilon)$. Hall and Tenenbaum further prove that $\tau^+(n)/\tau(n)$ has a distribution function. Erdős and Graham also asked whether there is a good inequality known for $\sum_{n \leq x} \tau^+(n)$. This was provided by Ford [Fo08] who proved $$ \sum_{n \leq x} \tau^+(n) \asymp x\frac{(\log x)^{1-\alpha}}{(\log\log x)^{3/2}} $$ where $$ \alpha = 1-\frac{1+\log\log 2}{\log 2} = 0.08607\cdots. $$
- notes: Erdos Problem 448 -- https://www.erdosproblems.com/448
- track: solved
- answer_shape: decide
- source_stem: 448
- mathdb_ref: erdos:448
- source_namespace: Erdos448
- source_theorem: erdos_448
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: tauPlus_six tauPlus_twelve tauPlus_le_tau
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Filter Asymptotics Topology

/-- `tauPlus n` (written $\tau^+(n)$) counts the number of $k$ such that $n$ has a divisor in
$[2^k, 2^{k+1})$. Equivalently, the number of distinct values $\lfloor \log_2 d \rfloor$ as $d$
ranges over the divisors of $n$: a divisor $d$ lies in $[2^k, 2^{k+1})$ iff `Nat.log 2 d = k`. -/
def tauPlus (n : ℕ) : ℕ := (n.divisors.image (Nat.log 2)).card

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Sanity check: $\tau^+(6) = 3$. Divisors $1, 2, 3, 6$ lie in dyadic blocks $k = 0, 1, 1, 2$,
so the distinct blocks are $\{0, 1, 2\}$. ($\tau(6) = 4$.) -/
@[category test, AMS 11]
theorem tauPlus_six : tauPlus 6 = 3 := by decide

/-- Sanity check: $\tau^+(12) = 4$. Divisors $1, 2, 3, 4, 6, 12$ lie in dyadic blocks
$k = 0, 1, 1, 2, 2, 3$, so the distinct blocks are $\{0, 1, 2, 3\}$. ($\tau(12) = 6$.) -/
@[category test, AMS 11]
theorem tauPlus_twelve : tauPlus 12 = 4 := by decide

/-- Always $\tau^+(n) \le \tau(n)$: the occupied dyadic blocks are the image of the divisor set
under `Nat.log 2`, and an image has at most as many elements as its source. This is what makes the
$\epsilon < 1$ comparison in the problem meaningful. -/
@[category test, AMS 11]
theorem tauPlus_le_tau (n : ℕ) : tauPlus n ≤ n.divisors.card :=
  Finset.card_image_le

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ ε : ℝ, 0 < ε →
          {n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.HasDensity 1

end Problem
