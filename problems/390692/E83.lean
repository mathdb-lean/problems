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

- problem_id: E83
- collection: erdos
- question_id: erdos:83
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/83.lean#erdos_83
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that we have a family $\mathcal{F}$ of subsets of $[4n]$ such that $\lvert A\rvert=2n$ for all $A\in\mathcal{F}$ and for every $A,B\in \mathcal{F}$ we have $\lvert A\cap B\rvert \geq 2$. Then $$\lvert \mathcal{F}\rvert \leq \frac{1}{2}\left(\binom{4n}{2n}-\binom{2n}{n}^2\right).$$ Conjectured by Erdős, Ko, and Rado [ErKoRa61]. This inequality would be best possible, as shown by taking $\mathcal{F}$ to be the collection of all subsets of $[4n]$ of size $2n$ containing at least $n+1$ elements from $[2n]$. Proved by Ahlswede and Khachatrian [AhKh97], who more generally showed the following. Let $2\leq t\leq k\leq m$ and let $r\geq 0$ be such that $$\frac{1}{r+1}\leq \frac{m-2k+2t-2}{(t-1)(k-t+1)}< \frac{1}{r}.$$ The largest possible family of subsets of $[m]$ of size $k$, such that the pairwise intersections have size at least $t$, is the family of all subsets of $[m]$ of size $k$ which contain at least $t+r$ elements from $\{1,\ldots,t+2r\}$. The number $\binom{4n}{2n}-\binom{2n}{n}^2$ is even, so the bound is an integer.
- notes: Erdos Problem 83 -- https://www.erdosproblems.com/83
- track: solved
- answer_shape: proof
- source_stem: 83
- mathdb_ref: erdos:83
- source_namespace: Erdos83
- source_theorem: erdos_83
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

abbrev Target : Prop :=
    ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n)
        (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card),
      F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

end Problem
