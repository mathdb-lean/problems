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

- problem_id: E841
- collection: erdos
- question_id: erdos:841
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/841.lean#erdos_841
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $t_n$ be minimal such that $\{n+1,\ldots,n+t_n\}$ contains a subset whose product with $n$ is a square number (and let $t_n=0$ if $n$ is itself square). Estimate $t_n$. A problem of Erdős, Graham, and Selfridge. For example, $t_6=6$ since $6\cdot 8\cdot 12=24^2$. It is trivial that $t_n\geq P(n)$, where $P(n)$ is the largest prime divisor of $n$. Bui, Pratt, and Zaharescu [BPZ24] proved that the distribution of $t_n$ continues to follow $P(n)$, in that for any fixed $c\in (0,1]$ $$\lim_{x\to \infty}\frac{\lvert \{ n\leq x : t_n\leq n^c\}\rvert}{x} = \lim_{x\to \infty}\frac{\lvert \{ n\leq x : P(n)\leq n^c\}\rvert}{x}.$$ The statement below is that the difference of the two counting functions is $o(x)$. This was formalized in Lean by Codex.
- notes: Erdos Problem 841 -- https://www.erdosproblems.com/841
- track: solved
- answer_shape: proof
- source_stem: 841
- mathdb_ref: erdos:841
- source_namespace: Erdos841
- source_theorem: erdos_841
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Real Topology

namespace Problem

/-- `t n` is the least `T` such that `{n + 1, …, n + T}` contains a subset whose product with `n`
is a square; `t n = 0` if and only if `n` is itself a square. -/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {T | ∃ J ⊆ Finset.Icc 1 T, IsSquare (n * ∏ j ∈ J, (n + j))}

open scoped Classical in
abbrev Target : Prop :=
    ∀ (c : ℝ) (hc : c ∈ Set.Ioc 0 1),
      Tendsto (fun x : ℕ ↦
        ((((Finset.Icc 1 x).filter fun n : ℕ ↦ (t n : ℝ) ≤ (n : ℝ) ^ c).card : ℝ) -
          ((Finset.Icc 1 x).filter fun n : ℕ ↦ (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ c).card) / x)
        atTop (𝓝 0)

end Problem
