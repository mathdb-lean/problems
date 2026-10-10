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

- problem_id: E1138
- collection: erdos
- question_id: erdos:1138
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1138.lean#erdos_1138
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 1138.** Let $x/2 < y < x$ and $C > 1$. If $d = \max_{p_n < x}(p_{n+1} - p_n)$, where $p_n$ denotes the $n$-th prime, then is it true that $$\pi(y + Cd) - \pi(y) \sim \frac{Cd}{\log y}$$?
- notes: Erdos Problem 1138 -- https://www.erdosproblems.com/1138
- track: solved
- answer_shape: decide
- source_stem: 1138
- mathdb_ref: erdos:1138
- source_namespace: Erdos1138
- source_theorem: erdos_1138
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat Filter Asymptotics Real Set

namespace Problem

/--
The maximal prime gap below $x$, i.e. $d(x) = \max_{p_n < x}(p_{n+1} - p_n)$, where $p_n$
denotes the $n$-th prime.
-/
noncomputable def sup_primeGap (x : ℝ) : ℕ := (Finset.range (primeCounting' ⌈x⌉₊)).sup primeGap

/--
The filter on $\mathbb{R} \times \mathbb{R}$ corresponding to sending $x \to \infty$ subject to $x/2 < y < x$
-/
abbrev snd_gt_half_fst : Filter (ℝ × ℝ) := atTop.comap Prod.fst ⊓ 𝓟 {p | p.2 ∈ Ioo (p.1 / 2) p.1}

/-- Given a pair $(x,y)$, this is the amount of primes in the interval above $y$, of length
equalling the largest prime gap before $x$, scaled by a constant $C$.
-/
noncomputable def primeCount_Ioc_mul_const (C : ℝ) : (ℝ × ℝ) → ℝ :=
  fun (x, y) ↦ (primeCounting ⌊y + C * sup_primeGap x⌋₊ - primeCounting ⌊y⌋₊)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀C > 1,
        primeCount_Ioc_mul_const C ~[snd_gt_half_fst] fun (x, y) ↦
          C * (sup_primeGap x) / Real.log y

end Problem
