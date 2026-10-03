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

- problem_id: E648
- collection: erdos
- question_id: erdos:648
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/648.lean#erdos_648
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $g(n)$ denote the largest $t$ such that there exist integers $2\leq a_1<a_2<\cdots <a_t <n$ such that $$P(a_1)>P(a_2)>\cdots >P(a_t)$$ where $P(m)$ is the greatest prime factor of $m$. Estimate $g(n)$. Stijn Cambie has proved [Ca25b] $$g(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}.$$ Cambie further asks whether there exists a constant $c$ such that $$g(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}.$$ Cambie's proof shows that such a $c$ must satisfy $2\leq c\leq 2\sqrt{2}$. The sequence $a_1<a_2<\cdots<a_t$ is packaged as a strictly monotone map `a : Fin t → ℕ` with $2\leq a_i<n$, the greatest prime factor $P$ is `Nat.maxPrimeFac`, and $g(n)$ is the supremum in `ℕ` of the achievable lengths $t$.
- notes: Erdos Problem 648 -- https://www.erdosproblems.com/648
- track: solved
- answer_shape: proof
- source_stem: 648
- mathdb_ref: erdos:648
- source_namespace: Erdos648
- source_theorem: erdos_648
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Asymptotics

namespace Problem

/-
Divergences from the hosted theorems (details in statements/648/draft.json):
- the sequence range follows the problem text, `2 ≤ a_1 < ⋯ < a_t < n` (`Set.Ico 2 n`);
  both hosted theorems allow `0 < m ≤ n` (`Set.Ioc 0 n`), which admits `1` and `n`.
- `P` is the FC-house `Nat.maxPrimeFac`; the hosted files define
  `P n = (n.primeFactors.max).getD 1`. The two agree on `2 ≤ m`.
- the sequence is a strictly monotone `a : Fin t → ℕ` (FC house shape); the hosted
  theorems use a `List ℕ` with `IsChain`.
-/

/--
`g n` is the largest `t` such that there exist integers `2 ≤ a 0 < a 1 < ⋯ < a (t - 1) < n`
whose greatest prime factors are strictly decreasing. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {t | ∃ a : Fin t → ℕ, StrictMono a ∧ (∀ i, a i ∈ Set.Ico 2 n) ∧
    StrictAnti fun i => (a i).maxPrimeFac}

abbrev Target : Prop :=
    (fun n => (g n : ℝ)) =Θ[atTop] fun n => Real.sqrt ((n : ℝ) / Real.log (n : ℝ))

end Problem
