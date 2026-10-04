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

- problem_id: E283
- collection: erdos
- question_id: erdos:283
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/283.lean#erdos_283
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $p\colon \mathbb{Z} \rightarrow \mathbb{Z}$ be a polynomial (with rational coefficients, taking integer values at all integers) whose leading coefficient is positive and such that there exists no $d≥2$ with $d ∣ p(n)$ for all $n≥1$. Is it true that, for all sufficiently large $m$, there exist integers $1≤n_1<\dots < n_k$ such that $$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$ and $$m=p(n_1)+\cdots+p(n_k)$$? GPT 5.5 Pro (prompted by Price) has given a proof that the answer is yes, for the stronger version with $1$ replaced by any rational $\alpha>0$. This was formalized in Lean by Ammanamanchi using Opus 4.6 and GPT 5.5 Pro.
- notes: Erdos Problem 283 -- https://www.erdosproblems.com/283
- track: solved
- answer_shape: decide
- source_stem: 283
- mathdb_ref: erdos:283
- source_namespace: Erdos283
- source_theorem: erdos_283
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Polynomial Finset

namespace Problem

/--
Given a polynomial `p` with rational coefficients, the predicate that if `p` takes integer values
at all integers, the leading coefficient is positive and there exists no $d≥2$ with $d ∣ p(n)$ for
all $n≥1$, then for all sufficiently large $m$, there exist integers $1≤n_1<\dots < n_k$ such that
$$1=\frac{1}{n_1}+\cdots+\frac{1}{n_k}$$ and $$m=p(n_1)+\cdots+p(n_k)$$?
-/
def Condition (p : ℚ[X]) : Prop :=
  (∀ n : ℤ, ∃ z : ℤ, p.eval (n : ℚ) = z) → p.leadingCoeff > 0 →
  ¬ (∃ d : ℤ, d ≥ 2 ∧ ∀ n : ℤ, n ≥ 1 → ∃ z : ℤ, p.eval (n : ℚ) = d * z) →
  ∀ᶠ (m : ℤ) in atTop, ∃ k ≥ 1, ∃ n : Fin (k + 1) → ℤ, 0 = n 0 ∧ StrictMono n ∧
  1 = ∑ i ∈ Finset.Icc 1 (Fin.last k), (1 : ℚ) / (n i) ∧
  (m : ℚ) = ∑ i ∈ Finset.Icc 1 (Fin.last k), p.eval (n i : ℚ)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ p : ℚ[X], Condition p

end Problem
