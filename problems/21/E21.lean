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

- problem_id: E21
- collection: erdos
- question_id: erdos:21
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/21.lean#erdos_21
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be minimal such that there is an intersecting family $\mathcal{F}$ of sets of size $n$ (so $A\cap B\neq\emptyset$ for all $A,B\in \mathcal{F}$) with $\lvert \mathcal{F}\rvert=f(n)$ such that any set $S$ with $\lvert S\rvert \leq n-1$ is disjoint from at least one $A\in \mathcal{F}$. Is it true that $$f(n) \ll n?$$ Conjectured by Erdős and Lovász [ErLo75], who proved that $$\frac{8}{3}n-3\leq f(n) \ll n^{3/2}\log n$$ for all $n$. The upper bound was improved by Kahn [Ka92b] to $f(n) \ll n\log n$. (The upper bound constructions in both cases are formed by taking a random set of lines from a projective plane of order $n-1$, assuming $n-1$ is a prime power.) This problem was solved by Kahn [Ka94] who proved the upper bound $f(n) \ll n$. The Erdős-Lovász lower bound of $\frac{8}{3}n-O(1)$ has not been improved, and it has been speculated (see e.g. [Ka94]) that the correct answer is $3n+O(1)$. It is trivial that $f(1)=1$ and $f(2)=3$. The values $f(3)=6$ and $f(4)=9$ were established by Tripathi [Tr14]. Barát and Wanless [BaWa21] proved that $f(5)=13$, and that $13\leq f(6)\leq 18$.
- notes: Erdos Problem 21 -- https://www.erdosproblems.com/21
- track: solved
- answer_shape: decide
- source_stem: 21
- mathdb_ref: erdos:21
- source_namespace: Erdos21
- source_theorem: erdos_21
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter

namespace Problem

/-- An Erdős–Lovász family of order `n`: an intersecting family of `n`-sets such that every set
of size at most `n - 1` is disjoint from some member. -/
def IsErdosLovaszFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
    ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/-- `f n` is the minimal size of an Erdős–Lovász family of order `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, f n ≤ C * n

end Problem
