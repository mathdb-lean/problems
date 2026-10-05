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

- problem_id: E185
- collection: erdos
- question_id: erdos:185
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/185.lean#erdos_185
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f_3(n)$ be the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points on a line. Is it true that $f_3(n)=o(3^n)$? Originally considered by Moser. It is trivial that $f_3(n)\geq R_3(3^n)$, the maximal size of a subset of $\{1,\ldots,3^n\}$ without a three-term arithmetic progression. Moser showed that $$f_3(n) \gg \frac{3^n}{\sqrt{n}}.$$ The answer is yes, which is a corollary of the density Hales-Jewett theorem, proved by Furstenberg and Katznelson [FuKa91].
- notes: Erdos Problem 185 -- https://www.erdosproblems.com/185
- track: solved
- answer_shape: decide
- source_stem: 185
- mathdb_ref: erdos:185
- source_namespace: Erdos185
- source_theorem: erdos_185
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Filter Asymptotics

namespace Problem

/-- $f_3(n)$ is the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points on a
line (in $\mathbb{R}^n$). -/
noncomputable def f3 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset (Fin n → Fin 3),
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z →
      ¬ Collinear ℝ ({fun i => ((x i : ℕ) : ℝ), fun i => ((y i : ℕ) : ℝ),
        fun i => ((z i : ℕ) : ℝ)} : Set (Fin n → ℝ))) ∧ A.card = m}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ (fun n : ℕ => (f3 n : ℝ)) =o[atTop] fun n : ℕ => (3 : ℝ) ^ n

end Problem
