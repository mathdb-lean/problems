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

- problem_id: E1133_refute
- collection: erdos
- question_id: erdos:1133
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1133.lean#erdos_1133
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $C>0$. There exists $\epsilon>0$ such that if $n$ is sufficiently large the following holds. For any $x_1,\ldots,x_n\in [-1,1]$ there exist $y_1,\ldots,y_n\in [-1,1]$ such that, if $P$ is a polynomial of degree $m<(1+\epsilon)n$ with $P(x_i)=y_i$ for at least $(1-\epsilon)n$ many $1\leq i\leq n$, then $$\max_{x\in [-1,1]}\lvert P(x)\rvert >C.$$
- notes: Erdos Problem 1133 -- https://www.erdosproblems.com/1133
- track: open
- answer_shape: refute
- pair_id: E1133
- pair_role: refute
- source_stem: 1133
- mathdb_ref: erdos:1133
- source_namespace: Erdos1133
- source_theorem: erdos_1133
- source_category: research open
- source_ams: 26 41
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter Set

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∀ C > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        ∀ x : Fin n → Icc (-1 : ℝ) 1,
          ∃ y : Fin n → Icc (-1 : ℝ) 1,
            ∀ P : Polynomial ℝ,
              (P.natDegree : ℝ) < (1 + ε) * (n : ℝ) →
              ((Finset.univ.filter (fun i ↦ P.eval (x i : ℝ) = (y i : ℝ))).card : ℝ) ≥
                (1 - ε) * (n : ℝ) →
              ∃ z ∈ Icc (-1 : ℝ) 1, |P.eval z| > C
    )

end Problem
