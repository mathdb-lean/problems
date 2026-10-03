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

- problem_id: E136
- collection: erdos
- question_id: erdos:136
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/136.lean#erdos_136
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be the smallest number of colours required to colour the edges of $K_n$ such that every $K_4$ contains at least $5$ colours. Determine the size of $f(n)$. Asked by Erdős and Gyárfás [Er97b], who proved $\frac56 (n - 1) < f(n) < n$ and $f(9) = 8$; Erdős believed that the upper bound is closer to the truth. In fact $f(n) \sim \frac56 n$, as shown by Bennett, Cushman, Dudek and Pralat [BCDP22]; Joos and Mubayi [JoMu22] found a shorter proof.
- notes: Erdos Problem 136 -- https://www.erdosproblems.com/136
- track: solved
- answer_shape: proof
- source_stem: 136
- mathdb_ref: erdos:136
- source_namespace: Erdos136
- source_theorem: erdos_136
- source_category: research solved
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Topology

namespace Problem

/-- An edge colouring of `K_n` with `k` colours is a `(4, 5)`-colouring if the six edges of every
copy of `K_4` receive at least five distinct colours. -/
def Is45Coloring {n k : ℕ} (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k)) : Prop :=
  open scoped Classical in
  ∀ v : Fin 4 ↪ Fin n, 5 ≤ (Finset.univ.image (C.pullback v)).card

/-- `K_n` admits a `(4, 5)`-colouring with `k` colours. -/
def Colorable (n k : ℕ) : Prop :=
  ∃ C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin k), Is45Coloring C

/-- `f n` is the least number of colours in a `(4, 5)`-colouring of `K_n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k | Colorable n k}

abbrev Target : Prop :=
    Tendsto (fun n : ℕ ↦ (f n : ℝ) / (n : ℝ)) atTop (𝓝 (5 / 6 : ℝ))

end Problem
