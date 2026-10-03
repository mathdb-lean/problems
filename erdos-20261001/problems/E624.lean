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

- problem_id: E624
- collection: erdos
- question_id: erdos:624
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/624.lean#erdos_624
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $X$ be a finite set of size $n$ and $H(n)$ be such that there is a function $f:\{A : A\subseteq X\}\to X$ so that for every $Y\subseteq X$ with $\lvert Y\rvert \geq H(n)$ we have $\left\{ f(A) : A\subseteq Y\right\}=X$. Prove that $H(n)-\log_2 n \to \infty$.
- notes: Erdos Problem 624 -- https://www.erdosproblems.com/624
- track: open
- answer_shape: proof
- source_stem: 624
- mathdb_ref: erdos:624
- source_namespace: Erdos624
- source_theorem: erdos_624
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter Finset

/--
The condition that an integer `m` ensures the existence of a function `f` covering `Fin n`
for all large enough subsets `Y`.
The property is invariant under bijection, so we use a representative `Fin n` for a finite set
of size `n`.
-/
def ExistsEventuallySurjective (n m : ℕ) : Prop :=
  ∃ (f : Finset (Fin n) → Fin n),
    ∀ (Y : Finset (Fin n)), #Y ≥ m →
      Y.powerset.image f = Finset.univ

/--
Let $H(n)$ be the minimum integer $m$ such that there is a function $f: \mathcal{P}(X) \to X$
where $X$ is a finite set of size $n$, such that for every subset $Y \subseteq X$ with $|Y| \ge m$,
the set $\{f(A) : A \subseteq Y\}$ covers $X$.
-/
noncomputable def H (n : ℕ) : ℕ :=
  if 0 < n then
    sInf {m : ℕ | ExistsEventuallySurjective n m}
  else 0

abbrev Target : Prop :=
    atTop.Tendsto (fun n : ℕ => H n - Real.logb 2 (n : ℝ)) atTop

end Problem
