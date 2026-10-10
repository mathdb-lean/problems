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

- problem_id: E609
- collection: erdos
- question_id: erdos:609
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/609.lean#erdos_609
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $f(n)$ be the minimal $m$ such that if the edges of $K_{2^n+1}$ are coloured with $n$ colours then there must be a monochromatic odd cycle of length at most $m$. Estimate $f(n)$.
- notes: Erdos Problem 609 -- https://www.erdosproblems.com/609
- track: open
- answer_shape: value
- answer_type: ℕ → ℝ
- answer_pinned: false
- answer_pinned_reason: relation_is_reflexive
- source_stem: 609
- mathdb_ref: erdos:609
- source_namespace: Erdos609
- source_theorem: erdos_609
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter

namespace Problem

/--
The monochromatic subgraph of color `i` under edge coloring `c : Sym2 V → Fin n`.
-/
def monochromaticGraph {V : Type*} {n : ℕ} (c : Sym2 V → Fin n) (i : Fin n) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v ↦ c s(u, v) = i)

/--
A coloring `c` has a monochromatic odd cycle of length at most `m`.
-/
def MonochromaticHasOddCycleLe (n : ℕ) (m : ℕ) (c : Sym2 (Fin (2 ^ n + 1)) → Fin n) : Prop :=
  ∃ (i : Fin n) (l : ℕ), l ∈ (monochromaticGraph c i).oddCycleLengths ∧ l ≤ m

/--
$f(n)$ is the minimal $m$ such that if the edges of $K_{2^n+1}$ are coloured with $n$ colours
then there must be a monochromatic odd cycle of length at most $m$.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (c : Sym2 (Fin (2 ^ n + 1)) → Fin n), MonochromaticHasOddCycleLe n m c}

abbrev Target (value : ℕ → ℝ) : Prop :=
    (fun n ↦ (f n : ℝ)) =Θ[atTop] value

end Problem
