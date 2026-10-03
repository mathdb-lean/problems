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

- problem_id: E769
- collection: erdos
- question_id: erdos:769
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/769.lean#erdos_769
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $c(n)$ be minimal such that if $k\geq c(n)$ then the $n$-dimensional unit cube can be decomposed into $k$ homothetic $n$-dimensional cubes. Give good bounds for $c(n)$ — in particular, is it true that $c(n)\gg n^n$? The `c(n) \gg n^n` conjecture is **false**: for odd `n`, one can tile the unit `n`-cube into `k` homothetic cubes for every `k ≥ U(n)` with `U(n)/n^n → 0`, so `c(n)/n^n → 0` along odd dimensions and no absolute constant lower-bounds it. Determining good bounds for `c(n)` in general remains open.
- notes: Erdos Problem 769 -- https://www.erdosproblems.com/769
- track: solved
- answer_shape: decide
- source_stem: 769
- mathdb_ref: erdos:769
- source_namespace: Erdos769
- source_theorem: erdos_769
- source_category: research solved
- source_ams: 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

open Filter

open scoped Topology

/-- An axis-parallel homothetic copy of the standard `n`-cube. -/
structure Cube (n : ℕ) where
  lower : Fin n → ℝ
  side : ℝ

/-- Membership in the half-open cube `∏ j, [lower j, lower j + side)`. -/
def Cube.Mem {n : ℕ} (Q : Cube n) (x : Fin n → ℝ) : Prop :=
  ∀ j, Q.lower j ≤ x j ∧ x j < Q.lower j + Q.side

/-- Membership in the half-open unit cube `[0,1)^n`. -/
def InUnit {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j < 1

/-- A cube is nondegenerate and contained in the closed unit cube. -/
def Cube.InsideUnit {n : ℕ} (Q : Cube n) : Prop :=
  0 < Q.side ∧ ∀ j, 0 ≤ Q.lower j ∧ Q.lower j + Q.side ≤ 1

/-- `tiles` is an exact decomposition of the unit `n`-cube into `k` homothetic
cubes: every tile is a positive homothet inside the unit cube, and every point
of `[0,1)^n` belongs to exactly one half-open tile. -/
def IsTiling {n k : ℕ} (tiles : Fin k → Cube n) : Prop :=
  (∀ i, (tiles i).InsideUnit) ∧ ∀ x, InUnit x → ∃! i, (tiles i).Mem x

/-- Exactly `k` homothetic `n`-cubes can tile the unit `n`-cube. -/
def Admissible (n k : ℕ) : Prop :=
  ∃ tiles : Fin k → Cube n, IsTiling tiles

/-- `c` is the minimal cutoff `c(n)`: every `k ≥ c` is admissible, and (when
`c > 0`) `c - 1` is not. -/
def IsCutoff (n c : ℕ) : Prop :=
  (∀ k, c ≤ k → Admissible n k) ∧ (c = 0 ∨ ¬Admissible n (c - 1))

/-- The highlighted conjecture `c(n) ≫ n^n`: there is an absolute positive
constant `A/B` with `c(n) ≥ (A/B) n^n` for all sufficiently large `n`. -/
def Erdos769LowerBound : Prop :=
  ∃ A B N : ℕ, 0 < A ∧ 0 < B ∧
    ∀ n c : ℕ, N ≤ n → IsCutoff n c → A * n ^ n ≤ B * c

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Erdos769LowerBound

end Problem
