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

- problem_id: E385_parts_i_refute
- collection: erdos
- question_id: erdos:385
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/385.lean#erdos_385.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $F(n) := \max\{m + p(m) \mid \textrm{$m < n$ composite}\}\}$ where $p(m)$ is the least prime divisor of $m$. Is it true that $F(n)>n$ for all sufficiently large $n$?
- notes: Erdos Problem 385 -- https://www.erdosproblems.com/385
- track: open
- answer_shape: refute
- pair_id: E385_parts_i
- pair_role: refute
- source_stem: 385
- mathdb_ref: erdos:385
- source_namespace: Erdos385
- source_theorem: erdos_385.parts.i
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: trivial_ub
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

open Filter

/-- Let $F(n) := \max\{m + p(m) \mid  \textrm{$m < n$ composite}\}\}$ where $p(m)$ is the least
prime divisor of $m$. -/
noncomputable def F (n : ℕ) : ℕ := sSup {m + m.minFac | (m < n) (_ : m.Composite)}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Note that trivially $F(n) \leq n + \sqrt{n}$. -/
@[category test, AMS 11]
theorem trivial_ub (n : ℕ) : F n ≤ n + √n := by
  have hkey : F n ≤ n + n.sqrt := by
    apply csSup_le'
    rintro x ⟨m, hm, hcomp, rfl⟩
    have h1 : 0 < m := by have := hcomp.1; omega
    have hsq : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self h1 hcomp.2
    have hmf : m.minFac ≤ m.sqrt := Nat.le_sqrt.mpr (by rw [← sq]; exact hsq)
    have hmn : m.sqrt ≤ n.sqrt := Nat.sqrt_le_sqrt hm.le
    omega
  calc (F n : ℝ) ≤ ((n + n.sqrt : ℕ) : ℝ) := by exact_mod_cast hkey
    _ = n + (n.sqrt : ℝ) := by push_cast; ring
    _ ≤ n + √n := by
        gcongr
        rw [show ((n.sqrt : ℕ) : ℝ) = √((n.sqrt ^ 2 : ℕ) : ℝ) from by
          push_cast; rw [Real.sqrt_sq (Nat.cast_nonneg _)]]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' n)

abbrev Target : Prop :=
    ¬ (
      ∀ᶠ n in atTop, n < F n
    )

end Problem
