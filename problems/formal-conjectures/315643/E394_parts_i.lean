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

- problem_id: E394_parts_i
- collection: erdos
- question_id: erdos:394
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/394.lean#erdos_394.parts.i
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $\sum_{n\leq x}t_2(n)\ll \frac{x^2}{(\log x)^c}$ for some $c>0$?
- notes: Erdos Problem 394 -- https://www.erdosproblems.com/394
- track: solved
- answer_shape: decide
- source_stem: 394
- mathdb_ref: erdos:394
- source_namespace: Erdos394
- source_theorem: erdos_394.parts.i
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: t_eq_of t_one
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: True
-/

open Nat Filter Finset
open scoped Asymptotics Topology Nat

namespace Problem

/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- `t k n = v` when `v` works and nothing positive below it does. -/
@[category API, AMS 11]
theorem t_eq_of {n k v : ℕ} (hv : 0 < v)
    (hdvd : n ∣ ∏ i ∈ range k, (v + i))
    (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    t k n = v := by
  refine le_antisymm (Nat.sInf_le ⟨hv, hdvd⟩) ?_
  by_contra! hc
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }.Nonempty := ⟨v, hv, hdvd⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  exact hlt _ (mem_range.mpr hc) hpos hd

/-- The least positive multiple of `n` is `n`, so `t 1 n = n`. -/
@[category API, AMS 11]
theorem t_one {n : ℕ} (hn : 0 < n) : t 1 n = n := by
  refine le_antisymm (Nat.sInf_le ⟨hn, by simp⟩) ?_
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range 1, (m + i) }.Nonempty := ⟨n, hn, by simp⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  rw [prod_range_one, add_zero] at hd
  exact Nat.le_of_dvd hpos hd

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
      ∃ c > (0 : ℝ), (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊,
      (t 2 n : ℝ)) ≪ (fun x ↦ x ^ 2 / (Real.log x) ^ c)

end Problem
