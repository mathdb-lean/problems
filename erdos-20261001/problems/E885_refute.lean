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

- problem_id: E885_refute
- collection: erdos
- question_id: erdos:885
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/885.lean#erdos_885
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that, for every $k \geq 1$, there exist integers $N_1 < \dots < N_k$ such that $|\cap_i D(N_i)| \geq k$?
- notes: Erdos Problem 885 -- https://www.erdosproblems.com/885
- track: open
- answer_shape: refute
- pair_id: E885
- pair_role: refute
- source_stem: 885
- mathdb_ref: erdos:885
- source_namespace: Erdos885
- source_theorem: erdos_885
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: mem_factorDifferenceSet_of_eq factorDifferenceSet_finite
- generator: adapters/formal_conjectures/adapter.py
-/

open Nat Set Finset

namespace Problem

/--
For integer $n \geq 1$ we define the factor difference set of $n$ by
$D(n) = \{|a-b| : n=ab\}$.
-/
def factorDifferenceSet (n : ℕ) : Set ℕ :=
  {d | ∃ a b : ℕ, n = a * b ∧ (d : ℤ) = |(a : ℤ) - b|}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category API, AMS 11]
lemma mem_factorDifferenceSet_of_eq {n d b : ℕ} (h : n = b * (b + d)) :
    d ∈ factorDifferenceSet n :=
  ⟨b, b + d, h, by push_cast; rw [show (b : ℤ) - (b + d) = -d by ring, abs_neg,
    abs_of_nonneg (by positivity)]⟩

@[category API, AMS 11]
lemma factorDifferenceSet_finite {n : ℕ} (hn : 1 ≤ n) : (factorDifferenceSet n).Finite := by
  refine (Set.finite_Iic n).subset ?_
  rintro d ⟨a, b, rfl, hd⟩
  have ha : 1 ≤ a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hb : 1 ≤ b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have h1 : (a : ℤ) ≤ a * b := by exact_mod_cast Nat.le_mul_of_pos_right a hb
  have h2 : (b : ℤ) ≤ a * b := by exact_mod_cast Nat.le_mul_of_pos_left b ha
  have : (d : ℤ) ≤ a * b := hd ▸ abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  exact_mod_cast this

abbrev Target : Prop :=
    ¬ (
      ∀ k ≥ 1,
          ∃ Ns : Finset ℕ,
            (∀ n ∈ Ns, 1 ≤ n) ∧
            Ns.card = k ∧
            (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k
    )

end Problem
