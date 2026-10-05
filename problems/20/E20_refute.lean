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

- problem_id: E20_refute
- collection: erdos
- question_id: erdos:20
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/20.lean#erdos_20
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Is it true that $f(n,k) < c_k^n$ for some constant $c_k>0$ and for all $n > 0$?
- notes: Erdos Problem 20 -- https://www.erdosproblems.com/20
- track: open
- answer_shape: refute
- pair_id: E20
- pair_role: refute
- source_stem: 20
- mathdb_ref: erdos:20
- source_namespace: Erdos20
- source_theorem: erdos_20
- source_category: research open
- source_ams: 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: f_0_1
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
Let $f(n,k)$ be minimal such that every $F$ family of $n$-uniform sets with $|F| \ge f(n,k)$
contains a $k$-sunflower.
-/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ f ∈ F, f.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 5]
theorem f_0_1 : f 0 1 = 1 := by
  refine IsLeast.csInf_eq ⟨fun F hF ↦ ?_, fun n hn ↦ n.pos_of_ne_zero fun hn₀ ↦ ?_⟩
  · obtain ⟨A, hA⟩ := F.nonempty_of_ncard_ne_zero (by omega)
    exact ⟨{A}, by simpa using ⟨hA, isSunflower_singleton _⟩⟩
  · obtain ⟨S, hS⟩ := (hn (α := ℕ) {} (by simpa))
    simp_all [bot_unique hS.1]

abbrev Target : Prop :=
    ¬ (
      ∃ (c : ℕ → ℕ), ∀ n k, n > 0 → f n k < (c k) ^ n
    )

end Problem
