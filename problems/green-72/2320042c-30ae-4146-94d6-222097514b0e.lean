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

- problem_id: G72_refute
- collection: green
- question_id: green:72
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/72.lean#green_72
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Green's Open Problem 72 / No-three-in-line problem**: For $N$ sufficiently large, is it impossible to have $2N$ points in $[N]^2$ with no three in a line? Green suspects the answer is yes, and that $(3/2 + o(1))N$ is optimal.
- notes: Green, open problem 72
- track: open
- answer_shape: refute
- pair_id: G72
- pair_role: refute
- source_stem: 72
- source_namespace: Green72
- source_theorem: green_72
- source_category: research open
- source_ams: 5 52
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: allowedSetSize_le
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- We say a subset of $[N]^2$ is allowed for some $k$ if it contains no $k$ points
which lie on a common line. -/
structure AllowedSet (k : ℕ) (N : ℕ) (s : Finset (ℕ × ℕ)) : Prop where
  is_bounded : ∀ i ∈ s, i.1 < N ∧ i.2 < N
  not_collinear : ∀ ⦃t : Finset (ℕ × ℕ)⦄, t ⊆ s → t.card = k →
    ¬ Collinear ℝ ({r | ∃ i ∈ t, r = ((↑i.1 : ℝ), (↑i.2 : ℝ))} : Set (ℝ × ℝ))

/-- The maximal size of an allowed set -/
noncomputable def AllowedSetSize (k : ℕ) (N : ℕ) : ℕ :=
  sSup {r | ∃ s, r = s.card ∧ AllowedSet k N s}

/-- The proposition that the allowed-set size for $k$ and $N$ is $(k - 1) * N$. -/
def NoKInLineFor (k : ℕ) (N : ℕ) : Prop :=
  AllowedSetSize k N = (k - 1) * N

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- By the pigeon hole principle, the size of a subset of an $N \times N$ grid such that no $k$
points lie on a line is bounded by $\leq (k - 1) * N$. -/
@[category textbook, AMS 5 52]
theorem allowedSetSize_le {k : ℕ} {N : ℕ} :
    AllowedSetSize k N ≤ (k - 1) * N := by
  refine csSup_le' ?_
  rintro r ⟨s, rfl, hs⟩
  -- Every column of the grid meets an allowed set in at most $k - 1$ points, since $k$ points
  -- sharing a first coordinate lie on a common vertical line.
  have key : ∀ x ∈ Finset.range N, (s.filter fun i => i.1 = x).card ≤ k - 1 := by
    intro x _
    by_contra hc
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := k)
      (s := s.filter fun i => i.1 = x) (by omega)
    refine hs.not_collinear (hts.trans (Finset.filter_subset _ _)) htc ?_
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    refine ⟨((x : ℝ), 0), (0, 1), ?_⟩
    rintro p ⟨i, hi, rfl⟩
    exact ⟨i.2, by simp [(Finset.mem_filter.mp (hts hi)).2]⟩
  calc s.card
      = ∑ x ∈ Finset.range N, (s.filter fun i => i.1 = x).card :=
        Finset.card_eq_sum_card_fiberwise fun i hi => Finset.mem_range.mpr (hs.is_bounded i hi).1
    _ ≤ ∑ _x ∈ Finset.range N, (k - 1) := Finset.sum_le_sum key
    _ = (k - 1) * N := by simp [mul_comm]

abbrev Target : Prop :=
    ¬ (
      ∀ᶠ N in Filter.atTop, ¬ NoKInLineFor 3 N
    )

end Problem
