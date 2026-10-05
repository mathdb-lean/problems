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

- problem_id: X2104_00502_BarkerSequence_barker_conjecture
- collection: arxiv
- question_id: arxiv:2104.00502/BarkerSequence
- source: formal-conjectures
- source_locator: FormalConjectures/Arxiv/2104.00502/BarkerSequence.lean#barker_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Every Barker sequence has length at most $13$.
- notes: arXiv 2104.00502/BarkerSequence -- https://arxiv.org/abs/2104.00502
- track: open
- answer_shape: proof
- source_stem: 2104.00502/BarkerSequence
- source_namespace: Arxiv.«2104.00502»
- source_theorem: barker_conjecture
- source_category: research open
- source_ams: 5 11 94
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: isBarkerSequence_length_thirteen isBarkerSequence_length_four not_isBarkerSequence_constant_four
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/-- The aperiodic autocorrelation $C_k(a)=\sum_i a_i a_{i+k}$. -/
def aperiodicAutocorrelation (a : List ℤ) (k : ℕ) : ℤ :=
  (List.zipWith (· * ·) a (a.drop k)).sum

/--
A Barker sequence has $\pm 1$ entries and nontrivial autocorrelations of magnitude at most one.
-/
def IsBarkerSequence (a : List ℤ) : Prop :=
  (∀ x ∈ a, x = 1 ∨ x = -1) ∧
    ∀ k : ℕ, 0 < k → k < a.length → |aperiodicAutocorrelation a k| ≤ 1

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
The known sequence $(1,1,1,1,1,-1,-1,1,1,-1,1,-1,1)$ of length $13$ is a Barker sequence.
-/
@[category test, AMS 5 11 94]
theorem isBarkerSequence_length_thirteen :
    IsBarkerSequence [1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1] := by
  constructor
  · simp
  · intro k hkpos hklen
    norm_num at hklen
    interval_cases k <;>
      norm_num [aperiodicAutocorrelation] at hkpos ⊢

/-- The sequence $(1,1,1,-1)$ is a Barker sequence. -/
@[category test, AMS 5 11 94]
theorem isBarkerSequence_length_four : IsBarkerSequence [1, 1, 1, -1] := by
  constructor
  · simp
  · intro k hkpos hklen
    norm_num at hklen
    interval_cases k <;>
      norm_num [aperiodicAutocorrelation] at hkpos ⊢

/-- The constant sequence $(1,1,1,1)$ is not a Barker sequence. -/
@[category test, AMS 5 11 94]
theorem not_isBarkerSequence_constant_four : ¬ IsBarkerSequence [1, 1, 1, 1] := by
  intro ha
  have h := ha.2 1 (by norm_num) (by norm_num)
  norm_num [aperiodicAutocorrelation] at h

abbrev Target : Prop :=
    ∀ (a : List ℤ) (ha : IsBarkerSequence a),
      a.length ≤ 13

end Problem
