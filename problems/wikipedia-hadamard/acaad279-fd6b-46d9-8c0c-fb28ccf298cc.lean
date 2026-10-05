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

- problem_id: NHadamard_HadamardConjecture
- collection: wikipedia
- question_id: wikipedia:Hadamard
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/Hadamard.lean#HadamardConjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: There exists a Hadamard matrix for all $n = 4k$.
- notes: Wikipedia: Hadamard -- https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture
- track: open
- answer_shape: proof
- source_stem: Hadamard
- source_namespace: Hadamard
- source_theorem: HadamardConjecture
- source_category: research open
- source_ams: 15
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: exists_hadamard_zero isHadamard_H12
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

/--
A square matrix $M$ with $±1$-entries that satisfies the equality $|M| ≤ n^\frac{n}{2}$ is called a *Hadamard matrix*.
-/
def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

/--
Equivalently, a square matrix $M$ with $±1$-entries $|A| ≤ n^\frac{n}{2}.$ if it satisfies the equality
$M^TM = n \cdot 1$, where $1$ denotes the unit matrix.
-/
def IsHadamard' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    M.transpose * M = ↑n

/--
Hadamard constructs a 12 x 12 matrix ...
-/
def H12 : Matrix (Fin 12) (Fin 12) ℝ :=
!![  1,  1,  1,   1,  1,  1,   1,  1,  1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,  -1, -1, -1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,   1,  1,  1,  -1, -1, -1;
     1, -1, -1,   1, -1, -1,  -1,  1,  1,  -1,  1,  1;
     1, -1, -1,  -1,  1, -1,   1, -1,  1,   1, -1,  1;
     1, -1, -1,  -1, -1,  1,   1,  1, -1,   1,  1, -1;
     1, -1,  1,  -1,  1,  1,  -1,  1, -1,  -1, -1,  1;
     1, -1,  1,   1, -1,  1,  -1, -1,  1,   1, -1, -1;
     1, -1,  1,   1,  1, -1,   1, -1, -1,  -1,  1, -1;
     1,  1, -1,  -1,  1,  1,  -1, -1,  1,  -1,  1, -1;
     1,  1, -1,   1, -1,  1,   1, -1, -1,  -1, -1,  1;
     1,  1, -1,   1,  1, -1,  -1,  1, -1,   1, -1, -1 ]

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

@[category test, AMS 15]
theorem exists_hadamard_zero : ∃ M, IsHadamard (n := 0) M := by
  use 0
  simp [IsHadamard]

/--
which satisfies the condition.
-/
@[category test, AMS 15]
theorem isHadamard_H12 : IsHadamard H12 := by
  have h : H12.transpose * H12 = (12 : ℝ) • 1 := by
    rw [← Matrix.ext_iff]
    norm_num +decide [Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_succ, H12,
      Matrix.one_apply]
  have hd : H12.det ^ 2 = 12 ^ 12 := by simpa [Matrix.det_smul, ← sq] using congrArg Matrix.det h
  refine ⟨by simp [Fin.forall_fin_succ, H12], ?_⟩
  rw [← Real.sqrt_sq_eq_abs, hd]
  norm_num

abbrev Target : Prop :=
    ∀ (k : ℕ),
      ∃ M, IsHadamard (n := 4 * k) M

end Problem
