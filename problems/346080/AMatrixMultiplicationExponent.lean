/-
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

import FormalConjecturesUtil

/-!
Stated in this library, not converted from another corpus: `source` is this
repository, `source_locator` this file, and `source_version` the commit that
holds it. The definitions are self-contained so that the obligation means the
same thing whatever Mathlib later adds.

- problem_id: AMatrixMultiplicationExponent
- collection: authored
- question_id: authored:MatrixMultiplicationExponent
- source: mathdb-lean
- source_locator: authored/MatrixMultiplicationExponent.lean#Target
- prose: The exponent of matrix multiplication is two: for every ε > 0, the tensor rank of the n × n matrix multiplication tensor over ℂ is O(n ^ (2 + ε)).
- notes: Exponent of matrix multiplication -- https://en.wikipedia.org/wiki/Computational_complexity_of_matrix_multiplication#Matrix_multiplication_exponent
- track: open
- answer_shape: proof
- source_category: research open
- source_ams: 68 15
- generator: adapters/authored/adapter.py
-/

namespace Problem

/-- `TensorRankLE T r`: the three-way array `T` is a sum of at most `r` rank-one tensors
`u ⊗ v ⊗ w`. -/
def TensorRankLE {a b c : ℕ} (T : Fin a → Fin b → Fin c → ℂ) (r : ℕ) : Prop :=
  ∃ (u : Fin r → Fin a → ℂ) (v : Fin r → Fin b → ℂ) (w : Fin r → Fin c → ℂ),
    ∀ i j k, T i j k = ∑ s, u s i * v s j * w s k

/-- The tensor rank of `T`: the least `r` such that `T` is a sum of `r` rank-one tensors.
Every tensor is a sum of `a * b * c` rank-one tensors, so the set is nonempty and the
infimum over `ℕ` is attained. -/
noncomputable def tensorRank {a b c : ℕ} (T : Fin a → Fin b → Fin c → ℂ) : ℕ :=
  sInf {r | TensorRankLE T r}

/-- The matrix multiplication tensor `⟨n, n, n⟩` over `ℂ`. Each of its three indices is a
matrix position, a pair in `Fin n × Fin n` packed into `Fin (n * n)` by `finProdFinEquiv`.
Reading the three positions as `(i, j)`, `(j', k)` and `(k', i')`, the entry is `1` when they
chain -- `j = j'`, `k = k'` and `i' = i` -- and `0` otherwise, so that contracting the tensor
against two matrices `A` and `B` on its first two indices yields the trace form of `A * B`.
Its tensor rank is the bilinear complexity of multiplying two `n × n` matrices. -/
def matrixMultiplicationTensor (n : ℕ) : Fin (n * n) → Fin (n * n) → Fin (n * n) → ℂ :=
  fun p q r =>
    let ij := finProdFinEquiv.symm p
    let jk := finProdFinEquiv.symm q
    let ki := finProdFinEquiv.symm r
    if ij.2 = jk.1 ∧ jk.2 = ki.1 ∧ ki.2 = ij.1 then 1 else 0

/-- The exponent of matrix multiplication `ω` is the infimum of the `τ` with
`rank ⟨n, n, n⟩ = O(n ^ τ)`; since `ω ≥ 2` always holds, `ω = 2` says exactly that for every
`ε > 0` the rank is `O(n ^ (2 + ε))`. Rank here is tensor rank over `ℂ`, which by Strassen
gives the same exponent as arithmetic-circuit complexity. -/
abbrev Target : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    (tensorRank (matrixMultiplicationTensor n) : ℝ) ≤ C * (n : ℝ) ^ (2 + ε)

end Problem

/-!
- source_version: b80da422c1869ddababb2992c7dc83556e0f930c
-/
