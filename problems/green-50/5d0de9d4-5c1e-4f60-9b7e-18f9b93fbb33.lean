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

- problem_id: G50_refute
- collection: green
- question_id: green:50
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/50.lean#green_50
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Let $A \subset \mathbb{F}_2^n$ be a set of density $\alpha > 0$. Does $10A$ contain a coset of some subspace of dimension at least $n - O(\log(1/\alpha))$? More precisely: does there exist an absolute constant $C > 0$ such that for all $n \geq 1$ and all nonempty $A \subseteq \mathbb{F}_2^n$ with density $\alpha > 0$, the sumset $10A$ contains a coset of some subspace of dimension at least $n - C \log_2(1/\alpha)$? The sumset $10A$ is defined as $\{a_1 + a_2 + \cdots + a_{10} : a_i \in A\}$, using the pointwise scalar multiplication notation `10 • A` where `•` denotes the iterated addition of a set. Note: We model $\mathbb{F}_2^n$ as `Fin n → ZMod 2`, which is an $n$-dimensional vector space over $\mathbb{F}_2$.
- notes: Green, open problem 50
- track: open
- answer_shape: refute
- pair_id: G50
- pair_role: refute
- source_stem: 50
- source_namespace: Green50
- source_theorem: green_50
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open scoped Pointwise

namespace Problem

abbrev Target : Prop :=
    ¬ (
      ∃ C > (0 : ℝ), ∀ n : ℕ, ∀ A : Finset (𝔽₂ n),
          A.Nonempty →
          let α : ℝ := A.dens
          ∃ (W : Submodule (ZMod 2) (𝔽₂ n)) (v : 𝔽₂ n),
            v +ᵥ (W : Set (𝔽₂ n)) ⊆ ↑(10 • A) ∧
            (n : ℝ) - C * Real.logb 2 (1 / α) ≤ Module.finrank (ZMod 2) W
    )

end Problem
