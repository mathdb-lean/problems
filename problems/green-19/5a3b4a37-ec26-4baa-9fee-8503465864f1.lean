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

- problem_id: G19
- collection: green
- question_id: green:19
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/19.lean#green_19
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: What is $C$, the infimum of all exponents $c$ for which the following is true, uniformly for $0 < \alpha < 1$? Suppose that $A \subset \mathbb{F}_2^n \times \mathbb{F}_2^n$ is a set of density $\alpha$. Write $N := 2^n$. Then there is some $d \neq 0$ such that $A$ contains $\gg \alpha^c N^2$ corners $(x,y), (x,y+d), (x+d,y)$. This question has been resolved by [FSS20], showing that $C = 4$.
- notes: Green, open problem 19
- track: solved
- answer_shape: proof
- source_stem: 19
- source_namespace: Green19
- source_theorem: green_19
- source_category: research solved
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset Real

namespace Problem

section GroupDefs

-- Abstract representation to ease notation [FSS20].
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- A corner in $A$ with common difference $d$ [FSS20]. -/
def IsCorner (A : Finset (G × G)) (x y d : G) : Prop :=
  (x, y) ∈ A ∧ (x + d, y) ∈ A ∧ (x, y + d) ∈ A

/--
From [FSS20]: given $A \subseteq G \times G$ and $d \in G$, let
$$S_d(A) = \lbrace (x, y) \in G \times G : (x, y), (x + d, y), (x, y + d) \in A \rbrace$$
-/
noncomputable def S (d : G) (A : Finset (G × G)) : Finset (G × G) :=
  open scoped Classical in
  univ.filter (fun p => IsCorner A p.1 p.2 d)

end GroupDefs

/--
True if the given exponent satisfies Green's conditions [Gr26].
-/
def ValidExponent (c : ℝ) : Prop :=
  ∃ K > 0,
    ∀ α, 0 < α → α < 1 →
      ∀ᶠ n in Filter.atTop,
        ∀ A : Finset (𝔽₂ n × 𝔽₂ n),
          let N : ℝ := (Fintype.card (𝔽₂ n) : ℝ)
          (A.card : ℝ) ≥ α * N^2 →
          ∃ d : 𝔽₂ n, d ≠ 0 ∧ ((S d A).card : ℝ) ≥ K * α^c * N^2

/-- The infimum of all valid exponents [Gr26]. -/
noncomputable def C : ℝ := sInf {c | ValidExponent c}

abbrev Target : Prop :=
    C = 4

end Problem
