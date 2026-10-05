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

- problem_id: E1128
- collection: erdos
- question_id: erdos:1128
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1128.lean#erdos_1128
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: **Erdős Problem 1128** (disproved by Prikry–Mills, 1978): Erdős asked whether every 2-colouring of $A \times B \times C$, where $|A| = |B| = |C| = \aleph_1$, must contain a monochromatic countable box $A_1 \times B_1 \times C_1$ with $|A_1| = |B_1| = |C_1| = \aleph_0$. The answer is **No**: Prikry and Mills constructed a 2-colouring of $\omega_1^3$ with no monochromatic countable box. Note: The positive statement asserts that every 2-colouring of every $\aleph_1^3$ contains a monochromatic countably infinite box. Since the answer is False, this positive statement fails.
- notes: Erdos Problem 1128 -- https://www.erdosproblems.com/1128
- track: solved
- answer_shape: decide
- source_stem: 1128
- mathdb_ref: erdos:1128
- source_namespace: Erdos1128
- source_theorem: erdos_1128
- source_category: research solved
- source_ams: 3 5
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Cardinal Set Ordinal Order

namespace Problem

/-- A subset $A_1 \times B_1 \times C_1$ of $A \times B \times C$ is **monochromatic**
under a 2-colouring $f : A \to B \to C \to \operatorname{Fin} 2$ if $f$ is constant on
$A_1 \times B_1 \times C_1$. -/
def IsMonochromaticBox {A B C : Type*} (f : A → B → C → Fin 2)
    (A₁ : Set A) (B₁ : Set B) (C₁ : Set C) : Prop :=
  ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ c' ∈ C₁, f a b c' = c

/-
Auxiliary lemmas for the Prikry–Mills construction.
These establish key countability and boundedness properties of ω₁.
-/

/-- The set of countable ordinals, expressed using Mathlib's `ω_ 1`. -/
abbrev Omega1 := {o : Ordinal.{0} // o < ω_ 1}

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔
        ∀ (A B C : Type) (_ : #A = aleph 1) (_ : #B = aleph 1) (_ : #C = aleph 1)
          (f : A → B → C → Fin 2),
          ∃ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
            #A₁ = aleph 0 ∧ #B₁ = aleph 0 ∧ #C₁ = aleph 0 ∧
            IsMonochromaticBox f A₁ B₁ C₁

end Problem
