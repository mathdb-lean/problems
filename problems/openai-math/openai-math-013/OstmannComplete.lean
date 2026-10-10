import Mathlib
/-
Copyright 2026 OpenAI. Licensed under the Apache License, Version 2.0.
Copyright 2026 The mathdb-lean Authors.

The definitions and the statements below are OpenAI's, from
github.com/openai/math at the revision named in the metadata block; see NOTICE.
What this library changed: each `sorry`-bodied theorem became the definition of
the proposition it stated, and `Problem.Target` conjoins those propositions.

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

/-!
Converted from github.com/openai/math. `source_locator` names the comparator
challenge this came from and `source_solution_module` the module there that
proves it; both are at `source_version`. The definitions are the challenge's
own; each sorried theorem became `<name>_statement`, and `Problem.Target`
below conjoins them. `track` is solved because comparator accepted OpenAI's
proof against this very statement. Whether the statement says what the paper's
title says is what the scope note, carried as a caveat, is about.

- problem_id: OstmannComplete
- collection: openai-math
- question_id: openai-math:013
- source: openai-math
- source_locator: lean/ComparatorChallenges/OstmannComplete.lean#OAI.Ostmann.inverseGoldbach
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that no finite modification of the primes can be written as $`A+B`$ with $`A,B\subseteq\mathbb Z_{\ge0}`$ each containing at least two elements. This resolves Ostmann's inverse Goldbach conjecture on additive indecomposability. ([Lean](lean/docs/013.md)) We prove Ostmann's inverse Goldbach conjecture: no set differing from the primes by finitely many elements can be written as $`A+B`$, where A and B are sets of nonnegative integers with at least two elements each.
- notes: OpenAI math result family 013, Ostmann’s inverse Goldbach conjecture -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/013.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Ostmann.inverseGoldbach OAI.Ostmann.twoInfiniteSummandsImpossible
- source_theorem_count: 2
- source_solution_module: OAI.NumberTheory.Ostmann.Complete
- source_papers: preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf
- source_scope_note: lean/docs/013.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

open scoped Pointwise symmDiff

namespace Ostmann

def primes : Set ℕ := {n | Nat.Prime n}

abbrev sumset (A B : Set ℕ) : Set ℕ := A + B

def EventuallyPrimeSumset (A B : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → (n ∈ sumset A B ↔ n.Prime)

def TwoInfiniteSummandsImpossible : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → ¬ EventuallyPrimeSumset A B

def InverseGoldbach : Prop :=
  ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite (@symmDiff (Set ℕ)
      (@SemilatticeSup.toMax (Set ℕ)
        (@Lattice.toSemilatticeSup (Set ℕ)
          (@CompleteLattice.toLattice (Set ℕ)
            (@CompleteBooleanAlgebra.toCompleteLattice (Set ℕ)
              (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set ℕ)
                (@Set.instCompleteAtomicBooleanAlgebra ℕ))))))
      Set.instSDiff (sumset A B) primes)

def inverseGoldbach_statement : Prop :=
  InverseGoldbach

def twoInfiniteSummandsImpossible_statement : Prop :=
  TwoInfiniteSummandsImpossible

end Ostmann

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Ostmann.inverseGoldbach_statement ∧
  _root_.OAI.Ostmann.twoInfiniteSummandsImpossible_statement

end Problem

/- Formalization scope, from lean/docs/013.md: The formalization proves Ostmann's inverse Goldbach conjecture. For any two sets $A,B$ of nonnegative integers, each containing at least two elements, the symmetric difference between their sumset $A+B$ and the set of primes is infinite. Thus no set differing from the primes by only finitely many elements can be decomposed as such a sumset. The linked statements include the full result and its two-infinite-summands case. -/
