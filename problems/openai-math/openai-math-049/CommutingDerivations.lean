import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Basic
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

- problem_id: CommutingDerivations
- collection: openai-math
- question_id: openai-math:049
- source: openai-math
- source_locator: lean/ComparatorChallenges/CommutingDerivations.lean#OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs a polynomial in four complex variables that is not a coordinate but becomes one after adjoining a single variable, disproving the Stable Coordinate conjecture in four variables. Every fiber is affine three-space, yet none of its embeddings is rectifiable, also disproving the Abhyankar–Sathaye conjecture even when all fibers are affine spaces. ([Lean](lean/docs/049.md)) We construct an explicit counterexample to the Abhyankar–Sathaye conjecture: a noncoordinate polynomial in four complex variables whose zero fibre is affine three-space. Adjoining variables gives counterexamples in every ambient dimension at least four. We construct an explicit degree-five polynomial over $`\mathbf C`$ that is not a coordinate in four variables but becomes one after adjoining a single variable. This gives a counterexample to the stable coordinate conjecture in four variables. Every fiber is isomorphic to affine three-space, yet its embedding in affine four-space is not rectifiable. Thus the example also disproves the Abhyankar–Sathaye embedding conjecture in ambient dimension four.
- notes: OpenAI math result family 049, A stable-coordinate counterexample in four variables -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/049.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras
- source_theorem_count: 1
- source_solution_module: OAI.AlgebraicGeometry.CommutingDerivations.OrdinaryExtraMain
- source_main_result: OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras
- source_papers: preprints/An-explicit-noncoordinate-polynomial-with-affine-three-space-zero-fibre-September-24-2026/paper.pdf preprints/A-stable-coordinate-that-is-not-a-coordinate-in-four-variables-October-5-2026/stable-coordinate-four-variables.pdf
- source_scope_note: lean/docs/049.md
- source_field: AlgebraicGeometry
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

namespace AbhyankarSathaye

def S {B : Type*} [CommRing B] (h u v w : B) : B :=
  2*u^3*v + 3*u^4*w + h*(v^2 - 3*u^2*w^2) + h^2*w^3

def P {B : Type*} [CommRing B] (x y s : B) : B :=
  -2*s^2*x + 3*s*y^2 - 3*s^3*y

abbrev R := MvPolynomial (Fin 4) ℂ

def h : R := MvPolynomial.X 0
def u : R := MvPolynomial.X 1
def v : R := MvPolynomial.X 2
def w : R := MvPolynomial.X 3
def x : R := u^3 + h*v
def y : R := -u^2 + h*w
def s : R := S h u v w
def p : R := P x y s
def F : R := h - p - 1

def fourInclusion {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

def extendedF {n : ℕ} (hn : 4 ≤ n) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.rename (fourInclusion hn) F

def blocksToAmbient {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 4 ≃ Fin n :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

def blocksToOutput {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 3 ≃ Fin (n-1) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

namespace CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

def LocallyNilpotent (D : Derivation K A A) : Prop :=
  ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0

open MvPolynomial

def commuting_derivations_with_ordinary_extras_statement : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n),
    ∃ d : Fin (n-1) → Derivation ℂ (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ),
      (∀ i, d i (extendedF hn + 1) = 0) ∧
      (∀ i j p, d i (d j p) = d j (d i p)) ∧
      (∀ i, LocallyNilpotent (d i)) ∧
      LinearIndependent (MvPolynomial (Fin n) ℂ) d ∧
      (∀ p, (∀ i, d i p = 0) ↔
        p ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ))) ∧
      (∀ g, (∀ i, d i g = 0) →
        ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (j : Fin n),
          e (X j) = g) ∧
      (∀ i : Fin (n-4), d (blocksToOutput hn (Sum.inl i)) =
        pderiv (blocksToAmbient hn (Sum.inl i)))

end CommutingDerivations

end AbhyankarSathaye

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.AbhyankarSathaye.CommutingDerivations.commuting_derivations_with_ordinary_extras_statement

end Problem

/- Formalization scope, from lean/docs/049.md: The stable coordinate conjecture predicts that a polynomial that becomes a coordinate after adjoining variables was already a coordinate. The formalization gives an explicit degree-five polynomial in four complex variables that becomes a coordinate after adjoining one variable but is not a coordinate in four variables. Every fiber is isomorphic to affine three-space, yet no fiber can be carried to a coordinate hyperplane by an ambient polynomial automorphism. The Abhyankar–Sathaye conjecture predicts that a polynomial defining an affine-space quotient must be an ambient coordinate. For every $n\ge4$, the formalized counterexample gives $F\in\mathbb C[x_1,\ldots,x_n]$ with quotient $\mathbb C[x_1,\ldots,x_n]/(F)\cong\mathbb C[y_1,\ldots,y_{n-1}]$, although $F$ is not a coordinate. A companion gives $n-1$ commuting, locally nilpotent derivations, linearly independent over the polynomial ring, whose common kernel is generated by the construction's explicit polynomial and contains no ambient coordinate. The extra $n-4$ derivations are ordinary partial derivatives in the added variables. The three-variable case is not covered. -/
