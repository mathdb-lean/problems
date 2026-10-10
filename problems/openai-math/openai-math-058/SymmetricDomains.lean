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

- problem_id: SymmetricDomains
- collection: openai-math
- question_id: openai-math:058
- source: openai-math
- source_locator: lean/ComparatorChallenges/SymmetricDomains.lean#OAI.Release061.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the Kollár–Pardon conjecture: the semialgebraic universal covers of connected normal projective complex varieties are exactly products $`D\times\mathbb C^m\times F`$, with D bounded symmetric and F simply connected, normal, and projective. A universal cover is quasi-projective exactly when the bounded symmetric factor is absent. In particular, a smooth projective variety covered by ℂn has a finite étale cover by an abelian variety. ([Lean](lean/docs/058.md)) Every nonempty connected semialgebraic bounded open subset of a complex affine variety admitting a properly discontinuous cocompact group of biholomorphisms is smooth and biholomorphic to a bounded symmetric domain. This answers the bounded-domain question of Kollár and Pardon affirmatively.
- notes: OpenAI math result family 058, Semialgebraic universal covers and bounded domains -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/058.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Release061.main
- source_theorem_count: 1
- source_solution_module: OAI.Analysis.SymmetricDomains.Main
- source_main_result: OAI.Release061.main
- source_papers: preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf
- source_scope_note: lean/docs/058.md
- source_field: Analysis
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace Release061

abbrev Affine (n : ℕ) := Fin n → ℂ

def realCoordinates {n : ℕ} (z : Affine n) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun j => (z j).re) (fun j => (z j).im)

def IsAffineAlgebraic {n : ℕ} (V : Set (Affine n)) : Prop :=
  ∃ P : Set (MvPolynomial (Fin n) ℂ),
    V = {z | ∀ p ∈ P, MvPolynomial.eval z p = 0}

inductive IsSemialgebraic {n : ℕ} : Set (Affine n) → Prop
  | zero (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | MvPolynomial.eval (realCoordinates z) p = 0}
  | positive (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | 0 < MvPolynomial.eval (realCoordinates z) p}
  | compl {S : Set (Affine n)} : IsSemialgebraic S → IsSemialgebraic Sᶜ
  | union {S T : Set (Affine n)} :
      IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic (S ∪ T)

def HolomorphicOnSubset {n m : ℕ} (S : Set (Affine n)) (f : S → Affine m) : Prop :=
  ∀ p : S, ∃ W : Set (Affine n), IsOpen W ∧ (p : Affine n) ∈ W ∧
    ∃ F : Affine n → Affine m, AnalyticOnNhd ℂ F W ∧
      ∀ q : S, (q : Affine n) ∈ W → F q = f q

structure Biholomorph {n m : ℕ} (S : Set (Affine n)) (T : Set (Affine m)) where
  toHomeomorph : S ≃ₜ T
  holomorphic_toFun : HolomorphicOnSubset S (fun p => (toHomeomorph p : Affine m))
  holomorphic_invFun : HolomorphicOnSubset T (fun q => (toHomeomorph.symm q : Affine n))

def IsSmooth {n : ℕ} (S : Set (Affine n)) : Prop :=
  ∀ p : S, ∃ (m : ℕ) (W : Set (Affine n)), W ⊆ S ∧
    IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ (p : Affine n) ∈ W ∧
    ∃ D : Set (Affine m), IsOpen D ∧ Nonempty (Biholomorph W D)

def IsBoundedSymmetricDomain {n : ℕ} (D : Set (Affine n)) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
    ∀ p : D, ∃ σ : Biholomorph D D,
      Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set D, IsOpen W ∧ p ∈ W ∧
        ∀ q ∈ W, σ.toHomeomorph q = q → q = p

def main_statement : Prop :=
  ∀ {n : ℕ} (V U : Set (Affine n)) (hV : IsAffineAlgebraic V) (hUV : U ⊆ V) (hopen : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) (hconn : IsConnected U) (hsa : IsSemialgebraic U) (hbounded : Bornology.IsBounded U) (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U] [CompactSpace (Quotient (MulAction.orbitRel Γ U))] (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)),
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D)

end Release061

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u_1} : Prop :=
  _root_.OAI.Release061.main_statement.{u_1}

end Problem

/- Formalization scope, from lean/docs/058.md: The formalized result answers the paper's symmetry question affirmatively. A nonempty connected bounded semialgebraic subset, relatively open in a complex affine algebraic set, is smooth and biholomorphic to a bounded symmetric domain whenever a discrete group acts properly and holomorphically with compact quotient. The action need not be free, and the ambient algebraic set may be singular. -/
