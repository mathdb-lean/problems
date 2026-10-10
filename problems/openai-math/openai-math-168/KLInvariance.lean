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

- problem_id: KLInvariance
- collection: openai-math
- question_id: openai-math:168
- source: openai-math
- source_locator: lean/ComparatorChallenges/KLInvariance.lean#OAI.KLInvariance.combinatorial_invariance
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Resolves the full combinatorial invariance conjecture: isomorphic Bruhat intervals in arbitrary Coxeter systems have identical equal-parameter Kazhdan–Lusztig polynomials. Thus the abstract order of the interval determines the polynomial, even across different Coxeter systems. ([Lean](lean/docs/168.md)) We prove that an isomorphism of Bruhat intervals in arbitrary Coxeter systems preserves their equal-parameter Kazhdan–Lusztig polynomials. This resolves the full combinatorial invariance conjecture positively.
- notes: OpenAI math result family 168, Combinatorial invariance of Kazhdan–Lusztig polynomials -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/168.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.KLInvariance.combinatorial_invariance
- source_theorem_count: 1
- source_solution_module: OAI.RepresentationTheory.KazhdanLusztig.Invariance
- source_papers: preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf
- source_scope_note: lean/docs/168.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- An upward edge in the *strong* Bruhat graph, with left reflection labels. -/
def BruhatStep (cs : CoxeterSystem M W) (x y : W) : Prop :=
  cs.length x < cs.length y ∧ ∃ t : W, cs.IsReflection t ∧ y = t * x

/-- The actual strong Bruhat order, not the weak order. -/
def BruhatLE (cs : CoxeterSystem M W) : W → W → Prop :=
  Relation.ReflTransGen (BruhatStep cs)

/-- The unlabelled interval, including both endpoints. -/
def Interval (cs : CoxeterSystem M W) (u b : W) :=
  {x : W // BruhatLE cs u x ∧ BruhatLE cs x b}

instance intervalOrder (cs : CoxeterSystem M W) (u b : W) :
    PartialOrder (Interval cs u b) where
  le left right := BruhatLE cs left.val right.val
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ forward backward := forward.trans backward
  le_antisymm left right forward backward := by
    apply Subtype.ext
    have length_mono : ∀ {lower upper : W}, BruhatLE cs lower upper →
        cs.length lower ≤ cs.length upper := by
      intro lower upper relation
      induction relation using Relation.ReflTransGen.head_induction_on with
      | refl => exact le_rfl
      | head step _ rest => exact le_trans step.1.le rest
    by_contra distinct
    rcases forward.cases_head with same | ⟨middle, step, rest⟩
    · exact distinct same
    · exact (not_lt_of_ge (length_mono backward))
        (lt_of_lt_of_le step.1 (length_mono rest))

/-- `d(x,y)` in the manuscript, used only for comparable endpoints. -/
noncomputable def rankDifference (cs : CoxeterSystem M W) (x y : W) : ℕ :=
  cs.length y - cs.length x

abbrev PolynomialFamilies (W : Type v) := (W → W → ℤ[X]) × (W → W → ℤ[X])

/-- Exact equal-parameter normalization in the introduction.
The first family is R and the second is P.  `reflect d p` is `q^d p(q⁻¹)`
when `p.natDegree ≤ d`, which follows here from the degree bound (or the
diagonal normalization). The sum is over the real Bruhat interval;
its finiteness is a separate theorem, not a different definition of order. -/
structure NormalizedKL (cs : CoxeterSystem M W) (RP : PolynomialFamilies W) : Prop where
  R_diagonal : ∀ x, RP.1 x x = 1
  R_zero : ∀ x y, ¬ BruhatLE cs x y → RP.1 x y = 0
  R_recursion : ∀ x y i, cs.length (cs.simple i * y) < cs.length y →
    RP.1 x y =
      if cs.length (cs.simple i * x) < cs.length x then
        RP.1 (cs.simple i * x) (cs.simple i * y)
      else
        (X - 1) * RP.1 x (cs.simple i * y) +
          X * RP.1 (cs.simple i * x) (cs.simple i * y)
  P_diagonal : ∀ x, RP.2 x x = 1
  P_zero : ∀ x y, ¬ BruhatLE cs x y → RP.2 x y = 0
  P_degree : ∀ x y, BruhatLE cs x y → x ≠ y →
    2 * (RP.2 x y).natDegree < rankDifference cs x y
  reciprocity : ∀ x y, BruhatLE cs x y →
    reflect (rankDifference cs x y) (RP.2 x y) =
      ∑ᶠ z : Interval cs x y, RP.1 x z.val * RP.2 z.val y

/-- The polynomial families selected by their equal-parameter normalization. -/
noncomputable def klFamilies (cs : CoxeterSystem M W) : PolynomialFamilies W :=
  Classical.epsilon (NormalizedKL cs)

noncomputable def klPolynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  (klFamilies cs).2 x y

end KLInvariance

namespace KLInvariance

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

def combinatorial_invariance_statement : Prop :=
  ∀ {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B} {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'} (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b') (ι : Interval cs u b ≃o Interval cs' u' b'),
    klPolynomial cs u b = klPolynomial cs' u' b'

end KLInvariance

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u, v, u', v'} : Prop :=
  _root_.OAI.KLInvariance.combinatorial_invariance_statement.{u, v, u', v'}

end Problem

/- Formalization scope, from lean/docs/168.md: The combinatorial invariance conjecture asks whether a Kazhdan–Lusztig polynomial depends only on its Bruhat interval as an ordered set. The formalization proves that every order isomorphism between Bruhat intervals in arbitrary Coxeter systems preserves the corresponding equal-parameter Kazhdan–Lusztig polynomial. The two intervals may come from different Coxeter systems. -/
