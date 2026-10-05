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

- problem_id: NNoetherProblem_noether_problem
- collection: wikipedia
- question_id: wikipedia:NoetherProblem
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/NoetherProblem.lean#noether_problem
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The **Noether Problem**: let `L` be the field of rational functions in `n` indeterminates over `K`, and let `G` be a finite group permuting these indeterminates. Is the fixed field `L^G` a rational extension of `K`, i.e. does `L/K` have the Noether property? Solution: False.
- notes: Wikipedia: NoetherProblem -- https://en.wikipedia.org/wiki/Rational_variety
- track: solved
- answer_shape: decide
- source_stem: NoetherProblem
- source_namespace: NoetherProblem
- source_theorem: noether_problem
- source_category: research solved
- source_ams: 12 14
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: rationalExtension_empty_index
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

namespace Problem

/--
A rational field extension is a field extension `L/K` isomorphic
to a field of rational functions (in some arbitrary number of indeterminates.)
-/
class IsRationalExtension (K L ι : Type*)
    [Field K] [Field L] [Algebra K L] where
  pure_transcendental :
    Nonempty (L ≃ₐ[K] ((FractionRing (MvPolynomial ι K))))

/--
We say that a rational extension `L` of `K` in the indeterminates `ι` has the _Noether Property_
if, for every identification of `L` with the rational function field `K(X_i : i ∈ ι)`, the fixed
field `L^H` of every group `H` of `K`-automorphisms of `L` permuting the indeterminates `X_i` is
again a rational extension of `K`. Such a group `H` is necessarily finite.
-/
def HasNoetherProperty (K L ι : Type) [Field K] [Field L] [Fintype ι]
    [Algebra K L] [IsRationalExtension K L ι] : Prop :=
  ∀ (e : L ≃ₐ[K] FractionRing (MvPolynomial ι K)) (H : Subgroup (L ≃ₐ[K] L)),
    (∀ h ∈ H, ∃ σ : Equiv.Perm ι, h = (AlgEquiv.autCongr e).symm
      (IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ))) →
    ∃ ι' : Type, IsRationalExtension K (IntermediateField.fixedField H) ι'

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- If the index set `ι` is empty, then `IsRationalExtension K L ι` means that
`K, L` are isomorphic as `K` algebras. -/
@[category test, AMS 12]
theorem rationalExtension_empty_index (K L ι : Type*) [Field K] [Field L] [Algebra K L] [IsEmpty ι]
    [IsRationalExtension K L ι] :
    Nonempty (L ≃ₐ[K] K) := by
  set a : L ≃ₐ[K] (FractionRing (MvPolynomial ι K)) :=
    Classical.choice IsRationalExtension.pure_transcendental
  set b : (MvPolynomial ι K) ≃ₐ[K] K := MvPolynomial.isEmptyAlgEquiv K ι
  set c : FractionRing (MvPolynomial ι K) ≃ₐ[K] K :=
    IsFractionRing.fieldEquivOfAlgEquiv K (FractionRing (MvPolynomial ι K)) K b
  apply Nonempty.intro (a.trans c)

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ ∀ (K L ι : Type)
        [Field K] [Field L] [Fintype ι] [Algebra K L] [IsRationalExtension K L ι],
        HasNoetherProperty K L ι

end Problem
