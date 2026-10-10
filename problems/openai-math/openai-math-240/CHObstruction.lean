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

- problem_id: CHObstruction
- collection: openai-math
- question_id: openai-math:240
- source: openai-math
- source_locator: lean/ComparatorChallenges/CHObstruction.lean#OAI.CHObstruction.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves Shelah's eventual categoricity conjecture in ZFC: for each bound on the Löwenheim–Skolem number, a uniform threshold makes categoricity of an abstract elementary class in one cardinal above that threshold imply categoricity throughout the same tail. Categoricity means uniqueness up to isomorphism at a given cardinality. Under the continuum hypothesis, a proposed specific Hanf threshold need not suffice. ([Lean](lean/docs/240.md)) Assuming the continuum hypothesis, we construct an abstract elementary class with Löwenheim–Skolem number ℵ0 that is categorical in every sufficiently large cardinal but has at least two nonisomorphic models of cardinality $`\beth_{\omega_2}`$. Thus categoricity does not transfer down to the proposed bound $`\beth_{(2^{\aleph_0})^+}`$, which equals $`\beth_{\omega_2}`$ under CH. Consequently, if ZFC is consistent, the prescribed-threshold form of Shelah's categoricity conjecture is not provable in ZFC.
- notes: OpenAI math result family 240, Shelah's eventual categoricity and the prescribed-threshold obstruction -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/240.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CHObstruction.main
- source_theorem_count: 1
- source_solution_module: OAI.ModelTheory.Categoricity.Main
- source_main_result: OAI.CHObstruction.main
- source_papers: preprints/A-CH-Obstruction-to-a-Prescribed-Categoricity-Threshold-September-24-2026/paper.pdf
- source_scope_note: lean/docs/240.md
- source_field: ModelTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

universe u

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

structure RelModel (L : ℕ → Type) where
  carrier : ZFSet.{u}
  rel : (n : ℕ) → L n → (Fin n → carrier) → Prop

namespace RelModel

variable {L : ℕ → Type}

structure IsSubstructure (M N : RelModel.{u} L) : Prop where
  subset : M.carrier ⊆ N.carrier
  restrict : ∀ (n) (r : L n) (a : Fin n → M.carrier),
    M.rel n r a ↔ N.rel n r (fun i => ⟨(a i).val, subset (a i).property⟩)

structure Iso (M N : RelModel.{u} L) where
  toEquiv : M.carrier ≃ N.carrier
  map_rel : ∀ (n) (r : L n) (a : Fin n → M.carrier),
    M.rel n r a ↔ N.rel n r (toEquiv ∘ a)

def IsUnion {ι : Type u} (F : ι → RelModel.{u} L) (U : RelModel.{u} L) : Prop :=
  (∀ i, IsSubstructure (F i) U) ∧
  ∀ x : U.carrier, ∃ i, x.val ∈ (F i).carrier

end RelModel

structure ClassData (L : ℕ → Type) where
  objects : RelModel.{u} L → Prop
  strong : RelModel.{u} L → RelModel.{u} L → Prop

namespace ClassData

variable {L : ℕ → Type} (K : ClassData.{u} L)

def LSBound (θ : Cardinal.{u}) : Prop :=
  ℵ₀ ≤ θ ∧ Cardinal.lift.{u, 0} (# (Σ n, L n)) ≤ θ ∧
  ∀ M, K.objects M → ∀ A : ZFSet.{u}, A ⊆ M.carrier →
    ∃ N, K.objects N ∧ K.strong N M ∧ A ⊆ N.carrier ∧ N.carrier.card ≤ A.card + θ

def HasLSNumber (θ : Cardinal.{u}) : Prop :=
  K.LSBound θ ∧ ∀ θ', K.LSBound θ' → θ ≤ θ'

structure IsAEC : Prop where
  strong_objects : ∀ {M N}, K.strong M N → K.objects M ∧ K.objects N
  refl : ∀ {M}, K.objects M → K.strong M M
  antisymm : ∀ {M N}, K.strong M N → K.strong N M → M = N
  trans : ∀ {M N P}, K.strong M N → K.strong N P → K.strong M P
  substructure : ∀ {M N}, K.strong M N → M.IsSubstructure N
  iso_objects : ∀ {M N}, K.objects M → Nonempty (M.Iso N) → K.objects N
  iso_strong : ∀ {M N M' N'} (h : K.strong M N)
    (e : M.Iso M') (f : N.Iso N'),
    (∀ x : M.carrier,
      (e.toEquiv x).val =
        (f.toEquiv ⟨x.val, (substructure h).subset x.property⟩).val) →
    K.strong M' N'
  coherence : ∀ {M₀ M₁ M₂}, M₀.IsSubstructure M₁ →
    K.strong M₀ M₂ → K.strong M₁ M₂ → K.strong M₀ M₁
  chain_union : ∀ (γ : Ordinal.{u}), γ ≠ 0 →
    ∀ (F : γ.ToType → RelModel.{u} L),
    (∀ i, K.objects (F i)) →
    (∀ i j, i ≤ j → K.strong (F i) (F j)) →
    ∃ U, K.objects U ∧ RelModel.IsUnion F U ∧
      (∀ i, K.strong (F i) U) ∧
      (∀ N, K.objects N → (∀ i, K.strong (F i) N) → K.strong U N)
  downward : ∃ θ, K.LSBound θ

def Categorical (μ : Cardinal.{u}) : Prop :=
  (∃ M, K.objects M ∧ M.carrier.card = μ) ∧
  ∀ M N, K.objects M → K.objects N →
    M.carrier.card = μ → N.carrier.card = μ → Nonempty (M.Iso N)

def TwoModels (μ : Cardinal.{u}) : Prop :=
  ∃ M N, K.objects M ∧ K.objects N ∧
    M.carrier.card = μ ∧ N.carrier.card = μ ∧ ¬ Nonempty (M.Iso N)

end ClassData

def CH : Prop := (2 : Cardinal.{u}) ^ ℵ₀ = ℵ_ 1

def hanf (κ : Cardinal.{u}) : Cardinal.{u} := beth (succ ((2 : Cardinal.{u}) ^ κ)).ord

def endpoint : Cardinal.{u} := beth (ω_ 2)

def tailThreshold : Cardinal.{u} := beth (succ ((2 : Cardinal.{u}) ^ (ℵ_ 1))).ord

def main_statement : Prop :=
  ∀ (hCH : CH.{u}),
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ

end CHObstruction

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.CHObstruction.main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/240.md: Under the continuum hypothesis, the formalized result refutes the proposed transfer of categoricity down to the Hanf threshold. It gives an abstract elementary class in a countable relational language, with Löwenheim–Skolem number $\aleph_0$, that has two nonisomorphic models at $\beth_{\omega_2}=h(\aleph_0)$ but is categorical in every cardinal at least $\beth_{(2^{\aleph_1})^+}$. No amalgamation, joint embedding, tameness, or absence-of-maximal-models assumption is imposed. The later canonical-point obstruction and the separate eventual-categoricity theorem are not included. -/
