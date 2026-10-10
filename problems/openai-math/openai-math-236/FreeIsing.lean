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

- problem_id: FreeIsing
- collection: openai-math
- question_id: openai-math:236
- source: openai-math
- source_locator: lean/ComparatorChallenges/FreeIsing.lean#OAI.Problem367.free_ising_factor_iff_threshold
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines when the free zero-field ferromagnetic Ising state on the infinite d-regular tree is a factor of independent vertex labels: exactly when $`\tanh\beta\le(d-1)^{-1/2}`$, including equality, for d ≥ 3 and β ≥ 0. The construction uses no root and is almost surely equivariant for each fixed tree automorphism, resolving the ferromagnetic case of Lyons's question. ([Lean](lean/docs/236.md)) For every integer d ≥ 3 and inverse temperature β ≥ 0, the free zero-field ferromagnetic Ising measure on the infinite d-regular tree is a factor of IID exactly when $`\tanh\beta\le(d-1)^{-1/2}`$. We prove the positive implication, including equality, resolving the conjecture of Nam, Sly and Zhang; the strict converse is known. The spin factor can be chosen to commute with every tree automorphism on every label input.
- notes: OpenAI math result family 236, The exact factor-of-IID threshold for free Ising spins on trees -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/236.md
- track: solved
- answer_shape: proof
- context_lemmas: IsingSpin.enumList_getElem?_ctorIdx_eq IsingSpin.enumList_nodup
- source_theorem: OAI.Problem367.free_ising_factor_iff_threshold
- source_theorem_count: 1
- source_solution_module: OAI.Probability.FreeIsing.Main
- source_main_result: OAI.Problem367.free_ising_factor_iff_threshold
- source_papers: preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf
- source_scope_note: lean/docs/236.md
- source_field: Probability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

abbrev TreeVertex (d : ℕ) :=
  {word : List (Fin d) // List.IsChain (fun first second : Fin d => first ≠ second) word}

def treeAdj {d : ℕ} (u v : TreeVertex d) : Prop :=
  (∃ c : Fin d, v.1 = u.1 ++ [c]) ∨
  (∃ c : Fin d, u.1 = v.1 ++ [c])

structure TreeAut (d : ℕ) where
  toEquiv : TreeVertex d ≃ TreeVertex d
  map_adj : ∀ u v, treeAdj (toEquiv u) (toEquiv v) ↔ treeAdj u v

def relabel {d : ℕ} {α : Type*} (g : TreeAut d)
    (x : TreeVertex d → α) : TreeVertex d → α :=
  fun v => x (g.toEquiv.symm v)

inductive IsingSpin where
  | neg
  | pos
  deriving DecidableEq

protected abbrev IsingSpin.enumList : List IsingSpin := [.neg, .pos]

protected theorem IsingSpin.enumList_getElem?_ctorIdx_eq (x : IsingSpin) :
    IsingSpin.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem IsingSpin.enumList_nodup : IsingSpin.enumList.Nodup := by decide

instance : Fintype IsingSpin where
  elems := ⟨IsingSpin.enumList, IsingSpin.enumList_nodup⟩
  complete x := by cases x <;> decide

instance isingSpinMeasurable : MeasurableSpace IsingSpin := ⊤

def uniform01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

instance uniform01Probability : IsProbabilityMeasure uniform01 where
  measure_univ := by simp [uniform01]

def labelMeasure (d : ℕ) : Measure (TreeVertex d → ℝ) := by
  classical
  exact Measure.infinitePi (fun _ : TreeVertex d => uniform01)

def ConnectedFinset {d : ℕ} (D : Finset (TreeVertex d)) : Prop :=
  D.Nonempty ∧
    ∀ u ∈ D, ∀ v ∈ D,
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ D ∧ y ∈ D ∧ treeAdj x y) u v

def inducedEdges {d : ℕ} (D : Finset (TreeVertex d)) :
    Finset (TreeVertex d × TreeVertex d) := by
  classical
  exact (D.product D).filter (fun e =>
    treeAdj e.1 e.2 ∧ e.1.1.length < e.2.1.length)

def freeCylinderWeight {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ENNReal :=
  ENNReal.ofReal
    ((1 / 2 : ℝ) *
      Finset.prod (inducedEdges D) (fun e =>
        (1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

def HasFreeIsingLaw {d : ℕ} (theta : ℝ)
    (mu : Measure (TreeVertex d → IsingSpin)) : Prop :=
  ∀ (D : Finset (TreeVertex d)), ConnectedFinset D →
    ∀ eta : TreeVertex d → IsingSpin,
      mu {x | ∀ v ∈ D, x v = eta v} = freeCylinderWeight theta D eta

def IsFactorOfIID (d : ℕ) (theta : ℝ) : Prop :=
  ∃ Phi : (TreeVertex d → ℝ) → (TreeVertex d → IsingSpin),
    Measurable Phi ∧
    HasFreeIsingLaw theta (Measure.map Phi (labelMeasure d)) ∧
    ∀ g : TreeAut d,
      ∀ᵐ U ∂labelMeasure d, Phi (relabel g U) = relabel g (Phi U)

def free_ising_factor_iff_threshold_statement : Prop :=
  ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → (IsFactorOfIID d (Real.tanh beta) ↔ Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1))

end Problem367

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Problem367.free_ising_factor_iff_threshold_statement

end Problem

/- Formalization scope, from lean/docs/236.md: The formalized result determines the factor-of-IID threshold for the free zero-field Ising law on the infinite $d$-regular tree. For every $d\ge3$ and $\beta\ge0$, the law is a factor of IID exactly when $\tanh\beta\le1/\sqrt{d-1}$, including equality. The factor uses independent uniform vertex labels and is almost surely equivariant for each fixed tree automorphism. Finitary coding and coding-radius bounds are not included. -/
