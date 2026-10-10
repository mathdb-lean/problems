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

- problem_id: CoboundaryExpanders
- collection: openai-math
- question_id: openai-math:177
- source: openai-math
- source_locator: lean/ComparatorChallenges/CoboundaryExpanders.lean#OAI.CoboundaryExpanders.main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs arbitrarily large finite d-dimensional simplicial complexes, for every d ≥ 3, with uniformly bounded vertex degrees and uniform 𝔽2 coboundary expansion in every degree below d. Together with the known graph and two-dimensional cases, this establishes the existence of such expanders in every positive dimension. ([Lean](lean/docs/177.md)) For every integer d ≥ 3, we construct arbitrarily large finite d-dimensional simplicial complexes with uniformly bounded vertex degrees and uniform 𝔽2 coboundary expansion in every degree below d. Together with the known graph and two-dimensional cases, this establishes the existence of bounded-degree 𝔽2 coboundary expanders in every positive dimension.
- notes: OpenAI math result family 177, Bounded-degree coboundary expanders -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/177.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.CoboundaryExpanders.main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Coboundary.Main
- source_papers: preprints/Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/paper.pdf
- source_scope_note: lean/docs/177.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
# Bounded-degree coboundary expanders in every dimension

Finite connected pure complexes with uniformly bounded top-face incidence and
uniform weighted coboundary expansion over F₂ in all degrees below the dimension.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders

/-- A finite abstract simplicial complex with every labelled vertex present. -/
structure Complex where
  vertexCount : ℕ
  faces : Finset (Finset (Fin vertexCount))
  empty_mem : ∅ ∈ faces
  downward : ∀ {σ τ}, σ ∈ faces → τ ⊆ σ → τ ∈ faces
  vertex_mem : ∀ v, {v} ∈ faces

namespace Complex

/-- Faces of dimension `i` have exactly `i + 1` vertices. -/
def facesOf (X : Complex) (i : ℕ) : Finset (Finset (Fin X.vertexCount)) :=
  X.faces.filter (fun σ => σ.card = i + 1)

def Face (X : Complex) (i : ℕ) := {σ // σ ∈ X.facesOf i}

instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := Subtype.fintype _
instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := Classical.decEq _

/-- Exact purity: top faces exist and every face lies in a top face. -/
def Pure (X : Complex) (s : ℕ) : Prop :=
  (X.facesOf s).Nonempty ∧
  ∀ σ ∈ X.faces, ∃ τ ∈ X.facesOf s, σ ⊆ τ

/-- Connectedness of the nonempty one-skeleton. -/
def Connected (X : Complex) : Prop :=
  Nonempty (Fin X.vertexCount) ∧
  ∀ v w : Fin X.vertexCount,
    Relation.ReflTransGen (fun a b => a ≠ b ∧ {a, b} ∈ X.faces) v w

abbrev Cochain (X : Complex) (i : ℕ) := X.Face i → ZMod 2

/-- Weights are normalized counts of incident top-dimensional faces. -/
def weight (X : Complex) (s i : ℕ) (σ : X.Face i) : ℝ :=
  (((X.facesOf s).filter (fun τ => σ.val ⊆ τ)).card : ℝ) /
    ((Nat.choose (s + 1) (i + 1) : ℝ) * (X.facesOf s).card)

/-- Weighted support norm. -/
def norm (X : Complex) (s i : ℕ) (f : X.Cochain i) : ℝ :=
  ∑ σ : X.Face i, if f σ ≠ 0 then X.weight s i σ else 0

/-- Simplicial coboundary over F₂. -/
def coboundary (X : Complex) (i : ℕ) (f : X.Cochain i) : X.Cochain (i + 1) :=
  fun τ => ∑ σ : X.Face i, if σ.val ⊆ τ.val then f σ else 0

/-- Actual coboundaries, with constant cochains in degree zero. -/
def coboundaries (X : Complex) : (i : ℕ) → Set (X.Cochain i)
  | 0 => {f | ∃ c : ZMod 2, f = fun _ => c}
  | i + 1 => Set.range (X.coboundary i)

/-- Distance in the weighted support norm; on a nonempty finite set it is a minimum. -/
def distance (X : Complex) (s i : ℕ) (f : X.Cochain i)
    (A : Set (X.Cochain i)) : ℝ :=
  sInf ((fun a => X.norm s i (f - a)) '' A)

/-- Number of top-dimensional faces incident to a vertex. -/
def topDegree (X : Complex) (s : ℕ) (v : Fin X.vertexCount) : ℕ :=
  ((X.facesOf s).filter (fun τ => v ∈ τ)).card

end Complex

/-- Both constants are uniform over the sequence, all degrees below `d`, and all cochains. -/
def MainStatement : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    ∃ (D : ℕ) (ε : ℝ), 0 < ε ∧
      ∃ X : ℕ → Complex,
        (∀ m, (X m).Pure d ∧ (X m).Connected) ∧
        Tendsto (fun m => ((X m).facesOf 0).card) atTop atTop ∧
        (∀ m (v : Fin (X m).vertexCount), (X m).topDegree d v ≤ D) ∧
        ∀ m i, i < d → ∀ f : (X m).Cochain i,
          ε * (X m).distance d i f ((X m).coboundaries i) ≤
            (X m).norm d (i + 1) ((X m).coboundary i f)

def main_statement : Prop :=
  MainStatement

end CoboundaryExpanders

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.CoboundaryExpanders.main_statement

end Problem

/- Formalization scope, from lean/docs/177.md: The formalization constructs bounded-degree $\mathbb F_2$ coboundary expanders in every dimension $d\ge3$. For each such $d$, it gives finite pure connected $d$-dimensional simplicial complexes with vertex counts tending to infinity, one uniform bound on top-dimensional degree at each vertex, and one positive coboundary-expansion constant in every degree below $d$. The constants may depend on $d$. The graph and two-dimensional cases used for the paper's all-positive-dimensions conclusion are separate. -/
