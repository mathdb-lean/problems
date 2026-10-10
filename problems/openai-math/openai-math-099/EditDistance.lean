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

- problem_id: EditDistance
- collection: openai-math
- question_id: openai-math:099
- source: openai-math
- source_locator: lean/ComparatorChallenges/EditDistance.lean#OAI.edit_distance_main
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines the least distortion of embedding edit distance on words of length at most d into real ℓ1: it is $`\exp(\Theta(\sqrt{\log d\,\log\log d}))`$. Insertions, deletions and substitutions have unit cost. The constants are uniform over all finite alphabets with at least two symbols, even when the alphabet grows with d; binary words already force the lower bound. ([Lean](lean/docs/099.md)) We determine the exponential scale of the least ℓ1 distortion of unit-cost edit distance on all strings of length at most d. For every sufficiently large d, uniformly over finite alphabets of size at least two, the distortion lies between $`\exp(c\sqrt{\log d\,\log\log d})`$ and $`\exp(C\sqrt{\log d\,\log\log d})`$ for absolute constants $`c,C\gt 0`$. The lower bound already holds on binary strings of one common length. Thus the order of logarithmic distortion is sharp up to absolute constants. We give two finite-circle constructions of binary strings whose least ℓ1 distortion is $`\exp(\Omega(\sqrt{\log d\,\log\log d}))`$, where d bounds their length. Both constructions supply words of one common length for every sufficiently large cap. Two direct binary coding arguments transfer the constructions with absolute distortion and logarithmic block width. We also develop the overlapping-substring method of Ostrovsky and Rabani into a complete finite histogram embedding at the same exponential scale, uniformly over all finite alphabets and all words of length at most d, including the empty word. We give two independent constructions of binary words of one length at most d whose ordinary edit-distance metrics require ℓ1 distortion $`\exp(\Omega(\sqrt{\log d\,\log\log d}))`$ for every sufficiently large d. We also prove a constant-distortion binary conversion for one prescribed input length. Together with the companion upper embedding theorem, these lower bounds determine the order of logarithmic distortion uniformly over finite alphabets with at least two symbols.
- notes: OpenAI math result family 099, The sharp exponential scale of edit-distance distortion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/099.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.edit_distance_main
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.EditDistance.Main
- source_papers: preprints/Edit-Distance-in-l1-Matching-Bounds-up-to-Constants-in-the-Exponent-September-27-2026/paper.pdf preprints/Finite-Circle-Obstructions-Binary-Codes-and-Histogram-Embeddings-for-Edit-Distance-September-27-2026/paper.pdf preprints/Tree-Constructions-for-the-l1-Distortion-of-Binary-Edit-Distance-September-27-2026/paper.pdf
- source_scope_note: lean/docs/099.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace EditDistortion

universe u

/-- A single unit-cost insertion, deletion, or (when enabled) substitution. -/
inductive Step (substitutions : Bool) {Alpha : Type u} : List Alpha → List Alpha → Prop
  | insert (p q : List Alpha) (a : Alpha) : Step substitutions (p ++ q) (p ++ a :: q)
  | delete (p q : List Alpha) (a : Alpha) : Step substitutions (p ++ a :: q) (p ++ q)
  | substitute (h : substitutions = true) (p q : List Alpha) (a b : Alpha) :
      Step substitutions (p ++ a :: q) (p ++ b :: q)

/-- An unrestricted script of exactly n unit edits. -/
inductive Script (substitutions : Bool) {Alpha : Type u} : ℕ → List Alpha → List Alpha → Prop
  | nil (x : List Alpha) : Script substitutions 0 x x
  | cons {n : ℕ} {x y z : List Alpha} (first : Step substitutions x y)
      (rest : Script substitutions n y z) : Script substitutions (n + 1) x z

/-- Minimum script length. Scripts always exist (delete x and insert y). -/
noncomputable def edit {Alpha : Type u} (x y : List Alpha) : ℕ :=
  sInf {n | Script true n x y}

abbrev L1 := lp (fun _ : ℕ => ℝ) 1

/-- The product of the two maximal distance ratios. -/
noncomputable def distortion {X : Type u} (ρ : X → X → ℝ) (f : X ↪ L1) : ℝ :=
  sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
    sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

/-- The infimum over injective maps to real absolutely summable sequences. -/
noncomputable def leastDistortion {X : Type u} (ρ : X → X → ℝ) : ℝ :=
  sInf (Set.range (distortion ρ))

abbrev Words (Alpha : Type u) (d : ℕ) := {x : List Alpha // x.length ≤ d}

noncomputable def E (Alpha : Type u) (d : ℕ) : ℝ :=
  leastDistortion (fun x y : Words Alpha d => (edit x.val y.val : ℝ))

noncomputable def exponentScale (c : ℝ) (d : ℕ) : ℝ :=
  Real.exp (c * Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))))

/-- Supremum over finite alphabet cardinalities. -/
noncomputable def alphabetSup (d : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ n : ℕ, 2 ≤ n ∧ r = E (Fin n) d}

/-- A finite nonempty subset of binary words of one common length. -/
def BinaryWitness (c : ℝ) (d : ℕ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧ ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧
    (∀ w ∈ S, w.length = n) ∧
    exponentScale c d ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ))

/-- Uniform two-sided bounds with common positive constants and threshold. -/
def MainClaim : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (Alpha : Type u) [Fintype Alpha], 2 ≤ Fintype.card Alpha →
      exponentScale c d ≤ E Alpha d ∧ E Alpha d ≤ exponentScale C d) ∧
    BinaryWitness c d ∧
    exponentScale c d ≤ alphabetSup d ∧ alphabetSup d ≤ exponentScale C d

end EditDistortion

universe u

def edit_distance_main_statement : Prop :=
  EditDistortion.MainClaim.{u}

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target.{u} : Prop :=
  _root_.OAI.edit_distance_main_statement.{u}

end Problem

/- Formalization scope, from lean/docs/099.md: The formalization determines the exponential scale of the least $\ell_1$ distortion of unit-cost edit distance on strings of length at most $d$. For every sufficiently large $d$, uniformly over finite alphabets with at least two symbols, the distortion lies between $\exp(c\sqrt{\log d\,\log\log d})$ and $\exp(C\sqrt{\log d\,\log\log d})$ for absolute constants $c,C>0$. The lower bound has a witness consisting of binary strings of one common length, and the same scale controls the supremum over finite alphabets. The formalization gives two finite-circle constructions of binary strings whose least $\ell_1$ distortion is at least $\exp(c\sqrt{\log d\,\log\log d})$ for all sufficiently large length caps $d$. The witnesses use strings of one common length and include the binary coding transfers with their stated uniform bounds. It also gives a finite histogram embedding with distortion at most $\exp(C\sqrt{\log d\,\log\log d})$ for all strings of length at most $d$, uniformly over finite alphabets, including the empty string. Thus the lower and upper exponential scales agree up to absolute constants. The formalization gives two lower-bound constructions for the $\ell_1$ distortion of ordinary edit distance on binary words. For every sufficiently large length cap $d$, each construction supplies a finite set of at least two binary words of one common length at most $d$ whose least $\ell_1$ distortion is at least $\exp(c\sqrt{\log d\,\log\log d})$ for an absolute $c>0$. The selected statements are the binary lower bounds. The paper's constant-distortion binary conversion and the companion upper embedding theorem are outside them. -/
