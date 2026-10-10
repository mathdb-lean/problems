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

- problem_id: SensitivitySeparation
- collection: openai-math
- question_id: openai-math:132
- source: openai-math
- source_locator: lean/ComparatorChallenges/SensitivitySeparation.lean#OAI.Paper320.quantitative_separation
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Constructs total Boolean functions with block sensitivity $`\mathop{\mathrm{bs}}\nolimits (f)\ge s(f)^\alpha`$ for a fixed α &gt; 2, disproving the quadratic strengthening of the Sensitivity Conjecture. Here $`s(f)`$ counts influential individual-bit flips, while block sensitivity allows disjoint groups of bits to change together. ([Lean](lean/docs/132.md)) We disprove the quadratic strengthening of the Sensitivity Conjecture by constructing nonconstant total Boolean functions whose block sensitivity grows faster than any constant multiple of sensitivity squared. In fact, for some fixed α &gt; 2, our examples have unbounded block sensitivity and satisfy $`\mathop{\mathrm{bs}}\nolimits (f)\ge s(f)^\alpha`$.
- notes: OpenAI math result family 132, A superquadratic separation of sensitivity and block sensitivity -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/132.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.Paper320.quantitative_separation
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.Sensitivity.Separation
- source_main_result: OAI.Paper320.quantitative_separation
- source_papers: preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/paper.pdf
- source_scope_note: lean/docs/132.md
- source_field: Combinatorics
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

noncomputable section
open scoped Classical

namespace Paper320

def flip {I : Type} (x : I → Bool) (B : Finset I) : I → Bool :=
  fun i => if i ∈ B then !(x i) else x i

def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (flip x {i}) ≠ f x).card

def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
    then blocks.card else 0

def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)

def quantitative_separation_statement : Prop :=
  ∀ (d : ℕ) (hd : 1 ≤ d),
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      0 < n ∧ f (fun _ => false) = false ∧
      (∃ x y : Fin n → Bool, f x ≠ f y) ∧
      (2 : ℝ) ^ d / (4 * ((d : ℝ) + 2) ^ 2) ≤
        (blockSensitivity f : ℝ) / (sensitivity f : ℝ) ^ 2

end Paper320

end

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.Paper320.quantitative_separation_statement

end Problem

/- Formalization scope, from lean/docs/132.md: The formalized result disproves a universal quadratic bound of block sensitivity by sensitivity for total Boolean functions. For every integer $d\ge1$, it constructs a nonconstant function with $\mathrm{bs}(f)/s(f)^2\ge2^d/(4(d+2)^2)$, making the ratio unbounded. The formalization also gives a fixed exponent $\alpha>2$ and a sequence with $s(f)^\alpha\le\mathrm{bs}(f,0)$ while the latter tends to infinity; here $\mathrm{bs}(f,0)$ is block sensitivity at the all-zero input. -/
