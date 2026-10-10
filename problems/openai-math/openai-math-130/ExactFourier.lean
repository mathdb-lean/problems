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

- problem_id: ExactFourier
- collection: openai-math
- question_id: openai-math:130
- source: openai-math
- source_locator: lean/ComparatorChallenges/ExactFourier.lean#OAI.ExactFourier.main_theorem
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Gives a deterministic length-n discrete Fourier transform algorithm using $`O(n(\log n)^{1-\delta})`$ operations for every n, with explicit $`\delta=10^{-13}`$. The model uses exact complex arithmetic, unrestricted coefficients and a supplied root of unity, and counts scalar preparation and logarithmic-word indexing. ([Lean](lean/docs/130.md)) We construct exact nonuniform Fourier circuits of size $`o(n\log n)`$ along an unbounded sequence of lengths, counting every addition, subtraction, and scalar multiplication. This refutes the $`\Omega(n\log n)`$ lower bound in the unrestricted complex linear-circuit model. The construction uses a finite tensor saving: a tensor power of some invertible nonmonomial complex matrix can be computed with fewer matrix calls than the standard tensor-axis algorithm on the same coordinates, when invertible monomial maps are allowed freely between calls. We give a deterministic algorithm that computes the discrete Fourier transform at every length n in $`O(n(\log n)^{1-10^{-13}})`$ operations. The model uses exact complex arithmetic, unrestricted coefficients, specified Fourier roots, and unit-cost logarithmic-size indexing; scalar preparation and array organization are included.
- notes: OpenAI math result family 130, Exact Fourier transforms below $`n\log n`$ -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/130.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.ExactFourier.main_theorem
- source_theorem_count: 1
- source_solution_module: OAI.Computability.FourierCircuit.Main
- source_main_result: OAI.ExactFourier.main_theorem
- source_papers: preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf
- source_scope_note: lean/docs/130.md
- source_field: Computability
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

/-!
Scalar circuits for exact discrete Fourier transforms.
No bounds on predetermined complex coefficients, reuse, storage, or conditioning.
-/

namespace ExactFourier

/-- One charged scalar gate, referencing only available values. -/
inductive Gate (w : ℕ) where
  | add (i j : Fin w)
  | sub (i j : Fin w)
  | scale (c : ℂ) (i : Fin w)

def Gate.eval {w : ℕ} (v : Fin w → ℂ) : Gate w → ℂ
  | .add i j => v i + v j
  | .sub i j => v i - v j
  | .scale c i => c * v i

/-- A topologically ordered scalar DAG; available values are never consumed. -/
inductive Program (n : ℕ) : ℕ → Type where
  | nil : Program n 0
  | step {k : ℕ} (p : Program n k) (g : Gate (n + 1 + k)) : Program n (k + 1)

def Program.eval {n : ℕ} : {k : ℕ} → Program n k → (Fin n → ℂ) →
    (Fin (n + 1 + k) → ℂ)
  | 0, .nil, x => Fin.snoc x 0
  | _ + 1, .step p g, x =>
      let v := p.eval x
      Fin.snoc v (g.eval v)

/-- Outputs name available values, so permutations and arbitrary fanout are uncharged. -/
structure Circuit (n : ℕ) where
  size : ℕ
  program : Program n size
  outputs : Fin n → Fin (n + 1 + size)

def Circuit.eval {n : ℕ} (C : Circuit n) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => C.program.eval x (C.outputs i)

noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
noncomputable def fourierMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => zeta n ^ (j.val * k.val)

def Circuit.Computes {n : ℕ} (C : Circuit n) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x, C.eval x = A.mulVec x

/-- The precise quantified formulation of source theorem `thm:main`. -/
def MainStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, 2 ≤ N₀ → ∃ n : ℕ, N₀ ≤ n ∧
    ∃ C : Circuit n, C.Computes (fourierMatrix n) ∧
      (C.size : ℝ) < c * (n : ℝ) * Real.logb 2 (n : ℝ)

def main_theorem_statement : Prop :=
  MainStatement

end ExactFourier

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.ExactFourier.main_theorem_statement

end Problem

/- Formalization scope, from lean/docs/130.md: The formalized result gives exact discrete Fourier transforms with arbitrarily small normalized circuit cost along an unbounded sequence of lengths. For every $c>0$ and every cutoff $N_0\ge2$, some $n\ge N_0$ has a circuit computing the unnormalized DFT with fewer than $cn\log_2 n$ gates. Addition, subtraction, and multiplication by a predetermined complex scalar each cost one gate; diagonal scalings are charged. The result is subsequential, with no all-length, bounded-coefficient, conditioning, or bit-complexity claim. A separate uniform formalization gives fixed deterministic programs for every positive length $n$, computing the canonical discrete Fourier transform and the full convolution of two length-$n$ complex vectors exactly. Their work is $O(n(\log n)^{1-10^{-13}})=o(n\log n)$, including root-order selection and scalar preparation. The chosen root of unity is supplied; the model permits exact complex arithmetic and unrestricted coefficients, while integer values and indices remain polynomially bounded in $n$. The synthesis appendix's extraction, search, and printer uniformization is outside these selected statements. -/
