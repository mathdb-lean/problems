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

- problem_id: PowerFreeValues
- collection: openai-math
- question_id: openai-math:020
- source: openai-math
- source_locator: lean/ComparatorChallenges/PowerFreeValues.lean#OAI.QuarticPowerFree.allDegrees
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves the squarefree-values conjecture for irreducible integer quartics with no fixed prime-square divisor: squarefree values on positive integers have the predicted positive Euler-product density. More generally, establishes the $`(d-2)`$-power-free density for irreducible integer polynomials of degrees four through eight under the necessary local condition; together with Browning's higher-degree theorem, this covers every d ≥ 4. ([Lean](lean/docs/020.md)) We prove that every irreducible integer quartic with no fixed prime-square divisor takes squarefree values with the predicted positive Euler-product density. More generally, we obtain the corresponding $`(d-2)`$-power-free density in degrees $`4\le d\le8`$. The proof combines number-field factorization, determinant estimates with adaptive auxiliary primes, and explicit low-degree geometry. Together with Browning's theorem for higher degrees, this gives the $`(d-2)`$-power-free density for every d ≥ 4.
- notes: OpenAI math result family 020, Squarefree quartics and power-free polynomial values -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/020.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.QuarticPowerFree.allDegrees
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.PowerFree.Main
- source_main_result: OAI.QuarticPowerFree.allDegrees
- source_papers: preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf
- source_scope_note: lean/docs/020.md
- source_field: NumberTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI



open Filter Asymptotics
open scoped Topology

namespace QuarticPowerFree

def PowerFree (k : ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ k ∣ a

def rho (f : Polynomial ℤ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun a : ℕ => (q : ℤ) ∣ f.eval (a : ℤ)).card

noncomputable def count (f : Polynomial ℤ) (k : ℕ) (X : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊X⌋₊).filter fun n : ℕ => PowerFree k (f.eval (n : ℤ))).card

def LocallyAdmissible (f : Polynomial ℤ) (k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → rho f (p ^ k) < p ^ k

noncomputable def localFactor (f : Polynomial ℤ) (k : ℕ) (p : Nat.Primes) : ℝ :=
  1 - (rho f (p.val ^ k) : ℝ) / (p.val : ℝ) ^ k

noncomputable def densityConstant (f : Polynomial ℤ) (k : ℕ) : ℝ :=
  ∏' p : Nat.Primes, localFactor f k p

def DensityStatement (f : Polynomial ℤ) (k : ℕ) : Prop :=
  Multipliable (localFactor f k) ∧
  0 < densityConstant f k ∧
  (fun X : ℝ => (count f k X : ℝ) - densityConstant f k * X) =o[atTop]
    (fun X : ℝ => X)

def allDegrees_statement : Prop :=
  ∀ (f : Polynomial ℤ) (hirr : Irreducible (f.map (Int.castRingHom ℚ))) (hdeglo : 4 ≤ f.natDegree) (hlocal : LocallyAdmissible f (f.natDegree - 2)),
    DensityStatement f (f.natDegree - 2)

end QuarticPowerFree

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.QuarticPowerFree.allDegrees_statement

end Problem

/- Formalization scope, from lean/docs/020.md: The formalized result proves positive-density power-free values for every integer polynomial $f$ irreducible over $\mathbb Q$ of degree $d\ge4$. Put $k=d-2$ and assume no prime $k$th power divides every value of $f$. Then the number of positive integers $n\le X$ for which $f(n)$ is $k$-free is $c_fX+o_f(X)$, where $c_f>0$ is the convergent product of local factors. Negative values are allowed and zero is excluded. No monicity, primitivity, or coefficient-height restriction is imposed. -/
