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

- problem_id: QuasiRiemannHypothesis
- collection: openai-math
- question_id: openai-math:003
- source: openai-math
- source_locator: lean/ComparatorChallenges/QuasiRiemannHypothesis.lean#OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Proves that every Dirichlet L-function, including $`\zeta(s)`$, is zero-free in $`\Re s\gt 7/8`$, resolving the quasi-Riemann hypothesis. The same half-plane is zero-free for every finite-order Hecke L-function over $`\mathbb Q(\sqrt{-3})`$. A companion gives a different proof of the zero-free half-plane $`\Re s\gt 11/12`$. ([Lean](lean/docs/003.md)) We prove that all finite-order Hecke L-functions over $`\mathbb Q(\sqrt{-3})`$ and all Dirichlet L-functions are zero-free in the half-plane $`\Re s\gt 7/8`$, with the principal pole at s = 1 allowed. In particular, the Riemann zeta function is zero-free in this half-plane, proving the quasi-Riemann hypothesis. We prove the uniform exclusion of Landau–Siegel zeros. There is an absolute constant c &gt; 0 such that every real zero $`\beta\in(0,1)`$ of every primitive nonprincipal real Dirichlet L-function of conductor q ≥ 3 satisfies $`(1-\beta)\log q\ge c`$.
- notes: OpenAI math result family 003, The quasi-Riemann hypothesis -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/003.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
- source_theorem_count: 1
- source_solution_module: OAI.NumberTheory.DirichletL.Nonvanishing
- source_main_result: OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
- source_papers: preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026/paper.pdf
- source_scope_note: lean/docs/003.md
- source_field: NumberTheory
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

def riemannZeta_ne_zero_of_seven_eighths_lt_re_statement : Prop :=
  ∀ {s : ℂ} (hs : (7 / 8 : ℝ) < s.re),
    riemannZeta s ≠ 0

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re_statement

end Problem

/- Formalization scope, from lean/docs/003.md: The quasi-Riemann hypothesis asks for a fixed zero-free half-plane $\Re s>\theta$ with $\theta<1$. The formalization gives $\theta=7/8$ for the Riemann zeta function and every Dirichlet $L$-function, uniformly over all positive moduli and all characters. It also establishes the same bound for finite-order Hecke $L$-functions over $\mathbb Q(\sqrt{-3})$. The principal-character poles at $s=1$ are excluded in the Dirichlet and Hecke statements. The paper's later applications are not included. The formalized result gives a uniform logarithmic exclusion region for Landau–Siegel zeros. There is one constant $c>0$ such that every primitive nonprincipal real Dirichlet character of conductor $q\ge3$ and every real zero $0<\beta<1$ of its $L$-function satisfy $1-\beta\ge c/\log q$. Both character parities are included. No explicit value of $c$ is given. This excludes real zeros in $1-c/\log q<\beta<1$, but does not rule out real zeros elsewhere in $(0,1)$. -/
