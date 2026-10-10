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

import MathDBUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: E1141
- collection: erdos
- question_id: erdos:1141
- source: formal-conjectures
- source_locator: FormalConjectures/ErdosProblems/1141.lean#erdos_1141
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many $n$ such that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$? In [Va99] it is asked whether $968$ is the largest integer with this property, but this is an error, since for example $968-9=7\cdot 137$. The list of $n$ satisfying the given property is [A214583] in the OEIS. The largest known such $n$ is $1722$. The answer is negative: [APSSV26b] proves a stronger finiteness theorem, deducing it from Pollack [Po17]. Oriike [Or26] formalised the deduction in Lean.
- notes: Erdos Problem 1141 -- https://www.erdosproblems.com/1141
- track: solved
- answer_shape: decide
- source_stem: 1141
- mathdb_ref: erdos:1141
- source_namespace: Erdos1141
- source_theorem: erdos_1141
- source_category: research solved
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- generator: adapters/formal_conjectures/adapter.py
- gold_answer: False
-/

open Nat Set

namespace Problem

/- ## The two external inputs

The formal proof linked on `erdos_1141` below assumes both of these, and states neither. They are
recorded here so the `assuming` clause on that theorem can name them. -/

/-- The cutoff $m^{1/4 + \varepsilon}$ of Theorem 1.3 of [Po17]. -/
noncomputable def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ := (m : ℝ) ^ ((1 / 4 : ℝ) + ε)

/--
The primes $\ell \leq m^{1/4+\varepsilon}$ with $\chi(\ell) = 1$.

This does not require $\chi$ to be quadratic. That hypothesis belongs to the theorem below, as it
does in the paper.
-/
noncomputable def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌈residuePrimeUpperBound m ε⌉₊ + 1)).filter fun ℓ =>
    ℓ.Prime ∧ (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧ χ (ℓ : ZMod m) = 1

/--
The property that $n-k^2$ is prime for all $k$ with $(n,k)=1$ and $k^2 < n$.
-/
def Erdos1141Prop (n : ℕ) : Prop :=
  ∀ k, k ^ 2 < n → Coprime n k → (n - k ^ 2).Prime

instance (n : ℕ) : Decidable (Erdos1141Prop n) :=
  decidable_of_iff (∀ k ≤ .sqrt (n - 1), Coprime n k → (n - k ^ 2).Prime) <| by
    cases n with
    | zero => simp [Erdos1141Prop]
    | succ n' =>
      simp [Erdos1141Prop, le_sqrt, pow_two]

abbrev Target (verdict : Prop) : Prop :=
    verdict ↔ Infinite { n | Erdos1141Prop n }

end Problem
