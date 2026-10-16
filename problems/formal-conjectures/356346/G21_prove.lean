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

- problem_id: G21_prove
- collection: green
- question_id: green:21
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/21.lean#green_21
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Suppose that $a_1, \dots, a_k$ are integers which do not satisfy Rado's condition: thus if $\sum_{i \in I} a_i = 0$ then $I = \emptyset$. It then follows from Rado's theorem that the equation $a_1x_1 + \cdots + a_kx_k = 0$ is not partition regular. Write $c(a_1, \dots, a_k)$ for the least number of colours required in order to colour $\mathbb{N}$ so that there is no monochromatic solution to $a_1x_1 + \cdots + a_kx_k = 0$. Is $c(a_1, \dots, a_k)$ bounded in terms of $k$ only? This problem, which is known as Rado's boundedness conjecture, dates back to 1933 [Ra33]. It is open for all $k \geq 4$.
- notes: Green, open problem 21 -- https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.21
- track: open
- answer_shape: prove
- pair_id: G21
- pair_role: prove
- source_stem: 21
- source_namespace: Green21
- source_theorem: green_21
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: not_radoCondition_iff ne_zero_of_not_radoCondition minColours_eq_zero minColours_ones
- generator: adapters/formal_conjectures/adapter.py
-/

open Finset

namespace Problem

/--
The coefficients $a_1, \dots, a_k$ satisfy **Rado's condition** if $\sum_{i \in I} a_i = 0$ for
some non-empty $I \subseteq [k]$.

For a single homogeneous equation with $k > 0$ nonzero coefficients this is exactly the
criterion of Rado's theorem [Ra33]: $a_1x_1 + \cdots + a_kx_k = 0$ is partition regular if and
only if the coefficients satisfy it. (With a zero coefficient the condition holds trivially, but
e.g. $0 \cdot x_1 + x_2 = 0$ has no solution in positive integers.)
-/
def RadoCondition {k : ℕ} (a : Fin k → ℤ) : Prop :=
  ∃ I : Finset (Fin k), I.Nonempty ∧ ∑ i ∈ I, a i = 0

/--
$c(a_1, \dots, a_k)$, the least number of colours required in order to colour $\mathbb{N}$ so
that there is no monochromatic solution to $a_1x_1 + \cdots + a_kx_k = 0$.

The solutions $x_i$ are required to be *positive*, as in [FoKl06]: were $0$ admitted then
$x_1 = \cdots = x_k = 0$ would be a monochromatic solution for every colouring, and no number of
colours would ever suffice. The $x_i$ are not required to be distinct.

When the coefficients do not satisfy `RadoCondition`, Rado's theorem [Ra33] guarantees that some
finite colouring has no monochromatic solution, so the set below is non-empty and this `sInf` is
a genuine minimum.
-/
noncomputable def minColours {k : ℕ} (a : Fin k → ℤ) : ℕ :=
  sInf {r | ∃ col : ℕ → Fin r, ∀ x : Fin k → ℕ, (∀ i, 0 < x i) →
    (∀ i j, col (x i) = col (x j)) → ∑ i, a i * x i ≠ 0}

/--
The largest $d \leq r$ such that $\sum_{i \in I} a_i \equiv 0 \pmod{2^d}$ for some non-empty
subset $I \subseteq [k]$, where $a_1, \dots, a_k \in \mathbb{Z}/2^r\mathbb{Z}$.

Congruence mod $2^d$ of an element of $\mathbb{Z}/2^r\mathbb{Z}$ is expressed through its
canonical representative `ZMod.val`; this is unambiguous because $d$ is capped at $r$.
-/
noncomputable def maxDepth {k r : ℕ} (a : Fin k → ZMod (2 ^ r)) : ℕ :=
  sSup {d | d ≤ r ∧ ∃ I : Finset (Fin k), I.Nonempty ∧ 2 ^ d ∣ (∑ i ∈ I, a i).val}

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
Not satisfying `RadoCondition` is Green's phrasing "if $\sum_{i \in I} a_i = 0$ then
$I = \emptyset$".
-/
@[category test, AMS 5 11]
theorem not_radoCondition_iff {k : ℕ} (a : Fin k → ℤ) :
    ¬ RadoCondition a ↔ ∀ I : Finset (Fin k), ∑ i ∈ I, a i = 0 → I = ∅ := by
  simp only [RadoCondition, not_exists, not_and, Finset.nonempty_iff_ne_empty]
  exact ⟨fun h I hI => by_contra fun hne => h I hne hI, fun h I hne hI => hne (h I hI)⟩

/--
A tuple failing `RadoCondition` has no zero coefficient, since a singleton is a non-empty subset.
-/
@[category test, AMS 5 11]
theorem ne_zero_of_not_radoCondition {k : ℕ} {a : Fin k → ℤ} (ha : ¬ RadoCondition a) (i : Fin k) :
    a i ≠ 0 := fun h => ha ⟨{i}, Finset.singleton_nonempty i, by simpa using h⟩

/--
In the degenerate case $k = 0$ the equation reads $0 = 0$, so the empty tuple is a monochromatic
solution for every colouring and `minColours` takes its junk value `0`. The bound asserted by
`green_21` is therefore vacuously satisfied at $k = 0$, and the content of the problem is
unaffected.
-/
@[category test, AMS 5 11]
theorem minColours_eq_zero (a : Fin 0 → ℤ) : minColours a = 0 := by
  have : {r | ∃ col : ℕ → Fin r, ∀ x : Fin 0 → ℕ, (∀ i, 0 < x i) →
      (∀ i j, col (x i) = col (x j)) → ∑ i, a i * x i ≠ 0} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    exact fun col h => h (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (by simp)
  rw [minColours, this, Nat.sInf_empty]

/--
A case where the infimum defining `minColours` is a genuine minimum rather than the junk value of
`sInf ∅`. The coefficients $(1, 1, 1)$ fail `RadoCondition`, and since the $x_i$ are positive the
equation $x_1 + x_2 + x_3 = 0$ has no solutions at all, so a single colour suffices; no colouring
of $\mathbb{N}$ into `Fin 0` exists, so $0$ is not attainable.
-/
@[category test, AMS 5 11]
theorem minColours_ones : minColours ![(1 : ℤ), 1, 1] = 1 := by
  have h1 : 1 ∈ {r | ∃ col : ℕ → Fin r, ∀ x : Fin 3 → ℕ, (∀ i, 0 < x i) →
      (∀ i j, col (x i) = col (x j)) → ∑ i, (![(1 : ℤ), 1, 1]) i * x i ≠ 0} := by
    refine ⟨fun _ => 0, fun x hx _ => ?_⟩
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, one_mul]
    omega
  have h0 : 0 ∉ {r | ∃ col : ℕ → Fin r, ∀ x : Fin 3 → ℕ, (∀ i, 0 < x i) →
      (∀ i j, col (x i) = col (x j)) → ∑ i, (![(1 : ℤ), 1, 1]) i * x i ≠ 0} := by
    rintro ⟨col, -⟩
    exact (col 0).elim0
  rw [minColours]
  exact le_antisymm (Nat.sInf_le h1) (Nat.one_le_iff_ne_zero.2 fun h =>
    h0 ((Nat.sInf_eq_zero.mp h).resolve_right (Set.nonempty_iff_ne_empty.mp ⟨1, h1⟩)))

abbrev Target : Prop :=
    ∃ B : ℕ → ℕ, ∀ (k : ℕ) (a : Fin k → ℤ),
        ¬ RadoCondition a → minColours a ≤ B k

end Problem
