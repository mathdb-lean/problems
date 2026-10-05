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

- problem_id: NBealConjecture_beal_conjecture
- collection: wikipedia
- question_id: wikipedia:BealConjecture
- source: formal-conjectures
- source_locator: FormalConjectures/Wikipedia/BealConjecture.lean#beal_conjecture
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: The **Beal Conjecture**: if we are given positive integers $A, B, C, x, y, z$ such that $x, y, z > 2$ and $A^x + B^y = C^z$ then $A, B, C$ have a common divisor.
- notes: Wikipedia: BealConjecture -- https://en.wikipedia.org/wiki/Beal_conjecture
- track: open
- answer_shape: proof
- source_stem: BealConjecture
- source_namespace: BealConjecture
- source_theorem: beal_conjecture
- source_category: research open
- source_ams: 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: flt_of_beal_conjecture
- generator: adapters/formal_conjectures/adapter.py
-/

namespace Problem

def bealConjecture : Prop := ∀ {A B C x y z : ℕ},
    A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < x → 2 < y → 2 < z →
    A^x + B^y = C^z → 1 < Finset.gcd {A, B, C} id

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/--
The Beal Conjecture implies Fermat's last theorem
-/
@[category textbook, AMS 11]
theorem flt_of_beal_conjecture (H : bealConjecture) :
    FermatLastTheorem := by
  intro n hn x y z hx hy hz
  by_contra h
  apply mul_ne_zero (mul_ne_zero hx hy) hz
  by_contra H''
  obtain ⟨hx, hy, hz⟩ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by aesop
  set G := Finset.gcd {x, y, z} id
  set x' := (x / G : ℕ)
  set y' := (y / G : ℕ)
  set z' := (z / G : ℕ)
  obtain ⟨hGx, hGy, hGz⟩ : G ∣ x ∧ G ∣ y ∧ G ∣ z := by
    refine ⟨?_, ?_, ?_⟩ <;> apply Finset.gcd_dvd (by aesop)
  obtain ⟨hx', hy', hz'⟩ : x' ≠ 0 ∧ y' ≠ 0 ∧ z' ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      apply Nat.div_ne_zero_iff_of_dvd (by assumption) |>.mpr ⟨(by assumption), _⟩ <;> aesop
  have Hxyz' : x'^n + y'^n = z'^n := by
    rwa [Nat.div_pow hGx, Nat.div_pow hGy, Nat.div_pow hGz,
      ←Nat.add_div_of_dvd_right, Nat.div_left_inj (dvd_add _ _)]
    all_goals apply pow_dvd_pow_of_dvd ; assumption
  apply ne_of_lt <| H hx' hy' hz' hn hn hn Hxyz'
  rw [←Finset.gcd_div_id_eq_one (Finset.mem_insert_self x {y, z}) (by trivial),
    Finset.gcd_eq_gcd_image, Finset.image_insert, Finset.image_insert,
    Finset.image_singleton]

abbrev Target : Prop :=
    bealConjecture

end Problem
