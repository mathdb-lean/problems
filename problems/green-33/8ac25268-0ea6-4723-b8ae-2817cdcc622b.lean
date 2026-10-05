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

import MathdbUtil

/-!
Converted from another corpus. `source` names it, `source_version`
pins the revision, and `source_locator` points at the one
declaration this came from. Every `source_` field describes that
declaration as it stands there, not as it stands here.

Read `track` for whether the problem is solved, which is a fact
about mathematics. `source_has_lean_proof` is a different claim --
whether that corpus holds a machine-checked proof -- and is false
for almost every problem, because it is a statement repository.

- problem_id: G33_refute
- collection: green
- question_id: green:33
- source: formal-conjectures
- source_locator: FormalConjectures/GreensOpenProblems/33.lean#green_33
- source_version: e04cc601840dd7a37f89b821a67f3a9e3c38d9c3
- prose: Are there infinitely many $q$ for which there is a set $A \subset \mathbb{Z}/q\mathbb{Z}$, $|A| = (\sqrt{2} + o(1))q^{1/2}$, with $A + A = \mathbb{Z}/q\mathbb{Z}$? [Gr24]
- notes: Green, open problem 33
- track: open
- answer_shape: refute
- pair_id: G33
- pair_role: refute
- source_stem: 33
- source_namespace: Green33
- source_theorem: green_33
- source_category: research open
- source_ams: 5 11
- source_has_lean_proof: false
- source_lean_proof_kernel_clean: n/a
- context_lemmas: green_33.sanity_sq_bound
- generator: adapters/formal_conjectures/adapter.py
-/

open Filter
open scoped Pointwise

namespace Problem

/-! Auxiliary lemmas upstream proves in the same file, frozen in with
the definitions: an answer may cite them or prove its own. Each is
tagged `API` or `test` upstream and is listed in `context_lemmas`
above. See docs/CONVERSION.md for what is deliberately not here. -/

/-- Trivial lower bound: if $A + A = \mathbb{Z}/q\mathbb{Z}$, then $|A|^2 \geq q$,
since the sumset $A + A$ has at most $|A|^2$ elements. -/
@[category test, AMS 5 11]
theorem green_33.sanity_sq_bound (q : ℕ+) (A : Finset (ZMod q))
    (hA : A + A = Finset.univ) : (q : ℕ) ≤ A.card ^ 2 := by
  calc (q : ℕ) = Fintype.card (ZMod q) := (ZMod.card q).symm
    _ = (Finset.univ : Finset (ZMod q)).card := Finset.card_univ.symm
    _ = (A + A).card := by rw [hA]
    _ ≤ A.card * A.card := Finset.card_add_le ..
    _ = A.card ^ 2 := (sq A.card).symm

-- TODO(jgd): Add variants from comments in [Gr24]

abbrev Target : Prop :=
    ¬ (
      ∀ ε : ℝ, 0 < ε →
          ∃ᶠ q : ℕ+ in atTop,
            ∃ A : Finset (ZMod q),
              A + A = Finset.univ ∧
              |((A.card : ℝ) / Real.sqrt q - Real.sqrt 2)| < ε
    )

end Problem
