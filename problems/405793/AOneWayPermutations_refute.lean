/-
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

import FormalConjecturesUtil

/-!
Stated in this library, not converted from another corpus: `source` is this
repository, `source_locator` this file, and `source_version` the commit that
holds it. The one-wayness definition is the one in
`authored/OneWayFunctions.lean`, repeated here because each obligation is a
self-contained module.

- problem_id: AOneWayPermutations_refute
- collection: authored
- question_id: authored:OneWayPermutations
- source: mathdb-lean
- source_locator: authored/OneWayPermutations.lean#Target
- prose: Do one-way permutations exist? A one-way function that, for every n, maps the n-bit strings bijectively onto the n-bit strings.
- notes: One-way permutation -- https://en.wikipedia.org/wiki/One-way_function#Related_concepts
- track: open
- answer_shape: refute
- pair_id: AOneWayPermutations
- pair_role: refute
- source_category: research open
- source_ams: 68 94
- generator: adapters/authored/adapter.py
-/

open ComplexityTheory Finset

namespace Problem

/-- Bitstrings of length `n`, as a finite type. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- `successCount f A n m`: the number of pairs `(x, r)` of an `n`-bit input `x` and `m`
random bits `r` for which the inverter `A`, given `f x` and `r`, returns some preimage of
`f x`. Dividing by `2 ^ (n + m)` gives the success probability of the inverter. -/
def successCount (f : List Bool → List Bool) (A : List Bool × List Bool → List Bool)
    (n m : ℕ) : ℕ :=
  (((univ : Finset (Bits n)) ×ˢ (univ : Finset (Bits m))).filter
    (fun xr => f (A (f (List.ofFn xr.1), List.ofFn xr.2)) = f (List.ofFn xr.1))).card

/-- `f` is a one-way function; see `authored/OneWayFunctions.lean` for the reading of each
clause. -/
def IsOneWayFunction (f : List Bool → List Bool) : Prop :=
  IsPolyTime f ∧
  ∀ A : List Bool × List Bool → List Bool, IsPolyTime A →
    ∀ m p : Polynomial ℕ, ∃ N : ℕ, ∀ n ≥ N,
      successCount f A n (n + m.eval n) * p.eval n < 2 ^ (n + (n + m.eval n))

/-- `f` is a one-way permutation: one-way, and for every `n` a bijection from the `n`-bit
strings onto the `n`-bit strings (so in particular length-preserving). -/
def IsOneWayPermutation (f : List Bool → List Bool) : Prop :=
  IsOneWayFunction f ∧
  ∀ n : ℕ, Set.BijOn f {x | x.length = n} {x | x.length = n}

/-- One-way permutations exist. -/
abbrev Target : Prop :=
  ¬ (
    ∃ f : List Bool → List Bool, IsOneWayPermutation f
  )

end Problem

/-!
- source_version: 2fe7c76111373ea1d5503c074350e836cf33de46
-/
