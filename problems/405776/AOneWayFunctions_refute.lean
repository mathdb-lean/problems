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
holds it. Polynomial time is `ComplexityTheory.IsPolyTime` from FormalConjecturesForMathlib,
the same notion the P versus NP statement uses.

- problem_id: AOneWayFunctions_refute
- collection: authored
- question_id: authored:OneWayFunctions
- source: mathdb-lean
- source_locator: authored/OneWayFunctions.lean#Target
- prose: Do one-way functions exist? A function on bitstrings computable in polynomial time such that every probabilistic polynomial-time algorithm, given f(x) for a uniformly random n-bit x, finds some preimage with probability smaller than 1/p(n) for every polynomial p and all sufficiently large n.
- notes: One-way function -- https://en.wikipedia.org/wiki/One-way_function
- track: open
- answer_shape: refute
- pair_id: AOneWayFunctions
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

/-- `f` is a one-way function (Goldreich, Foundations of Cryptography I, Definition 2.2.1):
it is computable in polynomial time, and for every polynomial-time inverter `A`, every
polynomial bound `m` on its random bits and every polynomial `p`, for all sufficiently
large `n` the probability over a uniform `n`-bit `x` and `n + m(n)` uniform random bits
that `A (f x, r)` is a preimage of `f x` is smaller than `1 / p(n)`.

A probabilistic polynomial-time algorithm is modelled as a deterministic polynomial-time
function of the pair (input, random bits). The inverter receives `n + m(n)` random bits
rather than `m(n)`, so that its input has length at least `n` whatever the length of
`f x`; this plays the role of the auxiliary input `1^n` in the textbook definition. -/
def IsOneWayFunction (f : List Bool → List Bool) : Prop :=
  IsPolyTime f ∧
  ∀ A : List Bool × List Bool → List Bool, IsPolyTime A →
    ∀ m p : Polynomial ℕ, ∃ N : ℕ, ∀ n ≥ N,
      successCount f A n (n + m.eval n) * p.eval n < 2 ^ (n + (n + m.eval n))

/-- One-way functions exist. -/
abbrev Target : Prop :=
  ¬ (
    ∃ f : List Bool → List Bool, IsOneWayFunction f
  )

end Problem

/-!
- source_version: 2fe7c76111373ea1d5503c074350e836cf33de46
-/
