/-
Copyright 2026 The Formal Conjectures Authors.
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
Stated in this library. The definitions follow formal-conjectures (e04cc601):
`HasMeromorphicContinuation` from `FormalConjectures/Wikipedia/HasseWeil.lean`
and `Weak` from `FormalConjectures/Millennium/BSD.lean`, whose statement
`weak_birch_swinnerton_dyer_conjecture_rat` imports the former file. The
converter drops that import -- the support library does not carry
`FormalConjectures/` -- so the settled target fails to elaborate; this file
carries the one definition it needs and nothing else changes.

- problem_id: ABirchSwinnertonDyer
- collection: authored
- question_id: authored:BirchSwinnertonDyer
- source: mathdb-lean
- source_locator: authored/BirchSwinnertonDyer.lean#Target
- prose: The weak Birch and Swinnerton-Dyer conjecture over the rationals, the Clay Millennium Prize statement: for every elliptic curve E over ℚ whose Mordell–Weil group is finitely generated, any meromorphic continuation of the L-series of E has order of vanishing at s = 1 equal to the rank of E(ℚ). Only the order of vanishing is stated, not the leading-coefficient formula.
- notes: Millennium Prize problem BSD -- https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/
- track: open
- answer_shape: proof
- source_category: research open
- source_ams: 11 14
- generator: adapters/authored/adapter.py
-/

namespace Problem

/-- The L-series of `E` has the meromorphic continuation `L`: `L` is meromorphic on `ℂ` and
agrees with `E.LSeries` on `Re s > 3/2`, where the series converges absolutely. -/
def HasMeromorphicContinuation {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The weak Birch and Swinnerton-Dyer conjecture for a number field `K`: for every elliptic
curve `E` over `K`, a meromorphic continuation of its L-series has order `rank E(K)` at `s = 1`.
The rank is `AddCommGroup.freeRank`, which needs `E(K)` finitely generated; that is the
Mordell–Weil theorem, which Mathlib does not have, so it appears as a hypothesis. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] [AddGroup.FG E.toAffine.Point] (L : ℂ → ℂ),
    HasMeromorphicContinuation E L →
      meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

/-- The weak Birch and Swinnerton-Dyer conjecture over `ℚ`, a Clay Millennium Prize problem. -/
abbrev Target : Prop :=
  Weak ℚ

end Problem

/-!
- source_version: b80da422c1869ddababb2992c7dc83556e0f930c
-/
