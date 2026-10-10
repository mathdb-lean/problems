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

- problem_id: FiniteCircle
- collection: openai-math
- question_id: openai-math:099
- source: openai-math
- source_locator: lean/ComparatorChallenges/FiniteCircle.lean#OAI.finiteCircle_fullMain
- source_version: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- prose: Determines the least distortion of embedding edit distance on words of length at most d into real ℓ1: it is $`\exp(\Theta(\sqrt{\log d\,\log\log d}))`$. Insertions, deletions and substitutions have unit cost. The constants are uniform over all finite alphabets with at least two symbols, even when the alphabet grows with d; binary words already force the lower bound. ([Lean](lean/docs/099.md)) We determine the exponential scale of the least ℓ1 distortion of unit-cost edit distance on all strings of length at most d. For every sufficiently large d, uniformly over finite alphabets of size at least two, the distortion lies between $`\exp(c\sqrt{\log d\,\log\log d})`$ and $`\exp(C\sqrt{\log d\,\log\log d})`$ for absolute constants $`c,C\gt 0`$. The lower bound already holds on binary strings of one common length. Thus the order of logarithmic distortion is sharp up to absolute constants. We give two finite-circle constructions of binary strings whose least ℓ1 distortion is $`\exp(\Omega(\sqrt{\log d\,\log\log d}))`$, where d bounds their length. Both constructions supply words of one common length for every sufficiently large cap. Two direct binary coding arguments transfer the constructions with absolute distortion and logarithmic block width. We also develop the overlapping-substring method of Ostrovsky and Rabani into a complete finite histogram embedding at the same exponential scale, uniformly over all finite alphabets and all words of length at most d, including the empty word. We give two independent constructions of binary words of one length at most d whose ordinary edit-distance metrics require ℓ1 distortion $`\exp(\Omega(\sqrt{\log d\,\log\log d}))`$ for every sufficiently large d. We also prove a constant-distortion binary conversion for one prescribed input length. Together with the companion upper embedding theorem, these lower bounds determine the order of logarithmic distortion uniformly over finite alphabets with at least two symbols.
- notes: OpenAI math result family 099, The sharp exponential scale of edit-distance distortion -- https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/099.md
- track: solved
- answer_shape: proof
- source_theorem: OAI.finiteCircle_fullMain
- source_theorem_count: 1
- source_solution_module: OAI.Combinatorics.FiniteCircle.Main
- source_papers: preprints/Edit-Distance-in-l1-Matching-Bounds-up-to-Constants-in-the-Exponent-September-27-2026/paper.pdf preprints/Finite-Circle-Obstructions-Binary-Codes-and-Histogram-Embeddings-for-Edit-Distance-September-27-2026/paper.pdf preprints/Tree-Constructions-for-the-l1-Distortion-of-Binary-Edit-Distance-September-27-2026/paper.pdf
- source_scope_note: lean/docs/099.md
- source_has_lean_proof: true
- source_lean_proof_kernel_clean: true
- generator: adapters/openai_math/adapter.py
-/


namespace OAI

namespace FiniteCircle

open scoped BigOperators List

universe u v

inductive EditStep {α : Type u} : List α → List α → Prop
  | insert (u v : List α) (a : α) : EditStep (u ++ v) (u ++ a :: v)
  | delete (u v : List α) (a : α) : EditStep (u ++ a :: v) (u ++ v)
  | substitute (u v : List α) (a b : α) : EditStep (u ++ a :: v) (u ++ b :: v)

inductive EditScript {α : Type u} : ℕ → List α → List α → Prop
  | nil (x : List α) : EditScript 0 x x
  | cons {n : ℕ} {x y z : List α} :
      EditStep x y → EditScript n y z → EditScript (n + 1) x z

noncomputable def editDistance {α : Type u} (x y : List α) : ℕ :=
  sInf {n : ℕ | EditScript n x y}

noncomputable def lcs {α : Type u} (x y : List α) : ℕ :=
  sSup {n : ℕ | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n}

noncomputable def deficit {α : Type u} (x y : List α) : ℕ := x.length - lcs x y

abbrev Words (α : Type u) (d : ℕ) := {x : List α // x.length ≤ d}
abbrev RealL1 := lp (fun _ : ℕ => ℝ) 1

noncomputable def distortion {α : Type u} {X : Type v} (word : X → List α)
    (f : X → RealL1) : ℝ :=
  (sSup {r : ℝ | ∃ x y : X, x ≠ y ∧
    r = ‖f x - f y‖ / (editDistance (word x) (word y) : ℝ)}) *
  (sSup {r : ℝ | ∃ x y : X, x ≠ y ∧
    r = (editDistance (word x) (word y) : ℝ) / ‖f x - f y‖})

noncomputable def optimalDistortion {α : Type u} {X : Type v}
    (word : X → List α) : ℝ :=
  sInf {D | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion word f}

noncomputable def E (α : Type u) (d : ℕ) : ℝ :=
  optimalDistortion (fun x : Words α d => x.val)

noncomputable def setDistortion (S : Set (List Bool)) : ℝ :=
  optimalDistortion (fun x : S => x.val)

noncomputable def alphabetSupremum (d : ℕ) : ℝ :=
  sSup {r | ∃ A : ℕ, 2 ≤ A ∧ r = E (Fin A) d}

noncomputable def exponentScale (d : ℕ) : ℝ :=
  Real.sqrt (Real.log d * Real.log (Real.log d))

def encode {α : Type u} {w : ℕ} (c : α → Fin w → Bool) (x : List α) : List Bool :=
  x.flatMap (fun a => List.ofFn (c a))

def interval {α : Type u} {w : ℕ} (c : α → Fin w → Bool)
    (a : α) (s len : ℕ) : List Bool :=
  ((List.ofFn (c a)).drop s).take len

def OffsetLocal {α : Type u} {w : ℕ} (δ : ℝ) (c : α → Fin w → Bool) : Prop :=
  ∀ a b : α, a ≠ b → ∀ s t : ℕ,
    s + w / 8 ≤ w → t + w / 8 ≤ w →
    (lcs (interval c a s (w / 8)) (interval c b t (w / 8)) : ℝ) ≤
      (1 - δ) * (w / 8 : ℕ)

def indexSpan {w : ℕ} (is : List (Fin w)) : ℕ :=
  match is with
  | [] => 0
  | i :: js => (js.getLastD i).val + 1 - i.val

def AnchorLocal {α : Type u} {w : ℕ} (ε : ℝ) (c : α → Fin w → Bool) : Prop :=
  ∀ a b : α, ∀ is js : List (Fin w),
    is.Pairwise (fun i j => i.val < j.val) →
    js.Pairwise (fun i j => i.val < j.val) →
    is.length = js.length → (w : ℝ) / 4 ≤ is.length →
    (indexSpan is - is.length : ℕ) ≤ ε * w →
    (indexSpan js - js.length : ℕ) ≤ ε * w →
    (∀ ij ∈ is.zip js, c a ij.1 = c b ij.2) →
    a = b ∧ ∃ i : Fin w, (i, i) ∈ is.zip js

def SubstitutionBounds {α : Type u} [Fintype α] {w : ℕ}
    (a C : ℝ) (c : α → Fin w → Bool) : Prop :=
  0 < w ∧ (w : ℝ) ≤ C * Real.log (2 * Fintype.card α) ∧
  (∀ L : ℕ, ∀ x y : List α, x.length = L → y.length = L →
    a * w * deficit x y ≤ (deficit (encode c x) (encode c y) : ℝ) ∧
    deficit (encode c x) (encode c y) ≤ w * deficit x y) ∧
  (∀ x y : List α, editDistance (encode c x) (encode c y) ≤ w * editDistance x y)

def TwoCodes (a C δ ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α], 2 ≤ Fintype.card α →
    (∃ (w : ℕ) (c : α → Fin w → Bool),
      SubstitutionBounds a C c ∧ OffsetLocal δ c) ∧
    (∃ (w : ℕ) (c : α → Fin w → Bool),
      SubstitutionBounds a C c ∧ AnchorLocal ε c)

def period (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) : ℕ := ∏ k : Fin h, p l k

def circleSize (h : ℕ) (p : ℕ → ℕ → ℕ) : ℕ :=
  2 * ∏ l : Fin h, period h p (l.val + 1)

def MaskPrimes (h : ℕ) (p : ℕ → ℕ → ℕ) : Prop :=
  (∀ l k : Fin h, Nat.Prime (p (l.val + 1) k)) ∧
  Function.Injective (fun lk : Fin h × Fin h => p (lk.1.val + 1) lk.2) ∧
  ∀ l k : Fin h, h ^ 3 ≤ p (l.val + 1) k ∧ p (l.val + 1) k ≤ 2 * h ^ 3

def ExcludedPrimes (m : ℕ) (p : ℕ → ℕ → ℕ) : Prop :=
  (∀ l k : Fin m, Nat.Prime (p (l.val + 1) k)) ∧
  Function.Injective (fun lk : Fin m × Fin m => p (lk.1.val + 1) lk.2) ∧
  ∀ l k : Fin m, m ^ 3 < p (l.val + 1) k ∧ p (l.val + 1) k ≤ m ^ 5

abbrev MaskTag (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) := Σ k : Fin h, Fin (p l k)

def maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) : List (MaskTag h p l) :=
  (List.ofFn fun k : Fin h => List.ofFn fun b : Fin (p l k) => Sigma.mk k b).flatten

def MaskAlphabet (h : ℕ) (p : ℕ → ℕ → ℕ) : ℕ → Type
  | 0 => Bool
  | l + 1 => MaskTag h p (l + 1) × MaskAlphabet h p l

instance maskAlphabetFintype (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype (MaskAlphabet h p l) := by
  induction l with
  | zero => exact inferInstanceAs (Fintype Bool)
  | succ l ih => exact @instFintypeProd _ _ inferInstance ih

def MaskState (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ) : ℕ → Type
  | 0 => ZMod M
  | l + 1 => MaskTag h p (l + 1) → MaskState h p M l

def shiftMaskState (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ) :
    (l : ℕ) → MaskState h p M l → ZMod M → MaskState h p M l
  | 0, v, θ => (show ZMod M from v) + θ
  | l + 1, v, θ => fun j => shiftMaskState h p M l (v j) θ

def maskGamma (h : ℕ) (p : ℕ → ℕ → ℕ) (M l a : ℕ)
    (j : MaskTag h p l) : ZMod M :=
  (∑ k : Fin h, ((M / p l k * (a % p l k) : ℕ) : ZMod M)) +
    ((j.2.val * (M / p l j.1) * (a % p l j.1) : ℕ) : ZMod M)

def maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ) :
    (l : ℕ) → MaskState h p M l → List (MaskAlphabet h p l)
  | 0, v => (List.range M).map (fun b => decide (((b : ZMod M) - (show ZMod M from v)).val < M / 2))
  | l + 1, v => (List.range (R * period h p (l + 1))).flatMap fun a =>
      (maskTags h p (l + 1)).flatMap fun j =>
        (maskWord h p R M l
          (shiftMaskState h p M l (v j) (maskGamma h p M (l + 1) a j))).map
          (fun x => (j, x))

def ExcludedAlphabet (m L : ℕ) : ℕ → Type
  | 0 => Fin L × Bool
  | l + 1 => Fin m × ExcludedAlphabet m L l

instance excludedAlphabetFintype (m L l : ℕ) : Fintype (ExcludedAlphabet m L l) := by
  induction l with
  | zero => exact inferInstanceAs (Fintype (Fin L × Bool))
  | succ l ih => exact @instFintypeProd _ _ inferInstance ih

def ExcludedState (m L : ℕ) : ℕ → Type
  | 0 => ZMod L
  | l + 1 => Fin m → ExcludedState m L l

def shiftExcludedState (m L : ℕ) :
    (l : ℕ) → ExcludedState m L l → ZMod L → ExcludedState m L l
  | 0, v, θ => (show ZMod L from v) + θ
  | l + 1, v, θ => fun i => shiftExcludedState m L l (v i) θ

def excludedTranslation (m : ℕ) (p : ℕ → ℕ → ℕ) (L l s : ℕ) (i : Fin m) :
    ZMod L := ∑ j ∈ Finset.univ.erase i, ((L / p l j * (s % p l j) : ℕ) : ZMod L)

def excludedWord (m : ℕ) (p : ℕ → ℕ → ℕ) (R L : ℕ) :
    (l : ℕ) → ExcludedState m L l → List (ExcludedAlphabet m L l)
  | 0, v => List.ofFn fun b : Fin L =>
      (b, decide (((b.val : ZMod L) - (show ZMod L from v)).val < L / 2))
  | l + 1, v => (List.range (R * period m p (l + 1))).flatMap fun s =>
      (List.ofFn fun i : Fin m =>
        (excludedWord m p R L l
          (shiftExcludedState m L l (v i) (excludedTranslation m p L (l + 1) s i))).map
          (fun x => (i, x))).flatten

def MaskWitness (a C δ lower : ℝ) (d : ℕ) : Prop :=
  ∃ h : ℕ, 2 ≤ h ∧ ∃ p : ℕ → ℕ → ℕ, MaskPrimes h p ∧
    ∃ (w : ℕ) (c : MaskAlphabet h p h → Fin w → Bool),
      SubstitutionBounds a C c ∧ OffsetLocal δ c ∧
      ∃ n : ℕ, 0 < n ∧ n ≤ d ∧
        (∀ v : MaskState h p (circleSize h p) h,
          (encode c (maskWord h p (h ^ (2 * h)) (circleSize h p) h v)).length = n) ∧
        Real.exp (lower * exponentScale d) ≤ setDistortion
          (Set.range fun v : MaskState h p (circleSize h p) h =>
            encode c (maskWord h p (h ^ (2 * h)) (circleSize h p) h v))

def ExcludedWitness (a C ε lower : ℝ) (d : ℕ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ p : ℕ → ℕ → ℕ, ExcludedPrimes m p ∧
    ∃ (w : ℕ) (c : ExcludedAlphabet m (circleSize m p) m → Fin w → Bool),
      SubstitutionBounds a C c ∧ AnchorLocal ε c ∧
      ∃ n : ℕ, 0 < n ∧ n ≤ d ∧
        (∀ v : ExcludedState m (circleSize m p) m,
          (encode c (excludedWord m p (m ^ (2 * m)) (circleSize m p) m v)).length = n) ∧
        Real.exp (lower * exponentScale d) ≤ setDistortion
          (Set.range fun v : ExcludedState m (circleSize m p) m =>
            encode c (excludedWord m p (m ^ (2 * m)) (circleSize m p) m v))

def UniformUpper (C : ℝ) (d₀ : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α], 2 ≤ Fintype.card α → ∀ d : ℕ, d₀ ≤ d →
    ∃ (M : ℕ) (F : Words α d → Fin M → ℝ), ∀ x y : Words α d,
      (editDistance x.val y.val : ℝ) ≤ ∑ i, |F x i - F y i| ∧
      (∑ i, |F x i - F y i|) ≤
        Real.exp (C * exponentScale d) * editDistance x.val y.val

def FullMain : Prop :=
  ∃ c C a Ccode δ ε : ℝ, ∃ d₀ : ℕ,
    0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < Ccode ∧ 0 < δ ∧ 0 < ε ∧
    TwoCodes a Ccode δ ε ∧ UniformUpper C d₀ ∧
    (∀ (α : Type) [Fintype α], 2 ≤ Fintype.card α → ∀ d : ℕ, d₀ ≤ d →
      Real.exp (c * exponentScale d) ≤ E α d ∧
      E α d ≤ Real.exp (C * exponentScale d)) ∧
    (∀ d : ℕ, d₀ ≤ d →
      MaskWitness a Ccode δ c d ∧ ExcludedWitness a Ccode ε c d ∧
      Real.exp (c * exponentScale d) ≤ alphabetSupremum d ∧
      alphabetSupremum d ≤ Real.exp (C * exponentScale d))

end FiniteCircle

def finiteCircle_fullMain_statement : Prop :=
  FiniteCircle.FullMain

end OAI

namespace Problem

/-- Every statement the challenge left open, conjoined. -/
abbrev Target : Prop :=
  _root_.OAI.finiteCircle_fullMain_statement

end Problem

/- Formalization scope, from lean/docs/099.md: The formalization determines the exponential scale of the least $\ell_1$ distortion of unit-cost edit distance on strings of length at most $d$. For every sufficiently large $d$, uniformly over finite alphabets with at least two symbols, the distortion lies between $\exp(c\sqrt{\log d\,\log\log d})$ and $\exp(C\sqrt{\log d\,\log\log d})$ for absolute constants $c,C>0$. The lower bound has a witness consisting of binary strings of one common length, and the same scale controls the supremum over finite alphabets. The formalization gives two finite-circle constructions of binary strings whose least $\ell_1$ distortion is at least $\exp(c\sqrt{\log d\,\log\log d})$ for all sufficiently large length caps $d$. The witnesses use strings of one common length and include the binary coding transfers with their stated uniform bounds. It also gives a finite histogram embedding with distortion at most $\exp(C\sqrt{\log d\,\log\log d})$ for all strings of length at most $d$, uniformly over finite alphabets, including the empty string. Thus the lower and upper exponential scales agree up to absolute constants. The formalization gives two lower-bound constructions for the $\ell_1$ distortion of ordinary edit distance on binary words. For every sufficiently large length cap $d$, each construction supplies a finite set of at least two binary words of one common length at most $d$ whose least $\ell_1$ distortion is at least $\exp(c\sqrt{\log d\,\log\log d})$ for an absolute $c>0$. The selected statements are the binary lower bounds. The paper's constant-distortion binary conversion and the companion upper embedding theorem are outside them. -/
