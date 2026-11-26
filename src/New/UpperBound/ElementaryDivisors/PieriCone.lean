module

import TauCeti.MeasureTheory.Measure.Lebesgue.PieriCone
public import Lib.Speed

/-!
# The Pieri cone, the step map and the slab: interlacing and volume of the cone

Vectors `ν` are real functions on pairs `(b, j)`, with `b` in `Fin k` and `j` a letter (in `ZMod N`
for the final volume formula). The step map `New.permStep` sends `ν` to signed gaps between
consecutive letters, twisted by permutations. The cone `New.pieriCone v P` is cut out by Pieri's
inequalities, one half of the interlacing inequalities between `ν` and `P` times its shift. The slab
`New.degreeSlab k D` is the set of nonnegative vectors whose sum at each letter `j` lies in the unit
interval `[D j - 1, D j]`, a product of slices of orthants.

The volume formula is deduced from `TauCeti.MeasureTheory.Measure.Lebesgue.PieriCone`. The result
serves the dimension bounds mod `p` from flags in `New.UpperBound.ElementaryDivisors.DefectCount`.

## Main definitions and results

* `New.permStep`, `New.degreeSlab`, `New.pieriCone`: the twisted step map, the degree slab and the
  Pieri cone.
* `New.prod_mul_volume_real_inter_degreeSlab`: for `P > 1`, a set whose preimage under
  `New.permStep` (with trivial permutations) is the cone fills a fraction
  `∏ l < k, (q - 1) / (q ^ (l + 1) - 1)` of the slab, with `q = P ^ N`.

## Notation

The Boolean `v j` selects the sign of the steps at the letter `j`: `+` for true, `-` for false. In
the application `v j` is true for even `j`.

## Relation to the literature

See `New.UpperBound.ElementaryDivisors.DefectCount` for related work.
-/

@[expose] public section

namespace New

open MeasureTheory Equiv Set Bornology

variable {k : ℕ}

section StepMap

variable {T : Type}

/-- The slab: the vectors `β ≥ 0` whose degree `∑ b, β (b, j)` lies in `[D j - 1, D j]` for every
letter `j`. -/
def degreeSlab (k : ℕ) (D : T → ℝ) : Set (Fin k × T → ℝ) :=
  {β : Fin k × T → ℝ | 0 ≤ β ∧ ∀ j : T, ∑ b : Fin k, β (b, j) ∈ Set.Icc (D j - 1) (D j)}

/-- Every subset of `degreeSlab k D` is bounded. -/
lemma isBounded_inter_degreeSlab [Fintype T] (D : T → ℝ) (Y : Set (Fin k × T → ℝ)) :
    IsBounded (Y ∩ degreeSlab k D) := by
  have h_slab : degreeSlab k D = TauCeti.degreeSlab k D := by
    ext β
    simp [degreeSlab, TauCeti.mem_degreeSlab]
  rw [h_slab]
  exact (TauCeti.isBounded_degreeSlab k D).subset inter_subset_right

variable [Add T] [One T] (v : T → Bool) (P : ℝ)

/-- The step map. For permutations `σ j` of `Fin k`, one for each letter `j`, it is the linear map
`ν ↦ β` with `β (b, j) = ± (P * ν (b, j + 1) - ν (σ j b, j))`, the sign being `+` if `v j` is true
and `-` otherwise. The entries of `β` are the steps of `ν`. -/
@[simps!]
def permStep (σ : T → Equiv.Perm (Fin k)) : Module.End ℝ (Fin k × T → ℝ) :=
  LinearMap.pi fun x : Fin k × T ↦
    (if v x.2 then (1 : ℝ) else -1) • (P • .proj (x.1, x.2 + 1) - .proj (σ x.2 x.1, x.2))

/-- The Pieri cone: the vectors `ν` such that, for all `j` and `b`,
`P * ν (b + 1, j + 1) ≤ ν (b, j)` if `v j` is true, and `ν (b + 1, j) ≤ P * ν (b, j + 1)`
otherwise. -/
def pieriCone : Set (Fin k × T → ℝ) :=
  {ν : Fin k × T → ℝ |
    ∀ (j : T) (b b' : Fin k), b.val + 1 = b' →
      permStep v P 1 ν ((if v j then b' else b), j) ≤ ν (b, j) - ν (b', j)}

end StepMap

/-- Volume of the image of the cone in a slab. Let `P > 1` and `q = P ^ N`, and let `Ω` be a set
whose preimage under the step map is the cone. Then the volume of `Ω ∩ degreeSlab k D`, multiplied
by `∏ l < k, (q ^ (l + 1) - 1) / (q - 1)`, equals the volume of the slab. -/
theorem prod_mul_volume_real_inter_degreeSlab {k N : ℕ} [NeZero N] {v : ZMod N → Bool} {P : ℝ}
    (hP : 1 < P) (D : ZMod N → ℝ) {Ω : Set (Fin k × ZMod N → ℝ)}
    (hΩ : ∀ ν : Fin k × ZMod N → ℝ, permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) :
    (∏ l : Fin k, ((P ^ N) ^ (l.val + 1) - 1) / (P ^ N - 1)) * volume.real (Ω ∩ degreeSlab k D) =
      volume.real (degreeSlab k D) := by
  have h_slab : degreeSlab k D = TauCeti.degreeSlab k D := by
    ext β
    simp [degreeSlab, TauCeti.mem_degreeSlab]
  rw [h_slab]
  refine TauCeti.prod_mul_volume_real_inter_degreeSlab (v := v) hP D ?_
  have h_step : TauCeti.pieriStepMap (k := k) v P 1 = permStep v P 1 := by
    ext ν x
    simp [TauCeti.pieriStepMap_apply]
  ext ν
  simp only [mem_preimage, h_step, hΩ, pieriCone, mem_ofPred_eq, TauCeti.mem_pieriCone,
    permStep_apply, Pi.one_apply, Perm.coe_one, id_eq]
  refine forall₄_congr fun j b b' _ ↦ ?_
  cases v j <;> simp
  constructor <;> intro h <;> linarith

end New
