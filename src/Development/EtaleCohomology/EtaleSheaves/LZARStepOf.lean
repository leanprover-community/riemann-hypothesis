module

public import Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace LateralTheory.E.LZARFacts

theorem LZARStep_of : LateralTheory.E.LZIdemSumNoetherian.LZARStep := by
  intro A _ _ _ M _ _ N P hN
  have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  set I := IsLocalRing.maximalIdeal A
  set Q : Submodule A N := P.comap N.subtype
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I Q
  refine ⟨c + 1, by omega, ?_⟩
  have hQ : I ^ (c + 1) • (⊤ : Submodule A N) ⊓ Q ≤ I • Q := by
    rw [hc (c + 1) (by omega), show c + 1 - c = 1 by omega, pow_one]
    exact Submodule.smul_mono (le_refl _) inf_le_right
  intro x ⟨hx, hxP⟩
  have hmap : I ^ (c + 1) • N = (I ^ (c + 1) • (⊤ : Submodule A N)).map N.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyQ : y ∈ Q := hxP
  have := hQ ⟨hy, hyQ⟩
  have h2 : (I • Q).map N.subtype ≤ I • P := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono (le_refl _) (Submodule.map_comap_le _ _)
  exact h2 ⟨y, this, rfl⟩

end LateralTheory.E.LZARFacts
