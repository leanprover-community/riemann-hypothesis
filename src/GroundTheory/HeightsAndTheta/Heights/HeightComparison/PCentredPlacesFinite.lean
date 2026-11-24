module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredPlacesFinite
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

theorem CentredPlacesFinite.proof : CentredPlacesFinite.Statement := by
  intro L _ _ O hft _ m _
  have hq : Algebra.FiniteType ℤ (O ⧸ m) :=
    @Algebra.FiniteType.of_surjective ℤ O (O ⧸ m) _ _ _ _ _ hft (Ideal.Quotient.mkₐ ℤ m)
      (Ideal.Quotient.mkₐ_surjective ℤ m)
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  obtain ⟨hp, -⟩ :=
    @natCard_eq_pow_length_of_finiteType (O ⧸ m) _
      (by convert hq <;> rfl) (ringChar (O ⧸ m))
      (ringChar.charP _)
  set p := ringChar (O ⧸ m)
  have hpm : (p : O) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (O ⧸ m) p
  have hp0 : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine (FinitePlace.hasFiniteMulSupport hp0).subset fun w hw ↦ ?_
  have hlt := (hw.2 (p : O)).mpr hpm
  have hcoe : ((p : O) : L) = (p : L) := by simp
  rw [hcoe] at hlt
  exact hlt.ne

end GroundTheory.Heights₂.Heights
