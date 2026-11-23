module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

def LinN {C : Type} [CommRing C] {dd : ℕ} (f : Pt C 1 dd) : Prop :=
  ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (f i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)

section Gen

variable {C : Type} [CommRing C] {dd : ℕ}

theorem linN_const {f : Pt C 1 dd} (hf : LinN f) (i : Fin dd) : constantCoeff (f i) = 0 := by
  have h := hf i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h, MvPowerSeries.coeff_zero_X]

end Gen

end LogEx

end Formalism.L2.FormalSeriesBounds
