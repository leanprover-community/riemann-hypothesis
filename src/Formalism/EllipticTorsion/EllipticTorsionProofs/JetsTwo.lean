module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := K) i H)

theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ j, MvPowerSeries.constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd

  rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy), Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR

end Formalism.ELL
