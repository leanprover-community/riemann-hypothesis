module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZeroStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

theorem maxCusps_iff_killed_coeff_vanish : MaxCuspsStatement := by
  intro E _ _ _ r ρ X hspan hbas la hχ c P hP
  exact ⟨fun h => GlobalTheory.T.maxCusp_killedCoefficient_eq_zero E r ρ X hbas la hχ c P h,
    fun h => GlobalTheory.T.maxCusp_mem_cuspForms_of_killedCoef_zero E r ρ X hspan hbas la hχ c P hP h⟩

end GlobalTheory
