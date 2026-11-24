module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleGeneric
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  intro K _ ι _ n
  refine ⟨fun V hK hV => ?_, fun P hP => ⟨?_, ?_⟩⟩
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.isArithVar_comap_of_isProjVarF hV
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  · haveI : P.IsPrime := hP.2.1.1
    apply ReciprocityTheory.AnForm.R.IntegerToRational.comap_map_eq
    intro m hm
    have h2 : m ∈ Ideal.comap (C : ℤ →+* MRing ι) P := hm
    rw [hP.2.2.1] at h2
    simpa using h2
