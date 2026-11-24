module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.psiCoordinate_eq_unit_mul_tauCoordinate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D.X] (oa : D.OAct O) (w0 : O), TraceFormTwistIso D oa w0 → ∀ (y : D.X) (r : R) (x : (FractionRing R)ˣ),
    PsiCoord D y r → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D y (w0 • y) x →
    ∃ u : Rˣ, algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u : R) * (x : FractionRing R) := by
  first | exact @GlobalTheory.PsiTauCoordRel.main | exact GlobalTheory.PsiTauCoordRel.main | (intros; apply GlobalTheory.PsiTauCoordRel.main <;> assumption)
