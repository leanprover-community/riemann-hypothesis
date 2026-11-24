module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSeriesOfNoPoleAwayUniformizerX
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A), Irreducible ϖ → ∀ (k : A →+* ℂ), Function.Injective k → ∀ (S : Type) [CommRing S] [Algebra (PowerSeries A) S] [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (ι : S →+* ℂ⸨X⸩), (∀ s : PowerSeries A, ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s)) → ∀ v : S, ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range → (∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s) → ∃ s : PowerSeries A, v = algebraMap _ S s := by
  first | exact @GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | exact GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap | (intros; apply GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap <;> assumption)
