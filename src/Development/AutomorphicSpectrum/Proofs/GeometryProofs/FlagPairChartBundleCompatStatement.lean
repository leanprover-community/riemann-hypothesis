module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagPairChartBundleCompat
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualRevDualRev
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)


theorem _root_.GlobalTheory.T.flag_pair_chart_bundle_compat : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ϖ : O) (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (x x' : Fin r → K → ℤ) (f g : Fin r → MvPolynomial (Σ k, J k) O), IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (C C' : ChartBundle O (segreVec y) r (Fin r → Ω)) (v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
      (∀ c, segreVec y c ≠ 0 → C.lat c = dotDual (chartRing O (segreVec y) c) (B.lat c) ∧
        C'.lat c = dotDual (chartRing O (segreVec y) c) (B'.lat c)) ∧
      IsFlagPair ϖ y C C' v v' (fun i => -x (Fin.rev i)) (fun i => -x' (Fin.rev i)) (fun i => g (Fin.rev i))
        (fun i => f (Fin.rev i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.DualPair.dualPair <;> assumption)
