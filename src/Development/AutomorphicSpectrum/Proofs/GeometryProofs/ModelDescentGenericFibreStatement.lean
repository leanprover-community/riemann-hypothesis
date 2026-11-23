module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentGenericFibre
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.model_descent_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O'), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ (n : ℕ) (Sg : Type) (r s : Sg → ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg) (Df : (∀ k, J k) → LieLatticeData Ω F n Sg r s), IsPreFamily O y p w σ φ Df → ∃ (χ : Sg → F → O') (Df' : (∀ k, J k) → LieLatticeData Ω' F n Sg r s), IsLatticeFamily O' (fun v => algebraMap Ω Ω' (y v)) p (algebraMap O O' w) χ φ Df' ∧ ∀ c, mseg y c ≠ 0 → ∀ τ, (Df' c).lie τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).lie τ) ∧ (Df' c).W τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).W τ) ∧ (Df' c).om τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).om τ) ∧ (Df' c).omHT τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).omHT τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main | exact GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main <;> assumption)
