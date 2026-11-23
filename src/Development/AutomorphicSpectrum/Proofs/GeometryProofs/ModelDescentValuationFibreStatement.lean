module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibre
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.model_descent_valuation_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O) (ϖ' : O'), Irreducible ϖ → Irreducible ϖ' → ∀ (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω)) (T : LocPair J O (Fin r)), IsFlagPair ϖ y B B' w w' T.x T.x' T.f T.g → ∃ (C₁ C₁' : ChartBundle O' (segreVec (fun v => algebraMap Ω Ω' (y v))) r (Fin r → Ω')) (v v' : Module.Basis (Fin r) Ω' (Fin r → Ω')), (∀ c, segreVec y c ≠ 0 → C₁.lat c = spanOver (chartRing O' (segreVec (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' B.lat c) ∧ C₁'.lat c = spanOver (chartRing O' (segreVec (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' B'.lat c)) ∧ IsFlagPair ϖ' (fun v => algebraMap Ω Ω' (y v)) C₁ C₁' v v' T.x T.x' (T.map (algebraMap O O')).f (T.map (algebraMap O O')).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext | exact GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext <;> assumption)
