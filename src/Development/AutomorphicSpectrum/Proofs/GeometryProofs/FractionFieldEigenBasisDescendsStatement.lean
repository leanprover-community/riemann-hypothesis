module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FractionFieldEigenBasisDescends
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem _root_.GlobalTheory.T.fraction_field_eigen_basis_descends : ∀ (E : Type) [Field E] [NumberField E] (K C V A : Type) [Field K] [CharZero K] [Field C] [CharZero C] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra V K] [IsFractionRing V K] [CommRing A] [IsDomain A] [Algebra A C]
    (j : K →+* C) (g n : ℕ) (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (σ : E →+* K) (b : Fin n → Fin g → K),
    (∀ a : K, a ∈ (algebraMap V K).range → j a ∈ (algebraMap A C).range) →
    (∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i)) →
    LinearIndependent K b → Submodule.span V (Set.range b) = HT.eigSub ρK σ (stdLat V K g) →
    LinearIndependent C (fun i k => j (b i k)) ∧
      Submodule.span C (Set.range fun i k => j (b i k)) = HT.eigSp ρC (j.comp σ) ∧
      Submodule.span A (Set.range fun i k => j (b i k)) = HT.eigSub ρC (j.comp σ) (stdLat A C g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.FlatEig.eigSub_baseChange <;> assumption)
