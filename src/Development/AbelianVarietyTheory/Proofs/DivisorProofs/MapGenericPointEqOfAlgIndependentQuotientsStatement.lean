module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointEqOfAlgIndependentQuotients
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  first | exact @GlobalTheory.GenericImage.map_genericPoint_eq | exact GlobalTheory.GenericImage.map_genericPoint_eq | (intros; apply GlobalTheory.GenericImage.map_genericPoint_eq <;> assumption)
