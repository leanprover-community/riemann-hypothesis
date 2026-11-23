module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjections
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grpObj_pullback_axes_cohomology_projections : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  first | exact @GlobalTheory.AbCoh.AxesPull.main | exact GlobalTheory.AbCoh.AxesPull.main | (intros; apply GlobalTheory.AbCoh.AxesPull.main <;> assumption)
