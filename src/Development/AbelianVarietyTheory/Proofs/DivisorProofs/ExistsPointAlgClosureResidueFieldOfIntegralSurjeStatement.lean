module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointAlgClosureResidueFieldOfIntegralSurje
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)),
    IsIntegralHom g → Surjective g → ∃ s : Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Y,
    s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)))) := by
  first | exact @GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom | exact GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom | (intros; apply GlobalTheory.exists_point_algClosure_residueField_of_isIntegralHom <;> assumption)
