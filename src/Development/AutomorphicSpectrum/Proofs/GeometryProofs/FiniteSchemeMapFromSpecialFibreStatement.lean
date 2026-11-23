module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibre
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.finite_scheme_map_from_special_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  exact @GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model
