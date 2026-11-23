module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preirreducibleSpace_primeSpectrum_tensor_localizationAway
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k]
    [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  intro hX
  letI : Algebra (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    (Algebra.TensorProduct.map (AlgHom.id A k)
      (IsScalarTower.toAlgHom A B (Localization.Away b))).toAlgebra
  haveI : IsScalarTower k (k ⊗[A] B) (k ⊗[A] Localization.Away b) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right A k (Submonoid.powers b)
    (Localization.Away b) (by ext; simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers] at hl
  haveI : IsLocalization.Away
      (Algebra.TensorProduct.includeRight (R := A) (A := k) b) (k ⊗[A] Localization.Away b) := hl
  exact (PrimeSpectrum.localization_away_isOpenEmbedding (k ⊗[A] Localization.Away b)
    (Algebra.TensorProduct.includeRight (R := A) (A := k) b)).preirreducibleSpace

end GlobalTheory
