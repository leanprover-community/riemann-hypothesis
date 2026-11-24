module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing



namespace GlobalTheory

noncomputable def tensorIntegralClosureInclusion (S L D : Type) [CommRing S] [Field L] [Algebra S L]
    [CommRing D] [Algebra S D] :
    integralClosure S L →ₐ[S] integralClosure D (TensorProduct S D L) where
  toRingHom := GlobalTheory.AbhyankarLocal.toNorm S L D
  commutes' s := by
    ext
    change (1 : D) ⊗ₜ[S] (algebraMap S L s) = _
    exact (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes s

noncomputable instance instAlgebraIntegralClosureTensor (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    Algebra (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  (GlobalTheory.AbhyankarLocal.toNorm S L D).toAlgebra

instance (S L D : Type) [CommRing S] [Field L] [Algebra S L] [CommRing D] [Algebra S D] :
    IsScalarTower S (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
  IsScalarTower.of_algebraMap_eq fun s =>
    ((tensorIntegralClosureInclusion S L D).commutes s).symm

theorem algebraMap_integralClosure_tensor_eq (S L D : Type) [CommRing S] [Field L]
    [Algebra S L] [CommRing D] [Algebra S D] :
    algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)) =
      GlobalTheory.AbhyankarLocal.toNorm S L D := rfl

end GlobalTheory
