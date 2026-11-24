module

public import GroundTheory.FunctionField.PlaceDefs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

noncomputable section
open GroundTheory.FunctionField
open scoped TensorProduct

namespace UpperTheory.Et.Sel

def SelAll (k K : Type) [Field k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) : Set Kˣ :=
  {f | ∀ v : Place k K, (q : ℤ) ∣ v.ord (f : K)}

def FinCls {K : Type} [Field K] (q : ℕ) (S : Set Kˣ) : Prop :=
  ∃ T : Finset Kˣ, ∀ f ∈ S, ∃ t ∈ T, ∃ u : Kˣ, f = t * u ^ q

abbrev inc {k K : Type} [Field k] [Field K] [Algebra k K] (L : Type) [Field L] [Algebra k L] (B : Subalgebra k K) :
    L ⊗[k] B →ₐ[k] L ⊗[k] K :=
  Algebra.TensorProduct.map (AlgHom.id k L) B.val

def LocPow {k K : Type} [Field k] [Field K] [Algebra k K] (q : ℕ) (L : Type) [Field L] [Algebra k L] (B : Subalgebra k K)
    (m : Ideal (L ⊗[k] B)) (F : L ⊗[k] K) : Prop :=
  ∃ s t a b : L ⊗[k] B, s ∉ m ∧ t ∉ m ∧ a ≠ 0 ∧ b ≠ 0 ∧ F * inc L B (s * b ^ q) = inc L B (t * a ^ q)

def IsChart {k K : Type} [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) : Prop :=
  Algebra.FiniteType k B ∧ IsDedekindDomain B ∧ ¬ IsField B ∧ IsFractionRing B K ∧
    ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], IsDedekindDomain (L ⊗[k] B) ∧ ¬ IsField (L ⊗[k] B)

def Charts (k K : Type) [Field k] [Field K] [Algebra k K] (q : ℕ) : Prop :=
  ∃ (n : ℕ) (B : Fin n → Subalgebra k K), (∀ i, IsChart (B i)) ∧
    ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L] (F : L ⊗[k] K), F ≠ 0 →
      (∀ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsMaximal → LocPow q L (B i) m F) →
      ∃ (f : Kˣ) (a b : L ⊗[k] K), a ≠ 0 ∧ b ≠ 0 ∧ F * b ^ q = (1 : L) ⊗ₜ[k] (f : K) * a ^ q

def Spz {k L A : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A] (R : Subalgebra k L) (φ : R →ₐ[k] k)
    (y : L ⊗[k] A) (a : A) : Prop :=
  ∃ y' : R ⊗[k] A, Algebra.TensorProduct.map R.val (AlgHom.id k A) y' = y ∧
    Algebra.TensorProduct.lid k A (Algebra.TensorProduct.map φ (AlgHom.id k A) y') = a

end UpperTheory.Et.Sel

end
