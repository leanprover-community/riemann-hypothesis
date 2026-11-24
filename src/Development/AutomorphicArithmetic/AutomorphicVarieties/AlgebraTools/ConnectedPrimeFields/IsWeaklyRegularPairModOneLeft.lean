module

public import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
public import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing

namespace UpperTheory.V.AlgebraTools.Conn

def Reg2 {A : Type} [CommRing A] (J : Ideal A) (u v : A) : Prop :=
  (∀ a, u * a ∈ J → a ∈ J) ∧ ∀ a, v * a ∈ J ⊔ Ideal.span {u} → a ∈ J ⊔ Ideal.span {u}

def ConnOn {R : Type} [CommRing R] (a : Ideal R) (k : WithBot ℕ∞) : Prop :=
  ∀ I : Ideal R, a ≤ I → ringKrullDim (R ⧸ I) < k →
    IsConnected (PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R))

structure IsBase (A : Type) [CommRing A] [IsLocalRing A] : Prop where
  dom : IsDomain A
  normal : IsIntegrallyClosed A
  cm : ReciprocityTheory.CA.IsCM A
  complete : IsAdicComplete (maximalIdeal A) A

def HasBase (R : Type) [CommRing R] : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (i : A →+* R),
    IsBase A ∧ Function.Injective i ∧ i.Finite

def CohenType (R : Type) [CommRing R] : Prop :=
  ∀ p : Ideal R, p.IsPrime → HasBase (R ⧸ p)

theorem isBase_field (K : Type) [Field K] : IsBase K := by
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact ⟨inferInstance, 0, by simp [ringKrullDim_eq_zero_of_field], [], rfl, by simp,
      RingTheory.Sequence.IsRegular.nil K K⟩
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

theorem isWeaklyRegularPairMod_one_left {A : Type} [CommRing A] (J : Ideal A) (v : A) : Reg2 J 1 v :=
  ⟨fun a h => by simpa using h, fun a _ => by simp⟩

end UpperTheory.V.AlgebraTools.Conn
