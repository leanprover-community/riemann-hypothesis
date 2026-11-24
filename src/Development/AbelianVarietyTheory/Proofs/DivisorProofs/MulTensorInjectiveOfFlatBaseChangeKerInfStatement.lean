module

public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  first | exact @GlobalTheory.TorStep.mul_tensor_injective | exact GlobalTheory.TorStep.mul_tensor_injective | (intros; apply GlobalTheory.TorStep.mul_tensor_injective <;> assumption)
