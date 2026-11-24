module

public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveOfLTensorFlatFamily
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

@[expose] public section

open TensorProduct

theorem _root_.GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) → (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) → (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  first | exact @GlobalTheory.bijective_of_lTensor_flat_family | exact GlobalTheory.bijective_of_lTensor_flat_family | (intros; apply GlobalTheory.bijective_of_lTensor_flat_family <;> assumption)
