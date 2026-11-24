module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.isIntegral_of_divisible_characters : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  first | exact @GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | exact GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | (intros; apply GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul <;> assumption)
