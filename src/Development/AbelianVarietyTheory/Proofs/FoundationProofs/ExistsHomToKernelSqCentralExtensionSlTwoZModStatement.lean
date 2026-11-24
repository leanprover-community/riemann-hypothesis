module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZMod
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

theorem _root_.GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  first | exact @GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | exact GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | (intros; apply GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 <;> assumption)
