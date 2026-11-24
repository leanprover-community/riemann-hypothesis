module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CapPoly
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

open NumberField

theorem UpperTheory.ConvolutionTheory.BW.zSpec :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.ZSpec E := by
  intro E _ _ _ n τ
  have key : ∀ ℓ : UpperTheory.V.Cm.UC E n →ₗ[ℂ] ℂ, ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ p.coeff n = ℓ 1 ∧
      (∀ u, p.eval u = ℓ (UpperTheory.V.Cm.capC τ u)) ∧ ∀ i, ℓ (zC E n τ i) = p.coeff (n - i) := fun ℓ => by
    obtain ⟨p, h1, h2, -, h4⟩ := exists_capPoly (UpperTheory.V.Cm.genC (a := n) τ) ℓ
    refine ⟨p, h1, h2, h4, fun i => ?_⟩
    have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) :=
      fun a _ b _ h => Fin.ext (Nat.cast_injective h)
    have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le h1)
    conv_rhs => rw [Lagrange.eq_interpolate hinj hd]

    rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, zC, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, h4, map_smul, smul_eq_mul, mul_comm]
    rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, -, h2, -, h4⟩ := key ℓ
    rw [map_sub, h4, Nat.sub_zero, h2, sub_self]
  · rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
    obtain ⟨p, h1, -, h3, h4⟩ := key ℓ

    rw [map_sub, sub_eq_zero, ← h3, map_sum, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
    ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, h4, smul_eq_mul, mul_comm]
    simp
