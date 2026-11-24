module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenOfNorm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.normEx : UpperTheory.V.Z.Sym.Loc.NormEx := by
  intro O K _ _ _ _ _ Δ L u
  obtain ⟨ε, s, hs, e⟩ := L.even
  obtain ⟨a, b, h⟩ := L.nm_unit ε u
  have h' : algebraMap O K a ^ 2 - algebraMap O K ε * algebraMap O K b ^ 2 = algebraMap O K u := by
    rw [← h]; simp
  refine ⟨⟨algebraMap O K a, algebraMap O K b / s⟩, ?_, ?_⟩
  · have e1 : (⟨algebraMap O K a, algebraMap O K b / s⟩ : Lsq K Δ) = algebraMap O _ a + algebraMap O _ b * ⟨0, 1 / s⟩ := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ), IsScalarTower.algebraMap_apply O K (Lsq K Δ) b]
      ext <;> simp [div_eq_mul_inv]
    rw [e1]
    refine isIntegral_algebraMap.add (isIntegral_algebraMap.mul (IsIntegral.of_pow (n := 2) (by norm_num) ?_))
    have : (⟨0, 1 / s⟩ : Lsq K Δ) ^ 2 = algebraMap O _ (ε : O) := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
      ext <;> simp [sq]
      rw [e]; field_simp
    rw [this]; exact isIntegral_algebraMap
  · rw [QuadraticAlgebra.norm_def, ← h']
    simp only
    rw [e]; field_simp; ring
