module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgClosureOfTower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], (∀ L : ℕ, IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L)) ∧ (∀ L : ℕ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L) ∧ (∀ m n : ℕ, eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) := by
  intro Ω _ _ _ ε l hl N _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  have hl1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl0
  have hN1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨fun L => GlobalTheory.K4.isPrimitiveRoot_eOm ε (mul_ne_zero hN0 (pow_ne_zero L hl0)), fun L => ?_, fun m n => ?_⟩
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : (N : ℚ) * (1 / ((N * l ^ L : ℕ) : ℚ)) = 1 / (l : ℚ) ^ L := by
      push_cast; field_simp
    rw [h]; rfl
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : ((l ^ n : ℕ) : ℚ) * (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) = 1 / ((N : ℚ) * (l : ℚ) ^ m) := by
      push_cast; rw [pow_add]; field_simp
    rw [h]
