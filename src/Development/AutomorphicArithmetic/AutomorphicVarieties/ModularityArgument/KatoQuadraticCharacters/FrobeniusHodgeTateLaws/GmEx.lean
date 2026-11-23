module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ThickFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open UpperTheory.V.Z.Kato.Joint
open scoped Matrix MatrixGroups

theorem UpperTheory.V.Z.Kato.Joint.gmEx :
    UpperTheory.V.Z.Kato.Joint.GmEx := by
  intro l _ N h
  have hN : (N : ZMod l) * (N : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one N h.symm
  let m : (ZMod l)ˣ → ℤ := fun r => (((-(r : ZMod l)) * (N : ZMod l)⁻¹).val : ℤ)
  have hm : ∀ r : (ZMod l)ˣ, (N : ZMod l) * ((m r : ℤ) : ZMod l) = -(r : ZMod l) := by
    intro r
    simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [mul_left_comm, hN, mul_one]
  refine ⟨fun r => ⟨!![1, 0; (N : ℤ) * m r, 1], by simp [Matrix.det_fin_two]⟩, fun r => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩ <;> simp
  · simp
  · simp [hm r]
  · refine ⟨-1, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hm r]
