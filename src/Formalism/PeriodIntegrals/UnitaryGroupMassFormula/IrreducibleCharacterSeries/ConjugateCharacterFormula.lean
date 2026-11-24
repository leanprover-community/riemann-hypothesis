module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.IrrCharIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
open Matrix ComplexOrder

namespace PI.SerBridgeGLW

theorem trace_inv_of_monoidHom {G : Type} [Group G] [Fintype G] {n : Type} [Fintype n] [DecidableEq n]
    (M : G →* Matrix n n ℂ) (x : G) : star (trace (M x)) = trace (M x⁻¹) := by
  classical
  set P : Matrix n n ℂ := ∑ g, (M g)ᴴ * M g with hPdef
  have hinv : ∀ y : G, M y * M y⁻¹ = 1 := fun y => by rw [← map_mul, mul_inv_cancel, map_one]
  have hP : (M x)ᴴ * P * M x = P := by
    rw [hPdef, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulRight x) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hPpd : P.PosDef := by
    rw [hPdef, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
    simp only [map_one, Matrix.conjTranspose_one, Matrix.mul_one]
    exact Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum _ fun g _ => Matrix.posSemidef_conjTranspose_mul_self _)
  have hPu : IsUnit P := hPpd.isUnit
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hPu)
  have hct : (M x)ᴴ = P * M x⁻¹ * P⁻¹ := by
    calc (M x)ᴴ = (M x)ᴴ * P * (M x * M x⁻¹) * P⁻¹ := by
          rw [hinv, Matrix.mul_one, Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ((M x)ᴴ * P * M x) * M x⁻¹ * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P * M x⁻¹ * P⁻¹ := by rw [hP]
  rw [← Matrix.trace_conjTranspose, hct, Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hPu), Matrix.one_mul]

theorem conjugate_character_formula : ConjChar := by
  intro G _ _ V x
  let b := Module.finBasis ℂ V
  let M : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp V.ρ
  have hc : ∀ y, V.character y = Matrix.trace (M y) := fun y => by
    simp only [FDRep.character, M, MonoidHom.comp_apply]
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  rw [hc, hc]
  exact trace_inv_of_monoidHom M x

end PI.SerBridgeGLW
