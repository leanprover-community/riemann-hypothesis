module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private theorem mulMat_stdLat_le {F : Type} [Field F] [NumberField F]
    (A : Matrix (Fin 2) (Fin 2) ℤ) :
    _root_.GlobalTheory.HilbFam.mulMat (_root_.GlobalTheory.HilbFam.stdLat F) A ≤
      _root_.GlobalTheory.HilbFam.stdLat F := by
  unfold _root_.GlobalTheory.HilbFam.mulMat
  rintro _ ⟨y, hy, rfl⟩
  unfold _root_.GlobalTheory.HilbFam.stdLat at hy ⊢
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  simp only [LinearMap.coe_restrictScalars, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : y j * (A.map Int.cast) j i = ((A j i : 𝓞 F)) • y j := by
    simp [Algebra.smul_def, mul_comm]
  rw [hj]
  exact Submodule.smul_mem _ _ (hy j (Set.mem_univ j))


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ)
    (L : _root_.GlobalTheory.HilbFam.Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)),
    _root_.GlobalTheory.HilbFam.HasLevel N L → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.twist N L α) := by
  intro F _ _ _ N L α hL
  obtain ⟨_, hle⟩ := hL
  unfold _root_.GlobalTheory.HilbFam.HasLevel _root_.GlobalTheory.HilbFam.twist
  refine ⟨fun x hx => Submodule.mem_sup_right ?_, sup_le ?_ (mulMat_stdLat_le _)⟩
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    convert Submodule.mem_map_of_mem hx using 1
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Matrix.natCast_apply] <;>
      rw [Algebra.smul_def, map_natCast, mul_comm]
  · unfold _root_.GlobalTheory.HilbFam.mulMat
    exact (Submodule.map_mono hle).trans (mulMat_stdLat_le _)

end GlobalTheory.HilbFam
