module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isHermitian_Jm_bracket {n : ℕ} (ε : Fin n → Bool) : (Jm ε).IsHermitian := by
  unfold Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dRep_bracket : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε, ∀ Y ∈ lieSet ε, dRep σ X (dRep σ Y w) - dRep σ Y (dRep σ X w) = dRep σ (X * Y - Y * X) w := by
  intro n ε H _ _ _ σ h w hw X hX Y hY
  have hd : (Jm ε).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)).ne_zero
  have key := fun v (hv : Sm ε σ v) =>
    GlobalTheory.HolDict.LieAct.main n (Jm ε) H σ (isHermitian_Jm_bracket ε) hd h.1 v v hv hv
  have hB : X * Y - Y * X ∈ lieSet ε := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
    noncomm_ring
  have hXw : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hYw : Sm ε σ (dRep σ Y w) := dRep_mem (isUnit_Jm ε) h.1 hw hY
  have e := ((key w hw).1 0 X Y).2.2
  rw [(key w hw).2.1 _ hB, (key w hw).2.1 X hX, (key w hw).2.1 Y hY, (key _ hXw).2.1 Y hY,
    (key _ hYw).2.1 X hX] at e
  exact e.symm

end GlobalTheory.TypeSum
