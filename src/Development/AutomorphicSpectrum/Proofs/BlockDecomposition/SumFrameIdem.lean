module

public import Formalism.SatakeDualWeyl.Statement
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

abbrev FrameIx (r : ℕ) : Type := Option (Fin r ⊕ Fin r)

variable {E : Type} [Field E] {n r : ℕ}

def frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    FrameIx r → Matrix (Fin n) (Fin n) E
  | some (Sum.inl i) => X * single i i (1 : E) * (cT S Y * J)
  | some (Sum.inr i) => Y * single i i (1 : E) * (cT S X * J)
  | none => 1 - X * (cT S Y * J) - Y * (cT S X * J)

def frameWt (t : Fin r → ℝ) : FrameIx r → ℝ
  | some (Sum.inl i) => t i
  | some (Sum.inr i) => (t i)⁻¹
  | none => 1

def frameLev (s : Fin r) : FrameIx r → ℕ
  | some (Sum.inl i) => if i ≤ s then 2 else 1
  | some (Sum.inr i) => if i ≤ s then 0 else 1
  | none => 1

theorem sum_frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    ∑ α, frameIdem S J X Y α = 1 := by
  have key : ∀ (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      ∑ i : Fin r, (A * (Matrix.single i i (1 : E) : Matrix (Fin r) (Fin r) E) * B : Matrix (Fin n) (Fin n) E) = A * B := fun A B => by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [frameIdem]
  rw [key, key]
  abel

theorem frameWt_pos {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (α : FrameIx r) : 0 < frameWt t α := by
  rcases α with _ | i | i
  · exact one_pos
  · exact ht i
  · exact inv_pos.2 (ht i)

end GlobalTheory.CompanionTheory.RapidDecay

end
