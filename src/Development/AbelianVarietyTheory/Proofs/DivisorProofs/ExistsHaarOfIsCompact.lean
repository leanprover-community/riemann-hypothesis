module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

noncomputable section
namespace GlobalTheory.StabHaar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

end GlobalTheory.StabHaar
