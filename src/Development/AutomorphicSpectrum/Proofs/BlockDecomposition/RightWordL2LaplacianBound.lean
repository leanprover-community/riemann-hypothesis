module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobSecK

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_congr (w : List (Ix n)) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Rw w f) (Rw w h) (GLs n) := by
  induction w with
  | nil => exact e
  | cons p w ih => exact RCalc.Rd_congr (bs p) ih

theorem Rw_smooth (w : List (Ix n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact RCalc.Rd_contDiffOn (bs p) ih

theorem Rw_append (w w' : List (Ix n)) (f : Mat n → V) : Rw w' (Rw w f) = Rw (w' ++ w) f := by
  induction w' with
  | nil => rfl
  | cons p w' ih =>
    show Rd (bs p) (Rw w' (Rw w f)) = Rd (bs p) (Rw (w' ++ w) f)
    rw [ih]

end Words

section HWords

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HWords

section Skew

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Skew

section Bracket

def cf (M : Mat n) (p : Ix n) : ℝ := if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem sum_cf (M : Mat n) : ∑ p : Ix n, cf M p • bs p = M := by
  rw [OmDec.sum_Ix]
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ext i j
  simp only [cf, bs, if_true, Bool.false_eq_true, if_false, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · simp only [h, and_self, if_true]
    obtain ⟨rfl, rfl⟩ := h
    simp [Complex.real_smul, Complex.re_add_im]
  · simp [h]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sum_cf (M : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd M f g = ∑ p : Ix n, ((cf M p : ℝ) : ℂ) • Rd (bs p) f g := by
  conv_lhs => rw [← sum_cf M]

  simp only [Rd, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, map_smul]
  exact (Complex.coe_smul _ _).symm

end Bracket

section HBracket

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)] {μ : Measure (G n)}

end HBracket

section Sections

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Sections

section Powers

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Powers

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

end Main

end GlobalTheory.CompanionTheory.SobSecK
