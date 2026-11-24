module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ENNReal

namespace GlobalTheory.Unf

variable {D : D7}

def realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : ℝ := ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖

def InBox {m n : ℕ} (K : Set (Mx D m n)) (x : Mx D m n) : Prop := ∃ k ∈ K, (x - k).map (finPart D) = 0


open Classical in
def maj (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : ℝ :=
  if InBox K x then ((1 + realSize θ x) ^ N)⁻¹ else 0

def supSob (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) d f

structure IsSobForm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  bound : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : NNReal),
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ‖ℓ f‖ₑ ≤ C * supSob ψ θ d f

theorem realSize_nonneg (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : 0 ≤ realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem maj_nonneg (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : 0 ≤ maj θ K N x := by
  unfold maj
  split_ifs
  · have := realSize_nonneg θ x; positivity
  · exact le_rfl

end GlobalTheory.Unf

end
