module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDecayInFrameOfTranslateDecay
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matrix_coefficient_decay_in_frame_of_translate_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  first | exact @GlobalTheory.FrameDecay.coef_frame_decay | exact GlobalTheory.FrameDecay.coef_frame_decay | (intros; apply GlobalTheory.FrameDecay.coef_frame_decay <;> assumption)
