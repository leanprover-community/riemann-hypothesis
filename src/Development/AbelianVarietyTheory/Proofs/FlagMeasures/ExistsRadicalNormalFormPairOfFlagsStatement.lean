module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlags
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_radical_normalForm_pair_of_flags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (p : Point ℂ (r + 1)), TwoFl k r z z' g₀ → ZhatO k r z z' g₀ = ptMat p → ∃ p₁ p₀ : PPar k r, pOf k r p₀ *ᵥ z' = z' ∧ IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) ∧ Zr k r (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) = Zr k r g₀ ∧ ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r := by
  first | exact @GlobalTheory.Amp.NormalEx.normal_form | exact GlobalTheory.Amp.NormalEx.normal_form | (intros; apply GlobalTheory.Amp.NormalEx.normal_form <;> assumption)
