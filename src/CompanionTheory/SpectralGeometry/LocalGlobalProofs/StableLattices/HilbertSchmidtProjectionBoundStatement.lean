module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HilbertSchmidtProjectionBound
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

theorem _root_.GlobalTheory.T.hilbert_schmidt_projection_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (A₀ A' : Matrix (Fin n) (Fin n) ℂ) (α β : ℝ) (x : PSub ε A₀) (k : S7.KG ε), IsGrad ε A₀ → IsGrad ε A' → Formalism.REAL.hs (Pm A₀ - Pm A') ≤ 1 / 4 → Formalism.REAL.hs (Pp A₀ - Pp A') ≤ 1 / 4 → 1 ≤ β → β ≤ α → (∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))⁻¹ *ᵥ y)) → Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pm A₀) ≤ 4 * n / α ∧ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pz A₀) ≤ 4 * n * β := by
  exact Est.est
