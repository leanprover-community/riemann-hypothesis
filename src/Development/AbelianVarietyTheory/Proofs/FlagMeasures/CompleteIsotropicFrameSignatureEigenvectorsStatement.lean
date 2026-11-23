module

public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectors
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.complete_isotropicFrame_signature_eigenvectors : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  first | exact @GlobalTheory.IsoFrame.complete_isotropic_frame | exact GlobalTheory.IsoFrame.complete_isotropic_frame | (intros; apply GlobalTheory.IsoFrame.complete_isotropic_frame <;> assumption)
