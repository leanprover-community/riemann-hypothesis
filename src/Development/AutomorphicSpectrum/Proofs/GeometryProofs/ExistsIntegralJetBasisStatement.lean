module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralJetBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.exists_integral_jet_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (n r : ℕ) (s : Fin r → Out.H0 D.t.PP.L n), ∃ J : ℕ → Fin r → L, (∀ (i : ℕ) (c : Fin r → 𝓞 L), (∀ k < i, ∑ j, (c j : L) * J k j = 0) → IsIntegral ℤ (∑ j, (c j : L) * J i j)) ∧ ∀ (σ : L →+* ℂ) (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ) (v : Fin D.g → ℂ), (∀ j, a.IsFn (s j) (f j)) → D.IsVec a x v → ∀ (i : ℕ) (c : Fin r → ℂ), ((∀ k < i, ∑ j, c j * σ (J k j) = 0) ↔ ∀ k < i, iteratedDeriv k (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0 = 0) ∧ ((∀ k < i, ∑ j, c j * σ (J k j) = 0) → ∑ j, c j * σ (J i j) = iteratedDeriv i (fun τ : ℂ => ∑ j, c j * f j (τ • v)) 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.JetMain.jets | exact GlobalTheory.CompanionTheory.Ar.JetMain.jets | (intros; apply GlobalTheory.CompanionTheory.Ar.JetMain.jets <;> assumption)
