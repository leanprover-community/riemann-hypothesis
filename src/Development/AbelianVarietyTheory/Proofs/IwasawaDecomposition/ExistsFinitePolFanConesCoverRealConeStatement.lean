module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinitePolFanConesCoverRealCone
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_finite_polFanCones_cover_realCone : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N p : ℕ) (P : Fin p → LinearMap.BilinForm ℤ X), IsPolFanOn (id : ℤ → ℤ) φ X → (∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u) → (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) → ∃ (s : ℕ) (m : Fin s → ℕ) (u : ∀ k, Fin (m k) → LinearMap.BilinForm ℤ X) (w : Fin s → (X × X) →₀ ℤ), (∀ k, IsCone (id : ℤ → ℤ) φ (u k) ∧ StrictWith (id : ℤ → ℤ) φ N (linW (w k)) (u k)) ∧ ∀ B ∈ rcone P, B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) → ∃ k, B ∈ rcone (u k) := by
  first | exact @GlobalTheory.PolCell.exists_finite_cover_rcone | exact GlobalTheory.PolCell.exists_finite_cover_rcone | (intros; apply GlobalTheory.PolCell.exists_finite_cover_rcone <;> assumption)
