module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannRelationsRationalCombinationFrame
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.riemannRelations_rationalCombinationFrame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  first | exact @GlobalTheory.PeriodFrame.riemann_relations_frame | exact GlobalTheory.PeriodFrame.riemann_relations_frame | (intros; apply GlobalTheory.PeriodFrame.riemann_relations_frame <;> assumption)
