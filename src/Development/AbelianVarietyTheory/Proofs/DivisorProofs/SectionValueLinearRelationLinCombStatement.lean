module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueLinearRelationLinComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

theorem _root_.GlobalTheory.T.sectionValue_linear_relation_linComb : ∀ {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)),
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c → ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y'),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ₁ j₁ → ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂ →
    valR y (LB.wchart L φ₁ j₁) (s₁.f j₁) = ∑ i, valR y ⊤ (c i) * valR (y ≫ h) (LB.wchart L φ₂ j₂) ((s₂ i).f j₂) := by
  first | exact @GlobalTheory.MBLow.TanGauge.valR_secLin | exact GlobalTheory.MBLow.TanGauge.valR_secLin | (intros; apply GlobalTheory.MBLow.TanGauge.valR_secLin <;> assumption)
