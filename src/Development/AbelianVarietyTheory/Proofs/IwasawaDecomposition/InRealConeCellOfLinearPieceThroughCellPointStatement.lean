module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfLinearPieceThroughCellPoint
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) := by
  first | exact @GlobalTheory.PolFan.inRCone_of_interior_linearOn' | exact GlobalTheory.PolFan.inRCone_of_interior_linearOn' | (intros; apply GlobalTheory.PolFan.inRCone_of_interior_linearOn' <;> assumption)
