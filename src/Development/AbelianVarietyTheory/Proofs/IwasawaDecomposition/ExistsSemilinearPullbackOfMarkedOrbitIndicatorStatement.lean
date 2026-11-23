module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
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

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one <;> assumption)
