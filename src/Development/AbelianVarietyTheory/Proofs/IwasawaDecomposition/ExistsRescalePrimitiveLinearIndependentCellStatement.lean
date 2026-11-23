module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCell
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

theorem _root_.GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | exact GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | (intros; apply GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim <;> assumption)
