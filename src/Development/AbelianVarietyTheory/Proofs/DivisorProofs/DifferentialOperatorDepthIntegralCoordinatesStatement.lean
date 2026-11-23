module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
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

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.differentialOperatorDepth_integral_coordinates : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ MvIsInt v (Ψ a) ∧ constantCoeff (Ψ a) = 0) → (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) → ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) → (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) → detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C // MvIsInt v f}, toE (v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f.1))) := by
  first | exact @GlobalTheory.FGDepth.Coord.depth_in_coords | exact GlobalTheory.FGDepth.Coord.depth_in_coords | (intros; apply GlobalTheory.FGDepth.Coord.depth_in_coords <;> assumption)
