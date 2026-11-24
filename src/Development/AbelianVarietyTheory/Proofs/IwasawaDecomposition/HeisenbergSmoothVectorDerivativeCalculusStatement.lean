module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

theorem _root_.GlobalTheory.T.heisenbergSmoothVector_derivative_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  first | exact @GlobalTheory.Mem.Lift.DCalc.dH_calculus | exact GlobalTheory.Mem.Lift.DCalc.dH_calculus | (intros; apply GlobalTheory.Mem.Lift.DCalc.dH_calculus <;> assumption)
