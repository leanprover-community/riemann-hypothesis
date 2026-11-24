module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvIntegralSqDiscreteSeriesCoefficientCompactDua
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | exact GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq | (intros; apply GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq <;> assumption)
