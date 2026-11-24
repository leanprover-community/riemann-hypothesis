module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerFderivKAveragedMinorOperatorIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

theorem _root_.GlobalTheory.T.inner_fderiv_kAveragedMinorOperator_integral : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ z ∈ U1 ε, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (y x : W), Integrable (fun k : KG ε => fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ)) (muK ε) ∧ ⟪y, fderiv ℂ (ps ε lam τ w) z A x⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, fderiv ℂ (Phi lam) ((toMK k)⁻¹ * z * toMK k) ((toMK k)⁻¹ * A * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, x⟫_ℂ) ∂(muK ε) := by
  first | exact @GlobalTheory.SphJet.PsDer.inner_fderiv_ps | exact GlobalTheory.SphJet.PsDer.inner_fderiv_ps | (intros; apply GlobalTheory.SphJet.PsDer.inner_fderiv_ps <;> assumption)
