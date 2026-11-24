module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FubiniCutoffIntegralGeneralLinearTorus
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.fubini_cutoff_integral_generalLinear_torus : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  first | exact @GlobalTheory.JR.LinDesc.fubini_cutoff | exact GlobalTheory.JR.LinDesc.fubini_cutoff | (intros; apply GlobalTheory.JR.LinDesc.fubini_cutoff <;> assumption)
