module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCurvatureFormSelfEqDualNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram

@[expose] public section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem _root_.GlobalTheory.T.chernCurvature_form_self_eq_dual_norm : ∀ (n g : ℕ) (H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ), MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → (∀ᶠ x in 𝓝 z, (H x).IsHermitian) → (∀ ξ η, mddbar H z ξ η = 0) → ∀ ξ v, form (H z) (curv H z ξ ξ *ᵥ v) v = form (H z)⁻¹ (mdel H z ξ *ᵥ v) (mdel H z ξ *ᵥ v) := by
  first | exact @GlobalTheory.CurvForm.form_curv_self_eq | exact GlobalTheory.CurvForm.form_curv_self_eq | (intros; apply GlobalTheory.CurvForm.form_curv_self_eq <;> assumption)
