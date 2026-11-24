module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
public import GroundTheory.AutomorphicForms.FourierWhittaker.UMatColXEqFromBlocks
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurComplementExtensionFunctionBlockDiagApply
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
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.schurComplementExtensionFunction_blockDiag_apply : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), ∀ h : GA E (m + 1), schurF β b₁ χ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h * b₁ 1 * (χ 0 : ℂ) := by
  first | (exact @GlobalTheory.SchurExt.schurF_blockGL) | (exact GlobalTheory.SchurExt.schurF_blockGL) | (intros; apply GlobalTheory.SchurExt.schurF_blockGL  <;> assumption)
