module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerDerivativeTranslate
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

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.derivative_right_translate_L2 :
    UpperTheory.V.Lit.Bor.DerivativeRightTranslateL2 := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder
  have hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2 :=
    (GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc
  have hI := hf.integral_hasStrictDerivAt 0 0
  have hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) =
      fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2 := by
    funext t
    rw [← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]
    abel
  rw [hE]
  have h := hI.hasDerivAt.add_const hφ.toL2
  simpa [hc0] using h
