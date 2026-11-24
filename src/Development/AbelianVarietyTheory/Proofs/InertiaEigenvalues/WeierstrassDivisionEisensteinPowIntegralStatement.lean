module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionEisensteinPowIntegral
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

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.weierstrass_division_eisensteinPow_integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  first | exact @GlobalTheory.weierstrassDiv_E_pow | exact GlobalTheory.weierstrassDiv_E_pow | (intros; apply GlobalTheory.weierstrassDiv_E_pow <;> assumption)
