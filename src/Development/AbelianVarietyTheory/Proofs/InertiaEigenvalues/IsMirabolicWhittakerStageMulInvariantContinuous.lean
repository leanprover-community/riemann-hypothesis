module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory.GoodMul

theorem good_mul_invariant : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ) (ψ : AddChar (Ad E) ℂ) (f c : GA E a → ℂ),
    Good ψ m f → Continuous c → (∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, c (ratGL E a γ * g) = c g) →
    (∀ (r l : ℕ) (y : UnipotentBlockColumnIndex a r l → Ad E) (g : GA E a), c (blkU y * g) = c g) → Good ψ m (fun g => c g * f g) := by
  intro E _ _ a m ψ f c hf hc hl hu
  refine ⟨hc.mul hf.cont, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hrm g => ?_⟩
  · show c _ * f _ = c g * f g
    rw [hl γ hγ g, hf.left γ hγ g]
  · show c _ * f _ = _ * (c g * f g)
    rw [hu k k y g, hf.law k hk y g]; ring
  · have h : (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) =
        fun x => c g * f (blkU x * g) := by
      funext x; rw [hu r m x g]
    show avg _ (fun x : UnipotentBlockColumnIndex a r m → Ad E => c (blkU x * g) * f (blkU x * g)) = 0
    rw [h, avg_const_mul, hf.van r hr hrm g, mul_zero]

end GlobalTheory.GoodMul
