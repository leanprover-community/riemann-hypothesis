module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtOfContinuousHom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WirtingerCombinationNeZero
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

namespace PositivityTheory.Rg.Cz

theorem hasDerivAt_of_mulHom (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) (hm : ∀ s t, χ (s + t) = χ s * χ t) :
    ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t :=
  GlobalTheory.CompanionTheory.CharDeriv.hasDerivAt_of_continuous_hom χ hc h0 hm

theorem wirtinger_ne_zero (χ : ℂ → ℂ) (hc : Continuous χ) (hm : ∀ z w, χ (z + w) = χ z * χ w) (hn : ∀ z, ‖χ z‖ = 1)
    (ht : ∃ z, χ z ≠ 1) (D : ℂ → ℂ) (hD : ∀ z, HasDerivAt (fun t : ℝ => χ (t * z)) (D z) 0) (β : ℂ) (hβ : β ≠ 0) :
    D β - Complex.I * D (β * Complex.I) ≠ 0 :=
  GlobalTheory.CompanionTheory.Unitary.wirtinger_combination_ne_zero χ hc hm hn ht D hD β hβ

end PositivityTheory.Rg.Cz
