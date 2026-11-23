module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.rootW_of :
    UpperTheory.Gal.W2.RootSumW → UpperTheory.Gal.W2.RootSumWOff → ListsEx → SchWEq → RootW := by
  intro hW hOff hL hS F _ _ n t₀ ε lam h hconj hexp
  rcases hexp with ⟨m, hm, hh⟩ | ⟨m, hm, hh⟩
  · obtain ⟨k₀, hk⟩ := hW F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep _ _ y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
  · obtain ⟨k₀, hk⟩ := hOff F n t₀ ε lam m hconj hm
    refine ⟨k₀, fun k hk' => ?_⟩
    obtain ⟨c, hc, hsum⟩ := hk k hk'
    refine ⟨c, hc, ?_⟩
    intro χ hdeg hsep h0 hq y
    obtain ⟨g, hg⟩ := hL F n χ hdeg
    rw [hsum χ g hsep hg h0 hq y, hS F n lam χ g hg]
    simp only [hh, pow_add, Finset.mul_sum]
