module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.congrRad_of :
    CongrRad := by
  intro R _ 𝔞 h𝔞 ι N N' H B' _ g hg
  have key : ∀ (a : ℕ) (m : ι →₀ ℕ),
      AddMonoidAlgebra.coeff (N.coeff a) m - AddMonoidAlgebra.coeff (N'.coeff a) m ∈ 𝔞 := by
    intro a m
    rw [← h𝔞.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔭 h𝔭
    obtain ⟨κ, _, f, hker, hf⟩ := H 𝔭 h𝔭
    rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
    have := congrArg (fun p => AddMonoidAlgebra.coeff (p.coeff a) m) hf
    simpa [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map] using this
  refine Polynomial.ext fun a => MvPolynomial.ext _ _ fun m => ?_
  simp only [mapP, Polynomial.coeff_map, MvPolynomial.coeff_map]
  rw [← sub_eq_zero, ← map_sub]
  exact hg _ (key a m)
