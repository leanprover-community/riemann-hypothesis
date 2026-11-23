module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt
public import GroundTheory.AutomorphicForms.Satake
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

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.symEx_pf :
    UpperTheory.Gal.Gen.SymEx := by
  intro n Φ
  refine ⟨polyEmb (n := n) (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩
  · show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _
    intro τ
    rw [← polyEmb_rename]
    congr 1
    rw [map_prod]
    simp_rw [MvPolynomial.rename_rename]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  · intro z
    rw [evalAt_polyEmb, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [MvPolynomial.aeval_rename]
    rfl
  · intro hΦ
    refine ⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro σ _ h
      apply hΦ
      exact MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])
    · rw [evalAt_polyEmb]
      rfl
