module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

theorem OrdPolynomialLocalization.comap_C_map_C {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R) (Ideal.map (C : R →+* MvPolynomial σ R) p) = p := by
  classical
  ext r
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h m
    rw [coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

theorem OrdPolynomialLocalization.proof : OrdPolynomialLocalization.Statement := by
  intro R _ σ p _ _ x
  set P := Ideal.map (C : R →+* MvPolynomial σ R) p with hPdef
  have : P.LiesOver p := ⟨by
    rw [Ideal.under, MvPolynomial.algebraMap_eq, hPdef]
    exact (OrdPolynomialLocalization.comap_C_map_C σ p).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p P
  set A := Localization.AtPrime p
  set B := Localization.AtPrime P
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R (MvPolynomial σ R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (MvPolynomial σ R) B, ← Ideal.map_map, MvPolynomial.algebraMap_eq,
      ← hPdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ Ideal.span {algebraMap R A x})
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (Ideal.span {algebraMap R A x})).toLinearEquiv.length_eq, Ideal.map_span,
    Set.image_singleton, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (MvPolynomial σ R) B, MvPolynomial.algebraMap_eq] at key
  exact key

end GroundTheory.Heights₂.Heights
