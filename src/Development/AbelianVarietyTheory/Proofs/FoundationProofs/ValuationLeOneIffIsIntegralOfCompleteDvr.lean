module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvrStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSpectralValuationAlgebraicExtensionStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

@[expose] public section

open scoped NNReal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_iff_isIntegral_of_complete_dvr :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field Ω] [Algebra R Ω]
      [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) →
      ∃ v : Valuation Ω ℝ≥0, ∀ x : Ω, v x ≤ 1 ↔ IsIntegral R x := by
  intro R Ω _ _ _ _ _ _ _ hinj
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr hinj
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective R (FractionRing R))
  obtain ⟨f, hna, hnt, hball, hcomp⟩ := GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr R (FractionRing R)
  obtain ⟨v, -, hv⟩ := GlobalTheory.T.exists_spectral_valuation_algebraic_extension (FractionRing R) Ω f hna hnt hcomp
  refine ⟨v, fun x => ?_⟩
  rw [hv]
  simp only [hball]
  constructor
  · intro h
    have hl : minpoly (FractionRing R) x ∈ Polynomial.lifts (algebraMap R (FractionRing R)) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr h
    obtain ⟨q, hq, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hmon, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (FractionRing R), hq]
    exact minpoly.aeval _ _
  · intro h i
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (FractionRing R) h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩

end GlobalTheory
