module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlaces
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.fixed_unit_eq_norm_almost_all_places : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  first | (exact @GlobalTheory.LocNorm.unit_fixed_is_norm) | (exact GlobalTheory.LocNorm.unit_fixed_is_norm) | (intros; apply GlobalTheory.LocNorm.unit_fixed_is_norm  <;> assumption)
