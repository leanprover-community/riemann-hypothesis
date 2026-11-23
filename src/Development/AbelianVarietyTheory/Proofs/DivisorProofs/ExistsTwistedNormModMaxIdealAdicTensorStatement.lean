module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmallB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) →
    ∀ θ : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑θ → IsIntB v bL ↑θ⁻¹ →
    Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑θ = -↑θ →
    ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e →
    IsIntB v bL ↑e → IsIntB v bL ↑e⁻¹ →
    ∃ z : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL z ∧
      IsSmallB v bL (z * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c z - ↑e) := by
  first | (exact @GlobalTheory.ResidueNorm.exists_norm_mod_small) | (exact GlobalTheory.ResidueNorm.exists_norm_mod_small) | (intros; apply GlobalTheory.ResidueNorm.exists_norm_mod_small  <;> assumption)
