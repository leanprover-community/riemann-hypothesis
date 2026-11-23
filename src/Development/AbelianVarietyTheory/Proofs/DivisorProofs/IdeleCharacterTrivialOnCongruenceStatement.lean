module

public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterTrivialOnCongruence
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK


theorem _root_.GlobalTheory.T.idele_character_trivial_on_congruence : ∀ (F : Type) [Field F] [NumberField F] (φ : (AdeleRing (𝓞 F) F)ˣ →* Circle),
    Continuous φ → (∀ b, φ b = 1 ∨ φ b = -1) → (∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → φ b = 1) →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (b : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      φ b = 1 := by
  first | exact @GlobalTheory.HeckeSignLevel.sign_char_trivial_on_congruence | exact GlobalTheory.HeckeSignLevel.sign_char_trivial_on_congruence | (intros; apply GlobalTheory.HeckeSignLevel.sign_char_trivial_on_congruence <;> assumption)
