module

public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdeleIdemPrimeCriterion
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.isPrimeIdem_eq_indicator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  intro F E _ _ _ _ _ σ Φ hΦ hint hplace P e f hprime
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem at hprime
  rcases hprime with ⟨hat, -⟩ | ⟨-, ⟨v, ε, hε, rfl⟩, hcrit⟩
  · unfold _root_.HeckeCharacterZeroLocus.ThmBIn.IsIdemAt _root_.HeckeCharacterZeroLocus.ThmBIn.IsSplitIdem at hat
    obtain ⟨⟨he, hce, v, ε, hε, hsum⟩, hcrit⟩ := hat
    have heε : e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e := by
      rw [← hsum, mul_add, he, hce, add_zero]
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace e P v ε hε he heε).mp hcrit
  · obtain ⟨h0, hind⟩ := hplace v ε hε
    have he : algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε =
        algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε := by
      apply Φ.injective
      rw [map_mul]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_mul, h0, mul_zero]
      · ext Q : 1
        change (Φ _).2 Q * (Φ _).2 Q = (Φ _).2 Q
        rw [hind Q]
        split_ifs <;> simp
    exact (_root_.GlobalTheory.adele_idem_prime_criterion F E Φ hΦ hint hplace _ P v ε hε he he).mp hcrit

end GlobalTheory
