module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMonicPolynomialOfUnitRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNormEtale

theorem exists_eq_sq_sub_mul_sq : ∀ (L : Type) [CommRing L] [IsReduced L] [Algebra ℚ L] [FiniteDimensional ℚ L] (v : IsDedekindDomain.HeightOneSpectrum ℤ), v.asIdeal ≠ Ideal.span {2} →
    ∀ m m' d d' : v.adicCompletion ℚ ⊗[ℚ] L, m * m' = 1 → d * d' = 1 →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m' f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d' f = 0) →
    ∃ a b : v.adicCompletion ℚ ⊗[ℚ] L, m = a * a - d * (b * b) := by
  intro L _ _ _ _ v hv m m' d d' hm hd im im' id id'
  obtain ⟨hH, hF⟩ := GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField v
  letI : Algebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) :=
    ((algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)).comp
      (v.adicCompletionIntegers ℚ).subtype).toAlgebra
  have key : ∀ x : v.adicCompletion ℚ ⊗[ℚ] L,
      (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧
        (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) →
      IsIntegral (v.adicCompletionIntegers ℚ) x := by
    rintro x ⟨f, hf, hc, hx⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := (v.adicCompletionIntegers ℚ).subtype)
      ((Polynomial.lifts_iff_coeff_lifts f).2 fun n => ⟨⟨_, hc n⟩, rfl⟩) hf
    refine ⟨g, hgm, ?_⟩
    rw [← hg, Polynomial.aeval_def, Polynomial.eval₂_map] at hx
    exact hx
  have h2 : (2 : ℤ) ∉ v.asIdeal := fun h =>
    hv ((PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible).eq_of_le
      v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2u : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := valuedAdicCompletion_eq_valuation' v (2 : ℚ)
    have h' : v.valuation ℚ (2 : ℚ) = 1 := by
      have := (valuation_eq_one_iff_notMem v (K := ℚ) (r := (2 : ℤ))).2 h2
      simpa using this
    rw [h'] at h
    rw [← h]
    congr 1
    exact (map_ofNat (algebraMap ℚ (v.adicCompletion ℚ)) 2).symm
  exact GlobalTheory.OddLocalNorm.exists_eq_of_isIntegral (v.adicCompletionIntegers ℚ) h2u hm hd
    (key _ im) (key _ im') (key _ id) (key _ id')

end GlobalTheory.OddLocalNormEtale
