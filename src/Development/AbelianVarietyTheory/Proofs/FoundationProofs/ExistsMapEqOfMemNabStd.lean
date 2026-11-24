module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (AddMonoidAlgebra.coeff F mo) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : AddMonoidAlgebra.coeff F mo = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * AddMonoidAlgebra.coeff F mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := by
      have h1 := congrArg (AddMonoidAlgebra.coeff · mo) hQ
      rw [MvPolynomial.coeff_smul] at h1
      have h2 : AddMonoidAlgebra.coeff (toK K _ Q) mo = ((AddMonoidAlgebra.coeff Q mo : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (AddMonoidAlgebra.coeff Q mo)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
