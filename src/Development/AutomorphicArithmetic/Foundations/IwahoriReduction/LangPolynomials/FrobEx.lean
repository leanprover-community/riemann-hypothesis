module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem frobEx_norm {l : ℕ} (hl : l.Prime) {v : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : normV v = l := by
  haveI : Fact l.Prime := ⟨hl⟩
  let e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = v.asIdeal.map (e : 𝓞 ℚ →+* ℤ) := by
    have hmax : (Ideal.span {((l : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
    apply hmax.eq_of_le
    · intro htop
      apply v.isPrime.ne_top
      exact (Ideal.map_eq_top_of_bijective _ e.bijective).1 htop
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have := Ideal.mem_map_of_mem (e : 𝓞 ℚ →+* ℤ) hv
      simpa using this
  unfold normV
  rw [Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ e hJ).toEquiv,
    Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]

theorem UpperTheory.Kd.C7.pFrobEx :
    UpperTheory.Kd.C7.SFrobEx := by
  intro l _ _ Ω _ _ _ A hA
  obtain ⟨v, hv, hlv⟩ := hA
  have hnorm : normV v = l := frobEx_norm Fact.out hlv
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  refine ⟨?_, fun σ _ σ' _ hσ hσ' => inv_mul_mem_Ine_of_isFrob hσ hσ',
    GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob (F := ℚ) hv
  rw [hnorm] at hσ
  obtain ⟨ι, hι, hιu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hval (cycZ ℚ Ω l σ)⁻¹
  have hfr : IsFrob A l (σ * ι) := isFrob_mul_of_mem_Ine hσ hι
  refine ⟨σ * ι, hfr.1, hfr, ?_⟩
  unfold cycBar
  rw [MonoidHom.comp_apply, map_mul, hιu, mul_inv_cancel, map_one]
