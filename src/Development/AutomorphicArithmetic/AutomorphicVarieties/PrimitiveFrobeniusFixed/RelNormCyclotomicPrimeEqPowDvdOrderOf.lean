module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.relNorm_cyclotomic_prime_eq_pow_dvd_orderOf :
    ∀ (N r : ℕ) [NeZero N] (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K'], r.Prime → ¬ r ∣ N → ∀ (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K')), (r : 𝓞 K') ∈ v'.asIdeal → (∀ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 K') y ∈ v'.asIdeal ↔ y ∈ v.asIdeal) → ∃ s : ℕ, s ∣ orderOf (r : ZMod N) ∧ Ideal.relNorm (𝓞 K) v'.asIdeal = v.asIdeal ^ s := by
  intro N r _ K K' _ _ _ _ _ _ hp hN v v' hr hvv
  have : Fact r.Prime := ⟨hp⟩
  have hvp : v'.asIdeal.IsPrime := v'.isPrime
  have hm : v.asIdeal.IsMaximal := v.isMaximal
  have hm' : v'.asIdeal.IsMaximal := v'.isMaximal
  have hmax : (Ideal.span {(r : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hlo : v'.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hr
  have hl2 : v'.asIdeal.LiesOver v.asIdeal := ⟨by
    ext y
    rw [Ideal.under_def, Ideal.mem_comap]
    exact (hvv y).symm⟩
  have h3 := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal v'.asIdeal
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K' v'.asIdeal hN] at h3
  refine ⟨v'.asIdeal.inertiaDeg (𝓞 K), ?_, ?_⟩
  · rw [h3]; exact Dvd.intro_left _ rfl
  · exact Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal v.asIdeal
