module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbCyc
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
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Formalism.ConjugateSelfDual.Statement
import Formalism.GaloisCohomology.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem totient_prime_pow_add_le_pow_mul_totient (l : ℕ) (hl : l.Prime) (n k : ℕ) :
    (l ^ (n + k)).totient ≤ l ^ k * (l ^ n).totient := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Nat.totient_le (l ^ k)
  · rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl hn]
    have : n + k - 1 = k + (n - 1) := by omega
    rw [this, pow_add, mul_assoc]

theorem UpperTheory.V.FW.embed :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K], ∃ f D : ℕ, f.Coprime l ∧ 1 < f ∧ ∀ (n n₀ : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'], ∃ (m : ℕ) (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K' L) (_ : IsCyclotomicExtension {f * l ^ m} ℚ L), n₀ ≤ m ∧ Module.finrank K' L ≤ D * l ^ n₀ := by
  intro l hl K _ _ _
  have hp : l.Prime := hl.out
  obtain ⟨N, hN, ⟨φ⟩⟩ := CF.kwHom K
  obtain ⟨e, f₀, hf₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hp.one_lt.ne'
  have hf₀c : f₀.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hf₀).symm
  have hf₀pos : 0 < f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · simp [h] at hN
    · exact h
  have hlc : (l + 1).Coprime l := by
    simp
  refine ⟨f₀ * (l + 1), f₀ * (l + 1) * l ^ e, Nat.Coprime.mul_left hf₀c hlc, ?_, ?_⟩
  · have : 1 < l + 1 := by have := hp.one_lt; omega
    calc 1 < l + 1 := this
      _ ≤ f₀ * (l + 1) := Nat.le_mul_of_pos_left _ hf₀pos
  intro n n₀ K' _ _ _ _
  set m := n + (e + n₀) with hm
  set M := f₀ * (l + 1) * l ^ m with hM
  have hMpos : 0 < M := by
    have := hp.pos
    positivity
  haveI : NeZero M := ⟨hMpos.ne'⟩
  let L := CyclotomicField M K'
  haveI : Module.Finite K' L := IsCyclotomicExtension.finite {M} K' L
  haveI : NumberField L := NumberField.of_module_finite K' L
  have hdvdN : l ^ e * f₀ ∣ M := by
    refine ⟨(l + 1) * l ^ (n + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hdvdm : l ^ n ∣ M := by
    refine ⟨f₀ * (l + 1) * l ^ (e + n₀), ?_⟩
    rw [hM, hm]
    ring
  have hcyc : IsCyclotomicExtension {M} ℚ L :=
    embCyc (l ^ e * f₀) (l ^ n) M K K' L hdvdN hdvdm ⟨φ⟩
  refine ⟨m, L, inferInstance, inferInstance, inferInstance, hcyc, by omega, ?_⟩
  have hL : Module.finrank ℚ L = M.totient := IsCyclotomicExtension.Rat.finrank M L
  have hlnpos : 0 < l ^ n := pow_pos hp.pos n
  have hK' : (l ^ n).totient ≤ Module.finrank ℚ K' := by
    have hz := IsCyclotomicExtension.zeta_spec (l ^ n) K K'
    have h1 := Polynomial.cyclotomic_eq_minpoly_rat hz hlnpos
    have h2 := minpoly.natDegree_le (A := ℚ) (IsCyclotomicExtension.zeta (l ^ n) K K')
    rw [← h1, Polynomial.natDegree_cyclotomic] at h2
    exact h2
  have htow := Module.finrank_mul_finrank ℚ K' L
  have htot : M.totient ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
    have hco : (f₀ * (l + 1)).Coprime (l ^ m) := (Nat.Coprime.mul_left hf₀c hlc).pow_right m
    rw [hM, Nat.totient_mul hco]
    calc (f₀ * (l + 1)).totient * (l ^ m).totient ≤ f₀ * (l + 1) * (l ^ m).totient :=
          Nat.mul_le_mul_right _ (Nat.totient_le _)
      _ ≤ f₀ * (l + 1) * (l ^ (e + n₀) * (l ^ n).totient) :=
          Nat.mul_le_mul_left _ (totient_prime_pow_add_le_pow_mul_totient l hp n (e + n₀))
      _ = f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := by
          rw [pow_add]
          ring
  have htpos : 0 < (l ^ n).totient := Nat.totient_pos.2 hlnpos
  refine Nat.le_of_mul_le_mul_right ?_ htpos
  calc Module.finrank K' L * (l ^ n).totient ≤ Module.finrank K' L * Module.finrank ℚ K' :=
        Nat.mul_le_mul_left _ hK'
    _ = M.totient := by rw [mul_comm, htow, hL]
    _ ≤ f₀ * (l + 1) * l ^ e * l ^ n₀ * (l ^ n).totient := htot
